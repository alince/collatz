/-
  CollatzFormal/Wave18WholeSpaceCore.lean
  Wave 18 Whole-Space Mathematical & CS Proof Loop (Core — Fronts A & B):
  1. Front A — All-Dimension (`∀ d ≥ 1`) Dual `.B`-Top-Row + `.T`-Subdiagonal Cascade Collapse
     (`12` Active `.T` Symbols on `c39`, `24` Active `.T` Symbols on `c78`, `26/39` `d = 2` Strict
     Matrix Rules) & Universal `GenOmegaDualBTopRowAndTSubdiagMatTower` Impossibility on `c39` & `c78`,
     Infinite 5-Parameter `d = 3` (`3 × 3`) Block-Nilpotent Cross-Channel `.B` + `.T` + `.R` Mixed
     Zero-Diagonal Cones (`rank2BlockNilpMat3DC39` & `rank2BlockNilpMat3DC78`, Strictly Orienting
     `37/39` and `74/78` Rules While Escaping `μ_0`-Only and Wave 17 Row-1/Row-2 Farkas Syzygies
     by `+10`) Locked by 3-Channel `(μ_0, β * μ_1, α * μ_2)` Bilinear Farkas Syzygies,
     & Unconditional `1..25`-Cycle Freedom Across ALL `DP2` Words + Infinite Parametric `m`-Block
     (`∀ m ≥ 2`) `.R`-Carrying `leftAnchoredDP2Step` Cycle Exclusions (`W18_H1`, Branch P4.3)
  2. Front B — General-`u` (`∀ u ≥ 1`) Rectangular `(U * T) × (U * T)` Unreduced `Nat.Coprime`
     Biconditional (`u = 1 ∧ ∀ 1 ≤ d < U, Nat.Coprime W d`), Bounded Overlap `gcd ∣ gcd(2^u - 1, W)`,
     & Infinite Odd-`u` Exact Primitive-Row `Nat.lcm = colFac * ((2^(W * u) - 1) / (2^u - 1))^(T * (U - T))`
     Product Law + `12 × 12` `(U = 4, T = 3, W = 5, K = 8, u = 3)` Odd-`u` `gcd = 343` Certificate,
     Rank-3 Order-4 `12 × 12` `(T = 4, U = 3)` `(5, 8)` `u = 2 > 0` vs `u = 5 < 0` Cone Sign-Flip,
     Global Zero-Free Non-Vanishing Across ALL `W, K ≥ 1` for `u ∈ {2, 3, 4, 5}` via Projective
     `P^1(F_p)` Sieves (`p = 67, 59, 59, 13`), Universal `∀ u ≥ 1` `2`-Adic Matrix Congruence
     `det_12(W, K, u) ≡ 2^(4 * u) * 3^(18 * u) * K^18 (mod 2^(5 * u))`, & Finite Multi-`u`
     Zero-Horizon `2^((u + 17) / 18) ≤ K / Nat.gcd W K`,
     & Universal Symbolic All-`m` (`∀ m ≥ 2`) `(m - 1)`-Pivot Closed-Form Brox Squeeze + `m = 7`
     Balanced (`> 94×`) & Convergent `(W = 41, K = 65)` Hensel (`105 * D`, `> 2×`) Eliminations
     (`W18_H2`, Branches P3.2–P3.4)

  Zero `sorry`, zero `native_decide`, zero custom axioms.
-/

import CollatzFormal.Wave17WholeSpace

namespace CollatzFormal

-- ============================================================================
-- SECTION 1: Front A (Branch P4.3) — All-Dimension Dual `.B`-Top-Row + `.T`-Subdiagonal
--            Cascade Collapse, 5-Parameter `d = 3` Block-Nilpotent Cross-Channel Cones
--            & 3-Channel Farkas Locks, & Unconditional `1..25`-Cycle Freedom +
--            Infinite Parametric `m`-Block `.R`-Carrying `DP2` Exclusions (`W18_H1`)
-- ============================================================================

private theorem mul_pow_w18c (a b : Nat) : ∀ n : Nat, (a * b) ^ n = a ^ n * b ^ n
  | 0 => rfl
  | n + 1 => by
    rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, mul_pow_w18c a b n]
    ac_rfl

private theorem pow_mono_base_w18c (a b : Nat) (hle : a ≤ b) : ∀ n : Nat, a ^ n ≤ b ^ n
  | 0 => Nat.le_refl 1
  | n + 1 => Nat.mul_le_mul (pow_mono_base_w18c a b hle n) hle

private def toFinWordW18 (N : Nat) (hN : N ≥ 1) : List Nat -> List (Fin N)
  | [] => []
  | x :: xs => (if h : x < N then ⟨x, h⟩ else ⟨0, hN⟩) :: toFinWordW18 N hN xs

private def toFinRulesW18 (N : Nat) (hN : N ≥ 1) :
    List (List Nat × List Nat) -> List (List (Fin N) × List (Fin N))
  | [] => []
  | (l, r) :: rs => (toFinWordW18 N hN l, toFinWordW18 N hN r) :: toFinRulesW18 N hN rs

private def c39RawRulesW18 : List (List Nat × List Nat) :=
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

private def c78RawRulesW18 : List (List Nat × List Nat) :=
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

private def c39FastRulesW18 : List (List (Fin 42) × List (Fin 42)) :=
  toFinRulesW18 42 (by decide) c39RawRulesW18

private def c78FastRulesW18 : List (List (Fin 84) × List (Fin 84)) :=
  toFinRulesW18 84 (by decide) c78RawRulesW18

private theorem toFinWordW18_map_val (N : Nat) (hN : N ≥ 1) :
    ∀ (xs : List Nat), xs.all (fun x => Nat.ble (x + 1) N) = true ->
      (toFinWordW18 N hN xs).map Fin.val = xs
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.all_cons] at h
    cases hx_b : Nat.ble (x + 1) N
    · rw [hx_b] at h; cases h
    · rw [hx_b, Bool.true_and] at h
      have hx : x < N := Nat.ble_eq.mp hx_b
      simp only [toFinWordW18, hx, dite_true, List.map_cons, toFinWordW18_map_val N hN xs h]

set_option maxRecDepth 65536 in
private theorem c39_beq_fastRules_w18 :
    (filterFinParikhUnoriented 42 wtTwoSidedMod3OmitR3
      (twoSidedLabelledCollatzRules 3 (by decide) all11OmitR3List) == c39FastRulesW18) = true := by decide

private theorem c39_eq_fastRules_w18 :
    filterFinParikhUnoriented 42 wtTwoSidedMod3OmitR3
      (twoSidedLabelledCollatzRules 3 (by decide) all11OmitR3List) = c39FastRulesW18 :=
  beq_iff_eq.mp c39_beq_fastRules_w18

set_option maxRecDepth 65536 in
private theorem c78_beq_fastRules_w18 :
    (filterFinParikhUnoriented 84 wtTwoSidedMod6OmitR3
      (twoSidedLabelledCollatzRules 6 (by decide) all11OmitR3List) == c78FastRulesW18) = true := by decide

private theorem c78_eq_fastRules_w18 :
    filterFinParikhUnoriented 84 wtTwoSidedMod6OmitR3
      (twoSidedLabelledCollatzRules 6 (by decide) all11OmitR3List) = c78FastRulesW18 :=
  beq_iff_eq.mp c78_beq_fastRules_w18

-- ----------------------------------------------------------------------------
-- Section 1A: All-Dimension (`∀ d ≥ 1`) Dual `.B`-Top-Row + `.T`-Subdiagonal
--             Cascade Collapse & Universal `GenOmegaDualBTopRowAndTSubdiagMatTower`
--             Impossibility on `c39` & `c78`
-- ----------------------------------------------------------------------------

/-- Concrete `d = 2` dual `.B`-top-row + `.T`-subdiagonal + `.R`-boundary-growth matrix witness
    on `Fin 42` (`c39`, strictly orienting `26/39` matrix rules at `k = 2`):
    - `.R`: `(M_6..8)_{0,0} = k, (M_6..8)_{1,1} = 1`, `(M_9..11)_{0,0} = k`,
    - `.B` top-row off-diagonals: `(M_{20})_{0,1} = (M_{22})_{0,1} = (M_{23})_{0,1} = 1`,
    - `.T` subdiagonals: `(M_s)_{1,0} = 1` for `s ∈ {28, 29, 31, 32, 36, 37, 38}`. -/
def dualBTRSubMat2DC39 (k : Nat) (s : Fin 42) (i j : Fin 2) : Nat :=
  let sv := s.val
  if i.val == 0 && j.val == 0 then
    if Nat.ble 6 sv && Nat.ble sv 11 then k else 1
  else if i.val == 0 && j.val == 1 then
    if sv == 20 || sv == 22 || sv == 23 then 1 else 0
  else if i.val == 1 && j.val == 0 then
    if sv == 28 || sv == 29 || sv == 31 || sv == 32 || sv == 36 || sv == 37 || sv == 38 then 1 else 0
  else
    if Nat.ble 6 sv && Nat.ble sv 8 then 1 else 0

/-- Dual `k`-level `ω^k` Hofbauer–Waldmann natural matrix tower over `Fin (14 * M)` of dimension
    `d ≥ 1` in the **dual `.B`-top-row + `.T`-subdiagonal + arbitrary-`.R` stratum**:
    - Every symbol satisfies `(M_s)_{0,0} ≥ 1`,
    - `.L` (`s < 2 * M`) has `(M_s)_{0,0} = 1` and zero off-topleft entries
      (`(i ≥ 1 ∨ j ≥ 1) -> (M_s)_{i,j} = 0`),
    - `.B` (`4 * M ≤ s < 8 * M`) has **top-row upper zero-diagonal** `[[1, b_b^T], [0, 0]]`
      (`(M_b)_{0,0} = 1` and `i ≥ 1 -> (M_b)_{i,j} = 0`),
    - `.T` (`s ≥ 8 * M`) has **zero top-row off-diagonals with arbitrary subdiagonals AND arbitrary
      `(d - 1) × (d - 1)` lower-right blocks** `[[(M_t)_{0,0}, 0], [c_t, D_t]]`
      (`j ≥ 1 -> (M_t)_{0,j} = 0`, with arbitrary `(M_t)_{0,0} ≥ 1`, arbitrary `(M_t)_{i,0}`, and
      unrestricted `(M_t)_{i,j}` for `i, j ≥ 1`, including block-nilpotent, rank-2, and full-rank blocks!),
    - `.R` (`2 * M ≤ s < 4 * M`) has **completely arbitrary** `d × d` entries (`(M_r)_{0,0} ≥ 1`). -/
def GenOmegaDualBTopRowAndTSubdiagMatTower (M d : Nat) (hd : d ≥ 1) :
    Nat -> List (List (Fin (14 * M)) × List (Fin (14 * M))) -> Prop
  | 0, rules => rules = []
  | k + 1, rules =>
    rules = [] ∨
    ∃ (rem : List (List (Fin (14 * M)) × List (Fin (14 * M))))
      (mat : Fin (14 * M) -> Fin d -> Fin d -> Nat)
      (v : Fin (14 * M) -> Fin d -> Nat),
      (∀ s : Fin (14 * M), mat s ⟨0, hd⟩ ⟨0, hd⟩ ≥ 1) ∧
      (∀ s : Fin (14 * M), s.val < 2 * M ->
        mat s ⟨0, hd⟩ ⟨0, hd⟩ = 1 ∧
        ∀ (i j : Fin d), (i.val ≥ 1 ∨ j.val ≥ 1) -> mat s i j = 0) ∧
      (∀ s : Fin (14 * M), 4 * M ≤ s.val ∧ s.val < 8 * M ->
        mat s ⟨0, hd⟩ ⟨0, hd⟩ = 1 ∧
        ∀ (i j : Fin d), i.val ≥ 1 -> mat s i j = 0) ∧
      (∀ s : Fin (14 * M), s.val ≥ 8 * M ->
        ∀ j : Fin d, j.val ≥ 1 -> mat s ⟨0, hd⟩ j = 0) ∧
      (∀ r ∈ rules,
        (∀ i j : Fin d, evalFinWordMat (14 * M) d mat r.1 i j ≥ evalFinWordMat (14 * M) d mat r.2 i j) ∧
        (∀ i : Fin d, evalFinWordVec (14 * M) d mat v r.1 i ≥ evalFinWordVec (14 * M) d mat v r.2 i)) ∧
      (∀ r ∈ rules,
        ¬ (evalFinWordVec (14 * M) d mat v r.1 ⟨0, hd⟩ >
           evalFinWordVec (14 * M) d mat v r.2 ⟨0, hd⟩) ->
        r ∈ rem) ∧
      GenOmegaDualBTopRowAndTSubdiagMatTower M d hd k rem

private def dualCascadeC39W18 : List (Nat × Nat × Nat × Nat) :=
  [(1, 18, 2, 36), (2, 20, 2, 38), (36, 22, 20, 40), (38, 16, 13, 31),
   (38, 23, 20, 41), (40, 17, 16, 32), (40, 21, 23, 39), (31, 14, 18, 29),
   (32, 13, 18, 28), (28, 18, 22, 33), (29, 20, 22, 35), (33, 22, 17, 37)]

private def dualCascadeC78W18 : List (Nat × Nat × Nat × Nat) :=
  [(1, 36, 2, 72), (1, 39, 5, 75), (5, 38, 2, 74), (5, 41, 5, 77),
   (74, 31, 28, 61), (74, 34, 25, 64), (75, 43, 41, 79), (75, 46, 38, 82),
   (77, 44, 38, 80), (77, 47, 41, 83), (79, 42, 44, 78), (79, 45, 47, 81),
   (82, 32, 31, 62), (82, 35, 34, 65), (62, 25, 39, 55), (62, 28, 36, 58),
   (64, 26, 36, 56), (64, 29, 39, 59), (55, 36, 43, 66), (55, 39, 46, 69),
   (59, 38, 43, 68), (59, 41, 46, 71), (69, 43, 35, 73), (69, 46, 32, 76)]

private def inDualUnitSetBoolW18 (M : Nat) (acc : List Nat) (x : Nat) : Bool :=
  Nat.ble (x + 1) (2 * M) || (Nat.ble (4 * M) x && Nat.ble (x + 1) (8 * M)) || acc.any (· == x)

private def hasLen2RuleValsBoolW18 (N s1 s2 u1 u2 : Nat) :
    List (List (Fin N) × List (Fin N)) -> Bool
  | [] => false
  | ([a, b], [c, d]) :: rs =>
    (a.val == s1 && b.val == s2 && c.val == u1 && d.val == u2) ||
      hasLen2RuleValsBoolW18 N s1 s2 u1 u2 rs
  | _ :: rs => hasLen2RuleValsBoolW18 N s1 s2 u1 u2 rs

private def checkDualUnitCascadeBoolW18 (M : Nat)
    (rules : List (List (Fin (14 * M)) × List (Fin (14 * M))))
    (acc : List Nat) : List (Nat × Nat × Nat × Nat) -> Option (List Nat)
  | [] => some acc
  | (s1, s2, u1, u2) :: rest =>
    if inDualUnitSetBoolW18 M acc s1 && Nat.ble (4 * M) s2 && Nat.ble (s2 + 1) (8 * M) &&
       hasLen2RuleValsBoolW18 (14 * M) s1 s2 u1 u2 rules then
      checkDualUnitCascadeBoolW18 M rules (u1 :: u2 :: acc) rest
    else none

private def lhsLen2HeadLOrTBoolW18 (M : Nat) : List (Fin (14 * M)) -> Bool
  | [s1, _] => Nat.ble (s1.val + 1) (2 * M) || Nat.ble (8 * M) s1.val
  | _ => false

private def checkDualCollapseCertBoolW18 (M : Nat)
    (rules : List (List (Fin (14 * M)) × List (Fin (14 * M))))
    (casc : List (Nat × Nat × Nat × Nat))
    (syz : List Nat) : Bool :=
  match checkDualUnitCascadeBoolW18 M rules [] casc with
  | none => false
  | some finalAcc =>
    rules.all (fun r =>
      lhsLen2HeadLOrTBoolW18 M r.1 &&
      (r.1 ++ r.2).all (fun s =>
        Nat.ble (s.val + 1) (8 * M) || inDualUnitSetBoolW18 M finalAcc s.val)) &&
    checkPositiveParikhSyzygyFastBool (14 * M) rules syz

private def checkWeakMat2DRulesBoolW18 (N : Nat) (mat : Fin N -> Fin 2 -> Fin 2 -> Nat)
    (rules : List (List (Fin N) × List (Fin N))) : Bool :=
  let z0 : Fin 2 := ⟨0, by decide⟩
  let z1 : Fin 2 := ⟨1, by decide⟩
  rules.all (fun r =>
    [z0, z1].all (fun i =>
      [z0, z1].all (fun j =>
        decide (evalFinWordMat N 2 mat r.1 i j ≥ evalFinWordMat N 2 mat r.2 i j))))

private def hasLen2RuleRawBoolW18 (s1 s2 u1 u2 : Nat) :
    List (List Nat × List Nat) -> Bool
  | [] => false
  | ([a, b], [c, d]) :: rs =>
    (a == s1 && b == s2 && c == u1 && d == u2) ||
      hasLen2RuleRawBoolW18 s1 s2 u1 u2 rs
  | _ :: rs => hasLen2RuleRawBoolW18 s1 s2 u1 u2 rs

private def checkDualUnitCascadeRawBoolW18 (M : Nat)
    (rawRules : List (List Nat × List Nat))
    (acc : List Nat) : List (Nat × Nat × Nat × Nat) -> Option (List Nat)
  | [] => some acc
  | (s1, s2, u1, u2) :: rest =>
    if inDualUnitSetBoolW18 M acc s1 && Nat.ble (4 * M) s2 && Nat.ble (s2 + 1) (8 * M) &&
       hasLen2RuleRawBoolW18 s1 s2 u1 u2 rawRules then
      checkDualUnitCascadeRawBoolW18 M rawRules (u1 :: u2 :: acc) rest
    else none

private def lhsLen2HeadLOrTRawBoolW18 (M : Nat) : List Nat -> Bool
  | [s1, _] => Nat.ble (s1 + 1) (2 * M) || Nat.ble (8 * M) s1
  | _ => false

private def checkDualCascadeAndCovRawBoolW18 (M : Nat)
    (rawRules : List (List Nat × List Nat))
    (casc : List (Nat × Nat × Nat × Nat)) : Bool :=
  match checkDualUnitCascadeRawBoolW18 M rawRules [] casc with
  | none => false
  | some finalAcc =>
    rawRules.all (fun r =>
      lhsLen2HeadLOrTRawBoolW18 M r.1 &&
      (r.1 ++ r.2).all (fun sv =>
        Nat.ble (sv + 1) (8 * M) || inDualUnitSetBoolW18 M finalAcc sv))

private theorem checkDualCollapseCertBoolW18_of_raw (M : Nat) (hN : 14 * M ≥ 1)
    (rawRules : List (List Nat × List Nat))
    (casc : List (Nat × Nat × Nat × Nat))
    (syz : List Nat)
    (hbnd : rawRules.all (fun r =>
      r.1.all (fun x => Nat.ble (x + 1) (14 * M)) &&
      r.2.all (fun x => Nat.ble (x + 1) (14 * M))) = true)
    (hraw : checkDualCascadeAndCovRawBoolW18 M rawRules casc = true)
    (hsyz : checkPositiveParikhSyzygyFastBool (14 * M) (toFinRulesW18 (14 * M) hN rawRules) syz = true) :
    checkDualCollapseCertBoolW18 M (toFinRulesW18 (14 * M) hN rawRules) casc syz = true := by
  have hhas_eq : ∀ (s1 s2 u1 u2 : Nat) (rs : List (List Nat × List Nat)),
      rs.all (fun r => r.1.all (fun x => Nat.ble (x + 1) (14 * M)) && r.2.all (fun x => Nat.ble (x + 1) (14 * M))) = true ->
      hasLen2RuleValsBoolW18 (14 * M) s1 s2 u1 u2 (toFinRulesW18 (14 * M) hN rs) =
        hasLen2RuleRawBoolW18 s1 s2 u1 u2 rs := by
    intro s1 s2 u1 u2 rs; induction rs with
    | nil => intros; rfl
    | cons r0 rtl ih =>
      rcases r0 with ⟨l, r⟩
      intro hall
      simp only [List.all_cons] at hall
      cases hlr : (l.all (fun x => Nat.ble (x + 1) (14 * M)) && r.all (fun x => Nat.ble (x + 1) (14 * M)))
      · rw [hlr] at hall; cases hall
      · rw [hlr, Bool.true_and] at hall
        rcases Bool.and_eq_true_iff.mp hlr with ⟨hl_b, hr_b⟩
        have hml := toFinWordW18_map_val (14 * M) hN l hl_b
        have hmr := toFinWordW18_map_val (14 * M) hN r hr_b
        cases l with
        | nil => simp [toFinRulesW18, toFinWordW18, hasLen2RuleValsBoolW18, hasLen2RuleRawBoolW18, ih hall]
        | cons a l1 =>
          cases l1 with
          | nil => simp [toFinRulesW18, toFinWordW18, hasLen2RuleValsBoolW18, hasLen2RuleRawBoolW18, ih hall]
          | cons b l2 =>
            cases l2 with
            | cons _ _ => simp [toFinRulesW18, toFinWordW18, hasLen2RuleValsBoolW18, hasLen2RuleRawBoolW18, ih hall]
            | nil =>
              cases r with
              | nil => simp [toFinRulesW18, toFinWordW18, hasLen2RuleValsBoolW18, hasLen2RuleRawBoolW18, ih hall]
              | cons c r1 =>
                cases r1 with
                | nil => simp [toFinRulesW18, toFinWordW18, hasLen2RuleValsBoolW18, hasLen2RuleRawBoolW18, ih hall]
                | cons d r2 =>
                  cases r2 with
                  | cons _ _ => simp [toFinRulesW18, toFinWordW18, hasLen2RuleValsBoolW18, hasLen2RuleRawBoolW18, ih hall]
                  | nil =>
                    simp only [toFinWordW18, List.map, List.cons.injEq, and_true] at hml hmr
                    simp only [toFinRulesW18, toFinWordW18, hasLen2RuleValsBoolW18, hasLen2RuleRawBoolW18, ih hall]
                    change ((if h : a < 14 * M then (⟨a, h⟩ : Fin (14 * M)) else ⟨0, hN⟩).val == s1 &&
                            (if h : b < 14 * M then (⟨b, h⟩ : Fin (14 * M)) else ⟨0, hN⟩).val == s2 &&
                            (if h : c < 14 * M then (⟨c, h⟩ : Fin (14 * M)) else ⟨0, hN⟩).val == u1 &&
                            (if h : d < 14 * M then (⟨d, h⟩ : Fin (14 * M)) else ⟨0, hN⟩).val == u2 || _) = _
                    rw [hml.1, hml.2, hmr.1, hmr.2]
  have hcasc_eq : ∀ (cs : List (Nat × Nat × Nat × Nat)) (acc : List Nat),
      checkDualUnitCascadeBoolW18 M (toFinRulesW18 (14 * M) hN rawRules) acc cs =
        checkDualUnitCascadeRawBoolW18 M rawRules acc cs := by
    intro cs; induction cs with
    | nil => intros; rfl
    | cons step rest ih =>
      rcases step with ⟨s1, s2, u1, u2⟩
      intro acc
      unfold checkDualUnitCascadeBoolW18 checkDualUnitCascadeRawBoolW18
      rw [hhas_eq s1 s2 u1 u2 rawRules hbnd]
      cases (inDualUnitSetBoolW18 M acc s1 && Nat.ble (4 * M) s2 && Nat.ble (s2 + 1) (8 * M) &&
             hasLen2RuleRawBoolW18 s1 s2 u1 u2 rawRules) <;> simp [ih]
  have hcov_eq : ∀ (finalAcc : List Nat) (rs : List (List Nat × List Nat)),
      rs.all (fun r => r.1.all (fun x => Nat.ble (x + 1) (14 * M)) && r.2.all (fun x => Nat.ble (x + 1) (14 * M))) = true ->
      (toFinRulesW18 (14 * M) hN rs).all (fun r =>
        lhsLen2HeadLOrTBoolW18 M r.1 &&
        (r.1 ++ r.2).all (fun s => Nat.ble (s.val + 1) (8 * M) || inDualUnitSetBoolW18 M finalAcc s.val)) =
      rs.all (fun r =>
        lhsLen2HeadLOrTRawBoolW18 M r.1 &&
        (r.1 ++ r.2).all (fun sv => Nat.ble (sv + 1) (8 * M) || inDualUnitSetBoolW18 M finalAcc sv)) := by
    have hall_val : ∀ (finalAcc : List Nat) (w : List (Fin (14 * M))),
        w.all (fun s => Nat.ble (s.val + 1) (8 * M) || inDualUnitSetBoolW18 M finalAcc s.val) =
        (w.map Fin.val).all (fun sv => Nat.ble (sv + 1) (8 * M) || inDualUnitSetBoolW18 M finalAcc sv) := by
      intro finalAcc w; induction w with
      | nil => rfl
      | cons s tl ih => simp only [List.map_cons, List.all_cons, ih]
    have hlhs_val : ∀ (w : List (Fin (14 * M))),
        lhsLen2HeadLOrTBoolW18 M w = lhsLen2HeadLOrTRawBoolW18 M (w.map Fin.val) := by
      intro w; cases w with
      | nil => rfl
      | cons a w1 => cases w1 with | nil => rfl | cons b w2 => cases w2 <;> rfl
    intro finalAcc rs; induction rs with
    | nil => intros; rfl
    | cons r0 rtl ih =>
      rcases r0 with ⟨l, r⟩
      intro hall
      simp only [List.all_cons] at hall
      cases hlr : (l.all (fun x => Nat.ble (x + 1) (14 * M)) && r.all (fun x => Nat.ble (x + 1) (14 * M)))
      · rw [hlr] at hall; cases hall
      · rw [hlr, Bool.true_and] at hall
        rcases Bool.and_eq_true_iff.mp hlr with ⟨hl_b, hr_b⟩
        simp only [toFinRulesW18, List.all_cons]
        rw [ih hall, hlhs_val, hall_val, List.map_append,
            toFinWordW18_map_val (14 * M) hN l hl_b, toFinWordW18_map_val (14 * M) hN r hr_b]
  unfold checkDualCollapseCertBoolW18
  unfold checkDualCascadeAndCovRawBoolW18 at hraw
  rw [hcasc_eq casc []]
  cases hc : checkDualUnitCascadeRawBoolW18 M rawRules [] casc with
  | none => rw [hc] at hraw; cases hraw
  | some finalAcc =>
    rw [hc] at hraw
    dsimp only at hraw ⊢
    rw [hcov_eq finalAcc rawRules hbnd, hraw, hsyz]; rfl

set_option maxRecDepth 65536 in
private theorem dual_wk2d_c39_w18 :
    checkWeakMat2DRulesBoolW18 42 (dualBTRSubMat2DC39 2) c39FastRulesW18 = true := by decide

set_option maxRecDepth 65536 in
private theorem dual_st26_c39_w18 :
    countStrictMat2DRules 42 (dualBTRSubMat2DC39 2) c39FastRulesW18 = 26 := by decide

private theorem dual_collapse_c39_ok_w18 :
    checkDualCollapseCertBoolW18 3 c39FastRulesW18 dualCascadeC39W18 syzTwoSidedMod3OmitR3Core39 = true :=
  checkDualCollapseCertBoolW18_of_raw 3 (by decide) c39RawRulesW18 dualCascadeC39W18 syzTwoSidedMod3OmitR3Core39
    (by decide) (by decide) (by set_option maxRecDepth 65536 in decide)

private theorem dual_collapse_c78_ok_w18 :
    checkDualCollapseCertBoolW18 6 c78FastRulesW18 dualCascadeC78W18 syzTwoSidedMod6OmitR3Core78 = true :=
  checkDualCollapseCertBoolW18_of_raw 6 (by decide) c78RawRulesW18 dualCascadeC78W18 syzTwoSidedMod6OmitR3Core78
    (by decide) (by decide) (by set_option maxRecDepth 65536 in decide)

private theorem dual_collapse_c39_c78_certs_w18 :
    checkWeakMat2DRulesBoolW18 42 (dualBTRSubMat2DC39 2) c39FastRulesW18 = true ∧
    countStrictMat2DRules 42 (dualBTRSubMat2DC39 2) c39FastRulesW18 = 26 ∧
    checkDualCollapseCertBoolW18 3 c39FastRulesW18 dualCascadeC39W18 syzTwoSidedMod3OmitR3Core39 = true ∧
    checkDualCollapseCertBoolW18 6 c78FastRulesW18 dualCascadeC78W18 syzTwoSidedMod6OmitR3Core78 = true ∧
    c39FastRulesW18 ≠ [] ∧
    c78FastRulesW18 ≠ [] :=
  ⟨dual_wk2d_c39_w18, dual_st26_c39_w18, dual_collapse_c39_ok_w18, dual_collapse_c78_ok_w18,
   (by intro h; cases h), (by intro h; cases h)⟩

private theorem natSumFin_zero_w18 (d : Nat) (f : Fin d -> Nat)
    (hz : ∀ k : Fin d, f k = 0) : natSumFin d f = 0 := by
  unfold natSumFin
  have hst : ∀ m : Nat, m ≤ d -> natSumPrefix d f m = 0 := by
    intro m hm; induction m with
    | zero => rfl
    | succ m' ih =>
      have hm_lt : m' < d := hm
      simp only [natSumPrefix, hm_lt, dite_true, ih (Nat.le_of_lt hm), hz ⟨m', hm_lt⟩, Nat.add_zero]
  exact hst d (Nat.le_refl d)

private theorem natSumFin_ge_at_w18 (d : Nat) (f : Fin d -> Nat) (k0 : Fin d) :
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

private theorem natSumFin_single_w18 (d : Nat) (f : Fin d -> Nat) (k0 : Fin d)
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

private theorem mem_of_countFinOcc_pos_w18 (N : Nat) (s : Fin N) :
    ∀ w : List (Fin N), countFinOcc N s w ≥ 1 -> s ∈ w
  | [], h => by simp [countFinOcc] at h
  | x :: xs, h => by
    by_cases hx : x = s
    · subst hx; exact List.Mem.head _
    · have hne_v : x.val ≠ s.val := fun hv => hx (Fin.ext hv)
      simp [countFinOcc, hne_v] at h
      exact List.Mem.tail x (mem_of_countFinOcc_pos_w18 N s xs h)

private theorem exists_rule_of_symAppearsInRulesBool_w18 (N : Nat) (s : Fin N) :
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
      · exact List.mem_append_left _ (mem_of_countFinOcc_pos_w18 N s l0 h1)
      · exact List.mem_append_right _ (mem_of_countFinOcc_pos_w18 N s r0 (by omega))
    · rcases exists_rule_of_symAppearsInRulesBool_w18 N s rtl hthere with ⟨r', hr', hs_m⟩
      exact ⟨r', List.Mem.tail (l0, r0) hr', hs_m⟩

private theorem dual_b_toprow_t_subdiag_collapse_sound_w18
    (M : Nat)
    (rules : List (List (Fin (14 * M)) × List (Fin (14 * M))))
    (casc : List (Nat × Nat × Nat × Nat))
    (syz : List Nat)
    (hcert : checkDualCollapseCertBoolW18 M rules casc syz = true)
    (d : Nat) (hd : d ≥ 1)
    (mat : Fin (14 * M) -> Fin d -> Fin d -> Nat)
    (hm_pos : ∀ s : Fin (14 * M), mat s ⟨0, hd⟩ ⟨0, hd⟩ ≥ 1)
    (hL_00 : ∀ s : Fin (14 * M), s.val < 2 * M -> mat s ⟨0, hd⟩ ⟨0, hd⟩ = 1)
    (hB : ∀ s : Fin (14 * M), 4 * M ≤ s.val ∧ s.val < 8 * M ->
      mat s ⟨0, hd⟩ ⟨0, hd⟩ = 1 ∧ ∀ (i j : Fin d), i.val ≥ 1 -> mat s i j = 0)
    (hweak_mat : ∀ r ∈ rules,
      ∀ i j : Fin d, evalFinWordMat (14 * M) d mat r.1 i j ≥ evalFinWordMat (14 * M) d mat r.2 i j) :
    (∀ s : Fin (14 * M), s.val ≥ 8 * M ->
      symAppearsInRulesBool (14 * M) s.val rules = true ->
      mat s ⟨0, hd⟩ ⟨0, hd⟩ = 1) ∧
    (∀ v : Fin (14 * M) -> Fin d -> Nat,
      (∀ s : Fin (14 * M), s.val < 2 * M -> ∀ j : Fin d, j.val ≥ 1 -> mat s ⟨0, hd⟩ j = 0) ->
      (∀ s : Fin (14 * M), s.val ≥ 8 * M -> ∀ j : Fin d, j.val ≥ 1 -> mat s ⟨0, hd⟩ j = 0) ->
      (∀ r ∈ rules, ∀ i : Fin d,
        evalFinWordVec (14 * M) d mat v r.1 i ≥ evalFinWordVec (14 * M) d mat v r.2 i) ->
      ∀ r ∈ rules,
        evalFinWordVec (14 * M) d mat v r.1 ⟨0, hd⟩ = evalFinWordVec (14 * M) d mat v r.2 ⟨0, hd⟩) := by
  let N := 14 * M
  let z0 : Fin d := ⟨0, hd⟩
  unfold checkDualCollapseCertBoolW18 at hcert
  cases hc_opt : checkDualUnitCascadeBoolW18 M rules [] casc with
  | none => rw [hc_opt] at hcert; cases hcert
  | some finalAcc =>
    rw [hc_opt] at hcert
    rcases bool_and_split hcert with ⟨hrules_cov, hsyz⟩
    have hmat1_eq : ∀ (x : Fin N) (i j : Fin d), evalFinWordMat N d mat [x] i j = mat x i j := by
      intro x i j
      change natSumFin d (fun k => mat x i k * natMatId d k j) = mat x i j
      rw [natSumFin_single_w18 d (fun k => mat x i k * natMatId d k j) j]
      · simp [natMatId]
      · intro k hkj; have hkv : k.val ≠ j.val := fun hv => hkj (Fin.ext hv); simp [natMatId, hkv]
    have hin_unit : ∀ (acc : List Nat),
        (∀ x ∈ acc, ∀ hx : x < N, mat ⟨x, hx⟩ z0 z0 = 1) ->
        ∀ (y : Nat) (hy : y < N), inDualUnitSetBoolW18 M acc y = true -> mat ⟨y, hy⟩ z0 z0 = 1 := by
      intro acc hacc y hy hin
      unfold inDualUnitSetBoolW18 at hin
      rcases Bool.or_eq_true_iff.mp hin with hlb_b | hany_b
      · rcases Bool.or_eq_true_iff.mp hlb_b with hlt2_b | h48_b
        · have hlt2 := Nat.ble_eq.mp hlt2_b
          exact hL_00 ⟨y, hy⟩ (by dsimp; omega)
        · rcases bool_and_split h48_b with ⟨h4_b, h8_b⟩
          have h4 := Nat.ble_eq.mp h4_b
          have h8 := Nat.ble_eq.mp h8_b
          exact (hB ⟨y, hy⟩ ⟨h4, by dsimp; omega⟩).1
      · rcases List.any_eq_true.mp hany_b with ⟨x, hx_m, hxy_b⟩
        have hxy : x = y := Nat.eq_of_beq_eq_true hxy_b
        subst hxy; exact hacc x hx_m hy
    have hex_len2 : ∀ (s1 s2 u1 u2 : Nat) (rs : List (List (Fin N) × List (Fin N))),
        hasLen2RuleValsBoolW18 N s1 s2 u1 u2 rs = true ->
        ∃ (a b c d : Fin N),
          a.val = s1 ∧ b.val = s2 ∧ c.val = u1 ∧ d.val = u2 ∧ ([a, b], [c, d]) ∈ rs := by
      intro s1 s2 u1 u2 rs; induction rs with
      | nil => intro h; cases h
      | cons r0 rtl ih =>
        rcases r0 with ⟨l0, r0_w⟩
        cases l0 with
        | nil => exact fun h => let ⟨a, b, c, d, h1, h2, h3, h4, hm⟩ := ih h; ⟨a, b, c, d, h1, h2, h3, h4, List.Mem.tail _ hm⟩
        | cons a l1 =>
          cases l1 with
          | nil => exact fun h => let ⟨a', b', c', d', h1, h2, h3, h4, hm⟩ := ih h; ⟨a', b', c', d', h1, h2, h3, h4, List.Mem.tail _ hm⟩
          | cons b l2 =>
            cases l2 with
            | cons _ _ => exact fun h => let ⟨a', b', c', d', h1, h2, h3, h4, hm⟩ := ih h; ⟨a', b', c', d', h1, h2, h3, h4, List.Mem.tail _ hm⟩
            | nil =>
              cases r0_w with
              | nil => exact fun h => let ⟨a', b', c', d', h1, h2, h3, h4, hm⟩ := ih h; ⟨a', b', c', d', h1, h2, h3, h4, List.Mem.tail _ hm⟩
              | cons c r1 =>
                cases r1 with
                | nil => exact fun h => let ⟨a', b', c', d', h1, h2, h3, h4, hm⟩ := ih h; ⟨a', b', c', d', h1, h2, h3, h4, List.Mem.tail _ hm⟩
                | cons d_f r2 =>
                  cases r2 with
                  | cons _ _ => exact fun h => let ⟨a', b', c', d', h1, h2, h3, h4, hm⟩ := ih h; ⟨a', b', c', d', h1, h2, h3, h4, List.Mem.tail _ hm⟩
                  | nil =>
                    intro h; unfold hasLen2RuleValsBoolW18 at h
                    rcases Bool.or_eq_true_iff.mp h with hhere | htl_b
                    · rcases bool_and_split hhere with ⟨h123, h4⟩
                      rcases bool_and_split h123 with ⟨h12, h3⟩
                      rcases bool_and_split h12 with ⟨h1, h2⟩
                      exact ⟨a, b, c, d_f, beq_iff_eq.mp h1, beq_iff_eq.mp h2,
                        beq_iff_eq.mp h3, beq_iff_eq.mp h4, List.Mem.head _⟩
                    · rcases ih htl_b with ⟨a', b', c', d', h1, h2, h3, h4, hm⟩
                      exact ⟨a', b', c', d', h1, h2, h3, h4, List.Mem.tail _ hm⟩
    have hwalk_unit : ∀ (steps : List (Nat × Nat × Nat × Nat)) (acc : List Nat),
        (∀ x ∈ acc, ∀ hx : x < N, mat ⟨x, hx⟩ z0 z0 = 1) ->
        checkDualUnitCascadeBoolW18 M rules acc steps = some finalAcc ->
        ∀ x ∈ finalAcc, ∀ hx : x < N, mat ⟨x, hx⟩ z0 z0 = 1 := by
      intro steps; induction steps with
      | nil =>
        intro acc hacc hs; simp only [checkDualUnitCascadeBoolW18, Option.some.injEq] at hs
        subst hs; exact hacc
      | cons st tl ih =>
        rcases st with ⟨s1, s2, u1, u2⟩
        intro acc hacc hs
        unfold checkDualUnitCascadeBoolW18 at hs
        by_cases hcond : (inDualUnitSetBoolW18 M acc s1 && Nat.ble (4 * M) s2 && Nat.ble (s2 + 1) (8 * M) &&
            hasLen2RuleValsBoolW18 (14 * M) s1 s2 u1 u2 rules) = true
        · rw [ite_true_of_w10 hcond] at hs
          rcases bool_and_split hcond with ⟨hs123, hmem_b⟩
          rcases bool_and_split hs123 with ⟨hs12, hs2_hi_b⟩
          rcases bool_and_split hs12 with ⟨hs1_b, hs2_lo_b⟩
          rcases hex_len2 s1 s2 u1 u2 rules hmem_b with ⟨a_f, b_f, c_f, d_f, ha_v, hb_v, hc_v, hd_v, hr_rules⟩
          have hb_B : 4 * M ≤ b_f.val ∧ b_f.val < 8 * M := by
            have := Nat.ble_eq.mp hs2_lo_b; have := Nat.ble_eq.mp hs2_hi_b; omega
          have hl00 : evalFinWordMat N d mat [a_f, b_f] z0 z0 = 1 := by
            change natSumFin d (fun k => mat a_f z0 k * evalFinWordMat N d mat [b_f] k z0) = 1
            rw [natSumFin_single_w18 d _ z0]
            · have ha_eq : a_f = ⟨s1, ha_v ▸ a_f.isLt⟩ := Fin.ext ha_v
              rw [hmat1_eq b_f z0 z0, ha_eq, hin_unit acc hacc s1 (ha_v ▸ a_f.isLt) hs1_b, (hB b_f hb_B).1]
            · intro k hk0
              have hk1 : k.val ≥ 1 := by have : k.val ≠ 0 := fun hv => hk0 (Fin.ext hv); omega
              rw [hmat1_eq b_f k z0, (hB b_f hb_B).2 k z0 hk1, Nat.mul_zero]
          have hr00_ge : evalFinWordMat N d mat [c_f, d_f] z0 z0 ≥ mat c_f z0 z0 * mat d_f z0 z0 := by
            change natSumFin d (fun k => mat c_f z0 k * evalFinWordMat N d mat [d_f] k z0) ≥ _
            have hg := natSumFin_ge_at_w18 d (fun k => mat c_f z0 k * evalFinWordMat N d mat [d_f] k z0) z0
            rwa [hmat1_eq d_f z0 z0] at hg
          have hwk00 := hweak_mat ([a_f, b_f], [c_f, d_f]) hr_rules z0 z0
          dsimp only [N] at hwk00 hl00 hr00_ge
          rw [hl00] at hwk00
          have hc_pos := hm_pos c_f
          have hd_pos := hm_pos d_f
          have hm_u1 : mat c_f z0 z0 * mat d_f z0 z0 ≥ mat c_f z0 z0 * 1 := Nat.mul_le_mul_left _ hd_pos
          have hm_u2 : mat c_f z0 z0 * mat d_f z0 z0 ≥ 1 * mat d_f z0 z0 := Nat.mul_le_mul_right _ hc_pos
          have hc_one : mat c_f z0 z0 = 1 := by dsimp only [z0] at *; omega
          have hd_one : mat d_f z0 z0 = 1 := by dsimp only [z0] at *; omega
          apply ih (u1 :: u2 :: acc) _ hs
          intro x hx_c hx_lt
          cases hx_c with
          | head => rw [show (⟨u1, hx_lt⟩ : Fin N) = c_f from Fin.ext hc_v.symm]; exact hc_one
          | tail _ htl1 =>
            cases htl1 with
            | head => rw [show (⟨u2, hx_lt⟩ : Fin N) = d_f from Fin.ext hd_v.symm]; exact hd_one
            | tail _ htl2 => exact hacc x htl2 hx_lt
        · rw [ite_false_of_w10 hcond] at hs; cases hs
    have hfinal_unit := hwalk_unit casc [] (fun _ h => by cases h) hc_opt
    have hall_cov := List.all_eq_true.mp hrules_cov
    have hT_unit : ∀ s : Fin N, s.val ≥ 8 * M ->
        symAppearsInRulesBool N s.val rules = true -> mat s z0 z0 = 1 := by
      intro s hs8 hact
      rcases exists_rule_of_symAppearsInRulesBool_w18 N s rules hact with ⟨r, hr_m, hs_m⟩
      rcases bool_and_split (hall_cov r hr_m) with ⟨_, hcov_s⟩
      rcases Bool.or_eq_true_iff.mp (List.all_eq_true.mp hcov_s s hs_m) with hlt8 | hin_b
      · have := Nat.ble_eq.mp hlt8; omega
      · exact hin_unit finalAcc hfinal_unit s.val s.isLt hin_b
    refine ⟨hT_unit, ?_⟩
    intro v hL_top0 hT_top0 hweak_vec
    let wt : Fin N -> Nat := fun s => v s z0
    have hvec_ge_par : ∀ w : List (Fin N), evalFinWordVec N d mat v w z0 ≥ evalFinParikh N wt w := by
      intro w; induction w with
      | nil => exact Nat.le_refl 0
      | cons a xs ih =>
        simp only [evalFinWordVec, natMatVec, evalFinParikh]
        have hg := natSumFin_ge_at_w18 d (fun j => mat a z0 j * evalFinWordVec N d mat v xs j) z0
        have hm := Nat.mul_le_mul (hm_pos a) ih
        dsimp only [z0, wt] at hg hm ⊢
        omega
    have hlhs_eq_par : ∀ r ∈ rules, evalFinWordVec N d mat v r.1 z0 = evalFinParikh N wt r.1 := by
      intro r hr_m
      rcases bool_and_split (hall_cov r hr_m) with ⟨hlhs_b, _⟩
      cases hl1 : r.1 with
      | nil => rw [hl1] at hlhs_b; cases hlhs_b
      | cons s1 xs1 =>
        cases xs1 with
        | nil => rw [hl1] at hlhs_b; cases hlhs_b
        | cons s2 xs2 =>
          cases xs2 with
          | cons _ _ => rw [hl1] at hlhs_b; cases hlhs_b
          | nil =>
            rw [hl1] at hlhs_b
            have hs1_lt_or_ge : s1.val < 2 * M ∨ s1.val ≥ 8 * M := by
              rcases Bool.or_eq_true_iff.mp hlhs_b with hlt_b | hge_b
              · have := Nat.ble_eq.mp hlt_b; omega
              · exact Or.inr (Nat.ble_eq.mp hge_b)
            have hs1_act : symAppearsInRulesBool N s1.val rules = true :=
              symAppearsInRulesBool_of_mem_lhs N s1 rules r hr_m (by rw [hl1]; exact List.Mem.head _)
            have hs1_00 : mat s1 z0 z0 = 1 := by
              rcases hs1_lt_or_ge with hlt2 | hge8
              · exact hL_00 s1 hlt2
              · exact hT_unit s1 hge8 hs1_act
            have hs1_top0 : ∀ j : Fin d, j ≠ z0 -> mat s1 z0 j = 0 := by
              intro j hne
              have hj1 : j.val ≥ 1 := by have : j.val ≠ 0 := fun hv => hne (Fin.ext hv); omega
              rcases hs1_lt_or_ge with hlt2 | hge8
              · exact hL_top0 s1 hlt2 j hj1
              · exact hT_top0 s1 hge8 j hj1
            have hv_s2 : evalFinWordVec N d mat v [s2] z0 = v s2 z0 := by
              simp only [evalFinWordVec, natMatVec]
              rw [natSumFin_zero_w18 d _ (fun _ => Nat.mul_zero _), Nat.add_zero]
            change v s1 z0 + natSumFin d (fun j => mat s1 z0 j * evalFinWordVec N d mat v [s2] j) =
              wt s1 + (wt s2 + 0)
            rw [natSumFin_single_w18 d _ z0]
            · rw [hs1_00, hv_s2, Nat.one_mul]; dsimp [wt]
            · intro j hne; rw [hs1_top0 j hne, Nat.zero_mul]
    unfold checkPositiveParikhSyzygyFastBool at hsyz
    rcases bool_and_split hsyz with ⟨hs1, hpairs⟩
    rcases bool_and_split hs1 with ⟨hs2, hpos_m⟩
    rcases bool_and_split hs2 with ⟨_, hlen_eq⟩
    have hlen : rules.length = syz.length := of_decide_eq_true hlen_eq
    rcases accumSymCountsW11_spec N rules syz with ⟨hacc_len, hacc_get⟩
    rcases weightedParikh_eq_sum_sym N wt rules syz with ⟨hl_sum, hr_sum⟩
    have hpar_le : weightedParikhLhs N wt rules syz ≤ weightedParikhRhs N wt rules syz := by
      rw [hl_sum, hr_sum]
      exact natSumPrefix_mono_w5 N _ _ (fun s => Nat.mul_le_mul_left (wt s) (by
        have hle := checkPairsLeBoolW11_sound _ hpairs s.val (by rw [hacc_len]; exact s.isLt)
        rwa [hacc_get s] at hle)) N
    have hpar_rule_ge : ∀ r ∈ rules, evalFinParikh N wt r.1 ≥ evalFinParikh N wt r.2 := by
      intro r hr
      have h1 := hlhs_eq_par r hr
      have h2 := hweak_vec r hr z0
      have h3 := hvec_ge_par r.2
      dsimp only [N, z0] at h1 h2 h3 ⊢
      omega
    have hpar_all_eq : ∀ (rs : List (List (Fin N) × List (Fin N))) (ms : List Nat),
        rs.length = ms.length ->
        checkAllPosNatList ms = true ->
        (∀ r ∈ rs, evalFinParikh N wt r.1 ≥ evalFinParikh N wt r.2) ->
        weightedParikhLhs N wt rs ms ≥ weightedParikhRhs N wt rs ms ∧
        (weightedParikhLhs N wt rs ms ≤ weightedParikhRhs N wt rs ms ->
          ∀ r ∈ rs, evalFinParikh N wt r.1 = evalFinParikh N wt r.2) := by
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
          have hm0_ge := Nat.mul_le_mul_left m0 (hw_r r0 (List.Mem.head _))
          simp only [weightedParikhLhs, weightedParikhRhs]
          refine ⟨by omega, fun htot_le r hr_m => ?_⟩
          cases hr_m with
          | head =>
            have heq_m : m0 * evalFinParikh N wt r0.1 = m0 * evalFinParikh N wt r0.2 := by omega
            exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < m0) heq_m
          | tail _ htl_m => exact himp_tl (by omega) r htl_m
    have heq_par_all := (hpar_all_eq rules syz hlen hpos_m hpar_rule_ge).2 hpar_le
    intro r hr
    have h1 := hlhs_eq_par r hr
    have h2 := hweak_vec r hr z0
    have h3 := hvec_ge_par r.2
    have h4 := heq_par_all r hr
    dsimp only [N, z0] at h1 h2 h3 h4 ⊢
    omega

/--
  Theorem W18.1a (`twosided_c39_c78_dual_b_toprow_and_t_subdiag_impossibility`,
  `zero custom axioms`):
  Universal All-Dimension (`∀ d ≥ 1`) Dual `.B`-Top-Row + `.T`-Subdiagonal Cascade Collapse
  (`12/12` Active `.T` Top-Left Unit Locks on `c39`, `24/24` Active `.T` Top-Left Unit Locks on `c78`,
  Orienting `26/39` Strict Matrix Rules in `d = 2` via `dualBTRSubMat2DC39 2`) & Universal
  Impossibility of `GenOmegaDualBTopRowAndTSubdiagMatTower` Across `TwoSided(2 × 3)` `c39` &
  `TwoSided(2 × 6)` `c78` (`Branch P4.3`, witness `ZPOS_C39_3D_BLOCK_NILP_AND_DUAL_BT_ESCAPE`,
  `W18_H1`).
-/
theorem twosided_c39_c78_dual_b_toprow_and_t_subdiag_impossibility :
    let c39 := filterFinParikhUnoriented 42 wtTwoSidedMod3OmitR3
      (twoSidedLabelledCollatzRules 3 (by decide) all11OmitR3List)
    let c78 := filterFinParikhUnoriented 84 wtTwoSidedMod6OmitR3
      (twoSidedLabelledCollatzRules 6 (by decide) all11OmitR3List)
    (countActiveTSymsBool 3 c39 = 12 ∧
     countActiveTSymsBool 6 c78 = 24 ∧
     countStrictMat2DRules 42 (dualBTRSubMat2DC39 2) c39 = 26 ∧
     (∀ r ∈ c39, ∀ i j : Fin 2,
       evalFinWordMat 42 2 (dualBTRSubMat2DC39 2) r.1 i j ≥
         evalFinWordMat 42 2 (dualBTRSubMat2DC39 2) r.2 i j)) ∧
    (∀ (d : Nat) (hd : d ≥ 1) (mat : Fin 42 -> Fin d -> Fin d -> Nat),
      (∀ s : Fin 42, mat s ⟨0, hd⟩ ⟨0, hd⟩ ≥ 1) ->
      (∀ s : Fin 42, s.val < 6 -> mat s ⟨0, hd⟩ ⟨0, hd⟩ = 1) ->
      (∀ s : Fin 42, 12 ≤ s.val ∧ s.val < 24 ->
        mat s ⟨0, hd⟩ ⟨0, hd⟩ = 1 ∧ ∀ (i j : Fin d), i.val ≥ 1 -> mat s i j = 0) ->
      (∀ r ∈ c39, ∀ i j : Fin d,
        evalFinWordMat 42 d mat r.1 i j ≥ evalFinWordMat 42 d mat r.2 i j) ->
      ∀ s : Fin 42, s.val ≥ 24 -> symAppearsInRulesBool 42 s.val c39 = true ->
        mat s ⟨0, hd⟩ ⟨0, hd⟩ = 1) ∧
    (∀ (d : Nat) (hd : d ≥ 1) (mat : Fin 84 -> Fin d -> Fin d -> Nat),
      (∀ s : Fin 84, mat s ⟨0, hd⟩ ⟨0, hd⟩ ≥ 1) ->
      (∀ s : Fin 84, s.val < 12 -> mat s ⟨0, hd⟩ ⟨0, hd⟩ = 1) ->
      (∀ s : Fin 84, 24 ≤ s.val ∧ s.val < 48 ->
        mat s ⟨0, hd⟩ ⟨0, hd⟩ = 1 ∧ ∀ (i j : Fin d), i.val ≥ 1 -> mat s i j = 0) ->
      (∀ r ∈ c78, ∀ i j : Fin d,
        evalFinWordMat 84 d mat r.1 i j ≥ evalFinWordMat 84 d mat r.2 i j) ->
      ∀ s : Fin 84, s.val ≥ 48 -> symAppearsInRulesBool 84 s.val c78 = true ->
        mat s ⟨0, hd⟩ ⟨0, hd⟩ = 1) ∧
    (∀ (d : Nat) (hd : d ≥ 1) (k : Nat),
      ¬ GenOmegaDualBTopRowAndTSubdiagMatTower 3 d hd k c39 ∧
      ¬ GenOmegaDualBTopRowAndTSubdiagMatTower 6 d hd k c78) := by
  dsimp only
  rcases twosided_c39_c78_nonuniform_mixed_zerodiag_tr_impossibility.1 with ⟨hcnt39_raw, hcnt78_raw⟩
  rw [c39_eq_fastRules_w18] at hcnt39_raw
  rw [c78_eq_fastRules_w18] at hcnt78_raw
  rw [c39_eq_fastRules_w18, c78_eq_fastRules_w18]
  rcases dual_collapse_c39_c78_certs_w18 with
    ⟨hwk2d, hst26, hcert39, hcert78, hne39, hne78⟩
  have hcnt39 := hcnt39_raw
  have hcnt78 := hcnt78_raw
  have hwk2d_prop : ∀ r ∈ c39FastRulesW18, ∀ i j : Fin 2,
      evalFinWordMat 42 2 (dualBTRSubMat2DC39 2) r.1 i j ≥
        evalFinWordMat 42 2 (dualBTRSubMat2DC39 2) r.2 i j := by
    intro r hr i j
    let z0 : Fin 2 := ⟨0, by decide⟩
    let z1 : Fin 2 := ⟨1, by decide⟩
    have hi_m : i ∈ [z0, z1] := by
      rcases (by have := i.isLt; omega : i.val = 0 ∨ i.val = 1) with h | h
      · rw [show i = z0 from Fin.ext h]; exact List.Mem.head _
      · rw [show i = z1 from Fin.ext h]; exact List.Mem.tail _ (List.Mem.head _)
    have hj_m : j ∈ [z0, z1] := by
      rcases (by have := j.isLt; omega : j.val = 0 ∨ j.val = 1) with h | h
      · rw [show j = z0 from Fin.ext h]; exact List.Mem.head _
      · rw [show j = z1 from Fin.ext h]; exact List.Mem.tail _ (List.Mem.head _)
    exact of_decide_eq_true
      (List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp hwk2d r hr) i hi_m) j hj_m)
  have hno_tower : ∀ (M : Nat) (core : List (List (Fin (14 * M)) × List (Fin (14 * M))))
      (casc : List (Nat × Nat × Nat × Nat)) (syz : List Nat),
      core ≠ [] ->
      checkDualCollapseCertBoolW18 M core casc syz = true ->
      ∀ (d : Nat) (hd : d ≥ 1) (k : Nat),
        ¬ GenOmegaDualBTopRowAndTSubdiagMatTower M d hd k core := by
    intro M core casc syz hne hcert d hd
    cases hcore : core with
    | nil => exact False.elim (hne hcore)
    | cons r0 rs =>
      rw [← hcore]
      have hmem0 : r0 ∈ core := hcore ▸ List.Mem.head _
      have himp : ∀ (k : Nat) (cur : List (List (Fin (14 * M)) × List (Fin (14 * M)))),
          (∀ r ∈ core, r ∈ cur) -> ¬ GenOmegaDualBTopRowAndTSubdiagMatTower M d hd k cur := by
        intro k; induction k with
        | zero =>
          intro cur hsub h0; rw [GenOmegaDualBTopRowAndTSubdiagMatTower] at h0; subst h0
          exact List.not_mem_nil (hsub r0 hmem0)
        | succ k' ih =>
          intro cur hsub hsucc
          rcases hsucc with rfl | ⟨rem, mat, v, hm1, hL, hB, hT, hweak, hkeep, hrem⟩
          · exact List.not_mem_nil (hsub r0 hmem0)
          · have heq := (dual_b_toprow_t_subdiag_collapse_sound_w18 M core casc syz hcert d hd mat
              hm1 (fun s hs => (hL s hs).1) hB (fun r hr => (hweak r (hsub r hr)).1)).2 v
              (fun s hs j hj => (hL s hs).2 ⟨0, hd⟩ j (Or.inr hj))
              hT
              (fun r hr => (hweak r (hsub r hr)).2)
            exact ih rem (fun r hr => hkeep r (hsub r hr)
              (by rw [heq r hr]; exact Nat.lt_irrefl _)) hrem
      exact fun k => himp k core (fun _ hr => hr)
  exact ⟨⟨hcnt39, hcnt78, hst26, hwk2d_prop⟩,
         fun d hd mat hm1 hL0 hB hwk =>
           (dual_b_toprow_t_subdiag_collapse_sound_w18 3 c39FastRulesW18 _ _ hcert39 d hd mat hm1 hL0 hB hwk).1,
         fun d hd mat hm1 hL0 hB hwk =>
           (dual_b_toprow_t_subdiag_collapse_sound_w18 6 c78FastRulesW18 _ _ hcert78 d hd mat hm1 hL0 hB hwk).1,
         fun d hd k =>
           ⟨hno_tower 3 c39FastRulesW18 _ _ hne39 hcert39 d hd k,
            hno_tower 6 c78FastRulesW18 _ _ hne78 hcert78 d hd k⟩⟩

-- ----------------------------------------------------------------------------
-- Section 1B: Infinite 5-Parameter `d = 3` (`3 × 3`) Block-Nilpotent Cross-Channel
--             `.B` + `.T` + `.R` Mixed Zero-Diagonal Cones & 3-Channel Farkas Locks
-- ----------------------------------------------------------------------------

/-- Infinite 5-parameter `d = 3` (`3 × 3`) block-nilpotent cross-channel `.B` + `.T` + `.R`
    mixed zero-diagonal matrix cone on `Fin 42` (`c39`, strictly orienting `37/39` rules!):
    - `.R`: `(M_{6..8}) = [[k, 0, 0], [0, 0, 0], [0, 0, 1]]`, `(M_{9..11}) = [[k, 0, 0], [0, 0, 0], [0, 0, 0]]`,
    - `.B` channel 1 (`{13, 14, 16, 17, 18, 21}`): `[[1, β, 0], [0, 0, 0], [0, 0, 0]]`,
    - `.B` channel 2 (`{20, 22, 23}`): `[[1, 0, α], [0, 0, 0], [0, 0, 0]]`,
    - `.T` cross-channel 1 (`{28, 29, 31, 32, 36, 37, 38}`):
      `[[1, (β on 28,32,36), (α on 37)], [0, 0, 0], [γ, 0, 0]]`,
    - `.T` block-nilpotent cross-channel 2 (`{33, 35, 39, 40, 41}`):
      `[[1, 0, (α on 40,41)], [δ, 0, δ], [0, 0, 0]]` (non-zero lower-right `(1, 2) = δ` entry!). -/
private def isBeta01SymW18 (v : Nat) : Bool :=
  v == 13 || v == 14 || v == 16 || v == 17 || v == 18 || v == 21 || v == 28 || v == 32 || v == 36

private def isAlpha02SymW18 (v : Nat) : Bool :=
  v == 20 || v == 22 || v == 23 || v == 37 || v == 40 || v == 41

private def isDelta1SymW18 (v : Nat) : Bool :=
  v == 33 || v == 35 || v == 39 || v == 40 || v == 41

private def isGamma20SymW18 (v : Nat) : Bool :=
  v == 28 || v == 29 || v == 31 || v == 32 || v == 36 || v == 37 || v == 38

def rank2BlockNilpMat3DC39 (k alpha beta gamma delta : Nat) (s : Fin 42) (i j : Fin 3) : Nat :=
  if i.val == 0 && j.val == 0 then
    if decide (6 ≤ s.val ∧ s.val ≤ 11) then k else 1
  else if i.val == 0 && j.val == 1 then
    if isBeta01SymW18 s.val then beta else 0
  else if i.val == 0 && j.val == 2 then
    if isAlpha02SymW18 s.val then alpha else 0
  else if i.val == 1 && (j.val == 0 || j.val == 2) then
    if isDelta1SymW18 s.val then delta else 0
  else if i.val == 2 && j.val == 0 then
    if isGamma20SymW18 s.val then gamma else 0
  else if i.val == 2 && j.val == 2 then
    if decide (6 ≤ s.val ∧ s.val ≤ 8) then 1 else 0
  else 0

/-- Lifted 5-parameter `d = 3` (`3 × 3`) block-nilpotent cross-channel cone on `Fin 84` (`c78`,
    strictly orienting `74/78` rules!). -/
def rank2BlockNilpMat3DC78 (k alpha beta gamma delta : Nat) (s : Fin 84) (i j : Fin 3) : Nat :=
  rank2BlockNilpMat3DC39 k alpha beta gamma delta (projSym84To42 s) i j

/-- Standard `3D` unit basis vector on `Fin N`. -/
def basisVec3D (N : Nat) (s0 : Fin N) (j0 : Fin 3) (s : Fin N) (j : Fin 3) : Nat :=
  if s.val == s0.val && j.val == j0.val then 1 else 0

/-- Count rules strictly oriented (`∃ i j : Fin 3, LHS > RHS`) by a `3 × 3` matrix interpretation. -/
def countStrictMat3DRules (N : Nat) (M : Fin N -> Fin 3 -> Fin 3 -> Nat) :
    List (List (Fin N) × List (Fin N)) -> Nat
  | [] => 0
  | (l, r) :: rs =>
    let z0 : Fin 3 := ⟨0, by decide⟩
    let z1 : Fin 3 := ⟨1, by decide⟩
    let z2 : Fin 3 := ⟨2, by decide⟩
    let is_st := [z0, z1, z2].any (fun i =>
      [z0, z1, z2].any (fun j =>
        decide (evalFinWordMat N 3 M l i j > evalFinWordMat N 3 M r i j)))
    (if is_st then 1 else 0) + countStrictMat3DRules N M rs

/-- Non-negative 4-rule cross-channel row-1 Farkas multipliers `μ_1(r)` for `rank2BlockNilpMat3DC39`
    (supported on `([28,18],[22,33]): 10`, `([31,14],[18,29]): 6`, `([36,22],[20,40]): 1`, `([38,16],[13,31]): 2`). -/
def farkasMu1BlockNilp3DC39 : List (Fin 42) -> Nat
  | a :: b :: _ =>
    let av := a.val; let bv := b.val
    if av == 28 && bv == 18 then 10
    else if av == 31 && bv == 14 then 6
    else if av == 36 && bv == 22 then 1
    else if av == 38 && bv == 16 then 2
    else 0
  | _ => 0

/-- Non-negative 8-rule cross-channel row-1 Farkas multipliers `μ_1(r)` for `rank2BlockNilpMat3DC78`. -/
def farkasMu1BlockNilp3DC78 : List (Fin 84) -> Nat
  | a :: b :: _ =>
    let av := a.val; let bv := b.val
    if av == 55 && bv == 36 then 34
    else if av == 55 && bv == 39 then 1
    else if av == 64 && bv == 26 then 1
    else if av == 64 && bv == 29 then 10
    else if av == 74 && bv == 31 then 1
    else if av == 75 && bv == 43 then 8
    else if av == 75 && bv == 46 then 1
    else if av == 76 && bv == 32 then 1
    else 0
  | _ => 0

private abbrev fin3Z0W18 : Fin 3 := ⟨0, by decide⟩
private abbrev fin3Z1W18 : Fin 3 := ⟨1, by decide⟩
private abbrev fin3Z2W18 : Fin 3 := ⟨2, by decide⟩

/-- 3-channel Farkas LHS functional `∑_r [μ_0 * v_0(l) + m_1 * v_1(l) + m_2 * v_2(l)]` on `rank2BlockNilpMat3DC39`. -/
def farkas3DVecLhsN (N : Nat) (proj : Fin N -> Fin 42)
    (mu0 m1 m2 : List (Fin N) -> Nat) (k alpha beta gamma delta : Nat)
    (v : Fin N -> Fin 3 -> Nat) : List (List (Fin N) × List (Fin N)) -> Nat
  | [] => 0
  | (l, _) :: rs =>
    let M := fun s => rank2BlockNilpMat3DC39 k alpha beta gamma delta (proj s)
    mu0 l * evalFinWordVec N 3 M v l fin3Z0W18 +
      m1 l * evalFinWordVec N 3 M v l fin3Z1W18 +
      m2 l * evalFinWordVec N 3 M v l fin3Z2W18 +
      farkas3DVecLhsN N proj mu0 m1 m2 k alpha beta gamma delta v rs

/-- 3-channel Farkas RHS functional `∑_r [μ_0 * v_0(r) + m_1 * v_1(r) + m_2 * v_2(r)]` on `rank2BlockNilpMat3DC39`. -/
def farkas3DVecRhsN (N : Nat) (proj : Fin N -> Fin 42)
    (mu0 m1 m2 : List (Fin N) -> Nat) (k alpha beta gamma delta : Nat)
    (v : Fin N -> Fin 3 -> Nat) : List (List (Fin N) × List (Fin N)) -> Nat
  | [] => 0
  | (l, r) :: rs =>
    let M := fun s => rank2BlockNilpMat3DC39 k alpha beta gamma delta (proj s)
    mu0 l * evalFinWordVec N 3 M v r fin3Z0W18 +
      m1 l * evalFinWordVec N 3 M v r fin3Z1W18 +
      m2 l * evalFinWordVec N 3 M v r fin3Z2W18 +
      farkas3DVecRhsN N proj mu0 m1 m2 k alpha beta gamma delta v rs

private theorem mat3_step_expandN_w18 (N : Nat) (M : Fin N -> Fin 3 -> Fin 3 -> Nat)
    (v : Fin N -> Fin 3 -> Nat) (s : Fin N) (rest : List (Fin N)) (i : Fin 3) :
    evalFinWordVec N 3 M v (s :: rest) i =
      v s i + M s i fin3Z0W18 * evalFinWordVec N 3 M v rest fin3Z0W18 +
        M s i fin3Z1W18 * evalFinWordVec N 3 M v rest fin3Z1W18 +
        M s i fin3Z2W18 * evalFinWordVec N 3 M v rest fin3Z2W18 := by
  change v s i + (((0 + M s i fin3Z0W18 * evalFinWordVec N 3 M v rest fin3Z0W18) +
    M s i fin3Z1W18 * evalFinWordVec N 3 M v rest fin3Z1W18) +
    M s i fin3Z2W18 * evalFinWordVec N 3 M v rest fin3Z2W18) = _
  omega

private theorem mat3_mul_step_w18 (N : Nat) (M : Fin N -> Fin 3 -> Fin 3 -> Nat)
    (s : Fin N) (rest : List (Fin N)) (i j : Fin 3) :
    evalFinWordMat N 3 M (s :: rest) i j =
      M s i fin3Z0W18 * evalFinWordMat N 3 M rest fin3Z0W18 j +
      M s i fin3Z1W18 * evalFinWordMat N 3 M rest fin3Z1W18 j +
      M s i fin3Z2W18 * evalFinWordMat N 3 M rest fin3Z2W18 j := by
  change ((0 + M s i fin3Z0W18 * evalFinWordMat N 3 M rest fin3Z0W18 j) +
    M s i fin3Z1W18 * evalFinWordMat N 3 M rest fin3Z1W18 j) +
    M s i fin3Z2W18 * evalFinWordMat N 3 M rest fin3Z2W18 j = _
  omega

private def wordShape3DMatBoolW18 : List (Fin 42) -> Bool
  | [s1] => decide (s1.val < 6 ∨ s1.val ≥ 12)
  | [s1, s2] =>
    if decide (6 ≤ s2.val ∧ s2.val ≤ 11) then
      decide ((s1.val < 6 ∨ s1.val ≥ 12) ∧
        (s2.val ≥ 9 ∨ s1.val = 28 ∨ s1.val = 31))
    else
      decide ((s1.val < 6 ∨ s1.val ≥ 12) ∧ (s2.val < 6 ∨ s2.val ≥ 12) ∧
        ((s1.val < 6 ∨ (12 ≤ s1.val ∧ s1.val < 24)) ∨ (12 ≤ s2.val ∧ s2.val < 24)))
  | [s1, s2, s3] =>
    decide ((s1.val = 14 ∨ s1.val = 20 ∨ s1.val = 23) ∧
      (s2.val = 13 ∨ s2.val = 16) ∧
      (6 ≤ s3.val ∧ s3.val ≤ 8))
  | _ => false

private def endInRBoolW18 : List (Fin 42) -> Bool
  | [] => false
  | [s] => decide (6 ≤ s.val ∧ s.val ≤ 11)
  | _ :: tl => endInRBoolW18 tl

private def evalWord3D9CoeffsW18 (w : List (Fin 42)) (i j : Fin 3) :
    Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat :=
  let m0 := evalFinWordMat 42 3 (rank2BlockNilpMat3DC39 1 0 0 0 0) w i j
  let ma := evalFinWordMat 42 3 (rank2BlockNilpMat3DC39 1 1 0 0 0) w i j - m0
  let mb := evalFinWordMat 42 3 (rank2BlockNilpMat3DC39 1 0 1 0 0) w i j - m0
  let mg := evalFinWordMat 42 3 (rank2BlockNilpMat3DC39 1 0 0 1 0) w i j - m0
  let md := evalFinWordMat 42 3 (rank2BlockNilpMat3DC39 1 0 0 0 1) w i j - m0
  let mag := evalFinWordMat 42 3 (rank2BlockNilpMat3DC39 1 1 0 1 0) w i j - m0 - ma - mg
  let mbd := evalFinWordMat 42 3 (rank2BlockNilpMat3DC39 1 0 1 0 1) w i j - m0 - mb - md
  let mad := evalFinWordMat 42 3 (rank2BlockNilpMat3DC39 1 1 0 0 1) w i j - m0 - ma - md
  let mbg := evalFinWordMat 42 3 (rank2BlockNilpMat3DC39 1 0 1 1 0) w i j - m0 - mb - mg
  (m0, ma, mb, mg, md, mag, mbd, mad, mbg)

private def checkRule3DCornersBoolW18 (r : List (Fin 42) × List (Fin 42)) : Bool :=
  wordShape3DMatBoolW18 r.1 && wordShape3DMatBoolW18 r.2 &&
  decide (endInRBoolW18 r.1 = endInRBoolW18 r.2) &&
  [fin3Z0W18, fin3Z1W18, fin3Z2W18].all (fun i =>
    [fin3Z0W18, fin3Z1W18, fin3Z2W18].all (fun j =>
      let cl := evalWord3D9CoeffsW18 r.1 i j
      let cr := evalWord3D9CoeffsW18 r.2 i j
      decide (cl.1 ≥ cr.1 ∧ cl.2.1 ≥ cr.2.1 ∧ cl.2.2.1 ≥ cr.2.2.1 ∧
              cl.2.2.2.1 ≥ cr.2.2.2.1 ∧ cl.2.2.2.2.1 ≥ cr.2.2.2.2.1 ∧
              cl.2.2.2.2.2.1 ≥ cr.2.2.2.2.2.1 ∧ cl.2.2.2.2.2.2.1 ≥ cr.2.2.2.2.2.2.1 ∧
              cl.2.2.2.2.2.2.2.1 ≥ cr.2.2.2.2.2.2.2.1 ∧ cl.2.2.2.2.2.2.2.2 ≥ cr.2.2.2.2.2.2.2.2)))

private def wordRow0BiLin3DBoolW18 (N : Nat) (proj : Fin N -> Fin 42) : List (Fin N) -> Bool
  | [] => true
  | [_] => true
  | [s1, _] => decide ((proj s1).val < 6 ∨ (proj s1).val ≥ 12)
  | [s1, s2, _] =>
    decide (((proj s1).val = 14 ∨ (proj s1).val = 20 ∨ (proj s1).val = 23) ∧
      ((proj s2).val = 13 ∨ (proj s2).val = 16))
  | _ => false

private def wordRow1Const3DBoolW18 (N : Nat) (proj : Fin N -> Fin 42) : List (Fin N) -> Bool
  | [] => true
  | [_] => true
  | s1 :: _ :: _ =>
    let p := (proj s1).val
    decide (p ≠ 33 ∧ p ≠ 35 ∧ p ≠ 39 ∧ p ≠ 40 ∧ p ≠ 41)

private def wordRow2Const3DBoolW18 (N : Nat) (proj : Fin N -> Fin 42) : List (Fin N) -> Bool
  | [] => true
  | [_] => true
  | s1 :: _ :: _ =>
    let p := (proj s1).val
    decide (p ≠ 6 ∧ p ≠ 7 ∧ p ≠ 8 ∧ p ≠ 28 ∧ p ≠ 29 ∧ p ≠ 31 ∧ p ≠ 32 ∧ p ≠ 36 ∧ p ≠ 37 ∧ p ≠ 38)

private def checkWordShape3DFarkasNBoolW18 (N : Nat) (proj : Fin N -> Fin 42)
    (mu0 mu1 mu2 : List (Fin N) -> Nat) (rs : List (List (Fin N) × List (Fin N))) : Bool :=
  rs.all (fun r =>
    wordRow0BiLin3DBoolW18 N proj r.1 && wordRow0BiLin3DBoolW18 N proj r.2 &&
    (decide (mu1 r.1 = 0) || (wordRow1Const3DBoolW18 N proj r.1 && wordRow1Const3DBoolW18 N proj r.2)) &&
    (decide (mu2 r.1 = 0) || (wordRow2Const3DBoolW18 N proj r.1 && wordRow2Const3DBoolW18 N proj r.2)) &&
    decide (mu0 r.1 ≥ 1))

private def evalWordVec3DTupleValW18 (N : Nat) (proj : Fin N -> Fin 42)
    (k alpha beta gamma delta : Nat) (s0Val : Nat) (j0 : Fin 3) :
    List (Fin N) -> Nat × Nat × Nat
  | [] => (0, 0, 0)
  | s :: rest =>
    let eq_s := s.val == s0Val
    let v0 := if eq_s && 0 == j0.val then 1 else 0
    let v1 := if eq_s && 1 == j0.val then 1 else 0
    let v2 := if eq_s && 2 == j0.val then 1 else 0
    let M := rank2BlockNilpMat3DC39 k alpha beta gamma delta (proj s)
    let sub := evalWordVec3DTupleValW18 N proj k alpha beta gamma delta s0Val j0 rest
    (v0 + M fin3Z0W18 fin3Z0W18 * sub.1 + M fin3Z0W18 fin3Z1W18 * sub.2.1 + M fin3Z0W18 fin3Z2W18 * sub.2.2,
     v1 + M fin3Z1W18 fin3Z0W18 * sub.1 + M fin3Z1W18 fin3Z1W18 * sub.2.1 + M fin3Z1W18 fin3Z2W18 * sub.2.2,
     v2 + M fin3Z2W18 fin3Z0W18 * sub.1 + M fin3Z2W18 fin3Z1W18 * sub.2.1 + M fin3Z2W18 fin3Z2W18 * sub.2.2)

private def farkas3DFastPairValW18 (N : Nat) (proj : Fin N -> Fin 42)
    (mu0 m1 m2 : List (Fin N) -> Nat) (k alpha beta gamma delta : Nat)
    (s0Val : Nat) (j0 : Fin 3) : List (List (Fin N) × List (Fin N)) -> Nat × Nat
  | [] => (0, 0)
  | (l, r) :: rs =>
    let sub := farkas3DFastPairValW18 N proj mu0 m1 m2 k alpha beta gamma delta s0Val j0 rs
    let w0 := mu0 l; let w1 := m1 l; let w2 := m2 l
    let vl := evalWordVec3DTupleValW18 N proj k alpha beta gamma delta s0Val j0 l
    let vr := evalWordVec3DTupleValW18 N proj k alpha beta gamma delta s0Val j0 r
    let lhs := w0 * vl.1 + w1 * vl.2.1 + w2 * vl.2.2
    let rhs := w0 * vr.1 + w1 * vr.2.1 + w2 * vr.2.2
    (lhs + sub.1, rhs + sub.2)

private def farkas3DFastPairW18 (N : Nat) (proj : Fin N -> Fin 42)
    (mu0 m1 m2 : List (Fin N) -> Nat) (k alpha beta gamma delta : Nat)
    (s0 : Fin N) (j0 : Fin 3) (rs : List (List (Fin N) × List (Fin N))) : Nat × Nat :=
  farkas3DFastPairValW18 N proj mu0 m1 m2 k alpha beta gamma delta s0.val j0 rs

private theorem farkas3DFastPairW18_eq (N : Nat) (proj : Fin N -> Fin 42)
    (mu0 m1 m2 : List (Fin N) -> Nat) (k alpha beta gamma delta : Nat)
    (s0 : Fin N) (j0 : Fin 3) (rs : List (List (Fin N) × List (Fin N))) :
    farkas3DFastPairW18 N proj mu0 m1 m2 k alpha beta gamma delta s0 j0 rs =
      (farkas3DVecLhsN N proj mu0 m1 m2 k alpha beta gamma delta (basisVec3D N s0 j0) rs,
       farkas3DVecRhsN N proj mu0 m1 m2 k alpha beta gamma delta (basisVec3D N s0 j0) rs) := by
  unfold farkas3DFastPairW18
  let Mfn := fun s => rank2BlockNilpMat3DC39 k alpha beta gamma delta (proj s)
  have hv_eq : ∀ (w : List (Fin N)),
      evalWordVec3DTupleValW18 N proj k alpha beta gamma delta s0.val j0 w =
        (evalFinWordVec N 3 Mfn (basisVec3D N s0 j0) w fin3Z0W18,
         evalFinWordVec N 3 Mfn (basisVec3D N s0 j0) w fin3Z1W18,
         evalFinWordVec N 3 Mfn (basisVec3D N s0 j0) w fin3Z2W18) := by
    intro w; induction w with
    | nil => rfl
    | cons s tl ih =>
      rw [mat3_step_expandN_w18 N Mfn _ s tl fin3Z0W18,
          mat3_step_expandN_w18 N Mfn _ s tl fin3Z1W18,
          mat3_step_expandN_w18 N Mfn _ s tl fin3Z2W18]
      dsimp only [evalWordVec3DTupleValW18, basisVec3D, fin3Z0W18, fin3Z1W18, fin3Z2W18, Mfn]
      rw [ih]
  induction rs with
  | nil => rfl
  | cons r0 rtl ih =>
    rcases r0 with ⟨l, r⟩
    dsimp only [Mfn] at hv_eq
    simp only [farkas3DFastPairValW18, farkas3DVecLhsN, farkas3DVecRhsN, ih, hv_eq]

private def mat3DC39FastNatW18 (k alpha beta gamma delta sv iv jv : Nat) : Nat :=
  if iv == 0 && jv == 0 then
    if Nat.ble 6 sv && Nat.ble sv 11 then k else 1
  else if iv == 0 && jv == 1 then
    if isBeta01SymW18 sv then beta else 0
  else if iv == 0 && jv == 2 then
    if isAlpha02SymW18 sv then alpha else 0
  else if iv == 1 && (jv == 0 || jv == 2) then
    if isDelta1SymW18 sv then delta else 0
  else if iv == 2 && jv == 0 then
    if isGamma20SymW18 sv then gamma else 0
  else if iv == 2 && jv == 2 then
    if Nat.ble 6 sv && Nat.ble sv 8 then 1 else 0
  else 0

private theorem mat3DC39FastNatW18_eq (k alpha beta gamma delta : Nat) (s : Fin 42) (i j : Fin 3) :
    mat3DC39FastNatW18 k alpha beta gamma delta s.val i.val j.val =
      rank2BlockNilpMat3DC39 k alpha beta gamma delta s i j := by
  have hb611 : (Nat.ble 6 s.val && Nat.ble s.val 11) = decide (6 ≤ s.val ∧ s.val ≤ 11) := by
    by_cases h : 6 ≤ s.val ∧ s.val ≤ 11
    · rw [decide_eq_true h, Bool.and_eq_true, Nat.ble_eq, Nat.ble_eq]; exact h
    · rw [decide_eq_false h, Bool.and_eq_false_iff]; by_cases h1 : 6 ≤ s.val
      · right; rw [Bool.eq_false_iff]; intro h2; exact h ⟨h1, Nat.ble_eq.mp h2⟩
      · left; rw [Bool.eq_false_iff]; intro h2; exact h1 (Nat.ble_eq.mp h2)
  have hb68 : (Nat.ble 6 s.val && Nat.ble s.val 8) = decide (6 ≤ s.val ∧ s.val ≤ 8) := by
    by_cases h : 6 ≤ s.val ∧ s.val ≤ 8
    · rw [decide_eq_true h, Bool.and_eq_true, Nat.ble_eq, Nat.ble_eq]; exact h
    · rw [decide_eq_false h, Bool.and_eq_false_iff]; by_cases h1 : 6 ≤ s.val
      · right; rw [Bool.eq_false_iff]; intro h2; exact h ⟨h1, Nat.ble_eq.mp h2⟩
      · left; rw [Bool.eq_false_iff]; intro h2; exact h1 (Nat.ble_eq.mp h2)
  unfold mat3DC39FastNatW18 rank2BlockNilpMat3DC39
  rw [hb611, hb68]

private def evalWordMat3DColFastNatW18 (k alpha beta gamma delta jv : Nat) :
    List Nat -> Nat × Nat × Nat
  | [] => (if jv == 0 then 1 else 0, if jv == 1 then 1 else 0, if jv == 2 then 1 else 0)
  | sv :: rest =>
    let m := mat3DC39FastNatW18 k alpha beta gamma delta sv
    match evalWordMat3DColFastNatW18 k alpha beta gamma delta jv rest with
    | (u0, u1, u2) =>
      (m 0 0 * u0 + m 0 1 * u1 + m 0 2 * u2,
       m 1 0 * u0 + m 1 1 * u1 + m 1 2 * u2,
       m 2 0 * u0 + m 2 1 * u1 + m 2 2 * u2)

private def evalWordMat3DFastNatW18 (k alpha beta gamma delta : Nat)
    (w : List Nat) (iv jv : Nat) : Nat :=
  match evalWordMat3DColFastNatW18 k alpha beta gamma delta jv w with
  | (c0, c1, c2) => if iv == 0 then c0 else if iv == 1 then c1 else c2

private theorem evalWordMat3DFastNatW18_eq_proj (N : Nat) (proj : Fin N -> Fin 42)
    (k alpha beta gamma delta : Nat) (w : List (Fin N)) (i j : Fin 3) :
    evalWordMat3DFastNatW18 k alpha beta gamma delta (w.map (fun s => (proj s).val)) i.val j.val =
      evalFinWordMat N 3 (fun s => rank2BlockNilpMat3DC39 k alpha beta gamma delta (proj s)) w i j := by
  let M := fun s => rank2BlockNilpMat3DC39 k alpha beta gamma delta (proj s)
  have hcol : ∀ xs : List (Fin N),
      evalWordMat3DColFastNatW18 k alpha beta gamma delta j.val (xs.map (fun s => (proj s).val)) =
        (evalFinWordMat N 3 M xs fin3Z0W18 j,
         evalFinWordMat N 3 M xs fin3Z1W18 j,
         evalFinWordMat N 3 M xs fin3Z2W18 j) := by
    intro xs; induction xs with
    | nil =>
      dsimp only [List.map, evalWordMat3DColFastNatW18, evalFinWordMat, natMatId, fin3Z0W18, fin3Z1W18, fin3Z2W18]
      rcases (by have := j.isLt; omega : j.val = 0 ∨ j.val = 1 ∨ j.val = 2) with hj | hj | hj <;> simp [hj]
    | cons s tl ih =>
      simp only [List.map_cons, evalWordMat3DColFastNatW18, ih,
        mat3_mul_step_w18 N M s tl fin3Z0W18 j,
        mat3_mul_step_w18 N M s tl fin3Z1W18 j,
        mat3_mul_step_w18 N M s tl fin3Z2W18 j]
      dsimp only [M]
      simp only [← mat3DC39FastNatW18_eq, fin3Z0W18, fin3Z1W18, fin3Z2W18]
  unfold evalWordMat3DFastNatW18
  rw [hcol w]
  dsimp only
  rcases (by have := i.isLt; omega : i.val = 0 ∨ i.val = 1 ∨ i.val = 2) with hi | hi | hi
  · rw [show i = fin3Z0W18 from Fin.ext hi]; rfl
  · rw [show i = fin3Z1W18 from Fin.ext hi]; rfl
  · rw [show i = fin3Z2W18 from Fin.ext hi]; rfl

private def evalWord3D9CoeffsFastW18 (wn : List Nat) (iv jv : Nat) :
    Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat :=
  let m0 := evalWordMat3DFastNatW18 1 0 0 0 0 wn iv jv
  let ma := evalWordMat3DFastNatW18 1 1 0 0 0 wn iv jv - m0
  let mb := evalWordMat3DFastNatW18 1 0 1 0 0 wn iv jv - m0
  let mg := evalWordMat3DFastNatW18 1 0 0 1 0 wn iv jv - m0
  let md := evalWordMat3DFastNatW18 1 0 0 0 1 wn iv jv - m0
  (m0, ma, mb, mg, md,
   evalWordMat3DFastNatW18 1 1 0 1 0 wn iv jv - m0 - ma - mg,
   evalWordMat3DFastNatW18 1 0 1 0 1 wn iv jv - m0 - mb - md,
   evalWordMat3DFastNatW18 1 1 0 0 1 wn iv jv - m0 - ma - md,
   evalWordMat3DFastNatW18 1 0 1 1 0 wn iv jv - m0 - mb - mg)

private def checkRule3DCornersFastBoolW18 (r : List (Fin 42) × List (Fin 42)) : Bool :=
  wordShape3DMatBoolW18 r.1 && wordShape3DMatBoolW18 r.2 &&
  decide (endInRBoolW18 r.1 = endInRBoolW18 r.2) &&
  [fin3Z0W18, fin3Z1W18, fin3Z2W18].all (fun i =>
    [fin3Z0W18, fin3Z1W18, fin3Z2W18].all (fun j =>
      match evalWord3D9CoeffsFastW18 (r.1.map Fin.val) i.val j.val,
            evalWord3D9CoeffsFastW18 (r.2.map Fin.val) i.val j.val with
      | (l0, la, lb, lg, ld, lag, lbd, lad, lbg),
        (r0, ra, rb, rg, rd, rag, rbd, rad, rbg) =>
        Nat.ble r0 l0 && (Nat.ble ra la && (Nat.ble rb lb &&
        (Nat.ble rg lg && (Nat.ble rd ld &&
        (Nat.ble rag lag && (Nat.ble rbd lbd &&
        (Nat.ble rad lad && Nat.ble rbg lbg)))))))))

private theorem checkRule3DCornersFast_eq_w18 (r : List (Fin 42) × List (Fin 42)) :
    checkRule3DCornersFastBoolW18 r = checkRule3DCornersBoolW18 r := by
  have hc_eq : ∀ (w : List (Fin 42)) (i j : Fin 3),
      evalWord3D9CoeffsFastW18 (w.map Fin.val) i.val j.val = evalWord3D9CoeffsW18 w i j := by
    intro w i j
    unfold evalWord3D9CoeffsFastW18 evalWord3D9CoeffsW18
    have hid : w.map Fin.val = w.map (fun s => (id s).val) := rfl
    rw [hid]
    simp only [evalWordMat3DFastNatW18_eq_proj 42 id]
    rfl
  have hble9 : ∀ (cl cr : Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat),
      (match cl, cr with
       | (l0, la, lb, lg, ld, lag, lbd, lad, lbg),
         (r0, ra, rb, rg, rd, rag, rbd, rad, rbg) =>
         Nat.ble r0 l0 && (Nat.ble ra la && (Nat.ble rb lb &&
         (Nat.ble rg lg && (Nat.ble rd ld &&
         (Nat.ble rag lag && (Nat.ble rbd lbd &&
         (Nat.ble rad lad && Nat.ble rbg lbg)))))))) =
      decide (cl.1 ≥ cr.1 ∧ cl.2.1 ≥ cr.2.1 ∧ cl.2.2.1 ≥ cr.2.2.1 ∧
              cl.2.2.2.1 ≥ cr.2.2.2.1 ∧ cl.2.2.2.2.1 ≥ cr.2.2.2.2.1 ∧
              cl.2.2.2.2.2.1 ≥ cr.2.2.2.2.2.1 ∧ cl.2.2.2.2.2.2.1 ≥ cr.2.2.2.2.2.2.1 ∧
              cl.2.2.2.2.2.2.2.1 ≥ cr.2.2.2.2.2.2.2.1 ∧ cl.2.2.2.2.2.2.2.2 ≥ cr.2.2.2.2.2.2.2.2) := by
    have hble : ∀ a b : Nat, Nat.ble b a = decide (a ≥ b) := by
      intro a b; by_cases h : b ≤ a
      · rw [Nat.ble_eq.mpr h, decide_eq_true h]
      · rw [Bool.eq_false_iff.mpr (fun hb => h (Nat.ble_eq.mp hb)), decide_eq_false h]
    rintro ⟨l0, la, lb, lg, ld, lag, lbd, lad, lbg⟩ ⟨r0, ra, rb, rg, rd, rag, rbd, rad, rbg⟩
    dsimp only
    simp only [hble, ← Bool.decide_and]
  unfold checkRule3DCornersFastBoolW18 checkRule3DCornersBoolW18
  simp only [hc_eq, hble9]

private def countStrictMat3DFastProjW18 (N : Nat) (proj : Fin N -> Fin 42) :
    List (List (Fin N) × List (Fin N)) -> Nat
  | [] => 0
  | (l, r) :: rs =>
    let ln := l.map (fun s => (proj s).val)
    let rn := r.map (fun s => (proj s).val)
    let is_st := [fin3Z0W18, fin3Z1W18, fin3Z2W18].any (fun i =>
      [fin3Z0W18, fin3Z1W18, fin3Z2W18].any (fun j =>
        Nat.ble (evalWordMat3DFastNatW18 2 1 1 1 1 rn i.val j.val + 1)
          (evalWordMat3DFastNatW18 2 1 1 1 1 ln i.val j.val)))
    (if is_st then 1 else 0) + countStrictMat3DFastProjW18 N proj rs

private theorem countStrictMat3DFastProj_eq_w18 (N : Nat) (proj : Fin N -> Fin 42)
    (rs : List (List (Fin N) × List (Fin N))) :
    countStrictMat3DFastProjW18 N proj rs =
      countStrictMat3DRules N (fun s => rank2BlockNilpMat3DC39 2 1 1 1 1 (proj s)) rs := by
  have hlt_ble : ∀ a b : Nat, Nat.ble (b + 1) a = decide (a > b) := by
    intro a b; by_cases h : b < a
    · rw [Nat.ble_eq.mpr h, decide_eq_true h]
    · rw [Bool.eq_false_iff.mpr (fun hb => h (Nat.ble_eq.mp hb)), decide_eq_false h]
  induction rs with
  | nil => rfl
  | cons r0 rtl ih =>
    rcases r0 with ⟨l, r⟩
    unfold countStrictMat3DFastProjW18 countStrictMat3DRules
    dsimp only [fin3Z0W18, fin3Z1W18, fin3Z2W18] at *
    simp only [hlt_ble, evalWordMat3DFastNatW18_eq_proj N proj, ih]

private def pack3DRulesNatW18 (N : Nat) (proj : Fin N -> Fin 42)
    (mu0 mu1 mu2 : List (Fin N) -> Nat) :
    List (List (Fin N) × List (Fin N)) ->
    List (Nat × Nat × Nat × List (Nat × Nat) × List (Nat × Nat))
  | [] => []
  | (l, r) :: rs =>
    (mu0 l, mu1 l, mu2 l,
     l.map (fun s => (s.val, (proj s).val)),
     r.map (fun s => (s.val, (proj s).val))) ::
    pack3DRulesNatW18 N proj mu0 mu1 mu2 rs

private def c39Packed3DW18 : List (Nat × Nat × Nat × List (Nat × Nat) × List (Nat × Nat)) :=
  [(1, 0, 0, [(1, 1), (14, 14)], [(2, 2)]), (9, 0, 0, [(2, 2), (13, 13)], [(1, 1)]),
   (1, 0, 0, [(4, 4), (14, 14)], [(5, 5)]), (2, 0, 0, [(5, 5), (13, 13)], [(4, 4)]),
   (9, 0, 0, [(2, 2), (20, 20)], [(2, 2), (38, 38)]), (8, 0, 0, [(1, 1), (18, 18)], [(2, 2), (36, 36)]),
   (1, 0, 0, [(5, 5), (20, 20)], [(5, 5), (38, 38)]), (1, 0, 0, [(4, 4), (18, 18)], [(5, 5), (36, 36)]),
   (7, 0, 0, [(29, 29), (20, 20)], [(22, 22), (35, 35)]), (6, 10, 0, [(28, 28), (18, 18)], [(22, 22), (33, 33)]),
   (7, 6, 0, [(31, 31), (14, 14)], [(18, 18), (29, 29)]), (9, 0, 0, [(32, 32), (13, 13)], [(18, 18), (28, 28)]),
   (3, 0, 3, [(35, 35), (16, 16)], [(21, 21), (28, 28)]), (1, 0, 0, [(32, 32), (20, 20)], [(14, 14), (38, 38)]),
   (1, 0, 0, [(31, 31), (18, 18)], [(14, 14), (36, 36)]), (4, 0, 4, [(35, 35), (23, 23)], [(17, 17), (38, 38)]),
   (6, 0, 6, [(33, 33), (22, 22)], [(17, 17), (37, 37)]), (1, 0, 0, [(37, 37), (17, 17)], [(13, 13), (32, 32)]),
   (12, 2, 0, [(38, 38), (16, 16)], [(13, 13), (31, 31)]), (9, 0, 0, [(40, 40), (17, 17)], [(16, 16), (32, 32)]),
   (3, 0, 0, [(41, 41), (16, 16)], [(16, 16), (31, 31)]), (3, 0, 0, [(38, 38), (23, 23)], [(20, 20), (41, 41)]),
   (10, 1, 0, [(36, 36), (22, 22)], [(20, 20), (40, 40)]), (2, 0, 0, [(37, 37), (21, 21)], [(20, 20), (39, 39)]),
   (1, 0, 0, [(41, 41), (23, 23)], [(23, 23), (41, 41)]), (3, 0, 1, [(39, 39), (22, 22)], [(23, 23), (40, 40)]),
   (1, 0, 0, [(40, 40), (21, 21)], [(23, 23), (39, 39)]), (2, 0, 0, [(28, 28), (8, 8)], [(22, 22), (11, 11)]),
   (2, 0, 0, [(28, 28), (7, 7)], [(22, 22), (10, 10)]), (2, 0, 0, [(28, 28), (6, 6)], [(22, 22), (9, 9)]),
   (1, 0, 0, [(31, 31), (8, 8)], [(14, 14), (13, 13), (8, 8)]), (1, 0, 0, [(31, 31), (7, 7)], [(14, 14), (13, 13), (7, 7)]),
   (5, 0, 0, [(31, 31), (6, 6)], [(14, 14), (13, 13), (6, 6)]), (1, 0, 0, [(37, 37), (11, 11)], [(20, 20), (16, 16), (8, 8)]),
   (1, 0, 0, [(37, 37), (10, 10)], [(20, 20), (16, 16), (7, 7)]), (1, 0, 0, [(37, 37), (9, 9)], [(20, 20), (16, 16), (6, 6)]),
   (1, 0, 0, [(40, 40), (11, 11)], [(23, 23), (16, 16), (8, 8)]), (1, 0, 0, [(40, 40), (10, 10)], [(23, 23), (16, 16), (7, 7)]),
   (1, 0, 0, [(40, 40), (9, 9)], [(23, 23), (16, 16), (6, 6)])]

private def c78Packed3DW18 : List (Nat × Nat × Nat × List (Nat × Nat) × List (Nat × Nat)) :=
  [(1, 0, 0, [(4, 1), (29, 14)], [(5, 2)]), (2, 0, 0, [(2, 2), (28, 13)], [(4, 1)]),
   (1, 0, 0, [(4, 1), (26, 14)], [(2, 2)]), (2, 0, 0, [(2, 2), (25, 13)], [(1, 1)]),
   (1, 0, 0, [(10, 4), (29, 14)], [(11, 5)]), (2, 0, 0, [(8, 5), (28, 13)], [(10, 4)]),
   (1, 0, 0, [(10, 4), (26, 14)], [(8, 5)]), (2, 0, 0, [(8, 5), (25, 13)], [(7, 4)]),
   (63, 0, 0, [(5, 2), (41, 20)], [(5, 2), (77, 38)]), (1, 0, 0, [(1, 1), (39, 18)], [(5, 2), (75, 36)]),
   (2, 0, 0, [(5, 2), (38, 20)], [(2, 2), (74, 38)]), (1, 0, 0, [(1, 1), (36, 18)], [(2, 2), (72, 36)]),
   (1, 0, 0, [(11, 5), (41, 20)], [(11, 5), (77, 38)]), (1, 0, 0, [(7, 4), (39, 18)], [(11, 5), (75, 36)]),
   (2, 0, 0, [(11, 5), (38, 20)], [(8, 5), (74, 38)]), (1, 0, 0, [(7, 4), (36, 18)], [(8, 5), (72, 36)]),
   (7, 0, 0, [(59, 29), (41, 20)], [(46, 22), (71, 35)]), (10, 1, 0, [(55, 28), (39, 18)], [(46, 22), (69, 33)]),
   (32, 0, 0, [(59, 29), (38, 20)], [(43, 22), (68, 35)]), (1, 34, 0, [(55, 28), (36, 18)], [(43, 22), (66, 33)]),
   (39, 10, 0, [(64, 31), (29, 14)], [(39, 18), (59, 29)]), (1, 0, 0, [(62, 32), (28, 13)], [(36, 18), (58, 28)]),
   (3, 1, 0, [(64, 31), (26, 14)], [(36, 18), (56, 29)]), (7, 0, 0, [(62, 32), (25, 13)], [(39, 18), (55, 28)]),
   (2, 0, 2, [(68, 35), (34, 16)], [(42, 21), (58, 28)]), (30, 0, 30, [(68, 35), (31, 16)], [(45, 21), (55, 28)]),
   (8, 0, 0, [(65, 32), (41, 20)], [(29, 14), (77, 38)]), (33, 0, 0, [(61, 31), (39, 18)], [(29, 14), (75, 36)]),
   (1, 0, 0, [(65, 32), (38, 20)], [(26, 14), (74, 38)]), (1, 0, 0, [(61, 31), (36, 18)], [(26, 14), (72, 36)]),
   (1, 0, 0, [(71, 35), (47, 23)], [(35, 17), (77, 38)]), (2, 0, 1, [(69, 33), (46, 22)], [(32, 17), (76, 37)]),
   (6, 0, 7, [(71, 35), (44, 23)], [(32, 17), (74, 38)]), (8, 0, 9, [(69, 33), (43, 22)], [(35, 17), (73, 37)]),
   (1, 0, 0, [(76, 37), (35, 17)], [(28, 13), (65, 32)]), (5, 0, 0, [(74, 38), (34, 16)], [(25, 13), (64, 31)]),
   (1, 1, 0, [(76, 37), (32, 17)], [(25, 13), (62, 32)]), (4, 1, 0, [(74, 38), (31, 16)], [(28, 13), (61, 31)]),
   (8, 0, 0, [(82, 40), (35, 17)], [(34, 16), (65, 32)]), (37, 0, 7, [(80, 41), (34, 16)], [(31, 16), (64, 31)]),
   (7, 0, 9, [(82, 40), (32, 17)], [(31, 16), (62, 32)]), (36, 0, 37, [(80, 41), (31, 16)], [(34, 16), (61, 31)]),
   (44, 0, 0, [(77, 38), (47, 23)], [(41, 20), (83, 41)]), (1, 1, 0, [(75, 36), (46, 22)], [(38, 20), (82, 40)]),
   (1, 0, 0, [(73, 37), (45, 21)], [(41, 20), (81, 39)]), (29, 0, 0, [(77, 38), (44, 23)], [(38, 20), (80, 41)]),
   (34, 8, 0, [(75, 36), (43, 22)], [(41, 20), (79, 40)]), (1, 0, 0, [(73, 37), (42, 21)], [(38, 20), (78, 39)]),
   (1, 0, 1, [(83, 41), (47, 23)], [(47, 23), (83, 41)]), (14, 0, 29, [(81, 39), (46, 22)], [(44, 23), (82, 40)]),
   (29, 0, 0, [(79, 40), (45, 21)], [(47, 23), (81, 39)]), (44, 0, 0, [(83, 41), (44, 23)], [(44, 23), (80, 41)]),
   (16, 0, 0, [(81, 39), (43, 22)], [(47, 23), (79, 40)]), (1, 0, 0, [(79, 40), (42, 21)], [(44, 23), (78, 39)]),
   (2, 0, 0, [(55, 28), (17, 8)], [(43, 22), (23, 11)]), (2, 0, 0, [(55, 28), (16, 7)], [(43, 22), (22, 10)]),
   (2, 0, 0, [(55, 28), (15, 6)], [(43, 22), (21, 9)]), (2, 0, 0, [(55, 28), (14, 8)], [(43, 22), (20, 11)]),
   (2, 0, 0, [(55, 28), (13, 7)], [(43, 22), (19, 10)]), (16, 0, 0, [(55, 28), (12, 6)], [(43, 22), (18, 9)]),
   (1, 0, 0, [(61, 31), (17, 8)], [(26, 14), (25, 13), (17, 8)]), (1, 0, 0, [(61, 31), (16, 7)], [(26, 14), (25, 13), (16, 7)]),
   (1, 0, 0, [(61, 31), (15, 6)], [(26, 14), (25, 13), (15, 6)]), (1, 0, 0, [(61, 31), (14, 8)], [(26, 14), (25, 13), (14, 8)]),
   (1, 0, 0, [(61, 31), (13, 7)], [(26, 14), (25, 13), (13, 7)]), (1, 0, 0, [(61, 31), (12, 6)], [(26, 14), (25, 13), (12, 6)]),
   (1, 0, 0, [(73, 37), (23, 11)], [(38, 20), (31, 16), (17, 8)]), (1, 0, 0, [(73, 37), (22, 10)], [(38, 20), (31, 16), (16, 7)]),
   (1, 0, 0, [(73, 37), (21, 9)], [(38, 20), (31, 16), (15, 6)]), (1, 0, 0, [(73, 37), (20, 11)], [(38, 20), (31, 16), (14, 8)]),
   (1, 0, 0, [(73, 37), (19, 10)], [(38, 20), (31, 16), (13, 7)]), (1, 0, 0, [(73, 37), (18, 9)], [(38, 20), (31, 16), (12, 6)]),
   (1, 0, 0, [(79, 40), (23, 11)], [(44, 23), (31, 16), (17, 8)]), (1, 0, 0, [(79, 40), (22, 10)], [(44, 23), (31, 16), (16, 7)]),
   (1, 0, 0, [(79, 40), (21, 9)], [(44, 23), (31, 16), (15, 6)]), (1, 0, 0, [(79, 40), (20, 11)], [(44, 23), (31, 16), (14, 8)]),
   (1, 0, 0, [(79, 40), (19, 10)], [(44, 23), (31, 16), (13, 7)]), (15, 0, 15, [(79, 40), (18, 9)], [(44, 23), (31, 16), (12, 6)])]

set_option maxRecDepth 65536 in
private theorem c39Packed3DW18_beq :
    (pack3DRulesNatW18 42 id farkasMu0CoupledC39 farkasMu1BlockNilp3DC39 farkasMu1BiBTRC39 c39FastRulesW18 ==
      c39Packed3DW18) = true := by decide

private theorem c39Packed3DW18_eq :
    pack3DRulesNatW18 42 id farkasMu0CoupledC39 farkasMu1BlockNilp3DC39 farkasMu1BiBTRC39 c39FastRulesW18 =
      c39Packed3DW18 := beq_iff_eq.mp c39Packed3DW18_beq

set_option maxRecDepth 65536 in
private theorem c78Packed3DW18_beq :
    (pack3DRulesNatW18 84 projSym84To42 farkasMu0CoupledC78 farkasMu1BlockNilp3DC78 farkasMu1BiBTRC78 c78FastRulesW18 ==
      c78Packed3DW18) = true := by decide

private theorem c78Packed3DW18_eq :
    pack3DRulesNatW18 84 projSym84To42 farkasMu0CoupledC78 farkasMu1BlockNilp3DC78 farkasMu1BiBTRC78 c78FastRulesW18 =
      c78Packed3DW18 := beq_iff_eq.mp c78Packed3DW18_beq

private def evalPackedWordVec3DW18 (k alpha beta gamma delta s0Val j0Val : Nat) :
    List (Nat × Nat) -> Nat × Nat × Nat
  | [] => (0, 0, 0)
  | (sv, pv) :: rest =>
    let eq_s := sv == s0Val
    let v0 := if eq_s && 0 == j0Val then 1 else 0
    let v1 := if eq_s && 1 == j0Val then 1 else 0
    let v2 := if eq_s && 2 == j0Val then 1 else 0
    match evalPackedWordVec3DW18 k alpha beta gamma delta s0Val j0Val rest with
    | (0, 0, 0) => (v0, v1, v2)
    | (u0, u1, u2) =>
      (v0 + (if Nat.ble 6 pv && Nat.ble pv 11 then k else 1) * u0 +
            (if beta == 0 then 0 else if isBeta01SymW18 pv then beta * u1 else 0) +
            (if alpha == 0 then 0 else if isAlpha02SymW18 pv then alpha * u2 else 0),
       v1 + (if delta == 0 then 0 else if isDelta1SymW18 pv then delta * u0 + delta * u2 else 0),
       v2 + (if gamma == 0 then 0 else if isGamma20SymW18 pv then gamma * u0 else 0) +
            (if Nat.ble 6 pv && Nat.ble pv 8 then u2 else 0))

private theorem evalPackedWordVec3DW18_step_eq (k alpha beta gamma delta s0Val j0Val sv pv : Nat)
    (rest : List (Nat × Nat)) :
    evalPackedWordVec3DW18 k alpha beta gamma delta s0Val j0Val ((sv, pv) :: rest) =
      let eq_s := sv == s0Val
      let v0 := if eq_s && 0 == j0Val then 1 else 0
      let v1 := if eq_s && 1 == j0Val then 1 else 0
      let v2 := if eq_s && 2 == j0Val then 1 else 0
      let m := mat3DC39FastNatW18 k alpha beta gamma delta pv
      let sub := evalPackedWordVec3DW18 k alpha beta gamma delta s0Val j0Val rest
      (v0 + m 0 0 * sub.1 + m 0 1 * sub.2.1 + m 0 2 * sub.2.2,
       v1 + m 1 0 * sub.1 + m 1 1 * sub.2.1 + m 1 2 * sub.2.2,
       v2 + m 2 0 * sub.1 + m 2 1 * sub.2.1 + m 2 2 * sub.2.2) := by
  have hb_eq : ∀ u1 : Nat,
      (if beta == 0 then 0 else if isBeta01SymW18 pv then beta * u1 else 0) =
        mat3DC39FastNatW18 k alpha beta gamma delta pv 0 1 * u1 := by
    intro u1; change _ = (if isBeta01SymW18 pv then beta else 0) * u1
    cases beta <;> cases isBeta01SymW18 pv <;> simp [Nat.zero_mul]
  have ha_eq : ∀ u2 : Nat,
      (if alpha == 0 then 0 else if isAlpha02SymW18 pv then alpha * u2 else 0) =
        mat3DC39FastNatW18 k alpha beta gamma delta pv 0 2 * u2 := by
    intro u2; change _ = (if isAlpha02SymW18 pv then alpha else 0) * u2
    cases alpha <;> cases isAlpha02SymW18 pv <;> simp [Nat.zero_mul]
  have hd_eq : ∀ u0 u1 u2 : Nat,
      (if delta == 0 then 0 else if isDelta1SymW18 pv then delta * u0 + delta * u2 else 0) =
        mat3DC39FastNatW18 k alpha beta gamma delta pv 1 0 * u0 +
        mat3DC39FastNatW18 k alpha beta gamma delta pv 1 1 * u1 +
        mat3DC39FastNatW18 k alpha beta gamma delta pv 1 2 * u2 := by
    intro u0 u1 u2
    change _ = (if isDelta1SymW18 pv then delta else 0) * u0 + 0 * u1 + (if isDelta1SymW18 pv then delta else 0) * u2
    cases delta <;> cases isDelta1SymW18 pv <;> simp [Nat.zero_mul]
  have hg_eq : ∀ u0 : Nat,
      (if gamma == 0 then 0 else if isGamma20SymW18 pv then gamma * u0 else 0) =
        mat3DC39FastNatW18 k alpha beta gamma delta pv 2 0 * u0 := by
    intro u0; change _ = (if isGamma20SymW18 pv then gamma else 0) * u0
    cases gamma <;> cases isGamma20SymW18 pv <;> simp [Nat.zero_mul]
  have h22_eq : ∀ u2 : Nat,
      (if Nat.ble 6 pv && Nat.ble pv 8 then u2 else 0) =
        mat3DC39FastNatW18 k alpha beta gamma delta pv 2 2 * u2 := by
    intro u2; change _ = (if Nat.ble 6 pv && Nat.ble pv 8 then 1 else 0) * u2
    cases (Nat.ble 6 pv && Nat.ble pv 8) <;> simp
  have h00_eq : mat3DC39FastNatW18 k alpha beta gamma delta pv 0 0 =
      (if Nat.ble 6 pv && Nat.ble pv 11 then k else 1) := rfl
  have h21_eq : mat3DC39FastNatW18 k alpha beta gamma delta pv 2 1 = 0 := rfl
  dsimp only [evalPackedWordVec3DW18]
  rcases evalPackedWordVec3DW18 k alpha beta gamma delta s0Val j0Val rest with ⟨u0, u1, u2⟩
  have hbody :
      (let eq_s := sv == s0Val
       let v0 := if eq_s && 0 == j0Val then 1 else 0
       let v1 := if eq_s && 1 == j0Val then 1 else 0
       let v2 := if eq_s && 2 == j0Val then 1 else 0
       (v0 + (if Nat.ble 6 pv && Nat.ble pv 11 then k else 1) * u0 +
             (if beta == 0 then 0 else if isBeta01SymW18 pv then beta * u1 else 0) +
             (if alpha == 0 then 0 else if isAlpha02SymW18 pv then alpha * u2 else 0),
        v1 + (if delta == 0 then 0 else if isDelta1SymW18 pv then delta * u0 + delta * u2 else 0),
        v2 + (if gamma == 0 then 0 else if isGamma20SymW18 pv then gamma * u0 else 0) +
             (if Nat.ble 6 pv && Nat.ble pv 8 then u2 else 0))) =
      (let eq_s := sv == s0Val
       let v0 := if eq_s && 0 == j0Val then 1 else 0
       let v1 := if eq_s && 1 == j0Val then 1 else 0
       let v2 := if eq_s && 2 == j0Val then 1 else 0
       let m := mat3DC39FastNatW18 k alpha beta gamma delta pv
       (v0 + m 0 0 * u0 + m 0 1 * u1 + m 0 2 * u2,
        v1 + m 1 0 * u0 + m 1 1 * u1 + m 1 2 * u2,
        v2 + m 2 0 * u0 + m 2 1 * u1 + m 2 2 * u2)) := by
    dsimp only
    rw [hb_eq u1, ha_eq u2, hd_eq u0 u1 u2, hg_eq u0, h22_eq u2, h00_eq, h21_eq]
    simp only [Nat.zero_mul, Nat.add_zero, ← Nat.add_assoc]
  by_cases hz : u0 = 0 ∧ u1 = 0 ∧ u2 = 0
  · rcases hz with ⟨rfl, rfl, rfl⟩
    dsimp only
    simp only [Nat.mul_zero, Nat.add_zero]
  · have hstep :
        (match (u0, u1, u2) with
         | (0, 0, 0) => (if (sv == s0Val) && 0 == j0Val then 1 else 0,
                         if (sv == s0Val) && 1 == j0Val then 1 else 0,
                         if (sv == s0Val) && 2 == j0Val then 1 else 0)
         | (u0, u1, u2) =>
           ((if (sv == s0Val) && 0 == j0Val then 1 else 0) +
              (if Nat.ble 6 pv && Nat.ble pv 11 then k else 1) * u0 +
              (if beta == 0 then 0 else if isBeta01SymW18 pv then beta * u1 else 0) +
              (if alpha == 0 then 0 else if isAlpha02SymW18 pv then alpha * u2 else 0),
            (if (sv == s0Val) && 1 == j0Val then 1 else 0) +
              (if delta == 0 then 0 else if isDelta1SymW18 pv then delta * u0 + delta * u2 else 0),
            (if (sv == s0Val) && 2 == j0Val then 1 else 0) +
              (if gamma == 0 then 0 else if isGamma20SymW18 pv then gamma * u0 else 0) +
              (if Nat.ble 6 pv && Nat.ble pv 8 then u2 else 0))) =
        (let eq_s := sv == s0Val
         let v0 := if eq_s && 0 == j0Val then 1 else 0
         let v1 := if eq_s && 1 == j0Val then 1 else 0
         let v2 := if eq_s && 2 == j0Val then 1 else 0
         (v0 + (if Nat.ble 6 pv && Nat.ble pv 11 then k else 1) * u0 +
               (if beta == 0 then 0 else if isBeta01SymW18 pv then beta * u1 else 0) +
               (if alpha == 0 then 0 else if isAlpha02SymW18 pv then alpha * u2 else 0),
          v1 + (if delta == 0 then 0 else if isDelta1SymW18 pv then delta * u0 + delta * u2 else 0),
          v2 + (if gamma == 0 then 0 else if isGamma20SymW18 pv then gamma * u0 else 0) +
               (if Nat.ble 6 pv && Nat.ble pv 8 then u2 else 0))) := by
      cases u0 with
      | zero => cases u1 with
        | zero => cases u2 with | zero => exact False.elim (hz ⟨rfl, rfl, rfl⟩) | succ _ => rfl
        | succ _ => rfl
      | succ _ => rfl
    rw [hstep, hbody]

private def wordHasSym3DW18 (s0Val : Nat) : List (Nat × Nat) -> Bool
  | [] => false
  | (sv, _) :: tl => if sv == s0Val then true else wordHasSym3DW18 s0Val tl

private theorem evalPackedWordVec3DW18_zero_of_not_has (k alpha beta gamma delta s0Val j0Val : Nat) :
    ∀ lp : List (Nat × Nat), wordHasSym3DW18 s0Val lp = false ->
      evalPackedWordVec3DW18 k alpha beta gamma delta s0Val j0Val lp = (0, 0, 0)
  | [], _ => rfl
  | (sv, pv) :: rest, h => by
    unfold wordHasSym3DW18 at h
    cases heq : sv == s0Val
    · rw [heq] at h; dsimp at h
      rw [evalPackedWordVec3DW18_step_eq]
      simp only [heq, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
        evalPackedWordVec3DW18_zero_of_not_has k alpha beta gamma delta s0Val j0Val rest h,
        Nat.mul_zero, Nat.add_zero]
    · rw [heq] at h; cases h

private def farkas3DPackedPairW18 (use1 use2 : Bool)
    (k alpha beta gamma delta s0Val j0Val : Nat) :
    List (Nat × Nat × Nat × List (Nat × Nat) × List (Nat × Nat)) -> Nat × Nat
  | [] => (0, 0)
  | (w0, u1, u2, lp, rp) :: tl =>
    if !(wordHasSym3DW18 s0Val lp || wordHasSym3DW18 s0Val rp) then
      farkas3DPackedPairW18 use1 use2 k alpha beta gamma delta s0Val j0Val tl
    else
      let w1 := if use1 then u1 else 0
      let w2 := if use2 then u2 else 0
      match farkas3DPackedPairW18 use1 use2 k alpha beta gamma delta s0Val j0Val tl,
            evalPackedWordVec3DW18 k alpha beta gamma delta s0Val j0Val lp,
            evalPackedWordVec3DW18 k alpha beta gamma delta s0Val j0Val rp with
      | (sl, sr), (vl0, vl1, vl2), (vr0, vr1, vr2) =>
        (w0 * vl0 + (if use1 then w1 * vl1 else 0) + (if use2 then w2 * vl2 else 0) + sl,
         w0 * vr0 + (if use1 then w1 * vr1 else 0) + (if use2 then w2 * vr2 else 0) + sr)

private theorem farkas3DPackedPairW18_eq (N : Nat) (proj : Fin N -> Fin 42)
    (mu0 mu1 mu2 : List (Fin N) -> Nat) (use1 use2 : Bool)
    (k alpha beta gamma delta s0Val : Nat) (j0 : Fin 3)
    (rs : List (List (Fin N) × List (Fin N))) :
    farkas3DPackedPairW18 use1 use2 k alpha beta gamma delta s0Val j0.val
      (pack3DRulesNatW18 N proj mu0 mu1 mu2 rs) =
    farkas3DFastPairValW18 N proj mu0
      (if use1 then mu1 else fun _ => 0)
      (if use2 then mu2 else fun _ => 0)
      k alpha beta gamma delta s0Val j0 rs := by
  have hw_eq : ∀ w : List (Fin N),
      evalPackedWordVec3DW18 k alpha beta gamma delta s0Val j0.val
        (w.map (fun s => (s.val, (proj s).val))) =
      evalWordVec3DTupleValW18 N proj k alpha beta gamma delta s0Val j0 w := by
    intro w; induction w with
    | nil => rfl
    | cons s tl ih =>
      simp only [List.map_cons, evalPackedWordVec3DW18_step_eq, ih]
      conv => rhs; unfold evalWordVec3DTupleValW18
      rcases evalWordVec3DTupleValW18 N proj k alpha beta gamma delta s0Val j0 tl with ⟨u0, u1, u2⟩
      simp only [
        mat3DC39FastNatW18_eq k alpha beta gamma delta (proj s) fin3Z0W18 fin3Z0W18,
        mat3DC39FastNatW18_eq k alpha beta gamma delta (proj s) fin3Z0W18 fin3Z1W18,
        mat3DC39FastNatW18_eq k alpha beta gamma delta (proj s) fin3Z0W18 fin3Z2W18,
        mat3DC39FastNatW18_eq k alpha beta gamma delta (proj s) fin3Z1W18 fin3Z0W18,
        mat3DC39FastNatW18_eq k alpha beta gamma delta (proj s) fin3Z1W18 fin3Z1W18,
        mat3DC39FastNatW18_eq k alpha beta gamma delta (proj s) fin3Z1W18 fin3Z2W18,
        mat3DC39FastNatW18_eq k alpha beta gamma delta (proj s) fin3Z2W18 fin3Z0W18,
        mat3DC39FastNatW18_eq k alpha beta gamma delta (proj s) fin3Z2W18 fin3Z1W18,
        mat3DC39FastNatW18_eq k alpha beta gamma delta (proj s) fin3Z2W18 fin3Z2W18]
  induction rs with
  | nil => rfl
  | cons r0 rtl ih =>
    rcases r0 with ⟨l, r⟩
    let lp := l.map (fun s => (s.val, (proj s).val))
    let rp := r.map (fun s => (s.val, (proj s).val))
    simp only [pack3DRulesNatW18, farkas3DPackedPairW18, farkas3DFastPairValW18]
    cases hhas : wordHasSym3DW18 s0Val lp || wordHasSym3DW18 s0Val rp
    · dsimp only [lp, rp] at hhas
      rcases Bool.or_eq_false_iff.mp hhas with ⟨hnl, hnr⟩
      have hzl := (hw_eq l).symm.trans (evalPackedWordVec3DW18_zero_of_not_has k alpha beta gamma delta s0Val j0.val _ hnl)
      have hzr := (hw_eq r).symm.trans (evalPackedWordVec3DW18_zero_of_not_has k alpha beta gamma delta s0Val j0.val _ hnr)
      simp only [Bool.not_false, ↓reduceIte, ih, hzl, hzr, Nat.mul_zero, Nat.add_zero, Nat.zero_add]
    · dsimp only [lp, rp] at hhas
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hw_eq, ih]
      rcases farkas3DFastPairValW18 N proj mu0 (if use1 then mu1 else fun _ => 0)
        (if use2 then mu2 else fun _ => 0) k alpha beta gamma delta s0Val j0 rtl with ⟨sl, sr⟩
      rcases evalWordVec3DTupleValW18 N proj k alpha beta gamma delta s0Val j0 l with ⟨vl0, vl1, vl2⟩
      rcases evalWordVec3DTupleValW18 N proj k alpha beta gamma delta s0Val j0 r with ⟨vr0, vr1, vr2⟩
      cases use1 <;> cases use2 <;> simp only [↓reduceIte, Bool.false_eq_true, Nat.zero_mul]

private def check3DFarkasPackedRangeW18
    (pk : List (Nat × Nat × Nat × List (Nat × Nat) × List (Nat × Nat)))
    (j0Val start : Nat) : Nat -> Bool
  | 0 => true
  | cnt + 1 =>
    let idx := start + cnt
    match farkas3DPackedPairW18 false false 1 0 0 0 0 idx j0Val pk,
          farkas3DPackedPairW18 false true 1 1 0 0 0 idx j0Val pk,
          farkas3DPackedPairW18 true false 1 0 1 0 0 idx j0Val pk with
    | (p0l, p0r), (pal, par), (pbl, pbr) =>
      Nat.ble p0l p0r && Nat.ble (pal - p0l) (par - p0r) &&
        Nat.ble (pbl - p0l) (pbr - p0r) &&
        check3DFarkasPackedRangeW18 pk j0Val start cnt

private theorem check3DFarkasPackedRangeW18_append
    (pk : List (Nat × Nat × Nat × List (Nat × Nat) × List (Nat × Nat)))
    (j0Val a b : Nat)
    (ha : check3DFarkasPackedRangeW18 pk j0Val 0 a = true)
    (hb : check3DFarkasPackedRangeW18 pk j0Val a b = true) :
    check3DFarkasPackedRangeW18 pk j0Val 0 (a + b) = true := by
  induction b with
  | zero => simpa using ha
  | succ b' ih =>
    rw [show a + (b' + 1) = (a + b') + 1 by omega]
    unfold check3DFarkasPackedRangeW18 at hb ⊢
    dsimp only at hb ⊢
    rw [Nat.zero_add]
    rcases hp0 : farkas3DPackedPairW18 false false 1 0 0 0 0 (a + b') j0Val pk with ⟨p0l, p0r⟩
    rcases hpa : farkas3DPackedPairW18 false true 1 1 0 0 0 (a + b') j0Val pk with ⟨pal, par⟩
    rcases hpb : farkas3DPackedPairW18 true false 1 0 1 0 0 (a + b') j0Val pk with ⟨pbl, pbr⟩
    simp only [hp0, hpa, hpb] at hb ⊢
    rcases bool_and_split hb with ⟨hc, hprev⟩
    rw [hc, ih hprev]; rfl

private def proj84NatW18 (v : Nat) : Nat :=
  (v / 12) * 6 + ((v % 12) / 6) * 3 + (v % 3)

private theorem c78_proj_to_c39_fast_w18 :
    c78FastRulesW18.all (fun r =>
      c39FastRulesW18.any (fun r39 =>
        (r.1.map projSym84To42, r.2.map projSym84To42) == r39)) = true := by
  have hb39 : c39RawRulesW18.all (fun r =>
      r.1.all (fun x => Nat.ble (x + 1) 42) && r.2.all (fun x => Nat.ble (x + 1) 42)) = true := by decide
  have hb78 : c78RawRulesW18.all (fun r =>
      r.1.all (fun x => Nat.ble (x + 1) 84) && r.2.all (fun x => Nat.ble (x + 1) 84)) = true := by decide
  have hraw : c78RawRulesW18.all (fun r =>
      c39RawRulesW18.any (fun r39 =>
        (r.1.map proj84NatW18, r.2.map proj84NatW18) == r39)) = true := by decide
  have hfin_eq_val : ∀ (u v : List (Fin 42)), (u == v) = (u.map Fin.val == v.map Fin.val) := by
    intro u; induction u with
    | nil => intro v; cases v <;> rfl
    | cons a utl ih =>
      intro v; cases v with
      | nil => rfl
      | cons b vtl =>
        have hab : (a == b) = (a.val == b.val) := rfl
        change ((a == b) && (utl == vtl)) = ((a.val == b.val) && (utl.map Fin.val == vtl.map Fin.val))
        rw [hab, ih vtl]
  have hany_eq : ∀ (lp rp : List (Fin 42)) (rs39 : List (List Nat × List Nat)),
      rs39.all (fun r => r.1.all (fun x => Nat.ble (x + 1) 42) && r.2.all (fun x => Nat.ble (x + 1) 42)) = true ->
      (toFinRulesW18 42 (by decide) rs39).any (fun r39 => (lp, rp) == r39) =
        rs39.any (fun r39 => (lp.map Fin.val, rp.map Fin.val) == r39) := by
    intro lp rp rs39; induction rs39 with
    | nil => intros; rfl
    | cons r0 rtl ih =>
      rcases r0 with ⟨l0, r0⟩
      intro hall; simp only [List.all_cons] at hall
      cases hlr : (l0.all (fun x => Nat.ble (x + 1) 42) && r0.all (fun x => Nat.ble (x + 1) 42))
      · rw [hlr] at hall; cases hall
      · rw [hlr, Bool.true_and] at hall
        rcases Bool.and_eq_true_iff.mp hlr with ⟨hl0, hr0⟩
        simp only [toFinRulesW18, List.any_cons, ih hall]
        have hp_eq : ((lp, rp) == (toFinWordW18 42 (by decide) l0, toFinWordW18 42 (by decide) r0)) =
            ((lp.map Fin.val, rp.map Fin.val) == (l0, r0)) := by
          change ((lp == toFinWordW18 42 (by decide) l0) && (rp == toFinWordW18 42 (by decide) r0)) =
            ((lp.map Fin.val == l0) && (rp.map Fin.val == r0))
          rw [hfin_eq_val lp _, hfin_eq_val rp _,
              toFinWordW18_map_val 42 (by decide) l0 hl0,
              toFinWordW18_map_val 42 (by decide) r0 hr0]
        rw [hp_eq]
  have hmap_proj : ∀ (w : List (Fin 84)),
      (w.map projSym84To42).map Fin.val = (w.map Fin.val).map proj84NatW18 := by
    intro w; induction w with | nil => rfl | cons s tl ih => simp only [List.map_cons, ih]; rfl
  have hall78_eq : ∀ (rs78 : List (List Nat × List Nat)),
      rs78.all (fun r => r.1.all (fun x => Nat.ble (x + 1) 84) && r.2.all (fun x => Nat.ble (x + 1) 84)) = true ->
      (toFinRulesW18 84 (by decide) rs78).all (fun r =>
        c39FastRulesW18.any (fun r39 => (r.1.map projSym84To42, r.2.map projSym84To42) == r39)) =
      rs78.all (fun r =>
        c39RawRulesW18.any (fun r39 => (r.1.map proj84NatW18, r.2.map proj84NatW18) == r39)) := by
    intro rs78; induction rs78 with
    | nil => intros; rfl
    | cons r0 rtl ih =>
      rcases r0 with ⟨l, r⟩
      intro hall; simp only [List.all_cons] at hall
      cases hlr : (l.all (fun x => Nat.ble (x + 1) 84) && r.all (fun x => Nat.ble (x + 1) 84))
      · rw [hlr] at hall; cases hall
      · rw [hlr, Bool.true_and] at hall
        rcases Bool.and_eq_true_iff.mp hlr with ⟨hl_b, hr_b⟩
        simp only [toFinRulesW18, List.all_cons, ih hall]
        unfold c39FastRulesW18
        rw [hany_eq _ _ c39RawRulesW18 hb39, hmap_proj, hmap_proj,
            toFinWordW18_map_val 84 (by decide) l hl_b,
            toFinWordW18_map_val 84 (by decide) r hr_b]
  change (toFinRulesW18 84 (by decide) c78RawRulesW18).all _ = true
  rw [hall78_eq c78RawRulesW18 hb78]; exact hraw

set_option maxRecDepth 65536 in
private theorem bn3d_fast_corners_c39_only_w18 :
    c39FastRulesW18.all checkRule3DCornersFastBoolW18 = true := by decide

private theorem bn3d_fast_corners_c39_w18 :
    c39FastRulesW18.all checkRule3DCornersFastBoolW18 = true ∧
    c78FastRulesW18.all (fun r =>
      c39FastRulesW18.any (fun r39 =>
        (r.1.map projSym84To42, r.2.map projSym84To42) == r39)) = true :=
  ⟨bn3d_fast_corners_c39_only_w18, c78_proj_to_c39_fast_w18⟩

set_option maxRecDepth 65536 in
private theorem bn3d_fast_farkas_shapes_w18 :
    checkWordShape3DFarkasNBoolW18 42 id
      farkasMu0CoupledC39 farkasMu1BlockNilp3DC39 farkasMu1BiBTRC39 c39FastRulesW18 = true ∧
    checkWordShape3DFarkasNBoolW18 84 projSym84To42
      farkasMu0CoupledC78 farkasMu1BlockNilp3DC78 farkasMu1BiBTRC78 c78FastRulesW18 = true := by decide

set_option maxRecDepth 65536 in
private theorem bn3d_fast_strict_counts_w18 :
    countStrictMat3DFastProjW18 42 id c39FastRulesW18 = 37 ∧
    countStrictMat3DFastProjW18 84 projSym84To42 c78FastRulesW18 = 74 := by decide

private theorem bn3d_fast_corners_and_counts_w18 :
    c39FastRulesW18.all checkRule3DCornersFastBoolW18 = true ∧
    c78FastRulesW18.all (fun r =>
      c39FastRulesW18.any (fun r39 =>
        (r.1.map projSym84To42, r.2.map projSym84To42) == r39)) = true ∧
    checkWordShape3DFarkasNBoolW18 42 id
      farkasMu0CoupledC39 farkasMu1BlockNilp3DC39 farkasMu1BiBTRC39 c39FastRulesW18 = true ∧
    checkWordShape3DFarkasNBoolW18 84 projSym84To42
      farkasMu0CoupledC78 farkasMu1BlockNilp3DC78 farkasMu1BiBTRC78 c78FastRulesW18 = true ∧
    countStrictMat3DFastProjW18 42 id c39FastRulesW18 = 37 ∧
    countStrictMat3DFastProjW18 84 projSym84To42 c78FastRulesW18 = 74 :=
  ⟨bn3d_fast_corners_c39_w18.1, bn3d_fast_corners_c39_w18.2,
   bn3d_fast_farkas_shapes_w18.1, bn3d_fast_farkas_shapes_w18.2,
   bn3d_fast_strict_counts_w18.1, bn3d_fast_strict_counts_w18.2⟩

private def farkas3DPackedR1FromU2W18
    (k alpha beta gamma delta s0Val j0Val : Nat) :
    List (Nat × Nat × Nat × List (Nat × Nat) × List (Nat × Nat)) -> Nat × Nat
  | [] => (0, 0)
  | (w0, _, u2, lp, rp) :: tl =>
    match farkas3DPackedR1FromU2W18 k alpha beta gamma delta s0Val j0Val tl,
          evalPackedWordVec3DW18 k alpha beta gamma delta s0Val j0Val lp,
          evalPackedWordVec3DW18 k alpha beta gamma delta s0Val j0Val rp with
    | (sl, sr), (vl0, vl1, _), (vr0, vr1, _) =>
      (w0 * vl0 + u2 * vl1 + sl, w0 * vr0 + u2 * vr1 + sr)

private theorem farkas3DPackedR1FromU2W18_eq (N : Nat) (proj : Fin N -> Fin 42)
    (mu0 mu1 mu2 : List (Fin N) -> Nat)
    (k alpha beta gamma delta s0Val : Nat) (j0 : Fin 3)
    (rs : List (List (Fin N) × List (Fin N))) :
    farkas3DPackedR1FromU2W18 k alpha beta gamma delta s0Val j0.val
      (pack3DRulesNatW18 N proj mu0 mu1 mu2 rs) =
    farkas3DFastPairValW18 N proj mu0 mu2 (fun _ => 0)
      k alpha beta gamma delta s0Val j0 rs := by
  have hw_eq : ∀ w : List (Fin N),
      evalPackedWordVec3DW18 k alpha beta gamma delta s0Val j0.val
        (w.map (fun s => (s.val, (proj s).val))) =
      evalWordVec3DTupleValW18 N proj k alpha beta gamma delta s0Val j0 w := by
    intro w; induction w with
    | nil => rfl
    | cons s tl ih =>
      simp only [List.map_cons, evalPackedWordVec3DW18_step_eq, ih]
      conv => rhs; unfold evalWordVec3DTupleValW18
      rcases evalWordVec3DTupleValW18 N proj k alpha beta gamma delta s0Val j0 tl with ⟨u0, u1, u2⟩
      simp only [
        mat3DC39FastNatW18_eq k alpha beta gamma delta (proj s) fin3Z0W18 fin3Z0W18,
        mat3DC39FastNatW18_eq k alpha beta gamma delta (proj s) fin3Z0W18 fin3Z1W18,
        mat3DC39FastNatW18_eq k alpha beta gamma delta (proj s) fin3Z0W18 fin3Z2W18,
        mat3DC39FastNatW18_eq k alpha beta gamma delta (proj s) fin3Z1W18 fin3Z0W18,
        mat3DC39FastNatW18_eq k alpha beta gamma delta (proj s) fin3Z1W18 fin3Z1W18,
        mat3DC39FastNatW18_eq k alpha beta gamma delta (proj s) fin3Z1W18 fin3Z2W18,
        mat3DC39FastNatW18_eq k alpha beta gamma delta (proj s) fin3Z2W18 fin3Z0W18,
        mat3DC39FastNatW18_eq k alpha beta gamma delta (proj s) fin3Z2W18 fin3Z1W18,
        mat3DC39FastNatW18_eq k alpha beta gamma delta (proj s) fin3Z2W18 fin3Z2W18]
  induction rs with
  | nil => rfl
  | cons r0 rtl ih =>
    rcases r0 with ⟨l, r⟩
    simp only [pack3DRulesNatW18, farkas3DPackedR1FromU2W18, farkas3DFastPairValW18, hw_eq, ih]
    rcases farkas3DFastPairValW18 N proj mu0 mu2 (fun _ => 0) k alpha beta gamma delta s0Val j0 rtl with ⟨sl, sr⟩
    rcases evalWordVec3DTupleValW18 N proj k alpha beta gamma delta s0Val j0 l with ⟨vl0, vl1, vl2⟩
    rcases evalWordVec3DTupleValW18 N proj k alpha beta gamma delta s0Val j0 r with ⟨vr0, vr1, vr2⟩
    simp only [Nat.zero_mul, Nat.add_zero]

private theorem block_nilp_3d_shape_and_witness_certs_w18 :
    c39FastRulesW18.all checkRule3DCornersBoolW18 = true ∧
    c78FastRulesW18.all (fun r =>
      c39FastRulesW18.any (fun r39 =>
        (r.1.map projSym84To42, r.2.map projSym84To42) == r39)) = true ∧
    checkWordShape3DFarkasNBoolW18 42 id
      farkasMu0CoupledC39 farkasMu1BlockNilp3DC39 farkasMu1BiBTRC39 c39FastRulesW18 = true ∧
    checkWordShape3DFarkasNBoolW18 84 projSym84To42
      farkasMu0CoupledC78 farkasMu1BlockNilp3DC78 farkasMu1BiBTRC78 c78FastRulesW18 = true ∧
    countStrictMat3DRules 42 (rank2BlockNilpMat3DC39 2 1 1 1 1) c39FastRulesW18 = 37 ∧
    countStrictMat3DRules 84 (rank2BlockNilpMat3DC78 2 1 1 1 1) c78FastRulesW18 = 74 ∧
    (let p_mu0 := farkas3DFastPairW18 42 id farkasMu0CoupledC39 (fun _ => 0) (fun _ => 0)
       2 1 1 1 1 ⟨22, by decide⟩ fin3Z1W18 c39FastRulesW18
     let p_w17_r1 := farkas3DFastPairW18 42 id farkasMu0CoupledC39 farkasMu1BiBTRC39 (fun _ => 0)
       2 1 1 1 1 ⟨22, by decide⟩ fin3Z1W18 c39FastRulesW18
     let p_w17_r2 := farkas3DFastPairW18 42 id farkasMu0CoupledC39 (fun _ => 0) farkasMu1BiBTRC39
       2 1 1 1 1 ⟨22, by decide⟩ fin3Z1W18 c39FastRulesW18
     p_mu0.1 - p_mu0.2 = 10 ∧
     p_w17_r1.1 - p_w17_r1.2 = 10 ∧
     p_w17_r2.1 - p_w17_r2.2 = 10) := by
  rcases bn3d_fast_corners_and_counts_w18 with ⟨hc, hp, hs39, hs78, hst37, hst74⟩
  have hc_all : c39FastRulesW18.all checkRule3DCornersBoolW18 = true := by
    rw [List.all_eq_true] at hc ⊢
    intro r hr; rw [← checkRule3DCornersFast_eq_w18 r]; exact hc r hr
  rw [countStrictMat3DFastProj_eq_w18 42 id] at hst37
  rw [countStrictMat3DFastProj_eq_w18 84 projSym84To42] at hst74
  have heq0 : farkas3DFastPairW18 42 id farkasMu0CoupledC39 (fun _ => 0) (fun _ => 0)
      2 1 1 1 1 ⟨22, by decide⟩ fin3Z1W18 c39FastRulesW18 =
      farkas3DPackedPairW18 false false 2 1 1 1 1 22 1 c39Packed3DW18 := by
    unfold farkas3DFastPairW18
    have h := (farkas3DPackedPairW18_eq 42 id farkasMu0CoupledC39 farkasMu1BlockNilp3DC39 farkasMu1BiBTRC39
      false false 2 1 1 1 1 22 fin3Z1W18 c39FastRulesW18).symm
    rw [c39Packed3DW18_eq] at h; exact h
  have heq1 : farkas3DFastPairW18 42 id farkasMu0CoupledC39 farkasMu1BiBTRC39 (fun _ => 0)
      2 1 1 1 1 ⟨22, by decide⟩ fin3Z1W18 c39FastRulesW18 =
      farkas3DPackedR1FromU2W18 2 1 1 1 1 22 1 c39Packed3DW18 := by
    unfold farkas3DFastPairW18
    have h := (farkas3DPackedR1FromU2W18_eq 42 id farkasMu0CoupledC39 farkasMu1BlockNilp3DC39 farkasMu1BiBTRC39
      2 1 1 1 1 22 fin3Z1W18 c39FastRulesW18).symm
    rw [c39Packed3DW18_eq] at h; exact h
  have heq2 : farkas3DFastPairW18 42 id farkasMu0CoupledC39 (fun _ => 0) farkasMu1BiBTRC39
      2 1 1 1 1 ⟨22, by decide⟩ fin3Z1W18 c39FastRulesW18 =
      farkas3DPackedPairW18 false true 2 1 1 1 1 22 1 c39Packed3DW18 := by
    unfold farkas3DFastPairW18
    have h := (farkas3DPackedPairW18_eq 42 id farkasMu0CoupledC39 farkasMu1BlockNilp3DC39 farkasMu1BiBTRC39
      false true 2 1 1 1 1 22 fin3Z1W18 c39FastRulesW18).symm
    rw [c39Packed3DW18_eq] at h; exact h
  dsimp only
  rw [heq0, heq1, heq2]
  exact ⟨hc_all, hp, hs39, hs78, hst37, hst74, by decide, by decide, by decide⟩

private def filterPackedBySym3DW18 (s0Val : Nat) :
    List (Nat × Nat × Nat × List (Nat × Nat) × List (Nat × Nat)) ->
    List (Nat × Nat × Nat × List (Nat × Nat) × List (Nat × Nat))
  | [] => []
  | (w0, u1, u2, lp, rp) :: tl =>
    if wordHasSym3DW18 s0Val lp || wordHasSym3DW18 s0Val rp then
      (w0, u1, u2, lp, rp) :: filterPackedBySym3DW18 s0Val tl
    else
      filterPackedBySym3DW18 s0Val tl

private theorem farkas3DPackedPairW18_filter_eq (use1 use2 : Bool)
    (k alpha beta gamma delta s0Val j0Val : Nat) :
    ∀ pk : List (Nat × Nat × Nat × List (Nat × Nat) × List (Nat × Nat)),
      farkas3DPackedPairW18 use1 use2 k alpha beta gamma delta s0Val j0Val (filterPackedBySym3DW18 s0Val pk) =
        farkas3DPackedPairW18 use1 use2 k alpha beta gamma delta s0Val j0Val pk
  | [] => rfl
  | (w0, u1, u2, lp, rp) :: tl => by
    unfold filterPackedBySym3DW18
    cases h : (wordHasSym3DW18 s0Val lp || wordHasSym3DW18 s0Val rp)
    · simp only [Bool.false_eq_true, ↓reduceIte, farkas3DPackedPairW18, h, Bool.not_false,
                 farkas3DPackedPairW18_filter_eq use1 use2 k alpha beta gamma delta s0Val j0Val tl]
    · simp only [↓reduceIte, farkas3DPackedPairW18, h, Bool.not_true, Bool.false_eq_true,
                 farkas3DPackedPairW18_filter_eq use1 use2 k alpha beta gamma delta s0Val j0Val tl]

private def checkOneRelAtJ0W18
    (rel : List (Nat × Nat × Nat × List (Nat × Nat) × List (Nat × Nat)))
    (idx j0Val : Nat) : Bool :=
  match farkas3DPackedPairW18 false false 1 0 0 0 0 idx j0Val rel,
        farkas3DPackedPairW18 false true 1 1 0 0 0 idx j0Val rel,
        farkas3DPackedPairW18 true false 1 0 1 0 0 idx j0Val rel with
  | (p0l, p0r), (pal, par), (pbl, pbr) =>
    Nat.ble p0l p0r && Nat.ble (pal - p0l) (par - p0r) && Nat.ble (pbl - p0l) (pbr - p0r)

private def check3DFarkasAllJ0FastRangeW18
    (pk : List (Nat × Nat × Nat × List (Nat × Nat) × List (Nat × Nat)))
    (start : Nat) : Nat -> Bool
  | 0 => true
  | cnt + 1 =>
    let idx := start + cnt
    let rel := filterPackedBySym3DW18 idx pk
    checkOneRelAtJ0W18 rel idx 0 &&
    checkOneRelAtJ0W18 rel idx 1 &&
    checkOneRelAtJ0W18 rel idx 2 &&
    check3DFarkasAllJ0FastRangeW18 pk start cnt

private theorem check3DFarkasAllJ0FastRangeW18_sound
    (pk : List (Nat × Nat × Nat × List (Nat × Nat) × List (Nat × Nat)))
    (start : Nat) :
    ∀ cnt : Nat, check3DFarkasAllJ0FastRangeW18 pk start cnt = true ->
      check3DFarkasPackedRangeW18 pk 0 start cnt = true ∧
      check3DFarkasPackedRangeW18 pk 1 start cnt = true ∧
      check3DFarkasPackedRangeW18 pk 2 start cnt = true
  | 0, _ => ⟨rfl, rfl, rfl⟩
  | cnt' + 1, h => by
    unfold check3DFarkasAllJ0FastRangeW18 at h
    dsimp only at h
    rcases bool_and_split h with ⟨hc012, hprev⟩
    rcases bool_and_split hc012 with ⟨hc01, hc2⟩
    rcases bool_and_split hc01 with ⟨hc0, hc1⟩
    rcases check3DFarkasAllJ0FastRangeW18_sound pk start cnt' hprev with ⟨hp0, hp1, hp2⟩
    have hone : ∀ (j0Val : Nat),
        checkOneRelAtJ0W18 (filterPackedBySym3DW18 (start + cnt') pk) (start + cnt') j0Val = true ->
        check3DFarkasPackedRangeW18 pk j0Val start cnt' = true ->
        check3DFarkasPackedRangeW18 pk j0Val start (cnt' + 1) = true := by
      intro j0Val hrel hpj
      unfold checkOneRelAtJ0W18 at hrel
      rw [farkas3DPackedPairW18_filter_eq, farkas3DPackedPairW18_filter_eq, farkas3DPackedPairW18_filter_eq] at hrel
      unfold check3DFarkasPackedRangeW18
      dsimp only
      rcases hp0_e : farkas3DPackedPairW18 false false 1 0 0 0 0 (start + cnt') j0Val pk with ⟨p0l, p0r⟩
      rcases hpa_e : farkas3DPackedPairW18 false true 1 1 0 0 0 (start + cnt') j0Val pk with ⟨pal, par⟩
      rcases hpb_e : farkas3DPackedPairW18 true false 1 0 1 0 0 (start + cnt') j0Val pk with ⟨pbl, pbr⟩
      simp only [hp0_e, hpa_e, hpb_e] at hrel ⊢
      rw [hrel, hpj]; rfl
    exact ⟨hone 0 hc0 hp0, hone 1 hc1 hp1, hone 2 hc2 hp2⟩

set_option maxRecDepth 65536 in
private theorem bn3d_c39_all_fast : check3DFarkasAllJ0FastRangeW18 c39Packed3DW18 0 42 = true := by decide

private theorem bn3d_c39_all_packed :
    check3DFarkasPackedRangeW18 c39Packed3DW18 0 0 42 = true ∧
    check3DFarkasPackedRangeW18 c39Packed3DW18 1 0 42 = true ∧
    check3DFarkasPackedRangeW18 c39Packed3DW18 2 0 42 = true :=
  check3DFarkasAllJ0FastRangeW18_sound c39Packed3DW18 0 42 bn3d_c39_all_fast

set_option maxRecDepth 65536 in
private theorem bn3d_c78_q0_fast : check3DFarkasAllJ0FastRangeW18 c78Packed3DW18 0 21 = true := by decide
set_option maxRecDepth 65536 in
private theorem bn3d_c78_q1_fast : check3DFarkasAllJ0FastRangeW18 c78Packed3DW18 21 21 = true := by decide
set_option maxRecDepth 65536 in
private theorem bn3d_c78_q2_fast : check3DFarkasAllJ0FastRangeW18 c78Packed3DW18 42 21 = true := by decide
set_option maxRecDepth 65536 in
private theorem bn3d_c78_q3_fast : check3DFarkasAllJ0FastRangeW18 c78Packed3DW18 63 21 = true := by decide

private theorem bn3d_c78_q0_sound :
    check3DFarkasPackedRangeW18 c78Packed3DW18 0 0 21 = true ∧
    check3DFarkasPackedRangeW18 c78Packed3DW18 1 0 21 = true ∧
    check3DFarkasPackedRangeW18 c78Packed3DW18 2 0 21 = true :=
  check3DFarkasAllJ0FastRangeW18_sound c78Packed3DW18 0 21 bn3d_c78_q0_fast

private theorem bn3d_c78_q1_sound :
    check3DFarkasPackedRangeW18 c78Packed3DW18 0 21 21 = true ∧
    check3DFarkasPackedRangeW18 c78Packed3DW18 1 21 21 = true ∧
    check3DFarkasPackedRangeW18 c78Packed3DW18 2 21 21 = true :=
  check3DFarkasAllJ0FastRangeW18_sound c78Packed3DW18 21 21 bn3d_c78_q1_fast

private theorem bn3d_c78_q2_sound :
    check3DFarkasPackedRangeW18 c78Packed3DW18 0 42 21 = true ∧
    check3DFarkasPackedRangeW18 c78Packed3DW18 1 42 21 = true ∧
    check3DFarkasPackedRangeW18 c78Packed3DW18 2 42 21 = true :=
  check3DFarkasAllJ0FastRangeW18_sound c78Packed3DW18 42 21 bn3d_c78_q2_fast

private theorem bn3d_c78_q3_sound :
    check3DFarkasPackedRangeW18 c78Packed3DW18 0 63 21 = true ∧
    check3DFarkasPackedRangeW18 c78Packed3DW18 1 63 21 = true ∧
    check3DFarkasPackedRangeW18 c78Packed3DW18 2 63 21 = true :=
  check3DFarkasAllJ0FastRangeW18_sound c78Packed3DW18 63 21 bn3d_c78_q3_fast

private theorem bn3d_c78_j0_packed : check3DFarkasPackedRangeW18 c78Packed3DW18 0 0 84 = true :=
  check3DFarkasPackedRangeW18_append c78Packed3DW18 0 63 21
    (check3DFarkasPackedRangeW18_append c78Packed3DW18 0 42 21
      (check3DFarkasPackedRangeW18_append c78Packed3DW18 0 21 21 bn3d_c78_q0_sound.1 bn3d_c78_q1_sound.1)
      bn3d_c78_q2_sound.1)
    bn3d_c78_q3_sound.1

private theorem bn3d_c78_j1_packed : check3DFarkasPackedRangeW18 c78Packed3DW18 1 0 84 = true :=
  check3DFarkasPackedRangeW18_append c78Packed3DW18 1 63 21
    (check3DFarkasPackedRangeW18_append c78Packed3DW18 1 42 21
      (check3DFarkasPackedRangeW18_append c78Packed3DW18 1 21 21 bn3d_c78_q0_sound.2.1 bn3d_c78_q1_sound.2.1)
      bn3d_c78_q2_sound.2.1)
    bn3d_c78_q3_sound.2.1

private theorem bn3d_c78_j2_packed : check3DFarkasPackedRangeW18 c78Packed3DW18 2 0 84 = true :=
  check3DFarkasPackedRangeW18_append c78Packed3DW18 2 63 21
    (check3DFarkasPackedRangeW18_append c78Packed3DW18 2 42 21
      (check3DFarkasPackedRangeW18_append c78Packed3DW18 2 21 21 bn3d_c78_q0_sound.2.2 bn3d_c78_q1_sound.2.2)
      bn3d_c78_q2_sound.2.2)
    bn3d_c78_q3_sound.2.2

private theorem hm_single_3d_w18 (M : Fin 42 -> Fin 3 -> Fin 3 -> Nat) (s : Fin 42) (i j : Fin 3) :
    evalFinWordMat 42 3 M [s] i j = M s i j := by
  rw [mat3_mul_step_w18]
  rcases (by have := j.isLt; omega : j.val = 0 ∨ j.val = 1 ∨ j.val = 2) with hj | hj | hj
  · rw [show j = fin3Z0W18 from Fin.ext hj]; change _ * 1 + _ * 0 + _ * 0 = _; omega
  · rw [show j = fin3Z1W18 from Fin.ext hj]; change _ * 0 + _ * 1 + _ * 0 = _; omega
  · rw [show j = fin3Z2W18 from Fin.ext hj]; change _ * 0 + _ * 0 + _ * 1 = _; omega

private theorem hsym_nonR_lin_3d_w18 (s : Fin 42) (hs_nr : s.val < 6 ∨ s.val ≥ 12) :
    (∀ k' a' b' g' d' i j,
      rank2BlockNilpMat3DC39 k' a' b' g' d' s i j =
        rank2BlockNilpMat3DC39 1 0 0 0 0 s i j +
        a' * (rank2BlockNilpMat3DC39 1 1 0 0 0 s i j - rank2BlockNilpMat3DC39 1 0 0 0 0 s i j) +
        b' * (rank2BlockNilpMat3DC39 1 0 1 0 0 s i j - rank2BlockNilpMat3DC39 1 0 0 0 0 s i j) +
        g' * (rank2BlockNilpMat3DC39 1 0 0 1 0 s i j - rank2BlockNilpMat3DC39 1 0 0 0 0 s i j) +
        d' * (rank2BlockNilpMat3DC39 1 0 0 0 1 s i j - rank2BlockNilpMat3DC39 1 0 0 0 0 s i j)) := by
  have hnot611 : ¬ (6 ≤ s.val ∧ s.val ≤ 11) := by omega
  have hnot68 : ¬ (6 ≤ s.val ∧ s.val ≤ 8) := by omega
  intro k' a' b' g' d' i j
  unfold rank2BlockNilpMat3DC39
  rcases (by have := i.isLt; omega : i.val = 0 ∨ i.val = 1 ∨ i.val = 2) with hi | hi | hi <;>
  rcases (by have := j.isLt; omega : j.val = 0 ∨ j.val = 1 ∨ j.val = 2) with hj | hj | hj
  · simp [hi, hj, hnot611]
  · simp only [hi, hj]; cases isBeta01SymW18 s.val <;> simp
  · simp only [hi, hj]; cases isAlpha02SymW18 s.val <;> simp
  · simp only [hi, hj]; cases isDelta1SymW18 s.val <;> simp
  · simp [hi, hj]
  · simp only [hi, hj]; cases isDelta1SymW18 s.val <;> simp
  · simp only [hi, hj]; cases isGamma20SymW18 s.val <;> simp
  · simp [hi, hj]
  · simp [hi, hj, hnot68]

private theorem hword_9mono_len2R_3d_w18 (k alpha beta gamma delta : Nat)
    (s1 s2 : Fin 42) (hsh : wordShape3DMatBoolW18 [s1, s2] = true)
    (hs2_R : 6 ≤ s2.val ∧ s2.val ≤ 11) (i j : Fin 3) :
    let c := evalWord3D9CoeffsW18 [s1, s2] i j
    evalFinWordMat 42 3 (rank2BlockNilpMat3DC39 k alpha beta gamma delta) [s1, s2] i j =
      (if endInRBoolW18 [s1, s2] then k else 1) *
        (c.1 + alpha * c.2.1 + beta * c.2.2.1 + gamma * c.2.2.2.1 + delta * c.2.2.2.2.1 +
         (alpha * gamma) * c.2.2.2.2.2.1 + (beta * delta) * c.2.2.2.2.2.2.1 +
         (alpha * delta) * c.2.2.2.2.2.2.2.1 + (beta * gamma) * c.2.2.2.2.2.2.2.2) := by
  dsimp only
  unfold wordShape3DMatBoolW18 at hsh; dsimp only at hsh
  simp only [hs2_R] at hsh
  rcases of_decide_eq_true hsh with ⟨hs1_nr, hs2_or⟩
  have he_end : endInRBoolW18 [s1, s2] = true := by simp [endInRBoolW18, hs2_R]
  simp only [he_end, reduceIte]
  have hm_r : ∀ k' a' b' g' d',
      evalFinWordMat 42 3 (rank2BlockNilpMat3DC39 k' a' b' g' d') [s1, s2] i j =
        if j.val = 0 then k' * rank2BlockNilpMat3DC39 1 a' b' g' d' s1 i fin3Z0W18
        else 0 := by
    intro k' a' b' g' d'
    rw [mat3_mul_step_w18, hm_single_3d_w18, hm_single_3d_w18, hm_single_3d_w18]
    have hs2_1 : rank2BlockNilpMat3DC39 k' a' b' g' d' s2 fin3Z1W18 j = 0 := by
      have hnd : isDelta1SymW18 s2.val = false := by
        rcases (by omega : s2.val = 6 ∨ s2.val = 7 ∨ s2.val = 8 ∨ s2.val = 9 ∨ s2.val = 10 ∨ s2.val = 11) with h|h|h|h|h|h <;>
        simp [isDelta1SymW18, h]
      unfold rank2BlockNilpMat3DC39; dsimp only [fin3Z1W18]
      rcases (by have := j.isLt; omega : j.val = 0 ∨ j.val = 1 ∨ j.val = 2) with hj | hj | hj <;>
      simp [hj, hnd]
    have hs2_2_prod : rank2BlockNilpMat3DC39 k' a' b' g' d' s1 i fin3Z2W18 *
        rank2BlockNilpMat3DC39 k' a' b' g' d' s2 fin3Z2W18 j = 0 := by
      rcases hs2_or with hge9 | h28 | h31
      · have hn68 : ¬ (6 ≤ s2.val ∧ s2.val ≤ 8) := by omega
        have hng : isGamma20SymW18 s2.val = false := by
          rcases (by omega : s2.val = 9 ∨ s2.val = 10 ∨ s2.val = 11) with h|h|h <;>
          simp [isGamma20SymW18, h]
        have hz : rank2BlockNilpMat3DC39 k' a' b' g' d' s2 fin3Z2W18 j = 0 := by
          unfold rank2BlockNilpMat3DC39; dsimp only [fin3Z2W18]
          rcases (by have := j.isLt; omega : j.val = 0 ∨ j.val = 1 ∨ j.val = 2) with hj | hj | hj <;>
          simp [hj, hn68, hng]
        rw [hz, Nat.mul_zero]
      · have hz : rank2BlockNilpMat3DC39 k' a' b' g' d' s1 i fin3Z2W18 = 0 := by
          unfold rank2BlockNilpMat3DC39; dsimp only [fin3Z2W18]
          rcases (by have := i.isLt; omega : i.val = 0 ∨ i.val = 1 ∨ i.val = 2) with hi | hi | hi <;>
          simp [hi, h28, isAlpha02SymW18, isDelta1SymW18]
        rw [hz, Nat.zero_mul]
      · have hz : rank2BlockNilpMat3DC39 k' a' b' g' d' s1 i fin3Z2W18 = 0 := by
          unfold rank2BlockNilpMat3DC39; dsimp only [fin3Z2W18]
          rcases (by have := i.isLt; omega : i.val = 0 ∨ i.val = 1 ∨ i.val = 2) with hi | hi | hi <;>
          simp [hi, h31, isAlpha02SymW18, isDelta1SymW18]
        rw [hz, Nat.zero_mul]
    rw [hs2_1, Nat.mul_zero, Nat.add_zero, hs2_2_prod, Nat.add_zero]
    by_cases hj0 : j.val = 0
    · rw [ite_true_of_w10 hj0, show j = fin3Z0W18 from Fin.ext hj0]
      have hs2_00 : rank2BlockNilpMat3DC39 k' a' b' g' d' s2 fin3Z0W18 fin3Z0W18 = k' := by
        unfold rank2BlockNilpMat3DC39; dsimp only [fin3Z0W18]; simp [hs2_R]
      have hs1_k : rank2BlockNilpMat3DC39 k' a' b' g' d' s1 i fin3Z0W18 =
          rank2BlockNilpMat3DC39 1 a' b' g' d' s1 i fin3Z0W18 := by
        rw [hsym_nonR_lin_3d_w18 s1 hs1_nr k' a' b' g' d' i fin3Z0W18,
            hsym_nonR_lin_3d_w18 s1 hs1_nr 1 a' b' g' d' i fin3Z0W18]
      rw [hs2_00, hs1_k, Nat.mul_comm]
    · rw [ite_false_of_w10 hj0]
      have hs2_0j : rank2BlockNilpMat3DC39 k' a' b' g' d' s2 fin3Z0W18 j = 0 := by
        have hnb : isBeta01SymW18 s2.val = false ∧ isAlpha02SymW18 s2.val = false := by
          rcases (by omega : s2.val = 6 ∨ s2.val = 7 ∨ s2.val = 8 ∨ s2.val = 9 ∨ s2.val = 10 ∨ s2.val = 11) with h|h|h|h|h|h <;>
          simp [isBeta01SymW18, isAlpha02SymW18, h]
        unfold rank2BlockNilpMat3DC39; dsimp only [fin3Z0W18]
        rcases (by have := j.isLt; omega : j.val = 1 ∨ j.val = 2) with hj | hj <;>
        simp [hj, hnb.1, hnb.2]
      rw [hs2_0j, Nat.mul_zero]
  unfold evalWord3D9CoeffsW18; dsimp only
  simp only [hm_r, Nat.one_mul]
  by_cases hj0 : j.val = 0
  · simp only [hj0, reduceIte]
    have hlin1 := hsym_nonR_lin_3d_w18 s1 hs1_nr
    rw [hlin1 1 alpha beta gamma delta i fin3Z0W18,
        hlin1 1 1 0 0 1 i fin3Z0W18, hlin1 1 1 0 1 0 i fin3Z0W18,
        hlin1 1 0 1 0 1 i fin3Z0W18, hlin1 1 0 1 1 0 i fin3Z0W18]
    generalize rank2BlockNilpMat3DC39 1 0 0 0 0 s1 i fin3Z0W18 = C0,
      rank2BlockNilpMat3DC39 1 1 0 0 0 s1 i fin3Z0W18 - rank2BlockNilpMat3DC39 1 0 0 0 0 s1 i fin3Z0W18 = CA,
      rank2BlockNilpMat3DC39 1 0 1 0 0 s1 i fin3Z0W18 - rank2BlockNilpMat3DC39 1 0 0 0 0 s1 i fin3Z0W18 = CB,
      rank2BlockNilpMat3DC39 1 0 0 1 0 s1 i fin3Z0W18 - rank2BlockNilpMat3DC39 1 0 0 0 0 s1 i fin3Z0W18 = CG,
      rank2BlockNilpMat3DC39 1 0 0 0 1 s1 i fin3Z0W18 - rank2BlockNilpMat3DC39 1 0 0 0 0 s1 i fin3Z0W18 = CD
    simp only [Nat.zero_mul, Nat.one_mul, Nat.add_zero]
    have z1 : C0 + CA + CG - C0 - CA - CG = 0 := by omega
    have z2 : C0 + CB + CD - C0 - CB - CD = 0 := by omega
    have z3 : C0 + CA + CD - C0 - CA - CD = 0 := by omega
    have z4 : C0 + CB + CG - C0 - CB - CG = 0 := by omega
    rw [z1, z2, z3, z4]; simp
  · simp [hj0]

private theorem hprod2_nonR_lb_3d_w18 (k alpha beta gamma delta : Nat)
    (a1 a2 : Fin 42) (_ha1 : a1.val < 6 ∨ a1.val ≥ 12) (ha2 : a2.val < 6 ∨ a2.val ≥ 12)
    (ha1_lb : a1.val < 6 ∨ (12 ≤ a1.val ∧ a1.val < 24)) (p q : Fin 3) :
    let c := evalWord3D9CoeffsW18 [a1, a2] p q
    evalFinWordMat 42 3 (rank2BlockNilpMat3DC39 k alpha beta gamma delta) [a1, a2] p q =
      c.1 + alpha * c.2.1 + beta * c.2.2.1 + gamma * c.2.2.2.1 + delta * c.2.2.2.2.1 +
      (alpha * gamma) * c.2.2.2.2.2.1 + (beta * delta) * c.2.2.2.2.2.2.1 +
      (alpha * delta) * c.2.2.2.2.2.2.2.1 + (beta * gamma) * c.2.2.2.2.2.2.2.2 := by
  dsimp only
  have hexp_all : ∀ k' a' b' g' d',
      evalFinWordMat 42 3 (rank2BlockNilpMat3DC39 k' a' b' g' d') [a1, a2] p q =
        rank2BlockNilpMat3DC39 k' a' b' g' d' a1 p fin3Z0W18 * rank2BlockNilpMat3DC39 k' a' b' g' d' a2 fin3Z0W18 q +
        rank2BlockNilpMat3DC39 k' a' b' g' d' a1 p fin3Z1W18 * rank2BlockNilpMat3DC39 k' a' b' g' d' a2 fin3Z1W18 q +
        rank2BlockNilpMat3DC39 k' a' b' g' d' a1 p fin3Z2W18 * rank2BlockNilpMat3DC39 k' a' b' g' d' a2 fin3Z2W18 q := by
    intro k' a' b' g' d'
    rw [mat3_mul_step_w18, hm_single_3d_w18, hm_single_3d_w18, hm_single_3d_w18]
  unfold evalWord3D9CoeffsW18; dsimp only
  simp only [hexp_all]
  have hn611_1 : ¬ (6 ≤ a1.val ∧ a1.val ≤ 11) := by omega
  have hn68_1 : ¬ (6 ≤ a1.val ∧ a1.val ≤ 8) := by omega
  have hn611_2 : ¬ (6 ≤ a2.val ∧ a2.val ≤ 11) := by omega
  have hn68_2 : ¬ (6 ≤ a2.val ∧ a2.val ≤ 8) := by omega
  have hd1 : isDelta1SymW18 a1.val = false ∧ isGamma20SymW18 a1.val = false := by
    unfold isDelta1SymW18 isGamma20SymW18
    simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne]
    exact ⟨⟨⟨⟨⟨by omega, by omega⟩, by omega⟩, by omega⟩, by omega⟩,
           ⟨⟨⟨⟨⟨⟨by omega, by omega⟩, by omega⟩, by omega⟩, by omega⟩, by omega⟩, by omega⟩⟩
  unfold rank2BlockNilpMat3DC39
  dsimp only [fin3Z0W18, fin3Z1W18, fin3Z2W18]
  rcases (by have := p.isLt; omega : p.val = 0 ∨ p.val = 1 ∨ p.val = 2) with hp | hp | hp <;>
  rcases (by have := q.isLt; omega : q.val = 0 ∨ q.val = 1 ∨ q.val = 2) with hq | hq | hq
  · simp only [hp, hq, hn611_1, hn611_2]
    cases isBeta01SymW18 a1.val <;> cases isAlpha02SymW18 a1.val <;>
    cases isDelta1SymW18 a2.val <;> cases isGamma20SymW18 a2.val <;>
    (simp; try omega)
  · simp only [hp, hq, hn611_1]
    cases isBeta01SymW18 a2.val <;> (simp; try omega)
  · simp only [hp, hq, hn611_1, hn68_2]
    cases isBeta01SymW18 a1.val <;> cases isAlpha02SymW18 a2.val <;> cases isDelta1SymW18 a2.val <;>
    (simp; try omega)
  · simp [hp, hq, hd1.1]
  · simp [hp, hq, hd1.1]
  · simp [hp, hq, hd1.1]
  · simp [hp, hq, hd1.2, hn68_1]
  · simp [hp, hq, hd1.2, hn68_1]
  · simp [hp, hq, hd1.2, hn68_1]

private theorem hprod2_nonR_rb_3d_w18 (k alpha beta gamma delta : Nat)
    (a1 a2 : Fin 42) (ha1 : a1.val < 6 ∨ a1.val ≥ 12) (ha2 : a2.val < 6 ∨ a2.val ≥ 12)
    (ha2_b : 12 ≤ a2.val ∧ a2.val < 24) (p q : Fin 3) :
    let c := evalWord3D9CoeffsW18 [a1, a2] p q
    evalFinWordMat 42 3 (rank2BlockNilpMat3DC39 k alpha beta gamma delta) [a1, a2] p q =
      c.1 + alpha * c.2.1 + beta * c.2.2.1 + gamma * c.2.2.2.1 + delta * c.2.2.2.2.1 +
      (alpha * gamma) * c.2.2.2.2.2.1 + (beta * delta) * c.2.2.2.2.2.2.1 +
      (alpha * delta) * c.2.2.2.2.2.2.2.1 + (beta * gamma) * c.2.2.2.2.2.2.2.2 := by
  dsimp only
  have hexp_all : ∀ k' a' b' g' d',
      evalFinWordMat 42 3 (rank2BlockNilpMat3DC39 k' a' b' g' d') [a1, a2] p q =
        rank2BlockNilpMat3DC39 k' a' b' g' d' a1 p fin3Z0W18 * rank2BlockNilpMat3DC39 k' a' b' g' d' a2 fin3Z0W18 q +
        rank2BlockNilpMat3DC39 k' a' b' g' d' a1 p fin3Z1W18 * rank2BlockNilpMat3DC39 k' a' b' g' d' a2 fin3Z1W18 q +
        rank2BlockNilpMat3DC39 k' a' b' g' d' a1 p fin3Z2W18 * rank2BlockNilpMat3DC39 k' a' b' g' d' a2 fin3Z2W18 q := by
    intro k' a' b' g' d'
    rw [mat3_mul_step_w18, hm_single_3d_w18, hm_single_3d_w18, hm_single_3d_w18]
  unfold evalWord3D9CoeffsW18; dsimp only
  simp only [hexp_all]
  have hn611_1 : ¬ (6 ≤ a1.val ∧ a1.val ≤ 11) := by omega
  have hn68_1 : ¬ (6 ≤ a1.val ∧ a1.val ≤ 8) := by omega
  have hn611_2 : ¬ (6 ≤ a2.val ∧ a2.val ≤ 11) := by omega
  have hn68_2 : ¬ (6 ≤ a2.val ∧ a2.val ≤ 8) := by omega
  have hd2 : isDelta1SymW18 a2.val = false ∧ isGamma20SymW18 a2.val = false := by
    unfold isDelta1SymW18 isGamma20SymW18
    simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne]
    exact ⟨⟨⟨⟨⟨by omega, by omega⟩, by omega⟩, by omega⟩, by omega⟩,
           ⟨⟨⟨⟨⟨⟨by omega, by omega⟩, by omega⟩, by omega⟩, by omega⟩, by omega⟩, by omega⟩⟩
  unfold rank2BlockNilpMat3DC39
  dsimp only [fin3Z0W18, fin3Z1W18, fin3Z2W18]
  rcases (by have := p.isLt; omega : p.val = 0 ∨ p.val = 1 ∨ p.val = 2) with hp | hp | hp <;>
  rcases (by have := q.isLt; omega : q.val = 0 ∨ q.val = 1 ∨ q.val = 2) with hq | hq | hq
  · simp [hp, hq, hn611_1, hn611_2, hd2.1, hd2.2]
  · simp only [hp, hq, hn611_1]
    cases isBeta01SymW18 a2.val <;> simp
  · simp only [hp, hq, hn611_1, hn68_2, hd2.1]
    cases isAlpha02SymW18 a2.val <;> simp
  · simp only [hp, hq, hn611_2, hd2.1, hd2.2]
    cases isDelta1SymW18 a1.val <;> simp
  · simp only [hp, hq, hd2.1]
    cases isDelta1SymW18 a1.val <;> cases isBeta01SymW18 a2.val <;>
    (simp; try ac_rfl)
  · simp only [hp, hq, hn68_2, hd2.1]
    cases isDelta1SymW18 a1.val <;> cases isAlpha02SymW18 a2.val <;>
    (simp; try ac_rfl)
  · simp only [hp, hq, hn68_1, hn611_2, hd2.1, hd2.2]
    cases isGamma20SymW18 a1.val <;> simp
  · simp only [hp, hq, hn68_1]
    cases isGamma20SymW18 a1.val <;> cases isBeta01SymW18 a2.val <;>
    (simp; try ac_rfl)
  · simp only [hp, hq, hn68_1, hn68_2, hd2.1]
    cases isGamma20SymW18 a1.val <;> cases isAlpha02SymW18 a2.val <;>
    (simp; try ac_rfl)

private theorem hword_9mono_len3_3d_w18 (k alpha beta gamma delta : Nat)
    (s1 s2 s3 : Fin 42) (hsh : wordShape3DMatBoolW18 [s1, s2, s3] = true) (i j : Fin 3) :
    let c := evalWord3D9CoeffsW18 [s1, s2, s3] i j
    evalFinWordMat 42 3 (rank2BlockNilpMat3DC39 k alpha beta gamma delta) [s1, s2, s3] i j =
      (if endInRBoolW18 [s1, s2, s3] then k else 1) *
        (c.1 + alpha * c.2.1 + beta * c.2.2.1 + gamma * c.2.2.2.1 + delta * c.2.2.2.2.1 +
         (alpha * gamma) * c.2.2.2.2.2.1 + (beta * delta) * c.2.2.2.2.2.2.1 +
         (alpha * delta) * c.2.2.2.2.2.2.2.1 + (beta * gamma) * c.2.2.2.2.2.2.2.2) := by
  dsimp only
  unfold wordShape3DMatBoolW18 at hsh
  rcases of_decide_eq_true hsh with ⟨hs1_c, hs2_c, hs3_c⟩
  have he_end : endInRBoolW18 [s1, s2, s3] = true := by
    have hs3_611 : 6 ≤ s3.val ∧ s3.val ≤ 11 := by omega
    simp [endInRBoolW18, hs3_611]
  simp only [he_end, reduceIte]
  have hm3 : ∀ k' a' b' g' d',
      evalFinWordMat 42 3 (rank2BlockNilpMat3DC39 k' a' b' g' d') [s1, s2, s3] i j =
        if i.val = 0 ∧ j.val = 0 then k' else 0 := by
    intro k' a' b' g' d'
    have hs3_0 : ∀ p : Fin 3,
        evalFinWordMat 42 3 (rank2BlockNilpMat3DC39 k' a' b' g' d') [s2, s3] p j =
        if p.val = 0 ∧ j.val = 0 then k' else 0 := by
      intro p
      rw [mat3_mul_step_w18, hm_single_3d_w18, hm_single_3d_w18, hm_single_3d_w18]
      unfold rank2BlockNilpMat3DC39 isBeta01SymW18 isAlpha02SymW18 isDelta1SymW18 isGamma20SymW18
      dsimp only [fin3Z0W18, fin3Z1W18, fin3Z2W18]
      rcases hs2_c with h2 | h2 <;>
      rcases (by omega : s3.val = 6 ∨ s3.val = 7 ∨ s3.val = 8) with h3 | h3 | h3 <;>
      rcases (by have := p.isLt; omega : p.val = 0 ∨ p.val = 1 ∨ p.val = 2) with hp | hp | hp <;>
      rcases (by have := j.isLt; omega : j.val = 0 ∨ j.val = 1 ∨ j.val = 2) with hj | hj | hj <;>
      (rw [h2, h3, hp, hj]; simp)
    rw [mat3_mul_step_w18, hs3_0, hs3_0, hs3_0]
    unfold rank2BlockNilpMat3DC39 isBeta01SymW18 isAlpha02SymW18 isDelta1SymW18 isGamma20SymW18
    dsimp only [fin3Z0W18, fin3Z1W18, fin3Z2W18]
    rcases hs1_c with h1 | h1 | h1 <;>
    rcases (by have := i.isLt; omega : i.val = 0 ∨ i.val = 1 ∨ i.val = 2) with hi | hi | hi <;>
    rcases (by have := j.isLt; omega : j.val = 0 ∨ j.val = 1 ∨ j.val = 2) with hj | hj | hj <;>
    (rw [h1, hi, hj]; simp)
  unfold evalWord3D9CoeffsW18; dsimp only
  simp only [hm3]
  by_cases hij : i.val = 0 ∧ j.val = 0
  · have hite : ∀ x : Nat, (if i.val = 0 ∧ j.val = 0 then x else 0) = x :=
      fun x => ite_true_of_w10 hij x 0
    simp only [hite]; omega
  · have hite : ∀ x : Nat, (if i.val = 0 ∧ j.val = 0 then x else 0) = 0 :=
      fun x => ite_false_of_w10 hij x 0
    simp only [hite]; omega

private theorem hword_9mono_all_3d_w18 (k alpha beta gamma delta : Nat)
    (w : List (Fin 42)) (hsh : wordShape3DMatBoolW18 w = true) (i j : Fin 3) :
    let c := evalWord3D9CoeffsW18 w i j
    evalFinWordMat 42 3 (rank2BlockNilpMat3DC39 k alpha beta gamma delta) w i j =
      (if endInRBoolW18 w then k else 1) *
        (c.1 + alpha * c.2.1 + beta * c.2.2.1 + gamma * c.2.2.2.1 + delta * c.2.2.2.2.1 +
         (alpha * gamma) * c.2.2.2.2.2.1 + (beta * delta) * c.2.2.2.2.2.2.1 +
         (alpha * delta) * c.2.2.2.2.2.2.2.1 + (beta * gamma) * c.2.2.2.2.2.2.2.2) := by
  dsimp only
  cases w with
  | nil => cases hsh
  | cons s1 xs1 =>
    cases xs1 with
    | nil =>
      have hs1_nr : s1.val < 6 ∨ s1.val ≥ 12 := of_decide_eq_true hsh
      have he_end : endInRBoolW18 [s1] = false := by
        unfold endInRBoolW18; exact decide_eq_false (by omega)
      simp only [he_end, Bool.false_eq_true, reduceIte, Nat.one_mul]
      unfold evalWord3D9CoeffsW18; dsimp only
      simp only [hm_single_3d_w18]
      have hlin1 := hsym_nonR_lin_3d_w18 s1 hs1_nr
      rw [hlin1 k alpha beta gamma delta i j,
          hlin1 1 1 0 0 1 i j, hlin1 1 1 0 1 0 i j,
          hlin1 1 0 1 0 1 i j, hlin1 1 0 1 1 0 i j]
      generalize rank2BlockNilpMat3DC39 1 0 0 0 0 s1 i j = C0,
        rank2BlockNilpMat3DC39 1 1 0 0 0 s1 i j - rank2BlockNilpMat3DC39 1 0 0 0 0 s1 i j = CA,
        rank2BlockNilpMat3DC39 1 0 1 0 0 s1 i j - rank2BlockNilpMat3DC39 1 0 0 0 0 s1 i j = CB,
        rank2BlockNilpMat3DC39 1 0 0 1 0 s1 i j - rank2BlockNilpMat3DC39 1 0 0 0 0 s1 i j = CG,
        rank2BlockNilpMat3DC39 1 0 0 0 1 s1 i j - rank2BlockNilpMat3DC39 1 0 0 0 0 s1 i j = CD
      simp only [Nat.zero_mul, Nat.one_mul, Nat.add_zero]
      have z1 : C0 + CA + CG - C0 - CA - CG = 0 := by omega
      have z2 : C0 + CB + CD - C0 - CB - CD = 0 := by omega
      have z3 : C0 + CA + CD - C0 - CA - CD = 0 := by omega
      have z4 : C0 + CB + CG - C0 - CB - CG = 0 := by omega
      rw [z1, z2, z3, z4]; simp
    | cons s2 xs2 =>
      cases xs2 with
      | nil =>
        by_cases hs2_R : 6 ≤ s2.val ∧ s2.val ≤ 11
        · exact hword_9mono_len2R_3d_w18 k alpha beta gamma delta s1 s2 hsh hs2_R i j
        · have hsh' := hsh
          unfold wordShape3DMatBoolW18 at hsh'; dsimp only at hsh'
          simp only [hs2_R, decide_false, Bool.false_eq_true, reduceIte] at hsh'
          rcases of_decide_eq_true hsh' with ⟨hs1_nr, hs2_nr, hlb_or⟩
          have he_end : endInRBoolW18 [s1, s2] = false := by simp [endInRBoolW18, hs2_R]
          simp only [he_end, Bool.false_eq_true, reduceIte, Nat.one_mul]
          rcases hlb_or with ha1_lb | ha2_b
          · exact hprod2_nonR_lb_3d_w18 k alpha beta gamma delta s1 s2 hs1_nr hs2_nr ha1_lb i j
          · exact hprod2_nonR_rb_3d_w18 k alpha beta gamma delta s1 s2 hs1_nr hs2_nr ha2_b i j
      | cons s3 xs3 =>
        cases xs3 with
        | nil => exact hword_9mono_len3_3d_w18 k alpha beta gamma delta s1 s2 s3 hsh i j
        | cons _ _ => cases hsh

private theorem weak_mat_orientation_5param_3d_cones_w18 (k alpha beta gamma delta : Nat) :
    (∀ r ∈ c39FastRulesW18, ∀ i j : Fin 3,
      evalFinWordMat 42 3 (rank2BlockNilpMat3DC39 k alpha beta gamma delta) r.1 i j ≥
        evalFinWordMat 42 3 (rank2BlockNilpMat3DC39 k alpha beta gamma delta) r.2 i j) ∧
    (∀ r ∈ c78FastRulesW18, ∀ i j : Fin 3,
      evalFinWordMat 84 3 (rank2BlockNilpMat3DC78 k alpha beta gamma delta) r.1 i j ≥
        evalFinWordMat 84 3 (rank2BlockNilpMat3DC78 k alpha beta gamma delta) r.2 i j) := by
  have hw39 : ∀ r ∈ c39FastRulesW18, ∀ i j : Fin 3,
      evalFinWordMat 42 3 (rank2BlockNilpMat3DC39 k alpha beta gamma delta) r.1 i j ≥
        evalFinWordMat 42 3 (rank2BlockNilpMat3DC39 k alpha beta gamma delta) r.2 i j := by
    have hall_c := block_nilp_3d_shape_and_witness_certs_w18.1
    intro r hr i j
    rcases bool_and_split (List.all_eq_true.mp hall_c r hr) with ⟨hb1, hall_ij⟩
    rcases bool_and_split hb1 with ⟨hsh12, hend_b⟩
    rcases bool_and_split hsh12 with ⟨hsh1, hsh2⟩
    have hend := of_decide_eq_true hend_b
    have hl := hword_9mono_all_3d_w18 k alpha beta gamma delta r.1 hsh1 i j
    have hr_e := hword_9mono_all_3d_w18 k alpha beta gamma delta r.2 hsh2 i j
    dsimp only at hl hr_e
    rw [hl, hr_e, hend]
    apply Nat.mul_le_mul_left
    have hi_m : i ∈ [fin3Z0W18, fin3Z1W18, fin3Z2W18] := by
      rcases (by have := i.isLt; omega : i.val = 0 ∨ i.val = 1 ∨ i.val = 2) with h | h | h
      · rw [show i = fin3Z0W18 from Fin.ext h]; exact List.Mem.head _
      · rw [show i = fin3Z1W18 from Fin.ext h]; exact List.Mem.tail _ (List.Mem.head _)
      · rw [show i = fin3Z2W18 from Fin.ext h]; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
    have hj_m : j ∈ [fin3Z0W18, fin3Z1W18, fin3Z2W18] := by
      rcases (by have := j.isLt; omega : j.val = 0 ∨ j.val = 1 ∨ j.val = 2) with h | h | h
      · rw [show j = fin3Z0W18 from Fin.ext h]; exact List.Mem.head _
      · rw [show j = fin3Z1W18 from Fin.ext h]; exact List.Mem.tail _ (List.Mem.head _)
      · rw [show j = fin3Z2W18 from Fin.ext h]; exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
    rcases of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp hall_ij i hi_m) j hj_m) with
      ⟨c0, ca, cb, cg, cd, cag, cbd, cad, cbg⟩
    exact Nat.add_le_add
      (Nat.add_le_add
        (Nat.add_le_add
          (Nat.add_le_add
            (Nat.add_le_add
              (Nat.add_le_add
                (Nat.add_le_add (Nat.add_le_add c0 (Nat.mul_le_mul_left _ ca)) (Nat.mul_le_mul_left _ cb))
                (Nat.mul_le_mul_left _ cg))
              (Nat.mul_le_mul_left _ cd))
            (Nat.mul_le_mul_left _ cag))
          (Nat.mul_le_mul_left _ cbd))
        (Nat.mul_le_mul_left _ cad))
      (Nat.mul_le_mul_left _ cbg)
  have hproj84 : ∀ (w : List (Fin 84)) (i j : Fin 3),
      evalFinWordMat 84 3 (rank2BlockNilpMat3DC78 k alpha beta gamma delta) w i j =
        evalFinWordMat 42 3 (rank2BlockNilpMat3DC39 k alpha beta gamma delta) (w.map projSym84To42) i j := by
    intro w; induction w with
    | nil => intros; rfl
    | cons s tl ih =>
      intro i j
      simp only [List.map_cons]
      rw [mat3_mul_step_w18 84 _ s tl i j,
          mat3_mul_step_w18 42 _ (projSym84To42 s) (tl.map projSym84To42) i j,
          ih fin3Z0W18 j, ih fin3Z1W18 j, ih fin3Z2W18 j]
      rfl
  refine ⟨hw39, ?_⟩
  have hc78_proj := block_nilp_3d_shape_and_witness_certs_w18.2.1
  intro r hr i j
  rw [hproj84 r.1 i j, hproj84 r.2 i j]
  rcases List.any_eq_true.mp (List.all_eq_true.mp hc78_proj r hr) with ⟨r39, hr39, hbeq⟩
  have heq_p := beq_iff_eq.mp hbeq
  rcases r39 with ⟨l39, r39_r⟩
  have hl_eq : r.1.map projSym84To42 = l39 := congrArg Prod.fst heq_p
  have hr_eq : r.2.map projSym84To42 = r39_r := congrArg Prod.snd heq_p
  rw [hl_eq, hr_eq]
  exact hw39 (l39, r39_r) hr39 i j

private theorem blockNilp3DProj_vec_linearity_w18 (N : Nat) (proj : Fin N -> Fin 42)
    (k alpha beta gamma delta : Nat) (v : Fin N -> Fin 3 -> Nat) :
    let matFn := fun k' a' b' g' d' (s : Fin N) => rank2BlockNilpMat3DC39 k' a' b' g' d' (proj s)
    (∀ w : List (Fin N), wordRow1Const3DBoolW18 N proj w = true ->
      evalFinWordVec N 3 (matFn k alpha beta gamma delta) v w fin3Z1W18 =
        evalFinWordVec N 3 (matFn 1 0 0 0 0) v w fin3Z1W18) ∧
    (∀ w : List (Fin N), wordRow2Const3DBoolW18 N proj w = true ->
      evalFinWordVec N 3 (matFn k alpha beta gamma delta) v w fin3Z2W18 =
        evalFinWordVec N 3 (matFn 1 0 0 0 0) v w fin3Z2W18) ∧
    (∀ w : List (Fin N), wordRow0BiLin3DBoolW18 N proj w = true ->
      evalFinWordVec N 3 (matFn 1 0 0 0 0) v w fin3Z0W18 ≤
        evalFinWordVec N 3 (matFn 1 1 0 0 0) v w fin3Z0W18 ∧
      evalFinWordVec N 3 (matFn 1 0 0 0 0) v w fin3Z0W18 ≤
        evalFinWordVec N 3 (matFn 1 0 1 0 0) v w fin3Z0W18 ∧
      evalFinWordVec N 3 (matFn k alpha beta gamma delta) v w fin3Z0W18 =
        evalFinWordVec N 3 (matFn 1 0 0 0 0) v w fin3Z0W18 +
          alpha * (evalFinWordVec N 3 (matFn 1 1 0 0 0) v w fin3Z0W18 -
            evalFinWordVec N 3 (matFn 1 0 0 0 0) v w fin3Z0W18) +
          beta * (evalFinWordVec N 3 (matFn 1 0 1 0 0) v w fin3Z0W18 -
            evalFinWordVec N 3 (matFn 1 0 0 0 0) v w fin3Z0W18)) := by
  dsimp only
  let matFn := fun k' a' b' g' d' (s : Fin N) => rank2BlockNilpMat3DC39 k' a' b' g' d' (proj s)
  have hv_single : ∀ (M : Fin N -> Fin 3 -> Fin 3 -> Nat) (s : Fin N) (i : Fin 3),
      evalFinWordVec N 3 M v [s] i = v s i := by
    intro M s i
    rw [mat3_step_expandN_w18 N M v s [] i]
    change v s i + _ * 0 + _ * 0 + _ * 0 = v s i; omega
  have hs00_unit : ∀ (s : Fin N), ((proj s).val < 6 ∨ (proj s).val ≥ 12) ->
      ∀ k' a' b' g' d', matFn k' a' b' g' d' s fin3Z0W18 fin3Z0W18 = 1 := by
    intro s hnr k' a' b' g' d'
    have hn611 : ¬ (6 ≤ (proj s).val ∧ (proj s).val ≤ 11) := by omega
    dsimp only [matFn, rank2BlockNilpMat3DC39, fin3Z0W18]
    simp [hn611]
  have hs012_lin : ∀ (s : Fin N) (k' a' b' g' d' : Nat),
      matFn k' a' b' g' d' s fin3Z0W18 fin3Z1W18 =
        b' * matFn 1 0 1 0 0 s fin3Z0W18 fin3Z1W18 ∧
      matFn k' a' b' g' d' s fin3Z0W18 fin3Z2W18 =
        a' * matFn 1 1 0 0 0 s fin3Z0W18 fin3Z2W18 := by
    intro s k' a' b' g' d'
    dsimp only [matFn]
    unfold rank2BlockNilpMat3DC39
    dsimp only [fin3Z0W18, fin3Z1W18, fin3Z2W18]
    refine ⟨?_, ?_⟩
    · cases isBeta01SymW18 (proj s).val <;> simp
    · cases isAlpha02SymW18 (proj s).val <;> simp
  refine ⟨?_, ?_, ?_⟩
  · intro w hbw
    cases w with
    | nil => rfl
    | cons s1 xs =>
      cases xs with
      | nil => rw [hv_single, hv_single]
      | cons s2 tl =>
        unfold wordRow1Const3DBoolW18 at hbw
        rcases of_decide_eq_true hbw with ⟨n33, n35, n39, n40, n41⟩
        have hnd : isDelta1SymW18 (proj s1).val = false := by
          unfold isDelta1SymW18
          simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne]
          exact ⟨⟨⟨⟨n33, n35⟩, n39⟩, n40⟩, n41⟩
        have hr1_0 : ∀ k' a' b' g' d' (j : Fin 3), matFn k' a' b' g' d' s1 fin3Z1W18 j = 0 := by
          intro k' a' b' g' d' j
          dsimp only [matFn]; unfold rank2BlockNilpMat3DC39; dsimp only [fin3Z1W18]
          rcases (by have := j.isLt; omega : j.val = 0 ∨ j.val = 1 ∨ j.val = 2) with hj | hj | hj <;>
          simp [hj, hnd]
        rw [mat3_step_expandN_w18 N (matFn k alpha beta gamma delta) v s1 (s2 :: tl) fin3Z1W18,
            mat3_step_expandN_w18 N (matFn 1 0 0 0 0) v s1 (s2 :: tl) fin3Z1W18,
            hr1_0 k alpha beta gamma delta fin3Z0W18, hr1_0 k alpha beta gamma delta fin3Z1W18,
            hr1_0 k alpha beta gamma delta fin3Z2W18, hr1_0 1 0 0 0 0 fin3Z0W18,
            hr1_0 1 0 0 0 0 fin3Z1W18, hr1_0 1 0 0 0 0 fin3Z2W18]
        omega
  · intro w hbw
    cases w with
    | nil => rfl
    | cons s1 xs =>
      cases xs with
      | nil => rw [hv_single, hv_single]
      | cons s2 tl =>
        unfold wordRow2Const3DBoolW18 at hbw
        rcases of_decide_eq_true hbw with ⟨n6, n7, n8, n28, n29, n31, n32, n36, n37, n38⟩
        have hn68 : ¬ (6 ≤ (proj s1).val ∧ (proj s1).val ≤ 8) := by omega
        have hng : isGamma20SymW18 (proj s1).val = false := by
          unfold isGamma20SymW18
          simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne]
          exact ⟨⟨⟨⟨⟨⟨n28, n29⟩, n31⟩, n32⟩, n36⟩, n37⟩, n38⟩
        have hr2_0 : ∀ k' a' b' g' d' (j : Fin 3), matFn k' a' b' g' d' s1 fin3Z2W18 j = 0 := by
          intro k' a' b' g' d' j
          dsimp only [matFn]; unfold rank2BlockNilpMat3DC39; dsimp only [fin3Z2W18]
          rcases (by have := j.isLt; omega : j.val = 0 ∨ j.val = 1 ∨ j.val = 2) with hj | hj | hj <;>
          simp [hj, hn68, hng]
        rw [mat3_step_expandN_w18 N (matFn k alpha beta gamma delta) v s1 (s2 :: tl) fin3Z2W18,
            mat3_step_expandN_w18 N (matFn 1 0 0 0 0) v s1 (s2 :: tl) fin3Z2W18,
            hr2_0 k alpha beta gamma delta fin3Z0W18, hr2_0 k alpha beta gamma delta fin3Z1W18,
            hr2_0 k alpha beta gamma delta fin3Z2W18, hr2_0 1 0 0 0 0 fin3Z0W18,
            hr2_0 1 0 0 0 0 fin3Z1W18, hr2_0 1 0 0 0 0 fin3Z2W18]
        omega
  · intro w hbw
    cases w with
    | nil => exact ⟨Nat.le_refl 0, Nat.le_refl 0, by simp [evalFinWordVec]⟩
    | cons s1 xs1 =>
      cases xs1 with
      | nil => simp [hv_single]
      | cons s2 xs2 =>
        cases xs2 with
        | nil =>
          have hs1_nr : (proj s1).val < 6 ∨ (proj s1).val ≥ 12 := of_decide_eq_true hbw
          have hexp : ∀ k' a' b' g' d',
              evalFinWordVec N 3 (matFn k' a' b' g' d') v [s1, s2] fin3Z0W18 =
                (v s1 fin3Z0W18 + v s2 fin3Z0W18) +
                a' * (matFn 1 1 0 0 0 s1 fin3Z0W18 fin3Z2W18 * v s2 fin3Z2W18) +
                b' * (matFn 1 0 1 0 0 s1 fin3Z0W18 fin3Z1W18 * v s2 fin3Z1W18) := by
            intro k' a' b' g' d'
            rw [mat3_step_expandN_w18 N (matFn k' a' b' g' d') v s1 [s2] fin3Z0W18,
                hs00_unit s1 hs1_nr k' a' b' g' d',
                (hs012_lin s1 k' a' b' g' d').1, (hs012_lin s1 k' a' b' g' d').2,
                hv_single, hv_single, hv_single, Nat.one_mul, Nat.mul_assoc, Nat.mul_assoc]
            omega
          rw [hexp 1 0 0 0 0, hexp 1 1 0 0 0, hexp 1 0 1 0 0, hexp k alpha beta gamma delta]
          generalize v s1 fin3Z0W18 + v s2 fin3Z0W18 = V0,
            matFn 1 1 0 0 0 s1 fin3Z0W18 fin3Z2W18 * v s2 fin3Z2W18 = VA,
            matFn 1 0 1 0 0 s1 fin3Z0W18 fin3Z1W18 * v s2 fin3Z1W18 = VB
          simp only [Nat.zero_mul, Nat.one_mul, Nat.add_zero]
          refine ⟨by omega, by omega, ?_⟩
          have sa : V0 + VA - V0 = VA := by omega
          have sb : V0 + VB - V0 = VB := by omega
          rw [sa, sb]
        | cons s3 xs3 =>
          cases xs3 with
          | nil =>
            unfold wordRow0BiLin3DBoolW18 at hbw
            rcases of_decide_eq_true hbw with ⟨hs1_c, hs2_c⟩
            have hs1_nr : (proj s1).val < 6 ∨ (proj s1).val ≥ 12 := by omega
            have hs2_tail : ∀ k' a' b' g' d',
                evalFinWordVec N 3 (matFn k' a' b' g' d') v [s2, s3] fin3Z0W18 =
                  v s2 fin3Z0W18 + v s3 fin3Z0W18 + b' * v s3 fin3Z1W18 ∧
                evalFinWordVec N 3 (matFn k' a' b' g' d') v [s2, s3] fin3Z1W18 =
                  v s2 fin3Z1W18 ∧
                evalFinWordVec N 3 (matFn k' a' b' g' d') v [s2, s3] fin3Z2W18 =
                  v s2 fin3Z2W18 := by
              intro k' a' b' g' d'
              have m00 : matFn k' a' b' g' d' s2 fin3Z0W18 fin3Z0W18 = 1 :=
                hs00_unit s2 (by omega) k' a' b' g' d'
              have m01 : matFn k' a' b' g' d' s2 fin3Z0W18 fin3Z1W18 = b' := by
                dsimp only [matFn]; unfold rank2BlockNilpMat3DC39; dsimp only [fin3Z0W18, fin3Z1W18]
                rcases hs2_c with h | h <;> simp [isBeta01SymW18, h]
              have m02 : matFn k' a' b' g' d' s2 fin3Z0W18 fin3Z2W18 = 0 := by
                dsimp only [matFn]; unfold rank2BlockNilpMat3DC39; dsimp only [fin3Z0W18, fin3Z2W18]
                rcases hs2_c with h | h <;> simp [isAlpha02SymW18, h]
              have m1 : ∀ q, matFn k' a' b' g' d' s2 fin3Z1W18 q = 0 := by
                intro q; dsimp only [matFn]; unfold rank2BlockNilpMat3DC39; dsimp only [fin3Z1W18]
                rcases (by have := q.isLt; omega : q.val = 0 ∨ q.val = 1 ∨ q.val = 2) with hq | hq | hq <;>
                (rcases hs2_c with h | h <;> simp [isDelta1SymW18, hq, h])
              have m2 : ∀ q, matFn k' a' b' g' d' s2 fin3Z2W18 q = 0 := by
                intro q; dsimp only [matFn]; unfold rank2BlockNilpMat3DC39; dsimp only [fin3Z2W18]
                rcases (by have := q.isLt; omega : q.val = 0 ∨ q.val = 1 ∨ q.val = 2) with hq | hq | hq <;>
                (rcases hs2_c with h | h <;> simp [isGamma20SymW18, hq, h])
              refine ⟨?_, ?_, ?_⟩
              · rw [mat3_step_expandN_w18 N _ v s2 [s3] fin3Z0W18, m00, m01, m02,
                    hv_single, hv_single, hv_single]; omega
              · rw [mat3_step_expandN_w18 N _ v s2 [s3] fin3Z1W18, hv_single,
                    m1 fin3Z0W18, m1 fin3Z1W18, m1 fin3Z2W18]; omega
              · rw [mat3_step_expandN_w18 N _ v s2 [s3] fin3Z2W18, hv_single,
                    m2 fin3Z0W18, m2 fin3Z1W18, m2 fin3Z2W18]; omega
            have hexp3 : ∀ k' a' b' g' d',
                evalFinWordVec N 3 (matFn k' a' b' g' d') v [s1, s2, s3] fin3Z0W18 =
                  (v s1 fin3Z0W18 + v s2 fin3Z0W18 + v s3 fin3Z0W18) +
                  a' * (matFn 1 1 0 0 0 s1 fin3Z0W18 fin3Z2W18 * v s2 fin3Z2W18) +
                  b' * (v s3 fin3Z1W18 + matFn 1 0 1 0 0 s1 fin3Z0W18 fin3Z1W18 * v s2 fin3Z1W18) := by
              intro k' a' b' g' d'
              rw [mat3_step_expandN_w18 N (matFn k' a' b' g' d') v s1 [s2, s3] fin3Z0W18,
                  hs00_unit s1 hs1_nr k' a' b' g' d',
                  (hs012_lin s1 k' a' b' g' d').1, (hs012_lin s1 k' a' b' g' d').2,
                  (hs2_tail k' a' b' g' d').1, (hs2_tail k' a' b' g' d').2.1,
                  (hs2_tail k' a' b' g' d').2.2, Nat.one_mul, Nat.mul_assoc, Nat.mul_assoc,
                  Nat.mul_add b']
              omega
            rw [hexp3 1 0 0 0 0, hexp3 1 1 0 0 0, hexp3 1 0 1 0 0, hexp3 k alpha beta gamma delta]
            generalize v s1 fin3Z0W18 + v s2 fin3Z0W18 + v s3 fin3Z0W18 = V0,
              matFn 1 1 0 0 0 s1 fin3Z0W18 fin3Z2W18 * v s2 fin3Z2W18 = VA,
              v s3 fin3Z1W18 + matFn 1 0 1 0 0 s1 fin3Z0W18 fin3Z1W18 * v s2 fin3Z1W18 = VB
            simp only [Nat.zero_mul, Nat.one_mul, Nat.add_zero]
            refine ⟨by omega, by omega, ?_⟩
            have sa : V0 + VA - V0 = VA := by omega
            have sb : V0 + VB - V0 = VB := by omega
            rw [sa, sb]
          | cons _ _ => cases hbw

private theorem bn3d_farkas_zero_strict_proj_w18
    (N : Nat) (proj : Fin N -> Fin 42)
    (mu0 mu1 mu2 : List (Fin N) -> Nat)
    (rs : List (List (Fin N) × List (Fin N)))
    (hshape_b : checkWordShape3DFarkasNBoolW18 N proj mu0 mu1 mu2 rs = true)
    (hbasis : ∀ (j0 : Fin 3) (s0 : Fin N),
      let p0 := farkas3DFastPairW18 N proj mu0 (fun _ => 0) (fun _ => 0) 1 0 0 0 0 s0 j0 rs
      let pa := farkas3DFastPairW18 N proj mu0 (fun _ => 0) mu2 1 1 0 0 0 s0 j0 rs
      let pb := farkas3DFastPairW18 N proj mu0 mu1 (fun _ => 0) 1 0 1 0 0 s0 j0 rs
      p0.1 ≤ p0.2 ∧ pa.1 - p0.1 ≤ pa.2 - p0.2 ∧ pb.1 - p0.1 ≤ pb.2 - p0.2)
    (k alpha beta gamma delta : Nat) (v : Fin N -> Fin 3 -> Nat)
    (hv_weak : ∀ r ∈ rs, ∀ i : Fin 3,
      evalFinWordVec N 3 (fun s => rank2BlockNilpMat3DC39 k alpha beta gamma delta (proj s)) v r.1 i ≥
        evalFinWordVec N 3 (fun s => rank2BlockNilpMat3DC39 k alpha beta gamma delta (proj s)) v r.2 i) :
    ∀ r ∈ rs,
      evalFinWordVec N 3 (fun s => rank2BlockNilpMat3DC39 k alpha beta gamma delta (proj s)) v r.1 fin3Z0W18 =
        evalFinWordVec N 3 (fun s => rank2BlockNilpMat3DC39 k alpha beta gamma delta (proj s)) v r.2 fin3Z0W18 := by
  let matFn := fun k' a' b' g' d' (s : Fin N) => rank2BlockNilpMat3DC39 k' a' b' g' d' (proj s)
  let m1_sc : List (Fin N) -> Nat := fun l => beta * mu1 l
  let m2_sc : List (Fin N) -> Nat := fun l => alpha * mu2 l
  have hfark_aff : ∀ (v0 : Fin N -> Fin 3 -> Nat)
      (xs : List (List (Fin N) × List (Fin N))),
      checkWordShape3DFarkasNBoolW18 N proj mu0 mu1 mu2 xs = true ->
      farkas3DVecLhsN N proj mu0 (fun _ => 0) (fun _ => 0) 1 0 0 0 0 v0 xs ≤
        farkas3DVecLhsN N proj mu0 (fun _ => 0) mu2 1 1 0 0 0 v0 xs ∧
      farkas3DVecRhsN N proj mu0 (fun _ => 0) (fun _ => 0) 1 0 0 0 0 v0 xs ≤
        farkas3DVecRhsN N proj mu0 (fun _ => 0) mu2 1 1 0 0 0 v0 xs ∧
      farkas3DVecLhsN N proj mu0 (fun _ => 0) (fun _ => 0) 1 0 0 0 0 v0 xs ≤
        farkas3DVecLhsN N proj mu0 mu1 (fun _ => 0) 1 0 1 0 0 v0 xs ∧
      farkas3DVecRhsN N proj mu0 (fun _ => 0) (fun _ => 0) 1 0 0 0 0 v0 xs ≤
        farkas3DVecRhsN N proj mu0 mu1 (fun _ => 0) 1 0 1 0 0 v0 xs ∧
      farkas3DVecLhsN N proj mu0 m1_sc m2_sc k alpha beta gamma delta v0 xs =
        farkas3DVecLhsN N proj mu0 (fun _ => 0) (fun _ => 0) 1 0 0 0 0 v0 xs +
          alpha * (farkas3DVecLhsN N proj mu0 (fun _ => 0) mu2 1 1 0 0 0 v0 xs -
            farkas3DVecLhsN N proj mu0 (fun _ => 0) (fun _ => 0) 1 0 0 0 0 v0 xs) +
          beta * (farkas3DVecLhsN N proj mu0 mu1 (fun _ => 0) 1 0 1 0 0 v0 xs -
            farkas3DVecLhsN N proj mu0 (fun _ => 0) (fun _ => 0) 1 0 0 0 0 v0 xs) ∧
      farkas3DVecRhsN N proj mu0 m1_sc m2_sc k alpha beta gamma delta v0 xs =
        farkas3DVecRhsN N proj mu0 (fun _ => 0) (fun _ => 0) 1 0 0 0 0 v0 xs +
          alpha * (farkas3DVecRhsN N proj mu0 (fun _ => 0) mu2 1 1 0 0 0 v0 xs -
            farkas3DVecRhsN N proj mu0 (fun _ => 0) (fun _ => 0) 1 0 0 0 0 v0 xs) +
          beta * (farkas3DVecRhsN N proj mu0 mu1 (fun _ => 0) 1 0 1 0 0 v0 xs -
            farkas3DVecRhsN N proj mu0 (fun _ => 0) (fun _ => 0) 1 0 0 0 0 v0 xs) := by
    intro v0 xs; induction xs with
    | nil => intros; simp [farkas3DVecLhsN, farkas3DVecRhsN]
    | cons r0 rtl ih =>
      rcases r0 with ⟨l0, r0_w⟩
      intro hbw
      unfold checkWordShape3DFarkasNBoolW18 at hbw
      simp only [List.all_cons] at hbw
      rcases bool_and_split hbw with ⟨h0_b, htl_b⟩
      rcases ih htl_b with ⟨hla_tl, hra_tl, hlb_tl, hrb_tl, htl_l, htl_r⟩
      rcases bool_and_split h0_b with ⟨hb_1, _⟩
      rcases bool_and_split hb_1 with ⟨hb_2, hm2_disj⟩
      rcases bool_and_split hb_2 with ⟨hb_3, hm1_disj⟩
      rcases bool_and_split hb_3 with ⟨hl_r0, hr_r0⟩
      rcases blockNilp3DProj_vec_linearity_w18 N proj k alpha beta gamma delta v0 with ⟨hr1_c, hr2_c, hr0_lin⟩
      rcases hr0_lin l0 hl_r0 with ⟨hle_la, hle_lb, hl0_ab⟩
      rcases hr0_lin r0_w hr_r0 with ⟨hle_ra, hle_rb, hr0_ab⟩
      have hm1_eq :
          m1_sc l0 * evalFinWordVec N 3 (matFn k alpha beta gamma delta) v0 l0 fin3Z1W18 =
            beta * (mu1 l0 * evalFinWordVec N 3 (matFn 1 0 1 0 0) v0 l0 fin3Z1W18) ∧
          m1_sc l0 * evalFinWordVec N 3 (matFn k alpha beta gamma delta) v0 r0_w fin3Z1W18 =
            beta * (mu1 l0 * evalFinWordVec N 3 (matFn 1 0 1 0 0) v0 r0_w fin3Z1W18) := by
        dsimp only [m1_sc]
        rcases Bool.or_eq_true_iff.mp hm1_disj with hm0 | hc12
        · rw [of_decide_eq_true hm0]; simp
        · rcases bool_and_split hc12 with ⟨hc1, hc2⟩
          have e1 := hr1_c l0 hc1
          have e1' := (blockNilp3DProj_vec_linearity_w18 N proj 1 0 1 0 0 v0).1 l0 hc1
          have e2 := hr1_c r0_w hc2
          have e2' := (blockNilp3DProj_vec_linearity_w18 N proj 1 0 1 0 0 v0).1 r0_w hc2
          dsimp only [matFn] at e1 e1' e2 e2' ⊢
          rw [e1, ← e1', e2, ← e2', Nat.mul_assoc, Nat.mul_assoc]
          exact ⟨rfl, rfl⟩
      have hm2_eq :
          m2_sc l0 * evalFinWordVec N 3 (matFn k alpha beta gamma delta) v0 l0 fin3Z2W18 =
            alpha * (mu2 l0 * evalFinWordVec N 3 (matFn 1 1 0 0 0) v0 l0 fin3Z2W18) ∧
          m2_sc l0 * evalFinWordVec N 3 (matFn k alpha beta gamma delta) v0 r0_w fin3Z2W18 =
            alpha * (mu2 l0 * evalFinWordVec N 3 (matFn 1 1 0 0 0) v0 r0_w fin3Z2W18) := by
        dsimp only [m2_sc]
        rcases Bool.or_eq_true_iff.mp hm2_disj with hm0 | hc12
        · rw [of_decide_eq_true hm0]; simp
        · rcases bool_and_split hc12 with ⟨hc1, hc2⟩
          have e1 := hr2_c l0 hc1
          have e1' := (blockNilp3DProj_vec_linearity_w18 N proj 1 1 0 0 0 v0).2.1 l0 hc1
          have e2 := hr2_c r0_w hc2
          have e2' := (blockNilp3DProj_vec_linearity_w18 N proj 1 1 0 0 0 v0).2.1 r0_w hc2
          dsimp only [matFn] at e1 e1' e2 e2' ⊢
          rw [e1, ← e1', e2, ← e2', Nat.mul_assoc, Nat.mul_assoc]
          exact ⟨rfl, rfl⟩
      simp only [farkas3DVecLhsN, farkas3DVecRhsN, Nat.zero_mul, Nat.add_zero]
      change _ ∧ _ ∧ _ ∧ _ ∧
        mu0 l0 * evalFinWordVec N 3 (matFn k alpha beta gamma delta) v0 l0 fin3Z0W18 +
          m1_sc l0 * evalFinWordVec N 3 (matFn k alpha beta gamma delta) v0 l0 fin3Z1W18 +
          m2_sc l0 * evalFinWordVec N 3 (matFn k alpha beta gamma delta) v0 l0 fin3Z2W18 +
          farkas3DVecLhsN N proj mu0 m1_sc m2_sc k alpha beta gamma delta v0 rtl = _ ∧
        mu0 l0 * evalFinWordVec N 3 (matFn k alpha beta gamma delta) v0 r0_w fin3Z0W18 +
          m1_sc l0 * evalFinWordVec N 3 (matFn k alpha beta gamma delta) v0 r0_w fin3Z1W18 +
          m2_sc l0 * evalFinWordVec N 3 (matFn k alpha beta gamma delta) v0 r0_w fin3Z2W18 +
          farkas3DVecRhsN N proj mu0 m1_sc m2_sc k alpha beta gamma delta v0 rtl = _
      rw [hl0_ab, hr0_ab, hm1_eq.1, hm1_eq.2, hm2_eq.1, hm2_eq.2, htl_l, htl_r]
      have hm_la := Nat.mul_le_mul_left (mu0 l0) hle_la
      have hm_lb := Nat.mul_le_mul_left (mu0 l0) hle_lb
      have hm_ra := Nat.mul_le_mul_left (mu0 l0) hle_ra
      have hm_rb := Nat.mul_le_mul_left (mu0 l0) hle_rb
      dsimp only [matFn] at hm_la hm_lb hm_ra hm_rb hle_la hle_lb hle_ra hle_rb ⊢
      refine ⟨by omega, by omega, by omega, by omega, ?_, ?_⟩
      · generalize evalFinWordVec N 3 (fun s => rank2BlockNilpMat3DC39 1 0 0 0 0 (proj s)) v0 l0 fin3Z0W18 = L0,
          evalFinWordVec N 3 (fun s => rank2BlockNilpMat3DC39 1 1 0 0 0 (proj s)) v0 l0 fin3Z0W18 = LA,
          evalFinWordVec N 3 (fun s => rank2BlockNilpMat3DC39 1 0 1 0 0 (proj s)) v0 l0 fin3Z0W18 = LB,
          mu2 l0 * evalFinWordVec N 3 (fun s => rank2BlockNilpMat3DC39 1 1 0 0 0 (proj s)) v0 l0 fin3Z2W18 = M2L,
          mu1 l0 * evalFinWordVec N 3 (fun s => rank2BlockNilpMat3DC39 1 0 1 0 0 (proj s)) v0 l0 fin3Z1W18 = M1L,
          farkas3DVecLhsN N proj mu0 (fun _ => 0) (fun _ => 0) 1 0 0 0 0 v0 rtl = TL0,
          farkas3DVecLhsN N proj mu0 (fun _ => 0) mu2 1 1 0 0 0 v0 rtl = TLA,
          farkas3DVecLhsN N proj mu0 mu1 (fun _ => 0) 1 0 1 0 0 v0 rtl = TLB at hm_la hm_lb hla_tl hlb_tl hle_la hle_lb ⊢
        have sa : (mu0 l0 * LA + M2L + TLA) - (mu0 l0 * L0 + TL0) =
            mu0 l0 * (LA - L0) + M2L + (TLA - TL0) := by rw [Nat.mul_sub_left_distrib]; omega
        have sb : (mu0 l0 * LB + M1L + TLB) - (mu0 l0 * L0 + TL0) =
            mu0 l0 * (LB - L0) + M1L + (TLB - TL0) := by rw [Nat.mul_sub_left_distrib]; omega
        change mu0 l0 * (L0 + alpha * (LA - L0) + beta * (LB - L0)) + beta * M1L + alpha * M2L + _ =
          (mu0 l0 * L0 + TL0) + alpha * ((mu0 l0 * LA + M2L + TLA) - (mu0 l0 * L0 + TL0)) +
          beta * ((mu0 l0 * LB + M1L + TLB) - (mu0 l0 * L0 + TL0))
        rw [sa, sb, Nat.mul_add (mu0 l0), Nat.mul_add (mu0 l0),
            Nat.mul_add alpha, Nat.mul_add alpha, Nat.mul_add beta, Nat.mul_add beta,
            ← Nat.mul_assoc alpha (mu0 l0), Nat.mul_comm alpha (mu0 l0), Nat.mul_assoc (mu0 l0) alpha,
            ← Nat.mul_assoc beta (mu0 l0), Nat.mul_comm beta (mu0 l0), Nat.mul_assoc (mu0 l0) beta]
        omega
      · generalize evalFinWordVec N 3 (fun s => rank2BlockNilpMat3DC39 1 0 0 0 0 (proj s)) v0 r0_w fin3Z0W18 = R0,
          evalFinWordVec N 3 (fun s => rank2BlockNilpMat3DC39 1 1 0 0 0 (proj s)) v0 r0_w fin3Z0W18 = RA,
          evalFinWordVec N 3 (fun s => rank2BlockNilpMat3DC39 1 0 1 0 0 (proj s)) v0 r0_w fin3Z0W18 = RB,
          mu2 l0 * evalFinWordVec N 3 (fun s => rank2BlockNilpMat3DC39 1 1 0 0 0 (proj s)) v0 r0_w fin3Z2W18 = M2R,
          mu1 l0 * evalFinWordVec N 3 (fun s => rank2BlockNilpMat3DC39 1 0 1 0 0 (proj s)) v0 r0_w fin3Z1W18 = M1R,
          farkas3DVecRhsN N proj mu0 (fun _ => 0) (fun _ => 0) 1 0 0 0 0 v0 rtl = TR0,
          farkas3DVecRhsN N proj mu0 (fun _ => 0) mu2 1 1 0 0 0 v0 rtl = TRA,
          farkas3DVecRhsN N proj mu0 mu1 (fun _ => 0) 1 0 1 0 0 v0 rtl = TRB at hm_ra hm_rb hra_tl hrb_tl hle_ra hle_rb ⊢
        have sa : (mu0 l0 * RA + M2R + TRA) - (mu0 l0 * R0 + TR0) =
            mu0 l0 * (RA - R0) + M2R + (TRA - TR0) := by rw [Nat.mul_sub_left_distrib]; omega
        have sb : (mu0 l0 * RB + M1R + TRB) - (mu0 l0 * R0 + TR0) =
            mu0 l0 * (RB - R0) + M1R + (TRB - TR0) := by rw [Nat.mul_sub_left_distrib]; omega
        change mu0 l0 * (R0 + alpha * (RA - R0) + beta * (RB - R0)) + beta * M1R + alpha * M2R + _ =
          (mu0 l0 * R0 + TR0) + alpha * ((mu0 l0 * RA + M2R + TRA) - (mu0 l0 * R0 + TR0)) +
          beta * ((mu0 l0 * RB + M1R + TRB) - (mu0 l0 * R0 + TR0))
        rw [sa, sb, Nat.mul_add (mu0 l0), Nat.mul_add (mu0 l0),
            Nat.mul_add alpha, Nat.mul_add alpha, Nat.mul_add beta, Nat.mul_add beta,
            ← Nat.mul_assoc alpha (mu0 l0), Nat.mul_comm alpha (mu0 l0), Nat.mul_assoc (mu0 l0) alpha,
            ← Nat.mul_assoc beta (mu0 l0), Nat.mul_comm beta (mu0 l0), Nat.mul_assoc (mu0 l0) beta]
        omega
  have hbasis_kabgd : ∀ (s0 : Fin N) (j0 : Fin 3),
      farkas3DVecLhsN N proj mu0 m1_sc m2_sc k alpha beta gamma delta (basisVec3D N s0 j0) rs ≤
        farkas3DVecRhsN N proj mu0 m1_sc m2_sc k alpha beta gamma delta (basisVec3D N s0 j0) rs := by
    intro s0 j0
    have hb := hbasis j0 s0
    dsimp only at hb
    rw [farkas3DFastPairW18_eq N proj mu0 (fun _ => 0) (fun _ => 0) 1 0 0 0 0 s0 j0 rs,
        farkas3DFastPairW18_eq N proj mu0 (fun _ => 0) mu2 1 1 0 0 0 s0 j0 rs,
        farkas3DFastPairW18_eq N proj mu0 mu1 (fun _ => 0) 1 0 1 0 0 s0 j0 rs] at hb
    dsimp only at hb
    rcases hb with ⟨hb0, hba, hbb⟩
    rcases hfark_aff (basisVec3D N s0 j0) rs hshape_b with ⟨_, _, _, _, hl_eq, hr_eq⟩
    rw [hl_eq, hr_eq]
    have hma := Nat.mul_le_mul_left alpha hba
    have hmb := Nat.mul_le_mul_left beta hbb
    generalize farkas3DVecLhsN N proj mu0 (fun _ => 0) (fun _ => 0) 1 0 0 0 0 (basisVec3D N s0 j0) rs = L0,
      farkas3DVecRhsN N proj mu0 (fun _ => 0) (fun _ => 0) 1 0 0 0 0 (basisVec3D N s0 j0) rs = R0 at hb0 hma hmb ⊢
    generalize alpha * (farkas3DVecLhsN N proj mu0 (fun _ => 0) mu2 1 1 0 0 0 (basisVec3D N s0 j0) rs - L0) = DA_L,
      alpha * (farkas3DVecRhsN N proj mu0 (fun _ => 0) mu2 1 1 0 0 0 (basisVec3D N s0 j0) rs - R0) = DA_R,
      beta * (farkas3DVecLhsN N proj mu0 mu1 (fun _ => 0) 1 0 1 0 0 (basisVec3D N s0 j0) rs - L0) = DB_L,
      beta * (farkas3DVecRhsN N proj mu0 mu1 (fun _ => 0) 1 0 1 0 0 (basisVec3D N s0 j0) rs - R0) = DB_R at hb0 hma hmb ⊢
    omega
  let M := matFn k alpha beta gamma delta
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
  have hv_lin : ∀ (w : List (Fin N)) (i : Fin 3),
      evalFinWordVec N 3 M v w i =
        natSumPrefix N (fun s0 =>
          v s0 fin3Z0W18 * evalFinWordVec N 3 M (basisVec3D N s0 fin3Z0W18) w i +
          v s0 fin3Z1W18 * evalFinWordVec N 3 M (basisVec3D N s0 fin3Z1W18) w i +
          v s0 fin3Z2W18 * evalFinWordVec N 3 M (basisVec3D N s0 fin3Z2W18) w i) N := by
    have hdelta : ∀ (s : Fin N) (j : Fin 3),
        v s j = natSumPrefix N (fun s0 =>
          v s0 fin3Z0W18 * basisVec3D N s0 fin3Z0W18 s j +
          v s0 fin3Z1W18 * basisVec3D N s0 fin3Z1W18 s j +
          v s0 fin3Z2W18 * basisVec3D N s0 fin3Z2W18 s j) N := by
      intro s j
      have hst : ∀ m : Nat, m ≤ N ->
          natSumPrefix N (fun s0 =>
            v s0 fin3Z0W18 * basisVec3D N s0 fin3Z0W18 s j +
            v s0 fin3Z1W18 * basisVec3D N s0 fin3Z1W18 s j +
            v s0 fin3Z2W18 * basisVec3D N s0 fin3Z2W18 s j) m =
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
            rcases (by have := j.isLt; omega : j.val = 0 ∨ j.val = 1 ∨ j.val = 2) with hj | hj | hj
            · rw [show j = fin3Z0W18 from Fin.ext hj]; dsimp only [basisVec3D, fin3Z0W18, fin3Z1W18, fin3Z2W18]; simp
            · rw [show j = fin3Z1W18 from Fin.ext hj]; dsimp only [basisVec3D, fin3Z0W18, fin3Z1W18, fin3Z2W18]; simp
            · rw [show j = fin3Z2W18 from Fin.ext hj]; dsimp only [basisVec3D, fin3Z0W18, fin3Z1W18, fin3Z2W18]; simp
          · have hne_b : (s.val == m') = false := beq_false_of_ne heq
            have hb0 : ∀ j0 : Fin 3, basisVec3D N ⟨m', hm_lt⟩ j0 s j = 0 := by
              intro j0; unfold basisVec3D; dsimp only; rw [hne_b]; rfl
            rw [hb0 fin3Z0W18, hb0 fin3Z1W18, hb0 fin3Z2W18,
                Nat.mul_zero, Nat.mul_zero, Nat.mul_zero,
                Nat.add_zero, Nat.add_zero, Nat.add_zero]
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
      rw [mat3_step_expandN_w18 N M v s rest i, hdelta s i,
          ih fin3Z0W18, ih fin3Z1W18, ih fin3Z2W18,
          hsum_mul (M s i fin3Z0W18), hsum_mul (M s i fin3Z1W18), hsum_mul (M s i fin3Z2W18),
          ← hsum_add, ← hsum_add, ← hsum_add]
      apply hcongr _ _ (fun s0 => ?_) N
      rw [mat3_step_expandN_w18 N M (basisVec3D N s0 fin3Z0W18) s rest i,
          mat3_step_expandN_w18 N M (basisVec3D N s0 fin3Z1W18) s rest i,
          mat3_step_expandN_w18 N M (basisVec3D N s0 fin3Z2W18) s rest i]
      simp only [Nat.mul_add]; ac_rfl
  have hfark_lin : ∀ xs : List (List (Fin N) × List (Fin N)),
      farkas3DVecLhsN N proj mu0 m1_sc m2_sc k alpha beta gamma delta v xs =
        natSumPrefix N (fun s0 =>
          v s0 fin3Z0W18 * farkas3DVecLhsN N proj mu0 m1_sc m2_sc k alpha beta gamma delta (basisVec3D N s0 fin3Z0W18) xs +
          v s0 fin3Z1W18 * farkas3DVecLhsN N proj mu0 m1_sc m2_sc k alpha beta gamma delta (basisVec3D N s0 fin3Z1W18) xs +
          v s0 fin3Z2W18 * farkas3DVecLhsN N proj mu0 m1_sc m2_sc k alpha beta gamma delta (basisVec3D N s0 fin3Z2W18) xs) N ∧
      farkas3DVecRhsN N proj mu0 m1_sc m2_sc k alpha beta gamma delta v xs =
        natSumPrefix N (fun s0 =>
          v s0 fin3Z0W18 * farkas3DVecRhsN N proj mu0 m1_sc m2_sc k alpha beta gamma delta (basisVec3D N s0 fin3Z0W18) xs +
          v s0 fin3Z1W18 * farkas3DVecRhsN N proj mu0 m1_sc m2_sc k alpha beta gamma delta (basisVec3D N s0 fin3Z1W18) xs +
          v s0 fin3Z2W18 * farkas3DVecRhsN N proj mu0 m1_sc m2_sc k alpha beta gamma delta (basisVec3D N s0 fin3Z2W18) xs) N := by
    intro xs; induction xs with
    | nil =>
      have hz : ∀ m : Nat, natSumPrefix N (fun _ => 0) m = 0 := by
        intro m; induction m with
        | zero => rfl
        | succ m' ih => simp only [natSumPrefix]; by_cases hm : m' < N <;> simp [hm, ih]
      refine ⟨?_, ?_⟩ <;> simpa [farkas3DVecLhsN, farkas3DVecRhsN] using (hz N).symm
    | cons r0 rtl ih =>
      rcases r0 with ⟨l0, r0_w⟩
      rcases ih with ⟨ihl, ihr⟩
      refine ⟨?_, ?_⟩
      · simp only [farkas3DVecLhsN]
        change mu0 l0 * evalFinWordVec N 3 M v l0 fin3Z0W18 +
          m1_sc l0 * evalFinWordVec N 3 M v l0 fin3Z1W18 +
          m2_sc l0 * evalFinWordVec N 3 M v l0 fin3Z2W18 +
          farkas3DVecLhsN N proj mu0 m1_sc m2_sc k alpha beta gamma delta v rtl = _
        rw [hv_lin l0 fin3Z0W18, hv_lin l0 fin3Z1W18, hv_lin l0 fin3Z2W18, ihl,
            hsum_mul (mu0 l0), hsum_mul (m1_sc l0), hsum_mul (m2_sc l0),
            ← hsum_add, ← hsum_add, ← hsum_add]
        apply hcongr _ _ (fun s0 => ?_) N; simp only [Nat.mul_add]; ac_rfl
      · simp only [farkas3DVecRhsN]
        change mu0 l0 * evalFinWordVec N 3 M v r0_w fin3Z0W18 +
          m1_sc l0 * evalFinWordVec N 3 M v r0_w fin3Z1W18 +
          m2_sc l0 * evalFinWordVec N 3 M v r0_w fin3Z2W18 +
          farkas3DVecRhsN N proj mu0 m1_sc m2_sc k alpha beta gamma delta v rtl = _
        rw [hv_lin r0_w fin3Z0W18, hv_lin r0_w fin3Z1W18, hv_lin r0_w fin3Z2W18, ihr,
            hsum_mul (mu0 l0), hsum_mul (m1_sc l0), hsum_mul (m2_sc l0),
            ← hsum_add, ← hsum_add, ← hsum_add]
        apply hcongr _ _ (fun s0 => ?_) N; simp only [Nat.mul_add]; ac_rfl
  have htot_le : farkas3DVecLhsN N proj mu0 m1_sc m2_sc k alpha beta gamma delta v rs ≤
      farkas3DVecRhsN N proj mu0 m1_sc m2_sc k alpha beta gamma delta v rs := by
    rcases hfark_lin rs with ⟨hl, hr⟩
    rw [hl, hr]
    exact natSumPrefix_mono_w5 N _ _ (fun s0 =>
      Nat.add_le_add
        (Nat.add_le_add
          (Nat.mul_le_mul_left _ (hbasis_kabgd s0 fin3Z0W18))
          (Nat.mul_le_mul_left _ (hbasis_kabgd s0 fin3Z1W18)))
        (Nat.mul_le_mul_left _ (hbasis_kabgd s0 fin3Z2W18))) N
  have hmu0_pos : ∀ r ∈ rs, mu0 r.1 ≥ 1 := by
    intro r hr
    unfold checkWordShape3DFarkasNBoolW18 at hshape_b
    rcases bool_and_split (List.all_eq_true.mp hshape_b r hr) with ⟨_, hm0_b⟩
    exact of_decide_eq_true hm0_b
  have hge_imp : ∀ xs : List (List (Fin N) × List (Fin N)),
      (∀ r ∈ xs, mu0 r.1 ≥ 1) ->
      (∀ r ∈ xs, ∀ i : Fin 3, evalFinWordVec N 3 M v r.1 i ≥ evalFinWordVec N 3 M v r.2 i) ->
      farkas3DVecLhsN N proj mu0 m1_sc m2_sc k alpha beta gamma delta v xs ≥
        farkas3DVecRhsN N proj mu0 m1_sc m2_sc k alpha beta gamma delta v xs ∧
      (farkas3DVecLhsN N proj mu0 m1_sc m2_sc k alpha beta gamma delta v xs =
        farkas3DVecRhsN N proj mu0 m1_sc m2_sc k alpha beta gamma delta v xs ->
        ∀ r ∈ xs, evalFinWordVec N 3 M v r.1 fin3Z0W18 = evalFinWordVec N 3 M v r.2 fin3Z0W18) := by
    intro xs; induction xs with
    | nil => intros; exact ⟨Nat.le_refl 0, fun _ _ hr => by cases hr⟩
    | cons r0 rtl ih =>
      rcases r0 with ⟨l0, r0_w⟩
      intro hmp hw
      rcases ih (fun r hr => hmp r (List.Mem.tail _ hr))
        (fun r hr => hw r (List.Mem.tail _ hr)) with ⟨hge_tl, heq_tl⟩
      simp only [farkas3DVecLhsN, farkas3DVecRhsN]
      have hm0_1 : mu0 l0 ≥ 1 := hmp (l0, r0_w) (List.Mem.head _)
      have hg0 := Nat.mul_le_mul_left (mu0 l0) (hw (l0, r0_w) (List.Mem.head _) fin3Z0W18)
      have hg1 := Nat.mul_le_mul_left (m1_sc l0) (hw (l0, r0_w) (List.Mem.head _) fin3Z1W18)
      have hg2 := Nat.mul_le_mul_left (m2_sc l0) (hw (l0, r0_w) (List.Mem.head _) fin3Z2W18)
      dsimp only [M, matFn] at hg0 hg1 hg2 ⊢
      refine ⟨by omega, fun heq_tot r hr => ?_⟩
      cases hr with
      | head =>
        dsimp only [M, matFn]
        have heq_m0 : mu0 l0 * evalFinWordVec N 3 (fun s => rank2BlockNilpMat3DC39 k alpha beta gamma delta (proj s)) v l0 fin3Z0W18 =
            mu0 l0 * evalFinWordVec N 3 (fun s => rank2BlockNilpMat3DC39 k alpha beta gamma delta (proj s)) v r0_w fin3Z0W18 := by omega
        exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < mu0 l0) heq_m0
      | tail _ htl_m => exact heq_tl (by omega) r htl_m
  rcases hge_imp rs hmu0_pos hv_weak with ⟨_, heq_imp⟩
  exact heq_imp (by omega)

private theorem packed_range_unpack_3d_w18 (N : Nat) (proj : Fin N -> Fin 42)
    (mu0 mu1 mu2 : List (Fin N) -> Nat) (j0 : Fin 3)
    (rs : List (List (Fin N) × List (Fin N)))
    (pk : List (Nat × Nat × Nat × List (Nat × Nat) × List (Nat × Nat)))
    (hpk : pack3DRulesNatW18 N proj mu0 mu1 mu2 rs = pk)
    (start : Nat) :
    ∀ cnt : Nat, check3DFarkasPackedRangeW18 pk j0.val start cnt = true ->
      ∀ (m : Nat) (hm : m < N), start ≤ m -> m < start + cnt ->
        let p0 := farkas3DFastPairW18 N proj mu0 (fun _ => 0) (fun _ => 0) 1 0 0 0 0 ⟨m, hm⟩ j0 rs
        let pa := farkas3DFastPairW18 N proj mu0 (fun _ => 0) mu2 1 1 0 0 0 ⟨m, hm⟩ j0 rs
        let pb := farkas3DFastPairW18 N proj mu0 mu1 (fun _ => 0) 1 0 1 0 0 ⟨m, hm⟩ j0 rs
        p0.1 ≤ p0.2 ∧ pa.1 - p0.1 ≤ pa.2 - p0.2 ∧ pb.1 - p0.1 ≤ pb.2 - p0.2
  | 0, _, _, _, hlo, hhi => by omega
  | cnt' + 1, hchk, m, hm, hlo, hhi => by
    unfold check3DFarkasPackedRangeW18 at hchk
    dsimp only at hchk
    rcases hp0 : farkas3DPackedPairW18 false false 1 0 0 0 0 (start + cnt') j0.val pk with ⟨p0l, p0r⟩
    rcases hpa : farkas3DPackedPairW18 false true 1 1 0 0 0 (start + cnt') j0.val pk with ⟨pal, par⟩
    rcases hpb : farkas3DPackedPairW18 true false 1 0 1 0 0 (start + cnt') j0.val pk with ⟨pbl, pbr⟩
    simp only [hp0, hpa, hpb] at hchk
    rcases bool_and_split hchk with ⟨hcur, hprev⟩
    by_cases hmeq : m = start + cnt'
    · subst hmeq
      rcases bool_and_split hcur with ⟨hc0a, hcb⟩
      rcases bool_and_split hc0a with ⟨hc0, hca⟩
      have eq0 := farkas3DPackedPairW18_eq N proj mu0 mu1 mu2 false false 1 0 0 0 0 (start + cnt') j0 rs
      have eqa := farkas3DPackedPairW18_eq N proj mu0 mu1 mu2 false true 1 1 0 0 0 (start + cnt') j0 rs
      have eqb := farkas3DPackedPairW18_eq N proj mu0 mu1 mu2 true false 1 0 1 0 0 (start + cnt') j0 rs
      rw [hpk] at eq0 eqa eqb
      simp only [Bool.false_eq_true, ↓reduceIte] at eq0 eqa eqb
      dsimp only [farkas3DFastPairW18] at eq0 eqa eqb ⊢
      rw [← eq0, ← eqa, ← eqb, hp0, hpa, hpb]
      dsimp only
      exact ⟨Nat.ble_eq.mp hc0, Nat.ble_eq.mp hca, Nat.ble_eq.mp hcb⟩
    · exact packed_range_unpack_3d_w18 N proj mu0 mu1 mu2 j0 rs pk hpk start cnt' hprev m hm hlo (by omega)

/--
  Theorem W18.1b (`simultaneous_d3_block_nilpotent_btr_farkas_locks`,
  `zero custom axioms`):
  Infinite 5-Parameter `d = 3` (`3 × 3`) Block-Nilpotent Cross-Channel `.B` + `.T` + `.R` Mixed
  Zero-Diagonal Cones on BOTH `c39` (`rank2BlockNilpMat3DC39 k α β γ δ`, `37/39` Strict Matrix Rules,
  Non-Zero Lower-Right `(M_{33})_{1,2} = δ`) AND `c78` (`rank2BlockNilpMat3DC78 k α β γ δ`, `74/78`
  Strict Matrix Rules), `+10` Escapes From `μ_0`-Only and Wave 17 Row-1/Row-2 Farkas Syzygies, &
  Universal 3-Channel `(μ_0, β * μ_1, α * μ_2)` Bilinear Farkas Zero-Strict-Drop Locks
  (`Branch P4.3`, witness `ZPOS_C39_3D_BLOCK_NILP_AND_DUAL_BT_ESCAPE`, `W18_H1`).
-/
theorem simultaneous_d3_block_nilpotent_btr_farkas_locks :
    let c39 := filterFinParikhUnoriented 42 wtTwoSidedMod3OmitR3
      (twoSidedLabelledCollatzRules 3 (by decide) all11OmitR3List)
    let c78 := filterFinParikhUnoriented 84 wtTwoSidedMod6OmitR3
      (twoSidedLabelledCollatzRules 6 (by decide) all11OmitR3List)
    (countStrictMat3DRules 42 (rank2BlockNilpMat3DC39 2 1 1 1 1) c39 = 37 ∧
     countStrictMat3DRules 84 (rank2BlockNilpMat3DC78 2 1 1 1 1) c78 = 74 ∧
     rank2BlockNilpMat3DC39 2 1 1 1 1 ⟨33, by decide⟩ ⟨1, by decide⟩ ⟨2, by decide⟩ = 1 ∧
     rank2BlockNilpMat3DC39 2 1 1 1 1 ⟨33, by decide⟩ ⟨1, by decide⟩ ⟨0, by decide⟩ = 1 ∧
     rank2BlockNilpMat3DC39 2 1 1 1 1 ⟨28, by decide⟩ ⟨2, by decide⟩ ⟨0, by decide⟩ = 1 ∧
     farkas3DVecLhsN 42 id farkasMu0CoupledC39 (fun _ => 0) (fun _ => 0) 2 1 1 1 1
       (basisVec3D 42 ⟨22, by decide⟩ ⟨1, by decide⟩) c39 -
       farkas3DVecRhsN 42 id farkasMu0CoupledC39 (fun _ => 0) (fun _ => 0) 2 1 1 1 1
         (basisVec3D 42 ⟨22, by decide⟩ ⟨1, by decide⟩) c39 = 10 ∧
     farkas3DVecLhsN 42 id farkasMu0CoupledC39 farkasMu1BiBTRC39 (fun _ => 0) 2 1 1 1 1
       (basisVec3D 42 ⟨22, by decide⟩ ⟨1, by decide⟩) c39 -
       farkas3DVecRhsN 42 id farkasMu0CoupledC39 farkasMu1BiBTRC39 (fun _ => 0) 2 1 1 1 1
         (basisVec3D 42 ⟨22, by decide⟩ ⟨1, by decide⟩) c39 = 10 ∧
     farkas3DVecLhsN 42 id farkasMu0CoupledC39 (fun _ => 0) farkasMu1BiBTRC39 2 1 1 1 1
       (basisVec3D 42 ⟨22, by decide⟩ ⟨1, by decide⟩) c39 -
       farkas3DVecRhsN 42 id farkasMu0CoupledC39 (fun _ => 0) farkasMu1BiBTRC39 2 1 1 1 1
         (basisVec3D 42 ⟨22, by decide⟩ ⟨1, by decide⟩) c39 = 10) ∧
    (∀ (k alpha beta gamma delta : Nat), k ≥ 2 -> alpha ≥ 1 -> beta ≥ 1 -> gamma ≥ 1 -> delta ≥ 1 ->
      (∀ r ∈ c39, ∀ i j : Fin 3,
        evalFinWordMat 42 3 (rank2BlockNilpMat3DC39 k alpha beta gamma delta) r.1 i j ≥
          evalFinWordMat 42 3 (rank2BlockNilpMat3DC39 k alpha beta gamma delta) r.2 i j) ∧
      (∀ v : Fin 42 -> Fin 3 -> Nat,
        (∀ r ∈ c39, ∀ i : Fin 3,
          evalFinWordVec 42 3 (rank2BlockNilpMat3DC39 k alpha beta gamma delta) v r.1 i ≥
            evalFinWordVec 42 3 (rank2BlockNilpMat3DC39 k alpha beta gamma delta) v r.2 i) ->
        ∀ r ∈ c39,
          evalFinWordVec 42 3 (rank2BlockNilpMat3DC39 k alpha beta gamma delta) v r.1 ⟨0, by decide⟩ =
            evalFinWordVec 42 3 (rank2BlockNilpMat3DC39 k alpha beta gamma delta) v r.2 ⟨0, by decide⟩)) ∧
    (∀ (k alpha beta gamma delta : Nat), k ≥ 2 -> alpha ≥ 1 -> beta ≥ 1 -> gamma ≥ 1 -> delta ≥ 1 ->
      (∀ r ∈ c78, ∀ i j : Fin 3,
        evalFinWordMat 84 3 (rank2BlockNilpMat3DC78 k alpha beta gamma delta) r.1 i j ≥
          evalFinWordMat 84 3 (rank2BlockNilpMat3DC78 k alpha beta gamma delta) r.2 i j) ∧
      (∀ v : Fin 84 -> Fin 3 -> Nat,
        (∀ r ∈ c78, ∀ i : Fin 3,
          evalFinWordVec 84 3 (rank2BlockNilpMat3DC78 k alpha beta gamma delta) v r.1 i ≥
            evalFinWordVec 84 3 (rank2BlockNilpMat3DC78 k alpha beta gamma delta) v r.2 i) ->
        ∀ r ∈ c78,
          evalFinWordVec 84 3 (rank2BlockNilpMat3DC78 k alpha beta gamma delta) v r.1 ⟨0, by decide⟩ =
            evalFinWordVec 84 3 (rank2BlockNilpMat3DC78 k alpha beta gamma delta) v r.2 ⟨0, by decide⟩)) := by
  dsimp only
  rw [c39_eq_fastRules_w18, c78_eq_fastRules_w18]
  rcases block_nilp_3d_shape_and_witness_certs_w18 with
    ⟨_, _, hsh39, hsh78, hst37, hst74, hexc0, hexc1, hexc2⟩
  rw [farkas3DFastPairW18_eq] at hexc0 hexc1 hexc2
  refine ⟨⟨hst37, hst74, rfl, rfl, rfl, hexc0, hexc1, hexc2⟩, ?_, ?_⟩
  · intro k alpha beta gamma delta _ _ _ _ _
    refine ⟨(weak_mat_orientation_5param_3d_cones_w18 k alpha beta gamma delta).1, ?_⟩
    intro v hv_weak
    apply bn3d_farkas_zero_strict_proj_w18 42 id farkasMu0CoupledC39 farkasMu1BlockNilp3DC39 farkasMu1BiBTRC39
      c39FastRulesW18 hsh39 _ k alpha beta gamma delta v hv_weak
    rcases bn3d_c39_all_packed with ⟨hp39_0, hp39_1, hp39_2⟩
    intro j0 s0
    rcases (by have := j0.isLt; omega : j0.val = 0 ∨ j0.val = 1 ∨ j0.val = 2) with hj | hj | hj
    · rw [show j0 = fin3Z0W18 from Fin.ext hj]
      exact packed_range_unpack_3d_w18 42 id _ _ _ fin3Z0W18 c39FastRulesW18 c39Packed3DW18
        c39Packed3DW18_eq 0 42 hp39_0 s0.val s0.isLt (Nat.zero_le _) s0.isLt
    · rw [show j0 = fin3Z1W18 from Fin.ext hj]
      exact packed_range_unpack_3d_w18 42 id _ _ _ fin3Z1W18 c39FastRulesW18 c39Packed3DW18
        c39Packed3DW18_eq 0 42 hp39_1 s0.val s0.isLt (Nat.zero_le _) s0.isLt
    · rw [show j0 = fin3Z2W18 from Fin.ext hj]
      exact packed_range_unpack_3d_w18 42 id _ _ _ fin3Z2W18 c39FastRulesW18 c39Packed3DW18
        c39Packed3DW18_eq 0 42 hp39_2 s0.val s0.isLt (Nat.zero_le _) s0.isLt
  · intro k alpha beta gamma delta _ _ _ _ _
    refine ⟨(weak_mat_orientation_5param_3d_cones_w18 k alpha beta gamma delta).2, ?_⟩
    intro v hv_weak
    apply bn3d_farkas_zero_strict_proj_w18 84 projSym84To42 farkasMu0CoupledC78 farkasMu1BlockNilp3DC78 farkasMu1BiBTRC78
      c78FastRulesW18 hsh78 _ k alpha beta gamma delta v hv_weak
    intro j0 s0
    rcases (by have := j0.isLt; omega : j0.val = 0 ∨ j0.val = 1 ∨ j0.val = 2) with hj | hj | hj
    · rw [show j0 = fin3Z0W18 from Fin.ext hj]
      exact packed_range_unpack_3d_w18 84 projSym84To42 _ _ _ fin3Z0W18 c78FastRulesW18 c78Packed3DW18
        c78Packed3DW18_eq 0 84 bn3d_c78_j0_packed s0.val s0.isLt (Nat.zero_le _) s0.isLt
    · rw [show j0 = fin3Z1W18 from Fin.ext hj]
      exact packed_range_unpack_3d_w18 84 projSym84To42 _ _ _ fin3Z1W18 c78FastRulesW18 c78Packed3DW18
        c78Packed3DW18_eq 0 84 bn3d_c78_j1_packed s0.val s0.isLt (Nat.zero_le _) s0.isLt
    · rw [show j0 = fin3Z2W18 from Fin.ext hj]
      exact packed_range_unpack_3d_w18 84 projSym84To42 _ _ _ fin3Z2W18 c78FastRulesW18 c78Packed3DW18
        c78Packed3DW18_eq 0 84 bn3d_c78_j2_packed s0.val s0.isLt (Nat.zero_le _) s0.isLt

-- ----------------------------------------------------------------------------
-- SECTION 2: Front B (Branches P3.2–P3.4) — General-`u` Rectangular Coprime
--            Biconditional & Infinite Odd-`u` Primitive-Row `Nat.lcm` Law,
--            Rank-3 Order-4 `12 × 12` `(T = 4, U = 3)` Global `u = 2..5`
--            Non-Vanishing & `∀ u ≥ 1` `2`-Adic Zero-Horizon, & Universal
--            Symbolic All-`m` `(m - 1)`-Pivot Brox + `m = 7` Eliminations (`W18_H2`)
-- ============================================================================

-- ----------------------------------------------------------------------------
-- Section 2A: General-`u` (`∀ u ≥ 1`) Rectangular `(U * T) × (U * T)` Unreduced
--             `Nat.Coprime` Biconditional, Bounded Overlap, & Infinite Odd-`u`
--             Exact Primitive-Row `Nat.lcm` Law (`W18_H2`, Branch P3.2)
-- ----------------------------------------------------------------------------

/-- Primitive row Vandermonde factor `((2^(W * u) - 1) / (2^u - 1))^(T * (U - T))` after factoring
    out the universal base overlap `(2^u - 1)^(T * (U - T))` across rectangular `(U * T) × (U * T)` grids. -/
def rectPrimitiveRowFactor (U T W u : Nat) : Nat :=
  ((2 ^ (W * u) - 1) / (2 ^ u - 1)) ^ (T * (U - T))

private theorem pow_dvd_of_dvd_w18 (a b k : Nat) (h : a ∣ b) : a ^ k ∣ b ^ k := by
  induction k with
  | zero => exact ⟨1, by simp⟩
  | succ k' ih =>
    rcases ih with ⟨q1, hq1⟩
    rcases h with ⟨q2, hq2⟩
    rw [Nat.pow_succ, Nat.pow_succ, hq1, hq2]
    exact ⟨q1 * q2, by ac_rfl⟩

private theorem geom_sum_pow_sub1_w18 (P : Nat) (hP : P ≥ 2) :
    ∀ W : Nat,
      (P - 1) ∣ (P ^ W - 1) ∧
      ((P ^ W - 1) / (P - 1)) % (P - 1) = W % (P - 1) ∧
      (W ≥ 1 -> P % 2 = 0 -> ((P ^ W - 1) / (P - 1)) % 2 = 1) := by
  have hp_pos : P - 1 ≥ 1 := by omega
  intro W; induction W with
  | zero =>
    refine ⟨⟨0, by simp⟩, ?_, fun hw _ => by omega⟩
    rw [Nat.pow_zero, show 1 - 1 = 0 from rfl, Nat.zero_div]
  | succ k ih =>
    rcases ih with ⟨⟨qk, hqk⟩, hmod_k, hodd_k⟩
    have hdiv_k : (P ^ k - 1) / (P - 1) = qk := by
      rw [hqk, Nat.mul_comm (P - 1) qk, Nat.mul_div_cancel qk hp_pos]
    have hnext_eq : P ^ (k + 1) - 1 = (P - 1) * (P * qk + 1) := by
      have hp_k_pos : P ^ k ≥ 1 := nat_pow_pos_of_pos P (by omega) k
      have h1 : P ^ (k + 1) - 1 = P * (P ^ k - 1) + (P - 1) := by
        rw [Nat.pow_succ P k, Nat.mul_comm (P ^ k) P, Nat.mul_sub_left_distrib, Nat.mul_one]
        have hle_p : P ≤ P * P ^ k := Nat.le_mul_of_pos_right P hp_k_pos
        omega
      rw [h1, hqk, Nat.mul_add (P - 1), Nat.mul_one]
      have : P * ((P - 1) * qk) = (P - 1) * (P * qk) := by ac_rfl
      rw [this]
    have hdiv_next : (P ^ (k + 1) - 1) / (P - 1) = P * qk + 1 := by
      rw [hnext_eq, Nat.mul_comm (P - 1), Nat.mul_div_cancel _ hp_pos]
    refine ⟨⟨P * qk + 1, hnext_eq⟩, ?_, ?_⟩
    · rw [hdiv_next]
      rw [hdiv_k] at hmod_k
      have hP_decomp : P * qk + 1 = (P - 1) * qk + (qk + 1) := by
        rw [Nat.sub_mul, Nat.one_mul]
        have hle_qk : qk ≤ P * qk := Nat.le_mul_of_pos_left qk (by omega)
        omega
      rw [hP_decomp, Nat.add_comm ((P - 1) * qk) (qk + 1), Nat.add_mul_mod_self_left,
          Nat.add_mod qk 1 (P - 1), hmod_k, ← Nat.add_mod]
    · intro _ hP_ev
      rw [hdiv_next]
      have : (P * qk) % 2 = 0 := by rw [Nat.mul_mod, hP_ev, Nat.zero_mul, Nat.zero_mod]
      omega

private theorem gcd_pow_sub1_of_coprime_w18 (P : Nat) (hP : P ≥ 2) :
    ∀ (fuel a b : Nat), a ≥ 1 -> b ≥ 1 -> a + b ≤ fuel -> Nat.Coprime a b ->
      Nat.gcd (P ^ a - 1) (P ^ b - 1) = P - 1
  | 0, a, _, ha, _, hle, _ => by omega
  | fuel + 1, a, b, ha, hb, hle, hcop => by
    by_cases hab : a = b
    · subst hab
      have ha1 : a = 1 := by simpa [Nat.coprime_iff_gcd_eq_one, Nat.gcd_self] using hcop
      subst ha1; simp [Nat.gcd_self]
    · by_cases hlt : a < b
      · let c := b - a
        have hb_eq : b = a + c := by omega
        have hc_pos : c ≥ 1 := by omega
        have hcop_ac : Nat.Coprime a c := by
          rw [Nat.coprime_iff_gcd_eq_one] at hcop ⊢
          have hg_a : Nat.gcd a c ∣ a := Nat.gcd_dvd_left a c
          have hg_b : Nat.gcd a c ∣ b := by rw [hb_eq]; exact Nat.dvd_add hg_a (Nat.gcd_dvd_right a c)
          exact Nat.eq_one_of_dvd_one (hcop ▸ Nat.dvd_gcd hg_a hg_b)
        have ih := gcd_pow_sub1_of_coprime_w18 P hP fuel a c ha hc_pos (by omega) hcop_ac
        have hdecomp : P ^ b - 1 = P ^ c * (P ^ a - 1) + (P ^ c - 1) := by
          rw [hb_eq, Nat.pow_add P a c, Nat.mul_comm (P ^ a) (P ^ c),
              Nat.mul_sub_left_distrib, Nat.mul_one]
          have hp_a : P ^ a ≥ 1 := nat_pow_pos_of_pos P (by omega) a
          have hp_c : P ^ c ≥ 1 := nat_pow_pos_of_pos P (by omega) c
          have hle_c : P ^ c ≤ P ^ c * P ^ a := Nat.le_mul_of_pos_right _ hp_a
          omega
        let g1 := Nat.gcd (P ^ a - 1) (P ^ b - 1)
        let g2 := Nat.gcd (P ^ a - 1) (P ^ c - 1)
        have hd12 : g1 ∣ g2 := by
          refine Nat.dvd_gcd (Nat.gcd_dvd_left _ _) ?_
          rcases Nat.gcd_dvd_left (P ^ a - 1) (P ^ b - 1) with ⟨qa, hqa⟩
          rcases Nat.gcd_dvd_right (P ^ a - 1) (P ^ b - 1) with ⟨qb, hqb⟩
          refine ⟨qb - P ^ c * qa, ?_⟩
          have h1 : g1 * qb = P ^ c * (g1 * qa) + (P ^ c - 1) := by
            dsimp [g1] at *; rw [← hqa, ← hqb]; exact hdecomp
          have h2 : g1 * (P ^ c * qa) = P ^ c * (g1 * qa) := by ac_rfl
          rw [Nat.mul_sub_left_distrib, h2]; omega
        have hd21 : g2 ∣ g1 := by
          refine Nat.dvd_gcd (Nat.gcd_dvd_left _ _) ?_
          rw [hdecomp]
          rcases (Nat.gcd_dvd_left (P ^ a - 1) (P ^ c - 1) : g2 ∣ P ^ a - 1) with ⟨qa2, hqa2⟩
          exact Nat.dvd_add ⟨P ^ c * qa2, by rw [hqa2]; dsimp [g2]; ac_rfl⟩ (Nat.gcd_dvd_right _ _)
        have hg1_pos : g1 ≥ 1 := Nat.gcd_pos_of_pos_left _ (by
          have hp1 : P ^ 1 ≤ P ^ a := nat_pow_mono_exp_pos P 1 a (by omega) ha
          rw [Nat.pow_one] at hp1; omega)
        have hg2_pos : g2 ≥ 1 := by dsimp [g2]; rw [ih]; omega
        have heq_g : g1 = g2 := Nat.dvd_antisymm hd12 hd21
        exact heq_g.trans ih
      · have hgt : b < a := by omega
        rw [Nat.gcd_comm]
        exact gcd_pow_sub1_of_coprime_w18 P hP (fuel + 1) b a hb ha (by omega) hcop.symm

private theorem gcd_mul_left_dvd_w18 (a b c : Nat) :
    Nat.gcd (a * b) c ∣ Nat.gcd a c * Nat.gcd b c := by
  let g := Nat.gcd (a * b) c
  by_cases hc0 : c = 0
  · subst hc0; simp
  · have hg_pos : g ≥ 1 := Nat.gcd_pos_of_pos_right _ (Nat.pos_of_ne_zero hc0)
    rcases (Nat.gcd_dvd_left (a * b) c : g ∣ a * b) with ⟨qab, hqab⟩
    let ga := Nat.gcd g a
    have hga_pos : ga ≥ 1 := Nat.gcd_pos_of_pos_left a hg_pos
    rcases (Nat.gcd_dvd_left g a : ga ∣ g) with ⟨g', hg'⟩
    rcases (Nat.gcd_dvd_right g a : ga ∣ a) with ⟨a', ha'⟩
    have hga_dvd_gac : ga ∣ Nat.gcd a c :=
      Nat.dvd_gcd (Nat.gcd_dvd_right g a) (Nat.dvd_trans (Nat.gcd_dvd_left g a) (Nat.gcd_dvd_right (a * b) c))
    have hcop_g'_a' : Nat.Coprime g' a' := by
      rw [Nat.coprime_iff_gcd_eq_one]
      let d := Nat.gcd g' a'
      have hd_g : ga * d ∣ g := by
        rcases (Nat.gcd_dvd_left g' a' : d ∣ g') with ⟨u1, hu1⟩
        exact ⟨u1, by rw [hg', hu1, Nat.mul_assoc]⟩
      have hd_a : ga * d ∣ a := by
        rcases (Nat.gcd_dvd_right g' a' : d ∣ a') with ⟨u2, hu2⟩
        exact ⟨u2, by rw [ha', hu2, Nat.mul_assoc]⟩
      have hd_ga : ga * d ∣ ga := Nat.dvd_gcd hd_g hd_a
      have hle : ga * d ≤ ga * 1 := by rw [Nat.mul_one]; exact Nat.le_of_dvd hga_pos hd_ga
      have hd_pos : d ≥ 1 := Nat.gcd_pos_of_pos_left a' (by
        cases g' with | zero => rw [Nat.mul_zero] at hg'; omega | succ _ => omega)
      have hd_le1 : d ≤ 1 := Nat.le_of_mul_le_mul_left hle hga_pos
      omega
    have hg'_dvd_b : g' ∣ b := by
      have hm : ga * (g' * qab) = ga * (a' * b) := by
        calc ga * (g' * qab) = (ga * g') * qab := (Nat.mul_assoc _ _ _).symm
          _ = g * qab := by rw [← hg']
          _ = a * b := hqab.symm
          _ = (ga * a') * b := by rw [← ha']
          _ = ga * (a' * b) := Nat.mul_assoc _ _ _
      have heq : a' * b = g' * qab := (Nat.eq_of_mul_eq_mul_left hga_pos hm).symm
      exact hcop_g'_a'.dvd_of_dvd_mul_left ⟨qab, heq⟩
    have hg'_dvd_gbc : g' ∣ Nat.gcd b c :=
      Nat.dvd_gcd hg'_dvd_b (Nat.dvd_trans ⟨ga, by change g = g' * ga; rw [hg', Nat.mul_comm]⟩ (Nat.gcd_dvd_right (a * b) c))
    rcases hga_dvd_gac with ⟨u1, hu1⟩
    rcases hg'_dvd_gbc with ⟨u2, hu2⟩
    refine ⟨u1 * u2, ?_⟩
    rw [hu1, hu2]
    change ga * u1 * (g' * u2) = g * (u1 * u2)
    rw [hg']
    dsimp only [ga]
    ac_rfl

private theorem gcd_pow_left_dvd_w18 (a c : Nat) :
    ∀ k : Nat, Nat.gcd (a ^ k) c ∣ (Nat.gcd a c) ^ k
  | 0 => ⟨1, by simp⟩
  | k + 1 => by
    rw [Nat.pow_succ, Nat.pow_succ]
    exact Nat.dvd_trans (gcd_mul_left_dvd_w18 (a ^ k) a c)
      (Nat.mul_dvd_mul (gcd_pow_left_dvd_w18 a c k) (Nat.dvd_refl _))

private def fastM0_12_583FnW18 (i j : Fin 12) : Int :=
  let r := i.val % 4; let s := i.val / 4
  let t := j.val % 3; let kc := (j.val / 3) * 3
  let x := r * 5 + s * 8
  let binv := match t with | 0 => 1 | 1 => x | 2 => (x * (x - 1)) / 2 | _ => laurentInterpBinom x t
  ((binv * 2 ^ (x * kc) : Nat) : Int)

private def intAt2DW18 (rows : List (List Int)) (r c : Nat) : Int :=
  match rows.drop r with
  | row :: _ =>
    match row.drop c with
    | x :: _ => x
    | [] => 0
  | [] => 0

private def intDiagProdPrefixW18 (N : Nat) (U : Fin N -> Fin N -> Int) : Nat -> Int
  | 0 => 1
  | k + 1 =>
    if h : k < N then intDiagProdPrefixW18 N U k * U ⟨k, h⟩ ⟨k, h⟩
    else intDiagProdPrefixW18 N U k

private def allFin12LoopW18 (p : Fin 12 -> Bool) : Nat -> Bool
  | 0 => true
  | k + 1 => (if h : k < 12 then p ⟨k, h⟩ else true) && allFin12LoopW18 p k

private theorem allFin12LoopW18_spec (p : Fin 12 -> Bool) (h : allFin12LoopW18 p 12 = true) :
    ∀ x : Fin 12, p x = true := by
  have hst : ∀ k : Nat, k ≤ 12 -> allFin12LoopW18 p k = true -> ∀ x : Fin 12, x.val < k -> p x = true := by
    intro k hk; induction k with
    | zero => intros _ _ hlt; omega
    | succ k' ih =>
      intro ha x hx_lt
      unfold allFin12LoopW18 at ha
      rcases bool_and_split ha with ⟨hcur, hprev⟩
      by_cases hxk : x.val = k'
      · have hk_lt : k' < 12 := hk
        simp only [hk_lt, dite_true] at hcur
        rwa [show x = ⟨k', hk_lt⟩ from Fin.ext hxk]
      · exact ih (Nat.le_of_lt hk) hprev x (by omega)
  intro x; exact hst 12 (Nat.le_refl _) h x x.isLt

private theorem intDet_mul_upper_tri_w18 (N : Nat) (A U : Fin N -> Fin N -> Int)
    (hupper : ∀ r c : Fin N, c.val < r.val -> U r c = 0) :
    intDet N (fun i j => intSumPrefix N (fun r => A i r * U r j) N) =
      intDiagProdPrefixW18 N U N * intDet N A := by
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
      intDet N (M_stage 0) = intDiagProdPrefixW18 N U k * intDet N (M_stage k) := by
    intro k hk; induction k with
    | zero => simp [intDiagProdPrefixW18]
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
      simp only [intDiagProdPrefixW18, hk'_lt, dite_true]
      exact (Int.mul_assoc (intDiagProdPrefixW18 N U k') (U jk jk) _).symm
  rw [h0_eq, hstep N (Nat.le_refl N), hN_eq]

private theorem intDet_lower_tri_w18 :
    ∀ (N : Nat) (L_mat : Fin N -> Fin N -> Int),
      (∀ r c : Fin N, r.val < c.val -> L_mat r c = 0) ->
      intDet N L_mat = intDiagProdPrefixW18 N L_mat N
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
    rw [intDet_lower_tri_w18 N (intSubMat L_mat z0) hsub_low]
    have hprod_shift : ∀ k : Nat, k ≤ N ->
        L_mat z0 z0 * intDiagProdPrefixW18 N (intSubMat L_mat z0) k =
          intDiagProdPrefixW18 (N + 1) L_mat (k + 1) := by
      intro k hk; induction k with
      | zero =>
        simp only [intDiagProdPrefixW18, Nat.zero_lt_succ, dite_true, Int.one_mul, Int.mul_one]
        rfl
      | succ k' ih =>
        have hk'_N : k' < N := hk
        have hk1_N1 : k' + 1 < N + 1 := Nat.succ_lt_succ hk
        simp only [intDiagProdPrefixW18, hk'_N, hk1_N1, dite_true, ← Int.mul_assoc, ih (Nat.le_of_lt hk)]
        simp only [intSubMat, skipFinIdx, z0, Nat.not_lt_zero, ite_false]
    exact hprod_shift N (Nat.le_refl N)

private def checkULDet12BoolW18 (A : Fin 12 -> Fin 12 -> Int) (uTbl : List (List Int)) (expDet : Int) : Bool :=
  let U (i j : Fin 12) : Int := intAt2DW18 uTbl i.val j.val
  let prodMat (i j : Fin 12) : Int := intSumPrefix 12 (fun r => A i r * U r j) 12
  let upperOk := allFin12LoopW18 (fun r =>
    allFin12LoopW18 (fun c => if c.val < r.val then U r c == 0 else true) 12) 12
  let lowerOk := allFin12LoopW18 (fun r =>
    allFin12LoopW18 (fun c => if r.val < c.val then prodMat r c == 0 else true) 12) 12
  let uDiag := intDiagProdPrefixW18 12 U 12
  let lDiag := intDiagProdPrefixW18 12 prodMat 12
  upperOk && lowerOk && (uDiag != 0) && (lDiag == uDiag * expDet)

private theorem checkULDet12BoolW18_sound (A : Fin 12 -> Fin 12 -> Int)
    (uTbl : List (List Int)) (expDet : Int)
    (h : checkULDet12BoolW18 A uTbl expDet = true) :
    intDet 12 A = expDet := by
  let U (i j : Fin 12) : Int := intAt2DW18 uTbl i.val j.val
  let prodMat (i j : Fin 12) : Int := intSumPrefix 12 (fun r => A i r * U r j) 12
  unfold checkULDet12BoolW18 at h
  rcases bool_and_split h with ⟨hb1, hl_eq_b⟩
  rcases bool_and_split hb1 with ⟨hb2, hu_nz_b⟩
  rcases bool_and_split hb2 with ⟨hup_b, hlo_b⟩
  have hupper : ∀ r c : Fin 12, c.val < r.val -> U r c = 0 := by
    intro r c hlt
    have hc := allFin12LoopW18_spec _ (allFin12LoopW18_spec _ hup_b r) c
    dsimp only at hc; rw [ite_true_of_w10 hlt] at hc
    exact beq_iff_eq.mp hc
  have hlower : ∀ r c : Fin 12, r.val < c.val -> prodMat r c = 0 := by
    intro r c hlt
    have hc := allFin12LoopW18_spec _ (allFin12LoopW18_spec _ hlo_b r) c
    dsimp only at hc; rw [ite_true_of_w10 hlt] at hc
    exact beq_iff_eq.mp hc
  have hu_nz : intDiagProdPrefixW18 12 U 12 ≠ 0 := bne_iff_ne.mp hu_nz_b
  have hl_eq : intDiagProdPrefixW18 12 prodMat 12 = intDiagProdPrefixW18 12 U 12 * expDet :=
    beq_iff_eq.mp hl_eq_b
  have hmul_det := intDet_mul_upper_tri_w18 12 A U hupper
  have hlow_det := intDet_lower_tri_w18 12 prodMat hlower
  dsimp only [prodMat] at hlow_det
  rw [hlow_det, hl_eq] at hmul_det
  exact (Int.eq_of_mul_eq_mul_left hu_nz hmul_det).symm

private def uM0_12_583TblW18 : List (List Int) :=
  [[1, 0, 0, -25, 2457600, -12708741120000, 2182440195366471771053096960, -33788970355541179146230108035152263249920, 27661999964950763042284700914512035840, -4146884017373005280302104443313932286574331563728470604703268939839727206400, 4694826831169315600900338839017345803319860830945581257483766248864159829276806433709012360888320, -43972099436659028909686056067777653074286097936110300410778841980292356893202055979970855068831913023954916321771797872640],
   [0, 1, -2, 2147188743, -70353712185344, 3376257220059594752, -477117977975556045428438549397504, 7353836596041842726815764789860064635658436608, -6003129909381896314773450765636554585014272, 887480631054858220021604653650059940478536593100889842784500765741044644693671936, -1004637139588509843866728818764242292093910488697438610130091962550113890744920017795459518662866632704, 9408923118302402063847217533105025364122684645088635742832753807602875885889826764105614047295032798920263903168459960624349184],
   [0, 0, 1, -1073676289, 35182224637952, -1702139387598340096, 240778364982427787228817741840384, -3711218812120235935157969765275243517268983808, 3029614152715306120257455662019023976005632, -447922397131934744493309649732081031123318553390836680711437502012301788468740096, 507053043819030938720492964190470127610090166506267063649247224214122734350682472289123930636931825664, -4748803925226777585865564574326840094654894749328755498588214956629563289350734775285451227014185145486088978478807088852107264],
   [0, 0, 0, 25, -2457600, 12708741120000, -2182440195366476525947579500, 33788970355541627246048342303409399398400, -27661999964951827627886284832117882880, 4146884017373669607793286053660563472669273012456405468558821862223307079680, -4694826831170074314946264662795664100643796836378738050907473170750521054794645407261955142451200, 43972099436666170935502874174096115644089364159503547334794265153823568823643096430968038214248476055098172526643621396480],
   [0, 0, 0, 0, 163835, -2022229254962, 367683548929166668117072986, -5699154384336888951094639989909604564992, 4669187073822235148151943162239123456, -702475272351015529292766503738503390522813191823093195755885087085981335552, 795317946998681873084061173937546079888065110590066613475548280475283127283054075919978654072832, -7449125015097308195625691186325397073785688486039707323207287982450527826876245788689484359908921827167327220367462760448],
   [0, 0, 0, 0, 0, 167854298521, -33334395527906813947804911, 517551892183025090936337868386914598912, -424471552165657740741085742021738496, 64188892909384630661896028470570022150103839029855105849800397505169457152, -72675300038220234336891252486095053822380413487601935261421539297256442558413331462131707543552, 680708388795932216400913259675529501200087720255283899598918961442417842472434456907504334797314366487167083174332203008],
   [0, 0, 0, 0, 0, 0, 4754894482540, -448099818234268257136148480, 1064585601583917605847040, -664327491181610346631310244699532188816262400372778355429825780, 758714045925823778360948153529110144281938502044244144148376770547318228688460840960, -7142025816818106320519415439133385722419435166204910608664607364195394717937968599672320494476929590372597760],
   [0, 0, 0, 0, 0, 0, 0, 24862393214510033636998845, -102742354572194193747786, 75001176884104878563094795127861361827676639254207687279662966, -85735367120172453149998072452267262177236232330330159676669725783800001320110358528, 807485740174796784684672821030128764534289568286564978623494571319198741002052561715522469192223296015302656],
   [0, 0, 0, 0, 0, 0, 0, 0, 5132366009635571402661, -4482152831509796247375281339083868225995187874943100581788681, 5129246978508128147115245340740595906626320829887397416992672735959966336035258368, -48340038825393913547138055671999456841512552637908115122424301486313431701082233406057170289294129156325376],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 124149758083460881398544819855971849952500, -42650829593104711125145078337322257787151252708344675745679278080, 2056845635867162329172511150781737077452676923154943720754823183109289351220724718549073920],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1848160038702286966417348527948669463615488269998347906206319495, -164608749206239766620985835072881033926069213035207838213661673193348948831917586536976782],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6839963048618215292586368510771921259483152084793168880984002957616914865868829596776647]]

private def expM0_12_583ValW18 : Int :=
  105384055554157636593660435336057604252111750766311822056532150282074727889705934674962091407243611738324977435495543812296340249746701673672549111329568986215674208424291432041483758933088344240907454936857492520405271784065694205442643850814171682165296967015158165193869615929455661993311017095546445301904132606240766984969638171012694238788846373306368

set_option exponentiation.threshold 2048 in
private theorem m0_12_583_ul_cert_w18 :
    checkULDet12BoolW18 fastM0_12_583FnW18 uM0_12_583TblW18 expM0_12_583ValW18 = true ∧
    expM0_12_583ValW18 % ((confluentFactorAllU 4 3 3 * (2 ^ (5 * 3) - 1) ^ (3 * (4 - 3)) : Nat) : Int) ≠ 0 ∧
    expM0_12_583ValW18 % ((confluentFactorAllU 4 3 3 * rectPrimitiveRowFactor 4 3 5 3 : Nat) : Int) = 0 := by
  decide

/--
  Theorem W18.2a (`laurent_rect_general_u_coprime_iff_and_primitive_lcm_law`,
  `zero custom axioms`):
  General-`u` (`∀ u ≥ 1`) Rectangular `(U * T) × (U * T)` Overlap & Coprime-`u` Primitive-Row
  `Nat.lcm` Product Law:
  1. Universal base-overlap factorization `rowFac = (2^u - 1)^(T*(U - T)) * rectPrimitiveRowFactor U T W u`
     with `(2^u - 1)^(T*(U - T)) ∣ Nat.gcd colFac rowFac` (`gcd ≥ 3^(T*(U - T)) > 1` for ALL `u ≥ 2`);
  2. Exact unreduced coprimality biconditional `Nat.Coprime colFac rowFac ↔ (u = 1 ∧ ∀ 1 ≤ d < U, Nat.Coprime W d)`;
  3. Bounded odd-overlap law `Nat.gcd colFac (rectPrimitiveRowFactor U T W u) ∣ (Nat.gcd (2^u - 1) W)^(triNumNat U * (T * T) * (T * (U - T)))`
     under `∀ 1 ≤ d < U, Nat.Coprime W d`;
  4. Exact `Nat.gcd colFac rowFac = (2^u - 1)^(T*(U - T))` AND `Nat.lcm colFac rowFac = colFac * rectPrimitiveRowFactor U T W u`
     whenever `Nat.Coprime (2^u - 1) W` — holding across **infinitely many odd `u = 2 * m + 1`**
     (e.g. for `W = 5` across ALL `m : Nat`!);
  5. `12 × 12` `(U = 4, T = 3, W = 5, K = 8, u = 3)` odd-`u` `gcd = 343` & unreduced failure vs
     exact `colFac * rectPrimitiveRowFactor 4 3 5 3` divisibility certificate (`Branch P3.2`, witness
     `LAURENT_12X12_T4U3_5_8_U5_FLIP_AND_RECT_ODD_U3_OVERLAP`, `W18_H2`).
-/
theorem laurent_rect_general_u_coprime_iff_and_primitive_lcm_law :
    (∀ (U T W u : Nat), T ≥ 1 -> U > T -> W ≥ 1 -> u ≥ 1 ->
      let colFac := confluentFactorAllU U T u
      let rowFac := (2 ^ (W * u) - 1) ^ (T * (U - T))
      let baseOv := (2 ^ u - 1) ^ (T * (U - T))
      let primRow := rectPrimitiveRowFactor U T W u
      rowFac = baseOv * primRow ∧
      baseOv ∣ colFac ∧
      baseOv ∣ Nat.gcd colFac rowFac ∧
      (u ≥ 2 -> Nat.gcd colFac rowFac ≥ 3 ^ (T * (U - T)) ∧ Nat.gcd colFac rowFac > 1) ∧
      (Nat.Coprime colFac rowFac ↔ (u = 1 ∧ ∀ d : Nat, 1 ≤ d -> d < U -> Nat.Coprime W d))) ∧
    (∀ (U T W u : Nat), T ≥ 1 -> U > T -> W ≥ 1 -> u ≥ 1 ->
      (∀ d : Nat, 1 ≤ d -> d < U -> Nat.Coprime W d) ->
      let colFac := confluentFactorAllU U T u
      let rowFac := (2 ^ (W * u) - 1) ^ (T * (U - T))
      let baseOv := (2 ^ u - 1) ^ (T * (U - T))
      let primRow := rectPrimitiveRowFactor U T W u
      Nat.gcd colFac ((2 ^ (W * u) - 1) / (2 ^ u - 1)) ∣
        (Nat.gcd (2 ^ u - 1) W) ^ (triNumNat U * (T * T)) ∧
      (Nat.Coprime (2 ^ u - 1) W ->
        Nat.Coprime colFac primRow ∧
        Nat.gcd colFac rowFac = baseOv ∧
        Nat.lcm colFac rowFac = colFac * primRow)) ∧
    (∀ m : Nat,
      let u := 2 * m + 1
      Nat.Coprime (2 ^ u - 1) 5 ∧
      ∀ (U T : Nat), T ≥ 1 -> U > T -> U ≤ 5 ->
        Nat.gcd (confluentFactorAllU U T u) ((2 ^ (5 * u) - 1) ^ (T * (U - T))) =
          (2 ^ u - 1) ^ (T * (U - T)) ∧
        Nat.lcm (confluentFactorAllU U T u) ((2 ^ (5 * u) - 1) ^ (T * (U - T))) =
          confluentFactorAllU U T u * rectPrimitiveRowFactor U T 5 u) ∧
    (let M0_12_583 : Fin 12 -> Fin 12 -> Int := fun i j =>
       (laurentZeroGapIntEntry 5 8 (laurentRectRows 4 3 i).1 (laurentRectRows 4 3 i).2
         (laurentColsAllU 4 3 3 j).1 (laurentColsAllU 4 3 3 j).2 : Int)
     Nat.gcd (confluentFactorAllU 4 3 3) ((2 ^ (5 * 3) - 1) ^ (3 * (4 - 3))) = 343 ∧
     ¬ (((confluentFactorAllU 4 3 3 * (2 ^ (5 * 3) - 1) ^ (3 * (4 - 3)) : Nat) : Int) ∣
       intDet 12 M0_12_583) ∧
     (((confluentFactorAllU 4 3 3 * rectPrimitiveRowFactor 4 3 5 3 : Nat) : Int) ∣
       intDet 12 M0_12_583)) := by
  -- Helper: `(2^u - 1)^m ∣ blockNodeDiffProd (2^u) m m`:
  have hbase_dvd_block : ∀ (u m : Nat), u ≥ 1 ->
      (2 ^ u - 1) ^ m ∣ blockNodeDiffProd (2 ^ u) m m := by
    intro u m hu
    let P := 2 ^ u
    have hP2 : P ≥ 2 := by simpa [P] using pow2_mono_nat hu
    have hst : ∀ k : Nat, k ≤ m -> (P - 1) ^ k ∣ blockNodeDiffProd P m k := by
      intro k hk; induction k with
      | zero => exact ⟨1, by simp [blockNodeDiffProd]⟩
      | succ k' ih =>
        simp only [blockNodeDiffProd, Nat.pow_succ]
        have hfac : P ^ m - P ^ k' = P ^ k' * (P ^ (m - k') - 1) := by
          conv => lhs; lhs; rw [show m = k' + (m - k') by omega, Nat.pow_add]
          rw [Nat.mul_sub_left_distrib, Nat.mul_one]
        rcases ih (Nat.le_of_lt hk) with ⟨q1, hq1⟩
        rcases (geom_sum_pow_sub1_w18 P hP2 (m - k')).1 with ⟨q2, hq2⟩
        rw [hq1, hfac, hq2]
        exact ⟨q1 * P ^ k' * q2, by ac_rfl⟩
    exact hst m (Nat.le_refl m)
  have hbase_dvd_conf : ∀ (U T u : Nat), u ≥ 1 ->
      (2 ^ u - 1) ^ (triNumNat U * (T * T)) ∣ confluentFactorAllU U T u := by
    intro U T u hu; unfold confluentFactorAllU
    induction U with
    | zero => simp [triNumNat, confluentFactorAllUAux]
    | succ m ih =>
      simp only [triNumNat, confluentFactorAllUAux, confluentBlockFactor]
      have hexp : (triNumNat m + m) * (T * T) = triNumNat m * (T * T) + m * (T * T) := Nat.add_mul _ _ _
      rw [hexp, Nat.pow_add]
      have hd_m := pow_dvd_of_dvd_w18 _ _ (T * T) (hbase_dvd_block u m hu)
      rw [pow_pow_eq_mul_w5 (2 ^ u - 1) m (T * T)] at hd_m
      rcases ih with ⟨q1, hq1⟩
      rcases hd_m with ⟨q2, hq2⟩
      rw [hq1, hq2]
      exact ⟨q1 * (2 ^ u) ^ (m * triNumNat T) * q2, by ac_rfl⟩
  -- Part 1:
  have hpart1 : ∀ (U T W u : Nat), T ≥ 1 -> U > T -> W ≥ 1 -> u ≥ 1 ->
      let colFac := confluentFactorAllU U T u
      let rowFac := (2 ^ (W * u) - 1) ^ (T * (U - T))
      let baseOv := (2 ^ u - 1) ^ (T * (U - T))
      let primRow := rectPrimitiveRowFactor U T W u
      rowFac = baseOv * primRow ∧
      baseOv ∣ colFac ∧
      baseOv ∣ Nat.gcd colFac rowFac ∧
      (u ≥ 2 -> Nat.gcd colFac rowFac ≥ 3 ^ (T * (U - T)) ∧ Nat.gcd colFac rowFac > 1) ∧
      (Nat.Coprime colFac rowFac ↔ (u = 1 ∧ ∀ d : Nat, 1 ≤ d -> d < U -> Nat.Coprime W d)) := by
    intro U T W u hT hUT hW hu; dsimp only
    let P := 2 ^ u
    have hP2 : P ≥ 2 := by simpa [P] using pow2_mono_nat hu
    have hWu_eq : 2 ^ (W * u) = P ^ W := by dsimp [P]; rw [Nat.mul_comm W u, pow_pow_eq_mul_w5 2 u W]
    rcases (geom_sum_pow_sub1_w18 P hP2 W).1 with ⟨qW, hqW⟩
    have hp_pos : P - 1 ≥ 1 := by omega
    have hq_div : (P ^ W - 1) / (P - 1) = qW := by
      rw [hqW, Nat.mul_comm (P - 1) qW, Nat.mul_div_cancel qW hp_pos]
    have hrf_eq : (2 ^ (W * u) - 1) ^ (T * (U - T)) =
        (2 ^ u - 1) ^ (T * (U - T)) * rectPrimitiveRowFactor U T W u := by
      unfold rectPrimitiveRowFactor
      rw [hWu_eq, hq_div, hqW, mul_pow_w18c (P - 1) qW (T * (U - T))]
    -- Bound `T * (U - T) ≤ triNumNat U * (T * T)`:
    have htri_ge : ∀ n : Nat, n ≥ 1 -> triNumNat n ≥ n - 1 := by
      intro n hn; cases n with
      | zero => omega
      | succ m => simp only [triNumNat, Nat.add_sub_cancel]; omega
    have hexp_le : T * (U - T) ≤ triNumNat U * (T * T) := by
      have h1 : U - T ≤ triNumNat U := Nat.le_trans (by omega : U - T ≤ U - 1) (htri_ge U (by omega))
      have h2 : T ≤ T * T := Nat.le_mul_of_pos_right T hT
      calc T * (U - T) = (U - T) * T := Nat.mul_comm _ _
        _ ≤ triNumNat U * (T * T) := Nat.mul_le_mul h1 h2
    have hbase_col : (2 ^ u - 1) ^ (T * (U - T)) ∣ confluentFactorAllU U T u := by
      have hd_pow : (2 ^ u - 1) ^ (T * (U - T)) ∣ (2 ^ u - 1) ^ (triNumNat U * (T * T)) := by
        conv => rhs; rw [show triNumNat U * (T * T) = T * (U - T) + (triNumNat U * (T * T) - T * (U - T)) by omega,
                          Nat.pow_add]
        exact ⟨_, rfl⟩
      exact Nat.dvd_trans hd_pow (hbase_dvd_conf U T u hu)
    have hbase_row : (2 ^ u - 1) ^ (T * (U - T)) ∣ (2 ^ (W * u) - 1) ^ (T * (U - T)) :=
      ⟨rectPrimitiveRowFactor U T W u, hrf_eq⟩
    have hbase_gcd : (2 ^ u - 1) ^ (T * (U - T)) ∣
        Nat.gcd (confluentFactorAllU U T u) ((2 ^ (W * u) - 1) ^ (T * (U - T))) :=
      Nat.dvd_gcd hbase_col hbase_row
    have hu2_gt : u ≥ 2 ->
        Nat.gcd (confluentFactorAllU U T u) ((2 ^ (W * u) - 1) ^ (T * (U - T))) ≥ 3 ^ (T * (U - T)) ∧
        Nat.gcd (confluentFactorAllU U T u) ((2 ^ (W * u) - 1) ^ (T * (U - T))) > 1 := by
      intro hu2
      have h2u_ge4 : 2 ^ u ≥ 4 := by simpa using pow2_mono_nat hu2
      have hbase_ge3 : (2 ^ u - 1) ^ (T * (U - T)) ≥ 3 ^ (T * (U - T)) :=
        pow_mono_base_w18c 3 (2 ^ u - 1) (by omega) _
      have hTUT_pos : T * (U - T) ≥ 1 := Nat.mul_pos hT (by omega)
      have h3_ge3 : 3 ^ (T * (U - T)) ≥ 3 := by
        simpa using nat_pow_mono_exp_pos 3 1 (T * (U - T)) (by decide) hTUT_pos
      have hrf_pos : (2 ^ (W * u) - 1) ^ (T * (U - T)) ≥ 1 := by
        have hp : 2 ^ (W * u) ≥ 2 := by simpa using pow2_mono_nat (Nat.mul_pos hW (by omega))
        exact nat_pow_pos_of_pos _ (by omega) _
      have hg_pos : Nat.gcd (confluentFactorAllU U T u) ((2 ^ (W * u) - 1) ^ (T * (U - T))) ≥ 1 :=
        Nat.gcd_pos_of_pos_right _ hrf_pos
      have hle_g := Nat.le_of_dvd hg_pos hbase_gcd
      exact ⟨by omega, by omega⟩
    refine ⟨hrf_eq, hbase_col, hbase_gcd, hu2_gt, ?_⟩
    constructor
    · intro hcop
      have hg_eq1 : Nat.gcd (confluentFactorAllU U T u) ((2 ^ (W * u) - 1) ^ (T * (U - T))) = 1 := hcop
      have hu_eq1 : u = 1 := by
        by_cases hu1 : u = 1
        · exact hu1
        · have hgt1 := (hu2_gt (by omega)).2
          omega
      subst hu_eq1
      refine ⟨rfl, ?_⟩
      intro d hd1 hdU
      rw [Nat.coprime_iff_gcd_eq_one]
      let g_wd := Nat.gcd W d
      have hg_wd_pos : g_wd ≥ 1 := Nat.gcd_pos_of_pos_left d hW
      -- Show `(2 ^ g_wd - 1)` divides BOTH `confluentFactorAllU U T 1` and `(2 ^ W - 1) ^ (T * (U - T))`:
      have h2g_dvd_W : (2 ^ g_wd - 1) ∣ (2 ^ W - 1) ^ (T * (U - T)) := by
        rcases Nat.gcd_dvd_left W d with ⟨qw, hqw⟩
        have h1 : (2 ^ g_wd - 1) ∣ ((2 ^ g_wd) ^ qw - 1) :=
          (geom_sum_pow_sub1_w18 (2 ^ g_wd) (by simpa using pow2_mono_nat hg_wd_pos) qw).1
        rw [pow_pow_eq_mul_w5 2 g_wd qw, ← hqw] at h1
        have hTUT_pos : T * (U - T) ≥ 1 := Nat.mul_pos hT (by omega)
        have hpow_d := pow_dvd_of_dvd_w18 _ _ (T * (U - T)) h1
        have h1_d : (2 ^ g_wd - 1) ∣ (2 ^ g_wd - 1) ^ (T * (U - T)) := by
          conv => rhs; rw [show T * (U - T) = 1 + (T * (U - T) - 1) by omega, Nat.pow_add, Nat.pow_one]
          exact ⟨_, rfl⟩
        exact Nat.dvd_trans h1_d hpow_d
      have h2d_dvd_blk : (2 ^ d - 1) ∣ blockNodeDiffProd 2 d d := by
        cases d with
        | zero => omega
        | succ d' =>
          have h1 : ∀ k : Nat, 1 ≤ k -> (2 ^ (d' + 1) - 1) ∣ blockNodeDiffProd 2 (d' + 1) k := by
            intro k hk; induction k with
            | zero => omega
            | succ k' ih =>
              cases k' with
              | zero =>
                simp only [blockNodeDiffProd, Nat.pow_zero, Nat.one_mul]
                exact Nat.dvd_refl _
              | succ q =>
                conv => rhs; unfold blockNodeDiffProd
                rcases ih (by omega) with ⟨c0, hc0⟩
                rw [hc0]; exact ⟨c0 * (2 ^ (d' + 1) - 2 ^ (q + 1)), by ac_rfl⟩
          exact h1 (d' + 1) (by omega)
      have h2d_dvd_conf : (2 ^ d - 1) ∣ confluentFactorAllU U T 1 := by
        unfold confluentFactorAllU
        have haux : ∀ m : Nat, d < m -> (2 ^ d - 1) ∣ confluentFactorAllUAux T 2 m := by
          intro m hm; induction m with
          | zero => omega
          | succ m' ihm =>
            simp only [confluentFactorAllUAux, confluentBlockFactor]
            by_cases hdm : d = m'
            · subst hdm
              have hTT_pos : T * T ≥ 1 := Nat.mul_pos hT hT
              have hd_tt : (2 ^ d - 1) ∣ (blockNodeDiffProd 2 d d) ^ (T * T) := by
                have hp := pow_dvd_of_dvd_w18 _ _ (T * T) h2d_dvd_blk
                have h1 : (2 ^ d - 1) ∣ (2 ^ d - 1) ^ (T * T) := by
                  conv => rhs; rw [show T * T = 1 + (T * T - 1) by omega, Nat.pow_add, Nat.pow_one]
                  exact ⟨_, rfl⟩
                exact Nat.dvd_trans h1 hp
              rcases hd_tt with ⟨q, hq⟩
              rw [hq]; exact ⟨confluentFactorAllUAux T 2 d * 2 ^ (d * triNumNat T) * q, by ac_rfl⟩
            · rcases ihm (by omega) with ⟨q, hq⟩
              rw [hq]; exact ⟨q * (2 ^ (m' * triNumNat T) * blockNodeDiffProd 2 m' m' ^ (T * T)), by ac_rfl⟩
        exact haux U hdU
      have h2g_dvd_d : (2 ^ g_wd - 1) ∣ (2 ^ d - 1) := by
        rcases Nat.gcd_dvd_right W d with ⟨qd, hqd⟩
        have h1 : (2 ^ g_wd - 1) ∣ ((2 ^ g_wd) ^ qd - 1) :=
          (geom_sum_pow_sub1_w18 (2 ^ g_wd) (by simpa using pow2_mono_nat hg_wd_pos) qd).1
        rwa [pow_pow_eq_mul_w5 2 g_wd qd, ← hqd] at h1
      have h2g_dvd_1 : (2 ^ g_wd - 1) ∣ 1 := by
        have hg_eq1' : Nat.gcd (confluentFactorAllU U T 1) ((2 ^ (W * 1) - 1) ^ (T * (U - T))) = 1 := hg_eq1
        rw [Nat.mul_one] at hg_eq1'
        conv => rhs; rw [← hg_eq1']
        exact Nat.dvd_gcd (Nat.dvd_trans h2g_dvd_d h2d_dvd_conf) h2g_dvd_W
      have h2g_eq1 : 2 ^ g_wd - 1 = 1 := Nat.eq_one_of_dvd_one h2g_dvd_1
      by_cases hg1 : g_wd = 1
      · exact hg1
      · have hge4 : 2 ^ g_wd ≥ 4 := by simpa using pow2_mono_nat (by omega : 2 ≤ g_wd)
        omega
    · rintro ⟨rfl, hcop_all⟩
      rw [Nat.mul_one]
      have hstep_cop : ∀ m : Nat, m ≤ U ->
          Nat.Coprime (confluentFactorAllUAux T 2 m) (2 ^ W - 1) := by
        intro m hm; induction m with
        | zero => exact Nat.coprime_one_left _
        | succ m' ihm =>
          simp only [confluentFactorAllUAux, confluentBlockFactor]
          have h2_cop : Nat.Coprime 2 (2 ^ W - 1) := by
            have hodd : (2 ^ W - 1) % 2 = 1 := by
              rw [show W = (W - 1) + 1 by omega, Nat.pow_succ]
              have hp := nat_pow_pos_of_pos 2 (by decide) (W - 1); omega
            rw [Nat.coprime_iff_gcd_eq_one]
            have hg2 : Nat.gcd 2 (2 ^ W - 1) ≤ 2 := Nat.le_of_dvd (by decide) (Nat.gcd_dvd_left _ _)
            have hgp : Nat.gcd 2 (2 ^ W - 1) ≥ 1 := Nat.gcd_pos_of_pos_left _ (by decide)
            have hgd := Nat.gcd_dvd_right 2 (2 ^ W - 1)
            by_cases h1 : Nat.gcd 2 (2 ^ W - 1) = 1
            · exact h1
            · have he2 : Nat.gcd 2 (2 ^ W - 1) = 2 := by omega
              rw [he2] at hgd; rcases hgd with ⟨q, hq⟩; omega
          have hblk_cop : ∀ k : Nat, k ≤ m' -> Nat.Coprime (blockNodeDiffProd 2 m' k) (2 ^ W - 1) := by
            intro k hk; induction k with
            | zero => exact Nat.coprime_one_left _
            | succ k' ihk =>
              simp only [blockNodeDiffProd]
              have hfac : 2 ^ m' - 2 ^ k' = 2 ^ k' * (2 ^ (m' - k') - 1) := by
                conv => lhs; lhs; rw [show m' = k' + (m' - k') by omega, Nat.pow_add]
                rw [Nat.mul_sub_left_distrib, Nat.mul_one]
              rw [hfac]
              have hgc : Nat.Coprime (2 ^ (m' - k') - 1) (2 ^ W - 1) := by
                rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm]
                exact gcd_pow_sub1_of_coprime_w18 2 (by decide) (W + (m' - k')) W (m' - k')
                  hW (by omega) (by omega) (hcop_all (m' - k') (by omega) (by omega))
              exact (ihk (Nat.le_of_lt hk)).mul_left ((h2_cop.pow_left k').mul_left hgc)
          exact (ihm (Nat.le_of_lt hm)).mul_left
            ((h2_cop.pow_left _).mul_left ((hblk_cop m' (Nat.le_refl m')).pow_left (T * T)))
      exact (hstep_cop U (Nat.le_refl U)).pow_right (T * (U - T))
  -- Part 2:
  have hpart2 : ∀ (U T W u : Nat), T ≥ 1 -> U > T -> W ≥ 1 -> u ≥ 1 ->
      (∀ d : Nat, 1 ≤ d -> d < U -> Nat.Coprime W d) ->
      let colFac := confluentFactorAllU U T u
      let rowFac := (2 ^ (W * u) - 1) ^ (T * (U - T))
      let baseOv := (2 ^ u - 1) ^ (T * (U - T))
      let primRow := rectPrimitiveRowFactor U T W u
      Nat.gcd colFac ((2 ^ (W * u) - 1) / (2 ^ u - 1)) ∣
        (Nat.gcd (2 ^ u - 1) W) ^ (triNumNat U * (T * T)) ∧
      (Nat.Coprime (2 ^ u - 1) W ->
        Nat.Coprime colFac primRow ∧
        Nat.gcd colFac rowFac = baseOv ∧
        Nat.lcm colFac rowFac = colFac * primRow) := by
    intro U T W u hT hUT hW hu hcop_d; dsimp only
    let P := 2 ^ u
    have hP2 : P ≥ 2 := by simpa [P] using pow2_mono_nat hu
    have hP_ev : P % 2 = 0 := by
      dsimp [P]; rw [show u = (u - 1) + 1 by omega, Nat.pow_succ]; omega
    let qW := (2 ^ (W * u) - 1) / (2 ^ u - 1)
    have hWu_P : 2 ^ (W * u) = P ^ W := by dsimp [P]; rw [Nat.mul_comm W u, pow_pow_eq_mul_w5 2 u W]
    have hqW_eq : qW = (P ^ W - 1) / (P - 1) := by dsimp [qW, P]; rw [hWu_P]
    rcases geom_sum_pow_sub1_w18 P hP2 W with ⟨hq_dvd, hq_mod, hq_odd_fn⟩
    have hqW_odd : qW % 2 = 1 := by rw [hqW_eq]; exact hq_odd_fn hW hP_ev
    have hP_cop_qW : Nat.Coprime P qW := by
      have h2_cop : Nat.Coprime 2 qW := by
        rw [Nat.coprime_iff_gcd_eq_one]
        have hg2 : Nat.gcd 2 qW ≤ 2 := Nat.le_of_dvd (by decide) (Nat.gcd_dvd_left _ _)
        have hgp : Nat.gcd 2 qW ≥ 1 := Nat.gcd_pos_of_pos_left _ (by decide)
        have hgd := Nat.gcd_dvd_right 2 qW
        by_cases h1 : Nat.gcd 2 qW = 1
        · exact h1
        · have he2 : Nat.gcd 2 qW = 2 := by omega
          rw [he2] at hgd; rcases hgd with ⟨q, hq⟩; omega
      exact h2_cop.pow_left u
    -- Key lemma: for `1 ≤ d < U`, `Nat.gcd (P^d - 1) qW ∣ Nat.gcd (P - 1) W`:
    have hgcd_Pd_qW : ∀ d : Nat, 1 ≤ d -> d < U ->
        Nat.gcd (P ^ d - 1) qW ∣ Nat.gcd (P - 1) W := by
      intro d hd1 hdU
      have hqW_dvd_PW : qW ∣ (P ^ W - 1) := by
        rcases hq_dvd with ⟨c_q, hc_q⟩
        have hdiv : (P ^ W - 1) / (P - 1) = c_q := by
          rw [hc_q, Nat.mul_comm (P - 1) c_q, Nat.mul_div_cancel c_q (by omega)]
        rw [hqW_eq, hdiv]; exact ⟨P - 1, by rw [Nat.mul_comm]; exact hc_q⟩
      have hd_P1 : Nat.gcd (P ^ d - 1) qW ∣ (P - 1) := by
        have hd_g : Nat.gcd (P ^ d - 1) qW ∣ Nat.gcd (P ^ d - 1) (P ^ W - 1) :=
          Nat.dvd_gcd (Nat.gcd_dvd_left _ _) (Nat.dvd_trans (Nat.gcd_dvd_right _ _) hqW_dvd_PW)
        rwa [gcd_pow_sub1_of_coprime_w18 P hP2 (d + W) d W hd1 hW (by omega) (hcop_d d hd1 hdU).symm] at hd_g
      refine Nat.dvd_gcd hd_P1 ?_
      -- Since `g ∣ (P - 1)` and `g ∣ qW`, and `qW % (P - 1) = W % (P - 1)`, `g ∣ W`!
      let g := Nat.gcd (P ^ d - 1) qW
      change g ∣ W
      have h1 := Nat.div_add_mod qW (P - 1)
      have h2 := Nat.div_add_mod W (P - 1)
      rw [← hqW_eq] at hq_mod
      let rem := W % (P - 1)
      have hrem_eq : qW % (P - 1) = rem := hq_mod
      rw [hrem_eq] at h1
      have hg_rem : g ∣ rem := by
        rcases hd_P1 with ⟨k1, hk1⟩
        rcases (Nat.gcd_dvd_right (P ^ d - 1) qW : g ∣ qW) with ⟨k2, hk2⟩
        refine ⟨k2 - k1 * (qW / (P - 1)), ?_⟩
        rw [Nat.mul_sub_left_distrib]
        have hmul_eq : g * (k1 * (qW / (P - 1))) = (P - 1) * (qW / (P - 1)) := by
          rw [← Nat.mul_assoc g k1, ← hk1]
        rw [hmul_eq, ← hk2]
        omega
      rcases hd_P1 with ⟨k0_p, hk0_p⟩
      have hg_W : g ∣ (P - 1) * (W / (P - 1)) + rem :=
        Nat.dvd_add ⟨k0_p * (W / (P - 1)), by rw [hk0_p, Nat.mul_assoc]⟩ hg_rem
      rwa [h2] at hg_W
    -- Bound `Nat.gcd (blockNodeDiffProd P m m) qW ∣ (Nat.gcd (P - 1) W)^m` for `m < U`:
    have hgcd_blk : ∀ m : Nat, m < U ->
        Nat.gcd (blockNodeDiffProd P m m) qW ∣ (Nat.gcd (P - 1) W) ^ m := by
      intro m hmU
      have hst : ∀ k : Nat, k ≤ m ->
          Nat.gcd (blockNodeDiffProd P m k) qW ∣ (Nat.gcd (P - 1) W) ^ k := by
        intro k hk; induction k with
        | zero => simp [blockNodeDiffProd]
        | succ k' ih =>
          simp only [blockNodeDiffProd, Nat.pow_succ]
          have hfac : P ^ m - P ^ k' = P ^ k' * (P ^ (m - k') - 1) := by
            conv => lhs; lhs; rw [show m = k' + (m - k') by omega, Nat.pow_add]
            rw [Nat.mul_sub_left_distrib, Nat.mul_one]
          rw [hfac]
          have hd1 := gcd_mul_left_dvd_w18 (blockNodeDiffProd P m k') (P ^ k' * (P ^ (m - k') - 1)) qW
          have hd2 := gcd_mul_left_dvd_w18 (P ^ k') (P ^ (m - k') - 1) qW
          have hc_pk : Nat.gcd (P ^ k') qW = 1 := hP_cop_qW.pow_left k'
          rw [hc_pk, Nat.one_mul] at hd2
          exact Nat.dvd_trans hd1 (Nat.mul_dvd_mul (ih (Nat.le_of_lt hk))
            (Nat.dvd_trans hd2 (hgcd_Pd_qW (m - k') (by omega) (by omega))))
      exact hst m (Nat.le_refl m)
    have hgcd_conf : ∀ m : Nat, m ≤ U ->
        Nat.gcd (confluentFactorAllUAux T P m) qW ∣ (Nat.gcd (P - 1) W) ^ (triNumNat m * (T * T)) := by
      intro m hmU; induction m with
      | zero => simp [confluentFactorAllUAux, triNumNat]
      | succ m' ih =>
        simp only [confluentFactorAllUAux, confluentBlockFactor, triNumNat]
        have hexp : (triNumNat m' + m') * (T * T) = triNumNat m' * (T * T) + m' * (T * T) := Nat.add_mul _ _ _
        rw [hexp, Nat.pow_add]
        have hd1 := gcd_mul_left_dvd_w18 (confluentFactorAllUAux T P m')
          (P ^ (m' * triNumNat T) * blockNodeDiffProd P m' m' ^ (T * T)) qW
        have hd2 := gcd_mul_left_dvd_w18 (P ^ (m' * triNumNat T)) (blockNodeDiffProd P m' m' ^ (T * T)) qW
        have hc_p : Nat.gcd (P ^ (m' * triNumNat T)) qW = 1 := hP_cop_qW.pow_left _
        rw [hc_p, Nat.one_mul] at hd2
        have hd3 := Nat.dvd_trans (gcd_pow_left_dvd_w18 (blockNodeDiffProd P m' m') qW (T * T))
          (pow_dvd_of_dvd_w18 _ _ (T * T) (hgcd_blk m' hmU))
        rw [pow_pow_eq_mul_w5 (Nat.gcd (P - 1) W) m' (T * T)] at hd3
        exact Nat.dvd_trans hd1 (Nat.mul_dvd_mul (ih (Nat.le_of_lt hmU)) (Nat.dvd_trans hd2 hd3))
    have hmain_dvd := hgcd_conf U (Nat.le_refl U)
    refine ⟨hmain_dvd, ?_⟩
    intro hcop_uW
    have hg_uW_1 : Nat.gcd (2 ^ u - 1) W = 1 := hcop_uW
    change Nat.gcd (confluentFactorAllUAux T (2 ^ u) U) qW ∣
      (Nat.gcd (2 ^ u - 1) W) ^ (triNumNat U * (T * T)) at hmain_dvd
    rw [hg_uW_1, Nat.one_pow] at hmain_dvd
    have hcop_col_qW : Nat.Coprime (confluentFactorAllU U T u) qW :=
      Nat.coprime_iff_gcd_eq_one.mpr (Nat.eq_one_of_dvd_one hmain_dvd)
    have hcop_col_prim : Nat.Coprime (confluentFactorAllU U T u) (rectPrimitiveRowFactor U T W u) :=
      hcop_col_qW.pow_right (T * (U - T))
    rcases hpart1 U T W u hT hUT hW hu with ⟨hrf_fac, ⟨colRem, hcol_fac⟩, _, _, _⟩
    let baseOv := (2 ^ u - 1) ^ (T * (U - T))
    let primRow := rectPrimitiveRowFactor U T W u
    have hbase_pos : baseOv ≥ 1 := nat_pow_pos_of_pos _ (by omega) _
    have hcop_rem_prim : Nat.Coprime colRem primRow := by
      have hc := hcop_col_prim
      rw [hcol_fac] at hc
      exact hc.coprime_mul_left
    have hgcd_exact : Nat.gcd (confluentFactorAllU U T u) ((2 ^ (W * u) - 1) ^ (T * (U - T))) = baseOv := by
      rw [hcol_fac, hrf_fac, Nat.gcd_mul_left baseOv colRem primRow]
      have hg1 : Nat.gcd colRem primRow = 1 := hcop_rem_prim
      rw [hg1, Nat.mul_one]
    have hlcm_exact : Nat.lcm (confluentFactorAllU U T u) ((2 ^ (W * u) - 1) ^ (T * (U - T))) =
        confluentFactorAllU U T u * primRow := by
      have hgl := Nat.gcd_mul_lcm (confluentFactorAllU U T u) ((2 ^ (W * u) - 1) ^ (T * (U - T)))
      rw [hgcd_exact] at hgl
      have hrhs : confluentFactorAllU U T u * (2 ^ (W * u) - 1) ^ (T * (U - T)) =
          baseOv * (confluentFactorAllU U T u * primRow) := by
        dsimp [baseOv, primRow]; rw [hrf_fac]; ac_rfl
      rw [hrhs] at hgl
      exact Nat.eq_of_mul_eq_mul_left hbase_pos hgl
    exact ⟨hcop_col_prim, hgcd_exact, hlcm_exact⟩
  -- Part 3: Infinite odd-`u = 2 * m + 1` family at `W = 5`:
  have hpart3 : ∀ m : Nat,
      let u := 2 * m + 1
      Nat.Coprime (2 ^ u - 1) 5 ∧
      ∀ (U T : Nat), T ≥ 1 -> U > T -> U ≤ 5 ->
        Nat.gcd (confluentFactorAllU U T u) ((2 ^ (5 * u) - 1) ^ (T * (U - T))) =
          (2 ^ u - 1) ^ (T * (U - T)) ∧
        Nat.lcm (confluentFactorAllU U T u) ((2 ^ (5 * u) - 1) ^ (T * (U - T))) =
          confluentFactorAllU U T u * rectPrimitiveRowFactor U T 5 u := by
    intro m; dsimp only
    have hmod5 : 2 ^ (2 * m + 1) % 5 = 2 ∨ 2 ^ (2 * m + 1) % 5 = 3 := by
      induction m with
      | zero => left; decide
      | succ m' ih =>
        rcases ih with h2 | h3
        · right
          rw [show 2 * (m' + 1) + 1 = (2 * m' + 1) + 2 by omega, Nat.pow_add, Nat.mul_mod, h2]
        · left
          rw [show 2 * (m' + 1) + 1 = (2 * m' + 1) + 2 by omega, Nat.pow_add, Nat.mul_mod, h3]
    have hcop5 : Nat.Coprime (2 ^ (2 * m + 1) - 1) 5 := by
      rw [Nat.coprime_iff_gcd_eq_one]
      let g := Nat.gcd (2 ^ (2 * m + 1) - 1) 5
      have hg5 : g ≤ 5 := Nat.le_of_dvd (by decide) (Nat.gcd_dvd_right _ _)
      have hg_pos : g ≥ 1 := Nat.gcd_pos_of_pos_right _ (by decide)
      have hgd5 : g ∣ 5 := Nat.gcd_dvd_right (2 ^ (2 * m + 1) - 1) 5
      have hgd_l : g ∣ 2 ^ (2 * m + 1) - 1 := Nat.gcd_dvd_left (2 ^ (2 * m + 1) - 1) 5
      rcases (by omega : g = 1 ∨ g = 2 ∨ g = 3 ∨ g = 4 ∨ g = 5) with h1 | h2 | h3 | h4 | h5
      · exact h1
      · rw [h2] at hgd5; rcases hgd5 with ⟨q, hq⟩; omega
      · rw [h3] at hgd5; rcases hgd5 with ⟨q, hq⟩; omega
      · rw [h4] at hgd5; rcases hgd5 with ⟨q, hq⟩; omega
      · exfalso
        rw [h5] at hgd_l
        rcases hgd_l with ⟨q, hq⟩
        have hp_pos : 2 ^ (2 * m + 1) ≥ 2 := by simpa using pow2_mono_nat (by omega : 1 ≤ 2 * m + 1)
        have hm1 : 2 ^ (2 * m + 1) % 5 = 1 := by
          have : 2 ^ (2 * m + 1) = 1 + 5 * q := by omega
          rw [this, Nat.add_mul_mod_self_left]
        rcases hmod5 with h | h <;> omega
    refine ⟨hcop5, ?_⟩
    intro U T hT hUT hU5
    have hcop_d5 : ∀ d : Nat, 1 ≤ d -> d < U -> Nat.Coprime 5 d := by
      intro d hd1 hdU
      rcases (by omega : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4) with rfl | rfl | rfl | rfl <;> decide
    rcases (hpart2 U T 5 (2 * m + 1) hT hUT (by decide) (by omega) hcop_d5).2 hcop5 with
      ⟨_, hgcd_eq, hlcm_eq⟩
    exact ⟨hgcd_eq, hlcm_eq⟩
  refine ⟨hpart1, hpart2, hpart3, ?_⟩
  -- Part 4: `12 × 12` `(U = 4, T = 3, W = 5, K = 8, u = 3)` odd-`u` overlap `gcd = 343` certificate:
  dsimp only
  let M0_12_583 : Fin 12 -> Fin 12 -> Int := fun i j =>
    (laurentZeroGapIntEntry 5 8 (laurentRectRows 4 3 i).1 (laurentRectRows 4 3 i).2
      (laurentColsAllU 4 3 3 j).1 (laurentColsAllU 4 3 3 j).2 : Int)
  have hm0_eq : M0_12_583 = fastM0_12_583FnW18 := by
    funext i j
    dsimp [M0_12_583, fastM0_12_583FnW18, laurentZeroGapIntEntry, laurentRectRows, laurentColsAllU]
    have ht_lt : j.val % 3 < 3 := Nat.mod_lt j.val (by decide)
    have hbin : ∀ x : Nat,
        laurentInterpBinom x 0 = 1 ∧ laurentInterpBinom x 1 = x ∧ (x * (x - 1)) / 2 = laurentInterpBinom x 2 := by
      intro x
      have hsq : ∀ n : Nat, laurentInterpBinom n 0 = 1 ∧ laurentInterpBinom n 1 = n ∧
          2 * laurentInterpBinom n 2 + n = n * n := by
        intro n; induction n with
        | zero => decide
        | succ n' ih =>
          refine ⟨rfl, by simp [laurentInterpBinom, ih.1, ih.2.1]; omega, ?_⟩
          simp only [laurentInterpBinom, ih.2.1]
          change 2 * (n' + laurentInterpBinom n' 2) + (n' + 1) = (n' + 1) * (n' + 1)
          rw [Nat.mul_add 2, show (n' + 1) * (n' + 1) = n' * n' + 2 * n' + 1 by simp only [Nat.add_mul, Nat.mul_add]; omega]
          have := ih.2.2; omega
      rcases hsq x with ⟨h0, h1, h2⟩
      refine ⟨h0, h1, ?_⟩
      have hm2 : x * (x - 1) = 2 * laurentInterpBinom x 2 := by
        cases x with
        | zero => exact h2.symm
        | succ m =>
          have hs : (m + 1) * m = (m + 1) * (m + 1) - (m + 1) := by
            simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
            generalize m * m = M2; omega
          simp only [Nat.add_sub_cancel]
          generalize laurentInterpBinom (m + 1) 2 = C2 at h2 ⊢
          generalize (m + 1) * (m + 1) = X2 at h2 hs
          generalize (m + 1) * m = P2 at hs ⊢
          omega
      generalize laurentInterpBinom x 2 = C2 at hm2 ⊢
      generalize x * (x - 1) = P2 at hm2 ⊢
      omega
    rcases hbin (i.val % 4 * 5 + i.val / 4 * 8) with ⟨hb0, hb1, hb2⟩
    rcases (by omega : j.val % 3 = 0 ∨ j.val % 3 = 1 ∨ j.val % 3 = 2) with h | h | h <;>
    simp [h, hb0, hb1, hb2]
  rcases m0_12_583_ul_cert_w18 with ⟨hul, hrem_nz, hrem_prim0⟩
  have hdet_m0 := checkULDet12BoolW18_sound fastM0_12_583FnW18 uM0_12_583TblW18 expM0_12_583ValW18 hul
  rw [← hm0_eq] at hdet_m0
  refine ⟨by decide, ?_, ?_⟩
  · rw [hdet_m0]
    rintro ⟨q, hq⟩
    rw [hq, Int.mul_emod_right] at hrem_nz
    exact hrem_nz rfl
  · rw [hdet_m0]
    exact Int.dvd_of_emod_eq_zero hrem_prim0

-- ----------------------------------------------------------------------------
-- Section 2B: Rank-3 Order-4 `12 × 12` `(T = 4, U = 3)` `(5, 8)` Cone Sign-Flip,
--             Global `u ∈ {2, 3, 4, 5}` Non-Vanishing, Universal `∀ u ≥ 1` `2`-Adic
--             Matrix Congruence, & Finite Multi-`u` Zero-Horizon (`W18_H2`, Branch P3.3)
-- ----------------------------------------------------------------------------

private def fastMat12T4U3FnW18 (W K u : Nat) (i j : Fin 12) : Int :=
  let r := i.val % 3; let s := i.val / 3
  let t := j.val % 4; let kc := (j.val / 4) * u
  let x := r * W + s * K
  let binv := match t with
    | 0 => 1 | 1 => x | 2 => (x * (x - 1)) / 2 | 3 => (x * (x - 1) * (x - 2)) / 6
    | _ => laurentInterpBinom x t
  ((binv * (2 ^ (r * kc) * 3 ^ (s * kc)) : Nat) : Int)

private theorem fastMat12T4U3FnW18_eq (W K u : Nat) :
    fastMat12T4U3FnW18 W K u = laurentTwoBaseT4U3Mat12 W K u := by
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
    intro n
    rcases hind n with ⟨h0, h1, h2, h3⟩
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
  unfold fastMat12T4U3FnW18 laurentTwoBaseT4U3Mat12 laurentInterpMat laurentInterpEntry
    laurentRowsTwoBase12 laurentColsT4U3_12
  dsimp only
  rcases hst (i.val % 3 * W + i.val / 3 * K) with ⟨hb0, hb1, hb2, hb3⟩
  have ht_lt : j.val % 4 < 4 := Nat.mod_lt j.val (by decide)
  rcases (by omega : j.val % 4 = 0 ∨ j.val % 4 = 1 ∨ j.val % 4 = 2 ∨ j.val % 4 = 3) with h | h | h | h <;>
  (simp only [h, hb0, hb1, hb2, hb3]; apply congrArg Int.ofNat; ac_rfl)

private def uT4U3_582TblW18 : List (List Int) :=
  [[1, 0, 0, 0, -50, 650, -12480, 28080, -12168, 1231776, 132054624, 344962800],
   [0, 1, -2, 6, -36, 354, 16028, -2556, -1260, 26280, 8935920, -195751080],
   [0, 0, 1, -4, 10, -70, -5304, 1224, 432, -4464, -2646432, 46854288],
   [0, 0, 0, 1, -7, 58, 4648, -1584, -36, -26928, -969408, -69937344],
   [0, 0, 0, 0, 50, -650, 12480, -28080, 12155, -1229410, -132364830, -281019375],
   [0, 0, 0, 0, 0, 15, -6659, 6351, -2310, 254620, 25835110, 142038225],
   [0, 0, 0, 0, 0, 0, 554, -694, 324, -32078, -3528744, -6725790],
   [0, 0, 0, 0, 0, 0, 0, 34, -27, 2294, 280412, -766980],
   [0, 0, 0, 0, 0, 0, 0, 0, 13, -2366, 310206, -63943425],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 65, -39445, 6844530],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1918, -498908],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18779]]

private def uT4U3_585TblW18 : List (List Int) :=
  [[1, 0, 0, 0, -100, 1501500, -292554468960, 176351829544800, -781888711577283223784640, 1741683963900692448000, -30197488817578257750540122806753647094855680, 65410087641315361259213226120796233465348531644928000],
   [0, 1, -2, 6, -13098, 44320868, -4014023301280, 1344248283777696, -5745933058805400650624640, 12361307251597575943680, -191542263286056323373912224461343004992332800, 294268758321333542475734998261582846929718982187893760],
   [0, 0, 1, -4, 9600, -31631700, 2718985497504, -844671299317920, 3587518937676483806136768, -7669535520705793521408, 116249257525038050967814339497732453822038016, -163261971438762570842234357793040562014210409536100352],
   [0, 0, 0, 1, -3361, 12546796, -1166983399472, 388383280462512, -1657914523404726221989344, 3561350522611452073344, -54884674548995181807158111852256745169261568, 82523674327937744141617530885230504134205373349011456],
   [0, 0, 0, 0, 100, -1501500, 292554468960, -176351829544800, 781888706387920209411760, -1741683881891231922280, 30197476583695620422702593941675547687516320, -65409930839128123509789916397789047092369508619198400],
   [0, 0, 0, 0, 0, 98695, -31975786367, 25756949687271, -115768768632763188619230, 261260401032424446160, -4709339431667061745452921265187538200451040, 11160686385548882847759843768902677657292378859768000],
   [0, 0, 0, 0, 0, 0, 1865727522, -2690677228330, 12332983640372751781446, -28355882966241026322, 538961319971850386463207945818595205007472, -1421567004486973522128563583324268271153556213475296],
   [0, 0, 0, 0, 0, 0, 0, 151407027052, -714018247223853670493, 1686877852620863446, -34493742012994246952042618454875541277136, 103220653353941330638857056917416062892787811156448],
   [0, 0, 0, 0, 0, 0, 0, 0, 5189363014372880, -82009460525720, 12233882637327837528865078099407339360, -156802187237749423309723007186372979023025729600],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 3013365699785, -868822603635384163393980923679629735, 15386857522823597440546268032336003837826267415],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32207517307966527097611432160722210, -1045290274423219075494441250430885028858494014],
   [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 36903197156608456551206039218454312684093422]]

set_option exponentiation.threshold 2048 in
private theorem t4u3_582_cert_w18 :
    checkULDet12BoolW18 (fastMat12T4U3FnW18 5 8 2) uT4U3_582TblW18
      7670713343317232068959875928780963840000 = true := by decide

set_option exponentiation.threshold 2048 in
private theorem t4u3_585_cert_w18 :
    checkULDet12BoolW18 (fastMat12T4U3FnW18 5 8 5) uT4U3_585TblW18
      (-1672565616913273357156942646537077388479879261317516242714101291766003701276115016188065480704) = true := by
  decide

private def apow12UW18 (u : Nat) (w k : Int) (i j : Fin 12) : Int :=
  let r := (laurentRowsTwoBase12 i).1
  let s := (laurentRowsTwoBase12 i).2
  let t := j.val % 4
  let m := (j.val / 4) * u
  intPowNat ((r : Int) * w + (s : Int) * k) t *
    ((2 ^ (r * m) * 3 ^ (s * m) : Nat) : Int)

private theorem stirling_3blk_1728_w18 (xFn : Fin 12 -> Nat) (eFn : Fin 12 -> Nat -> Int) :
    1728 * intDet 12 (fun i j => ((laurentInterpBinom (xFn i) (j.val % 4) : Nat) : Int) * eFn i (j.val / 4)) =
      intDet 12 (fun i j => intPowNat ((xFn i : Nat) : Int) (j.val % 4) * eFn i (j.val / 4)) := by
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
  let blkSt (b_done : Nat) (i j : Fin 12) : Int :=
    if j.val / 4 < b_done then intPowNat ((xFn i : Nat) : Int) (j.val % 4) * eFn i (j.val / 4)
    else ((laurentInterpBinom (xFn i) (j.val % 4) : Nat) : Int) * eFn i (j.val / 4)
  have hstep : ∀ m : Nat, m < 3 -> 12 * intDet 12 (blkSt m) = intDet 12 (blkSt (m + 1)) := by
    intro m hm3
    let c1 : Fin 12 := ⟨4 * m + 1, by omega⟩
    let c2 : Fin 12 := ⟨4 * m + 2, by omega⟩
    let c3 : Fin 12 := ⟨4 * m + 3, by omega⟩
    let B0 := blkSt m
    let B1 : Fin 12 -> Fin 12 -> Int := fun i j => if j = c2 then 2 * B0 i c2 else B0 i j
    let B2 : Fin 12 -> Fin 12 -> Int := fun i j => if j = c3 then 6 * B1 i c3 else B1 i j
    have hd1 : intDet 12 B1 = 2 * intDet 12 B0 := intDet_col_scale 2 12 c2 B0
    have hd2 : intDet 12 B2 = 6 * intDet 12 B1 := intDet_col_scale 6 12 c3 B1
    let B3 : Fin 12 -> Fin 12 -> Int := fun i j => if j = c2 then B2 i c2 - (-1) * B2 i c1 else B2 i j
    have hd3 : intDet 12 B3 = intDet 12 B2 :=
      intDet_sub_col_mul_other 12 c2 c1 (by intro h; have := congrArg Fin.val h; dsimp [c1, c2] at this; omega) (-1) B2
    let B4 : Fin 12 -> Fin 12 -> Int := fun i j => if j = c3 then B3 i c3 - (-3) * B3 i c2 else B3 i j
    have hd4 : intDet 12 B4 = intDet 12 B3 :=
      intDet_sub_col_mul_other 12 c3 c2 (by intro h; have := congrArg Fin.val h; dsimp [c2, c3] at this; omega) (-3) B3
    let B5 : Fin 12 -> Fin 12 -> Int := fun i j => if j = c3 then B4 i c3 - 2 * B4 i c1 else B4 i j
    have hd5 : intDet 12 B5 = intDet 12 B4 :=
      intDet_sub_col_mul_other 12 c3 c1 (by intro h; have := congrArg Fin.val h; dsimp [c1, c3] at this; omega) 2 B4
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
        · let c0_m : Fin 12 := ⟨4 * m, by omega⟩
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
  have hb0 : blkSt 0 = (fun i j => ((laurentInterpBinom (xFn i) (j.val % 4) : Nat) : Int) * eFn i (j.val / 4)) := by
    funext i j; simp [blkSt]
  have hb3 : blkSt 3 = (fun i j => intPowNat ((xFn i : Nat) : Int) (j.val % 4) * eFn i (j.val / 4)) := by
    funext i j; dsimp [blkSt]; rw [ite_true_of_w10 (by have := j.isLt; omega : j.val / 4 < 3)]
  calc 1728 * intDet 12 (fun i j => ((laurentInterpBinom (xFn i) (j.val % 4) : Nat) : Int) * eFn i (j.val / 4))
      = 12 * (12 * (12 * intDet 12 (blkSt 0))) := by rw [hb0]; omega
    _ = intDet 12 (blkSt 3) := by rw [hstep 0 (by decide), hstep 1 (by decide), hstep 2 (by decide)]
    _ = intDet 12 (fun i j => intPowNat ((xFn i : Nat) : Int) (j.val % 4) * eFn i (j.val / 4)) := by rw [hb3]

private theorem stirling_1728_det12_t4u3_u_w18 (u W K : Nat) :
    1728 * intDet 12 (laurentTwoBaseT4U3Mat12 W K u) =
      intDet 12 (apow12UW18 u (W : Int) (K : Int)) := by
  have heq_in : laurentTwoBaseT4U3Mat12 W K u =
      (fun i j => ((laurentInterpBinom ((laurentRowsTwoBase12 i).1 * W + (laurentRowsTwoBase12 i).2 * K) (j.val % 4) : Nat) : Int) *
        ((2 ^ ((laurentRowsTwoBase12 i).1 * ((j.val / 4) * u)) * 3 ^ ((laurentRowsTwoBase12 i).2 * ((j.val / 4) * u)) : Nat) : Int)) := by
    funext i j
    unfold laurentTwoBaseT4U3Mat12 laurentInterpMat laurentInterpEntry laurentColsT4U3_12
    dsimp only
    rw [← Int.natCast_mul]
    apply congrArg Int.ofNat; ac_rfl
  rw [heq_in, stirling_3blk_1728_w18
        (fun i => (laurentRowsTwoBase12 i).1 * W + (laurentRowsTwoBase12 i).2 * K)
        (fun i m => ((2 ^ ((laurentRowsTwoBase12 i).1 * (m * u)) * 3 ^ ((laurentRowsTwoBase12 i).2 * (m * u)) : Nat) : Int))]
  rfl

private def qCubicW18 (r : Nat) (w y : Int) : Int :=
  match r with
  | 0 => (y - w) * (y - 2 * w)
  | 1 => (w + y) * (y - w)
  | _ => (2 * w + y) * (w + y)

private def apow12KDivW18 (u : Nat) (w k : Int) (i j : Fin 12) : Int :=
  let r := i.val % 3; let s := i.val / 3
  let t := j.val % 4; let m := j.val / 4
  let E : Int := ((2 ^ (r * (m * u)) * 3 ^ (s * (m * u)) : Nat) : Int)
  if t < 3 then intPowNat ((r : Int) * w + (s : Int) * k) t * E
  else (s : Int) * qCubicW18 r w ((s : Int) * k) * E

private def degKW18 (j : Nat) : Nat := if j % 4 < 3 then j % 4 else 2

private def degPrefKW18 : Nat -> Nat
  | 0 => 0
  | c + 1 => degKW18 c + degPrefKW18 c

private theorem apow12_extract_k3_and_homog15_w18 (u : Nat) :
    (∀ w k : Int,
      intDet 12 (apow12UW18 u w k) = intPowNat k 3 * intDet 12 (apow12KDivW18 u w k)) ∧
    (∀ w k g : Int,
      intDet 12 (apow12KDivW18 u (g * w) (g * k)) =
        intPowNat g 15 * intDet 12 (apow12KDivW18 u w k)) := by
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
      y * qCubicW18 r w y := by
    intro r hr w y
    rw [hgen_cub ((r : Int) * w + y) w]
    rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2) with rfl | rfl | rfl
    · simp only [qCubicW18, show ((0 : Nat) : Int) = 0 from rfl, Int.zero_mul, Int.zero_add]
    · simp only [qCubicW18, show ((1 : Nat) : Int) = 1 from rfl, Int.one_mul]
      rw [show w + y - w = y by omega, show w + y - 2 * w = y - w by omega]; ac_rfl
    · simp only [qCubicW18, show ((2 : Nat) : Int) = 2 from rfl]
      rw [show 2 * w + y - w = w + y by omega, show 2 * w + y - 2 * w = y by omega]; ac_rfl
  refine ⟨?_, ?_⟩
  · intro w k
    let blkK (b_done : Nat) (i j : Fin 12) : Int :=
      if j.val / 4 < b_done then apow12KDivW18 u w k i j else apow12UW18 u w k i j
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
          unfold apow12UW18 apow12KDivW18 laurentRowsTwoBase12
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
            k * ((s : Int) * qCubicW18 r w ((s : Int) * k) * E)
          calc intPowNat ((r : Int) * w + (s : Int) * k) 3 * E -
                 3 * w * (intPowNat ((r : Int) * w + (s : Int) * k) 2 * E) -
                 -(2 * (w * w)) * (intPowNat ((r : Int) * w + (s : Int) * k) 1 * E)
              = (intPowNat ((r : Int) * w + (s : Int) * k) 3 -
                 3 * w * intPowNat ((r : Int) * w + (s : Int) * k) 2 +
                 2 * (w * w) * intPowNat ((r : Int) * w + (s : Int) * k) 1) * E := by
                simp only [Int.sub_mul, Int.add_mul, Int.neg_mul]
                rw [Int.sub_neg, Int.mul_assoc (3 * w), Int.mul_assoc (2 * (w * w))]
            _ = (((s : Int) * k) * qCubicW18 r w ((s : Int) * k)) * E := by rw [hcub]
            _ = k * ((s : Int) * qCubicW18 r w ((s : Int) * k) * E) := by ac_rfl
        · rw [ite_false_of_w10 hj3]
          dsimp [B2, B1]; rw [ite_false_of_w10 hj3, ite_false_of_w10 hj3]
          dsimp [B0, blkK]
          by_cases hjm : j.val / 4 = m
          · have hj_lt3 : j.val % 4 < 3 := by
              by_cases h3 : j.val % 4 = 3
              · exfalso; apply hj3; apply Fin.ext; dsimp [c3]; have := Nat.div_add_mod j.val 4; omega
              · have := Nat.mod_lt j.val (by decide : 0 < 4); omega
            rw [hjm, ite_false_of_w10 (Nat.lt_irrefl m), ite_true_of_w10 (Nat.lt_succ_self m)]
            unfold apow12KDivW18 apow12UW18 laurentRowsTwoBase12
            dsimp only; rw [ite_true_of_w10 hj_lt3]
          · by_cases hlt_m : j.val / 4 < m
            · rw [ite_true_of_w10 hlt_m, ite_true_of_w10 (by omega)]
            · rw [ite_false_of_w10 hlt_m, ite_false_of_w10 (by omega)]
      rw [← hd1, ← hd2, hB2_eq]
      exact intDet_col_scale k 12 c3 (blkK (m + 1))
    have hb0 : blkK 0 = apow12UW18 u w k := by funext i j; simp [blkK]
    have hb3 : blkK 3 = apow12KDivW18 u w k := by
      funext i j; dsimp [blkK]; rw [ite_true_of_w10 (by have := j.isLt; omega : j.val / 4 < 3)]
    rw [← hb0, hstep 0 (by decide), hstep 1 (by decide), hstep 2 (by decide), hb3]
    simp only [intPowNat, Int.mul_one]; ac_rfl
  · intro w k g
    let colSc (c_done : Nat) (i j : Fin 12) : Int :=
      if j.val < c_done then intPowNat g (degKW18 j.val) * apow12KDivW18 u w k i j
      else apow12KDivW18 u w k i j
    have hmul_pow : ∀ (a b : Int) (d : Nat), intPowNat (a * b) d = intPowNat a d * intPowNat b d := by
      intro a b d; induction d with
      | zero => simp [intPowNat]
      | succ d' ih => simp only [intPowNat, ih]; ac_rfl
    have hadd_pow : ∀ (a : Int) (d1 d2 : Nat), intPowNat a (d1 + d2) = intPowNat a d1 * intPowNat a d2 := by
      intro a d1; induction d1 with
      | zero => intro d2; simp [intPowNat]
      | succ d1' ih => intro d2; rw [Nat.succ_add, intPowNat, intPowNat, ih d2, Int.mul_assoc]
    have hsc_step : ∀ (c : Nat) (hc : c < 12),
        intDet 12 (colSc (c + 1)) = intPowNat g (degKW18 c) * intDet 12 (colSc c) := by
      intro c hc
      let jc : Fin 12 := ⟨c, hc⟩
      have heq_m : colSc (c + 1) = (fun i j =>
          if j = jc then intPowNat g (degKW18 c) * colSc c i jc else colSc c i j) := by
        funext i j
        by_cases hj : j = jc
        · subst hj; dsimp [colSc, jc]
          rw [ite_true_of_w10 (Nat.lt_succ_self c), ite_true_of_w10 rfl, ite_false_of_w10 (Nat.lt_irrefl c)]
        · dsimp [colSc]; rw [ite_false_of_w10 hj]
          have hjv : j.val ≠ c := fun hv => hj (Fin.ext hv)
          by_cases hlt : j.val < c
          · rw [ite_true_of_w10 (by omega), ite_true_of_w10 hlt]
          · rw [ite_false_of_w10 (by omega), ite_false_of_w10 hlt]
      rw [heq_m]; exact intDet_col_scale (intPowNat g (degKW18 c)) 12 jc (colSc c)
    have hind : ∀ n : Nat, n ≤ 12 ->
        intDet 12 (colSc n) = intPowNat g (degPrefKW18 n) * intDet 12 (colSc 0) := by
      intro n; induction n with
      | zero => intro _; simp [degPrefKW18, intPowNat]
      | succ n' ihn =>
        intro hn
        rw [hsc_step n' hn, ihn (Nat.le_of_lt hn), ← Int.mul_assoc, ← hadd_pow]
        rfl
    have h12 := hind 12 (Nat.le_refl 12)
    have hdeg15 : degPrefKW18 12 = 15 := by decide
    have h0 : colSc 0 = apow12KDivW18 u w k := by funext i j; simp [colSc]
    have h12_eq : colSc 12 = apow12KDivW18 u (g * w) (g * k) := by
      funext i j
      dsimp [colSc]; rw [ite_true_of_w10 j.isLt]
      unfold apow12KDivW18 degKW18
      dsimp only
      let E : Int := ((2 ^ (i.val % 3 * (j.val / 4 * u)) * 3 ^ (i.val / 3 * (j.val / 4 * u)) : Nat) : Int)
      by_cases ht3 : j.val % 4 < 3
      · rw [ite_true_of_w10 ht3, ite_true_of_w10 ht3, ite_true_of_w10 ht3]
        have hlin : ((i.val % 3 : Nat) : Int) * (g * w) + ((i.val / 3 : Nat) : Int) * (g * k) =
            g * (((i.val % 3 : Nat) : Int) * w + ((i.val / 3 : Nat) : Int) * k) := by
          rw [Int.mul_add]; congr 1 <;> ac_rfl
        rw [hlin, hmul_pow, Int.mul_assoc]
      · rw [ite_false_of_w10 ht3, ite_false_of_w10 ht3, ite_false_of_w10 ht3]
        have hq : qCubicW18 (i.val % 3) (g * w) ((i.val / 3 : Int) * (g * k)) =
            intPowNat g 2 * qCubicW18 (i.val % 3) w ((i.val / 3 : Int) * k) := by
          let s : Int := (i.val / 3 : Int)
          change qCubicW18 (i.val % 3) (g * w) (s * (g * k)) = intPowNat g 2 * qCubicW18 (i.val % 3) w (s * k)
          rcases (by have := Nat.mod_lt i.val (by decide : 0 < 3); omega : i.val % 3 = 0 ∨ i.val % 3 = 1 ∨ i.val % 3 = 2) with h | h | h
          · have h1 : s * (g * k) - g * w = g * (s * k - w) := by rw [Int.mul_sub]; congr 1; ac_rfl
            have h2 : s * (g * k) - 2 * (g * w) = g * (s * k - 2 * w) := by rw [Int.mul_sub]; congr 1 <;> ac_rfl
            rw [h]; dsimp only [qCubicW18, intPowNat]; rw [Int.mul_one, h1, h2]; ac_rfl
          · have h1 : g * w + s * (g * k) = g * (w + s * k) := by rw [Int.mul_add]; congr 1; ac_rfl
            have h2 : s * (g * k) - g * w = g * (s * k - w) := by rw [Int.mul_sub]; congr 1; ac_rfl
            rw [h]; dsimp only [qCubicW18, intPowNat]; rw [Int.mul_one, h1, h2]; ac_rfl
          · have h1 : 2 * (g * w) + s * (g * k) = g * (2 * w + s * k) := by rw [Int.mul_add]; congr 1 <;> ac_rfl
            have h2 : g * w + s * (g * k) = g * (w + s * k) := by rw [Int.mul_add]; congr 1; ac_rfl
            rw [h]; dsimp only [qCubicW18, intPowNat]; rw [Int.mul_one, h1, h2]; ac_rfl
        change intPowNat g 2 * ((i.val / 3 : Int) * qCubicW18 (i.val % 3) w ((i.val / 3 : Int) * k) * E) =
          (i.val / 3 : Int) * qCubicW18 (i.val % 3) (g * w) ((i.val / 3 : Int) * (g * k)) * E
        rw [hq]; ac_rfl
    rw [hdeg15, h0, h12_eq] at h12
    exact h12

private theorem det12_t4u3_homog18_w18 (u g W K : Nat) :
    intDet 12 (laurentTwoBaseT4U3Mat12 (g * W) (g * K) u) =
      intPowNat (g : Int) 18 * intDet 12 (laurentTwoBaseT4U3Mat12 W K u) := by
  have h1 := stirling_1728_det12_t4u3_u_w18 u (g * W) (g * K)
  have h2 := stirling_1728_det12_t4u3_u_w18 u W K
  rcases apow12_extract_k3_and_homog15_w18 u with ⟨hk3, hhom15⟩
  have hm : 1728 * intDet 12 (laurentTwoBaseT4U3Mat12 (g * W) (g * K) u) =
      1728 * (intPowNat (g : Int) 18 * intDet 12 (laurentTwoBaseT4U3Mat12 W K u)) := by
    rw [h1]
    simp only [Int.natCast_mul]
    rw [hk3 ((g : Int) * (W : Int)) ((g : Int) * (K : Int)),
        hhom15 (W : Int) (K : Int) (g : Int)]
    have hrhs_apow : intDet 12 (apow12UW18 u (W : Int) (K : Int)) =
        intPowNat (K : Int) 3 * intDet 12 (apow12KDivW18 u (W : Int) (K : Int)) := hk3 _ _
    have hmul_g3 : intPowNat ((g : Int) * (K : Int)) 3 = intPowNat (g : Int) 3 * intPowNat (K : Int) 3 := by
      simp only [intPowNat, Int.mul_one]; ac_rfl
    have hg18 : intPowNat (g : Int) 3 * intPowNat (g : Int) 15 = intPowNat (g : Int) 18 :=
      (intPowNat_add (g : Int) 3 15).symm
    calc intPowNat ((g : Int) * (K : Int)) 3 * (intPowNat (g : Int) 15 * intDet 12 (apow12KDivW18 u (W : Int) (K : Int)))
        = (intPowNat (g : Int) 3 * intPowNat (g : Int) 15) *
            (intPowNat (K : Int) 3 * intDet 12 (apow12KDivW18 u (W : Int) (K : Int))) := by rw [hmul_g3]; ac_rfl
      _ = intPowNat (g : Int) 18 * (intPowNat (K : Int) 3 * intDet 12 (apow12KDivW18 u (W : Int) (K : Int))) := by rw [hg18]
      _ = intPowNat (g : Int) 18 * (1728 * intDet 12 (laurentTwoBaseT4U3Mat12 W K u)) := by rw [← hrhs_apow, ← h2]
      _ = 1728 * (intPowNat (g : Int) 18 * intDet 12 (laurentTwoBaseT4U3Mat12 W K u)) :=
            Int.mul_left_comm (intPowNat (g : Int) 18) 1728 _
  exact Int.eq_of_mul_eq_mul_left (by decide : (1728 : Int) ≠ 0) hm

-- Signed-column-swap + unit-upper-triangular `SL_12(Z)` mod-`p` projective sieve certificates:
private def powModFuelNatW18 : Nat -> Nat -> Nat -> Nat -> Nat
  | 0, _, _, _ => 1
  | f' + 1, b, e, m =>
    if e = 0 then 1 % m
    else
      let half := powModFuelNatW18 f' b (e / 2) m
      let sq := (half * half) % m
      if e % 2 = 1 then (sq * (b % m)) % m else sq

private theorem powModFuelNatW18_eq_of_lt :
    ∀ (f b e m : Nat), e < 2 ^ f -> powModFuelNatW18 (f + 1) b e m = (b ^ e) % m
  | 0, b, e, m, he => by
    have he0 : e = 0 := by simp at he; exact he
    subst he0; simp [powModFuelNatW18]
  | f' + 1, b, e, m, he => by
    unfold powModFuelNatW18
    by_cases he0 : e = 0
    · subst he0; simp
    · rw [ite_false_of_w10 he0]
      have he_half : e / 2 < 2 ^ f' := by rw [Nat.pow_succ] at he; omega
      have ih := powModFuelNatW18_eq_of_lt f' b (e / 2) m he_half
      dsimp only
      rw [ih]
      have hsq : (((b ^ (e / 2) % m) * (b ^ (e / 2) % m)) % m) = (b ^ (2 * (e / 2))) % m := by
        rw [← Nat.mul_mod, ← Nat.pow_add, Nat.two_mul]
      rw [hsq]
      have hdm := (Nat.div_add_mod e 2).symm
      by_cases hodd : e % 2 = 1
      · rw [ite_true_of_w10 hodd, ← Nat.mul_mod]
        conv => rhs; rw [hdm, hodd, Nat.pow_add, Nat.pow_one]
      · have hev : e % 2 = 0 := by omega
        rw [ite_false_of_w10 hodd]
        conv => rhs; rw [hdm, hev, Nat.add_zero]

private theorem powModFuelNatW18_all_eq (b e m : Nat) :
    powModFuelNatW18 (e + 1) b e m = (b ^ e) % m := by
  have hlt : ∀ n : Nat, n < 2 ^ n := by
    intro n; induction n with
    | zero => decide
    | succ n' ih => rw [Nat.pow_succ]; omega
  exact powModFuelNatW18_eq_of_lt e b e m (hlt e)

private theorem intPowNat_natCast_w18 (n d : Nat) :
    intPowNat (n : Int) d = ((n ^ d : Nat) : Int) := by
  induction d with
  | zero => rfl
  | succ d' ih => simp only [intPowNat, ih, Nat.pow_succ, Int.natCast_mul]; ac_rfl

private theorem int_mod_sub_dvd_w18 (a pNat : Nat) :
    (pNat : Int) ∣ (((a % pNat : Nat) : Int) - (a : Int)) := by
  refine ⟨-((a / pNat : Nat) : Int), ?_⟩
  have hc := congrArg (fun n : Nat => (n : Int)) (Nat.div_add_mod a pNat)
  simp only [Int.natCast_add, Int.natCast_mul] at hc
  rw [Int.mul_neg]; omega

private def fastApow12KDivNatW18 (u w k : Nat) (i j : Fin 12) : Int :=
  let r := i.val % 3; let s := i.val / 3
  let t := j.val % 4; let m := j.val / 4
  let E : Int := ((2 ^ (r * (m * u)) * 3 ^ (s * (m * u)) : Nat) : Int)
  if t < 3 then (((r * w + s * k) ^ t : Nat) : Int) * E
  else (s : Int) * qCubicW18 r (w : Int) ((s * k : Nat) : Int) * E

private theorem fastApow12KDivNatW18_eq (u w k : Nat) :
    fastApow12KDivNatW18 u w k = apow12KDivW18 u (w : Int) (k : Int) := by
  funext i j
  unfold fastApow12KDivNatW18 apow12KDivW18
  dsimp only
  by_cases ht3 : j.val % 4 < 3
  · rw [ite_true_of_w10 ht3, ite_true_of_w10 ht3, ← intPowNat_natCast_w18]
    simp only [Int.natCast_add, Int.natCast_mul]
  · rw [ite_false_of_w10 ht3, ite_false_of_w10 ht3]
    simp only [Int.natCast_mul]

private def applySignedSwapsW18 :
    List (Nat × Nat) -> (Fin 12 -> Fin 12 -> Int) -> (Fin 12 -> Fin 12 -> Int)
  | [], M => M
  | (c1, c2) :: rest, M =>
    let M' :=
      if h : c1 < 12 ∧ c2 < 12 ∧ c1 ≠ c2 then
        fun i j =>
          if j = ⟨c1, h.1⟩ then M i ⟨c2, h.2.1⟩
          else if j = ⟨c2, h.2.1⟩ then -(M i ⟨c1, h.1⟩)
          else M i j
      else M
    applySignedSwapsW18 rest M'

private theorem signedColSwap_det_w18 (c1 c2 : Fin 12) (hne : c1 ≠ c2)
    (M : Fin 12 -> Fin 12 -> Int) :
    intDet 12 (fun i j => if j = c1 then M i c2 else if j = c2 then -(M i c1) else M i j) =
      intDet 12 M := by
  let M1 : Fin 12 -> Fin 12 -> Int := fun i j => if j = c1 then M i c1 - (-1) * M i c2 else M i j
  let M2 : Fin 12 -> Fin 12 -> Int := fun i j => if j = c2 then M1 i c2 - 1 * M1 i c1 else M1 i j
  let M3 : Fin 12 -> Fin 12 -> Int := fun i j => if j = c1 then M2 i c1 - (-1) * M2 i c2 else M2 i j
  have hd1 : intDet 12 M1 = intDet 12 M := intDet_sub_col_mul_other 12 c1 c2 (Ne.symm hne) (-1) M
  have hd2 : intDet 12 M2 = intDet 12 M1 := intDet_sub_col_mul_other 12 c2 c1 hne 1 M1
  have hd3 : intDet 12 M3 = intDet 12 M2 := intDet_sub_col_mul_other 12 c1 c2 (Ne.symm hne) (-1) M2
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

private theorem dite_pos_w18 {p : Prop} [inst : Decidable p] {α : Sort _}
    {t : p -> α} {e : ¬ p -> α} (hp : p) : (if h : p then t h else e h) = t hp := by
  cases inst with
  | isTrue _ => rfl
  | isFalse hn => exact False.elim (hn hp)

private theorem dite_neg_w18 {p : Prop} [inst : Decidable p] {α : Sort _}
    {t : p -> α} {e : ¬ p -> α} (hnp : ¬ p) : (if h : p then t h else e h) = e hnp := by
  cases inst with
  | isTrue hp => exact False.elim (hnp hp)
  | isFalse _ => rfl

private theorem applySignedSwapsW18_det :
    ∀ (swaps : List (Nat × Nat)) (M : Fin 12 -> Fin 12 -> Int),
      intDet 12 (applySignedSwapsW18 swaps M) = intDet 12 M
  | [], _ => rfl
  | (c1, c2) :: rest, M => by
    unfold applySignedSwapsW18
    by_cases h : c1 < 12 ∧ c2 < 12 ∧ c1 ≠ c2
    · rw [dite_pos_w18 h, applySignedSwapsW18_det rest]
      exact signedColSwap_det_w18 ⟨c1, h.1⟩ ⟨c2, h.2.1⟩ (fun heq => h.2.2 (congrArg Fin.val heq)) M
    · rw [dite_neg_w18 h, applySignedSwapsW18_det rest]

private def natAt1DW18 : List Nat -> Nat -> Nat
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, k + 1 => natAt1DW18 xs k

private def natRowAtW18 : List (List Nat) -> Nat -> List Nat
  | [], _ => []
  | r :: _, 0 => r
  | _ :: rs, k + 1 => natRowAtW18 rs k

private def natAt2DW18 (rows : List (List Nat)) (r c : Nat) : Nat :=
  natAt1DW18 (natRowAtW18 rows r) c

private def buildRow12NatW18 (f : Nat -> Nat) : List Nat :=
  [f 0, f 1, f 2, f 3, f 4, f 5, f 6, f 7, f 8, f 9, f 10, f 11]

private def buildMat12NatW18 (f : Nat -> Nat -> Nat) : List (List Nat) :=
  [buildRow12NatW18 (f 0), buildRow12NatW18 (f 1), buildRow12NatW18 (f 2), buildRow12NatW18 (f 3),
   buildRow12NatW18 (f 4), buildRow12NatW18 (f 5), buildRow12NatW18 (f 6), buildRow12NatW18 (f 7),
   buildRow12NatW18 (f 8), buildRow12NatW18 (f 9), buildRow12NatW18 (f 10), buildRow12NatW18 (f 11)]

private theorem natAt1DW18_buildRow12 (f : Nat -> Nat) (k : Nat) (hk : k < 12) :
    natAt1DW18 (buildRow12NatW18 f) k = f k := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨
      k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem natRowAtW18_buildMat12 (f : Nat -> Nat -> Nat) (r : Nat) (hr : r < 12) :
    natRowAtW18 (buildMat12NatW18 f) r = buildRow12NatW18 (fun c => f r c) := by
  rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨
      r = 6 ∨ r = 7 ∨ r = 8 ∨ r = 9 ∨ r = 10 ∨ r = 11) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem natAt2DW18_buildMat12 (f : Nat -> Nat -> Nat) (r c : Nat) (hr : r < 12) (hc : c < 12) :
    natAt2DW18 (buildMat12NatW18 f) r c = f r c := by
  unfold natAt2DW18
  rw [natRowAtW18_buildMat12 f r hr, natAt1DW18_buildRow12 _ c hc]

private def natSubModPW18 (pNat posPart negPart : Nat) : Nat :=
  (posPart % pNat + pNat - negPart % pNat) % pNat

private theorem natSubModPW18_dvd_int (pNat posPart negPart : Nat) (hp : pNat ≥ 1) :
    (pNat : Int) ∣ (((natSubModPW18 pNat posPart negPart : Nat) : Int) -
      ((posPart : Int) - (negPart : Int))) := by
  unfold natSubModPW18
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

private def fastApow12EntryModPNatW18 (pNat u w k rCol cCol : Nat) : Nat :=
  let r := rCol % 3; let s := rCol / 3
  let t := cCol % 4; let m := cCol / 4
  let E := (powModFuelNatW18 (r * (m * u) + 1) 2 (r * (m * u)) pNat *
    powModFuelNatW18 (s * (m * u) + 1) 3 (s * (m * u)) pNat) % pNat
  let sk := s * k
  let poly :=
    if Nat.ble (t + 1) 3 then ((r * w + sk) ^ t) % pNat
    else
      let qc :=
        match r with
        | 0 => (natSubModPW18 pNat sk w * natSubModPW18 pNat sk (2 * w)) % pNat
        | 1 => (((w + sk) % pNat) * natSubModPW18 pNat sk w) % pNat
        | _ => (((2 * w + sk) % pNat) * ((w + sk) % pNat)) % pNat
      (s * qc) % pNat
  (poly * E) % pNat

private def swapOneMat12NatW18 (pNat c1 c2 : Nat) (M : List (List Nat)) : List (List Nat) :=
  if Nat.ble (c1 + 1) 12 && Nat.ble (c2 + 1) 12 && (c1 != c2) then
    buildMat12NatW18 (fun r j =>
      if j == c1 then natAt2DW18 M r c2
      else if j == c2 then natSubModPW18 pNat 0 (natAt2DW18 M r c1)
      else natAt2DW18 M r j)
  else M

private def applySignedSwapsMat12NatW18 (pNat : Nat) :
    List (Nat × Nat) -> List (List Nat) -> List (List Nat)
  | [], M => M
  | (c1, c2) :: rest, M =>
    applySignedSwapsMat12NatW18 pNat rest (swapOneMat12NatW18 pNat c1 c2 M)

private def uStrictNatValW18 (uRows : List (List Nat)) (r c : Nat) : Nat :=
  if Nat.ble (c + 1) r then 0
  else if c == r then 1
  else natAt2DW18 uRows r (c - r - 1)

private def dotPrefix12NatW18 (row col : List Nat) : Nat -> Nat
  | 0 => 0
  | n + 1 =>
    dotPrefix12NatW18 row col n + natAt1DW18 row n * natAt1DW18 col n

private def dotListsPrefixW18 : Nat -> List Nat -> List Nat -> Nat
  | 0, _, _ => 0
  | n + 1, x :: xs, y :: ys =>
    (if x == 0 || y == 0 then 0 else x * y) + dotListsPrefixW18 n xs ys
  | _, _, _ => 0

private theorem dotListsPrefixW18_eq :
    ∀ (n : Nat) (xs ys : List Nat),
      dotListsPrefixW18 n xs ys = dotPrefix12NatW18 xs ys n := by
  have hnil_l : ∀ (m : Nat) (ys : List Nat), dotPrefix12NatW18 [] ys m = 0 := by
    intro m ys; induction m with
    | zero => rfl
    | succ m' ih => simp [dotPrefix12NatW18, natAt1DW18, ih]
  have hnil_r : ∀ (m : Nat) (xs : List Nat), dotPrefix12NatW18 xs [] m = 0 := by
    intro m xs; induction m with
    | zero => rfl
    | succ m' ih => simp [dotPrefix12NatW18, natAt1DW18, ih]
  have hcons : ∀ (m x y : Nat) (xs ys : List Nat),
      dotPrefix12NatW18 (x :: xs) (y :: ys) (m + 1) = x * y + dotPrefix12NatW18 xs ys m := by
    intro m x y xs ys; induction m with
    | zero => simp [dotPrefix12NatW18, natAt1DW18]
    | succ m' ih =>
      change dotPrefix12NatW18 (x :: xs) (y :: ys) (m' + 1) +
          natAt1DW18 xs m' * natAt1DW18 ys m' =
        x * y + (dotPrefix12NatW18 xs ys m' + natAt1DW18 xs m' * natAt1DW18 ys m')
      rw [ih, Nat.add_assoc]
  intro n; induction n with
  | zero => intros; rfl
  | succ n' ih =>
    intro xs ys
    cases xs with
    | nil => simp [dotListsPrefixW18, hnil_l]
    | cons x xtl =>
      cases ys with
      | nil => simp [dotListsPrefixW18, hnil_r]
      | cons y ytl =>
        rw [hcons n' x y xtl ytl]
        unfold dotListsPrefixW18
        rw [ih xtl ytl]
        apply congrArg (· + dotPrefix12NatW18 xtl ytl n')
        cases x <;> cases y <;> simp

private def allNatLoopW18 (p : Nat -> Bool) : Nat -> Bool
  | 0 => true
  | k + 1 => p k && allNatLoopW18 p k

private theorem allNatLoopW18_spec (p : Nat -> Bool) :
    ∀ k : Nat, allNatLoopW18 p k = true -> ∀ x : Nat, x < k -> p x = true
  | 0, _, _, hx => by omega
  | k' + 1, ha, x, hx => by
    unfold allNatLoopW18 at ha
    rcases bool_and_split ha with ⟨hk, hprev⟩
    by_cases heq : x = k'
    · subst heq; exact hk
    · exact allNatLoopW18_spec p k' hprev x (by omega)

private def natDiagProdModPW18 (pNat : Nat) (apRows uCols : List (List Nat)) : Nat -> Nat
  | 0 => 1 % pNat
  | k + 1 =>
    let dk := dotListsPrefixW18 (k + 1) (natRowAtW18 apRows k) (natRowAtW18 uCols k) % pNat
    (natDiagProdModPW18 pNat apRows uCols k * dk) % pNat

private def checkRawMatULModP12BoolW18 (pNat : Nat) (a0 : List (List Nat))
    (cert : List (Nat × Nat) × List (List Nat)) : Bool :=
  let apRows := applySignedSwapsMat12NatW18 pNat cert.1 a0
  let uCols := buildMat12NatW18 (fun c r => uStrictNatValW18 cert.2 r c)
  allNatLoopW18 (fun r =>
    let row_r := natRowAtW18 apRows r
    allNatLoopW18 (fun c =>
      if Nat.ble (r + 1) c then
        dotListsPrefixW18 (c + 1) row_r (natRowAtW18 uCols c) % pNat == 0
      else true) 12) 12 &&
  (natDiagProdModPW18 pNat apRows uCols 12 != 0)

private theorem checkRawMatULModP12BoolW18_sound (pNat : Nat) (hp : pNat ≥ 2)
    (a0 : List (List Nat)) (cert : List (Nat × Nat) × List (List Nat))
    (h : checkRawMatULModP12BoolW18 pNat a0 cert = true) :
    intDet 12 (fun i j => (natAt2DW18 a0 i.val j.val : Int)) % (pNat : Int) ≠ 0 := by
  let p : Int := (pNat : Int)
  have hp1 : pNat ≥ 1 := by omega
  let matOf (T : List (List Nat)) (i j : Fin 12) : Int := (natAt2DW18 T i.val j.val : Int)
  have hd_trans : ∀ a b c : Int, p ∣ (a - b) -> p ∣ (b - c) -> p ∣ (a - c) := by
    intro a b c ⟨q1, h1⟩ ⟨q2, h2⟩; exact ⟨q1 + q2, by rw [Int.mul_add]; omega⟩
  have hd_sub_r : ∀ a b : Nat, p ∣ (((a : Int) - (b : Int)) - (natSubModPW18 pNat a b : Int)) := by
    intro a b
    rcases natSubModPW18_dvd_int pNat a b hp1 with ⟨q, hq⟩
    exact ⟨-q, by dsimp [p]; rw [Int.mul_neg]; omega⟩
  let apRows := applySignedSwapsMat12NatW18 pNat cert.1 a0
  let uCols := buildMat12NatW18 (fun c r => uStrictNatValW18 cert.2 r c)
  have hd_swaps : ∀ (swaps : List (Nat × Nat)) (M : List (List Nat)),
      p ∣ (intDet 12 (matOf M) - intDet 12 (matOf (applySignedSwapsMat12NatW18 pNat swaps M))) := by
    intro swaps; induction swaps with
    | nil => intro M; exact ⟨0, by simp [applySignedSwapsMat12NatW18]⟩
    | cons sw rest ih =>
      rcases sw with ⟨c1, c2⟩
      intro M
      unfold applySignedSwapsMat12NatW18
      let M' := swapOneMat12NatW18 pNat c1 c2 M
      have hd_one : p ∣ (intDet 12 (matOf M) - intDet 12 (matOf M')) := by
        dsimp only [M']; unfold swapOneMat12NatW18
        by_cases hc : c1 < 12 ∧ c2 < 12 ∧ c1 ≠ c2
        · have hcond : (Nat.ble (c1 + 1) 12 && Nat.ble (c2 + 1) 12 && (c1 != c2)) = true := by
            rw [Nat.ble_eq.mpr hc.1, Nat.ble_eq.mpr hc.2.1, bne_iff_ne.mpr hc.2.2]; rfl
          change p ∣ (intDet 12 (matOf M) - intDet 12 (matOf
            (if (Nat.ble (c1 + 1) 12 && Nat.ble (c2 + 1) 12 && (c1 != c2)) = true then
              buildMat12NatW18 (fun r j =>
                if j == c1 then natAt2DW18 M r c2
                else if j == c2 then natSubModPW18 pNat 0 (natAt2DW18 M r c1)
                else natAt2DW18 M r j)
            else M)))
          rw [ite_true_of_w10 hcond]
          let fc1 : Fin 12 := ⟨c1, hc.1⟩
          let fc2 : Fin 12 := ⟨c2, hc.2.1⟩
          let S_int (i j : Fin 12) : Int :=
            if j = fc1 then matOf M i fc2 else if j = fc2 then -(matOf M i fc1) else matOf M i j
          rw [← signedColSwap_det_w18 fc1 fc2 (fun h => hc.2.2 (congrArg Fin.val h)) (matOf M)]
          apply intDet_congr_dvd p 12 S_int
          intro i j
          dsimp only [S_int, matOf]
          rw [natAt2DW18_buildMat12 _ i.val j.val i.isLt j.isLt]
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
              simpa using hd_sub_r 0 (natAt2DW18 M i.val c1)
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
  let U (r c : Fin 12) : Int := (uStrictNatValW18 cert.2 r.val c.val : Int)
  let prodFull (r c : Fin 12) : Int := intSumPrefix 12 (fun k_f => Ap r k_f * U k_f c) 12
  let prodTrunc (r c : Fin 12) : Int := intSumPrefix 12 (fun k_f => Ap r k_f * U k_f c) (c.val + 1)
  unfold checkRawMatULModP12BoolW18 at h
  rcases bool_and_split h with ⟨hsup_b, hdiag_nz_b⟩
  have hdiag_nz := bne_iff_ne.mp hdiag_nz_b
  have hupper : ∀ r c : Fin 12, c.val < r.val -> U r c = 0 := by
    intro r c hlt; dsimp [U, uStrictNatValW18]; rw [ite_true_of_w10 (Nat.ble_eq.mpr hlt)]; rfl
  have hu_diag1 : intDiagProdPrefixW18 12 U 12 = 1 := by
    have hst : ∀ m : Nat, m ≤ 12 -> intDiagProdPrefixW18 12 U m = 1 := by
      intro m hm; induction m with
      | zero => rfl
      | succ m' ih =>
        have hm_lt : m' < 12 := hm
        simp only [intDiagProdPrefixW18, hm_lt, dite_true, ih (Nat.le_of_lt hm), Int.one_mul]
        dsimp [U, uStrictNatValW18]
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
    have hm := intDet_mul_upper_tri_w18 12 Ap U hupper
    dsimp only [prodFull]; rw [hm, hu_diag1, Int.one_mul]
  have hdot_eq : ∀ (r c : Fin 12) (n : Nat), n ≤ 12 ->
      ((dotPrefix12NatW18 (natRowAtW18 apRows r.val) (natRowAtW18 uCols c.val) n : Nat) : Int) =
        intSumPrefix 12 (fun k_f => Ap r k_f * U k_f c) n := by
    intro r c n hn; induction n with
    | zero => rfl
    | succ n' ih =>
      have hn_lt : n' < 12 := hn
      simp only [dotPrefix12NatW18, intSumPrefix, hn_lt, dite_true,
                 Int.natCast_add, Int.natCast_mul, ih (Nat.le_of_lt hn)]
      have hu_at : natAt1DW18 (natRowAtW18 uCols c.val) n' = uStrictNatValW18 cert.2 n' c.val := by
        dsimp only [uCols]
        rw [natRowAtW18_buildMat12 _ c.val c.isLt, natAt1DW18_buildRow12 _ n' hn_lt]
      rw [hu_at]; rfl
  let prodLow (r c : Fin 12) : Int := if r.val < c.val then 0 else prodTrunc r c
  have hd_low : p ∣ (intDet 12 prodTrunc - intDet 12 prodLow) := by
    apply intDet_congr_dvd p 12 prodTrunc prodLow
    intro r c; dsimp [prodLow]
    by_cases hrc : r.val < c.val
    · rw [ite_true_of_w10 hrc, Int.sub_zero]
      have hr_b := allNatLoopW18_spec _ 12 hsup_b r.val r.isLt
      have hc_b := allNatLoopW18_spec _ 12 hr_b c.val c.isLt
      rw [Nat.ble_eq.mpr hrc, dotListsPrefixW18_eq] at hc_b
      have hm_nat := beq_iff_eq.mp hc_b
      have hm_int : prodTrunc r c % p = 0 := by
        dsimp only [prodTrunc, p]
        rw [← hdot_eq r c (c.val + 1) (by have := c.isLt; omega)]
        exact (Int.natCast_emod _ pNat).symm.trans (by rw [hm_nat]; rfl)
      exact Int.dvd_of_emod_eq_zero hm_int
    · rw [ite_false_of_w10 hrc, Int.sub_self]; exact ⟨0, by simp⟩
  have hdet_low : intDet 12 prodLow = intDiagProdPrefixW18 12 prodTrunc 12 := by
    rw [intDet_lower_tri_w18 12 prodLow (fun r c hrc => by dsimp [prodLow]; rw [ite_true_of_w10 hrc])]
    have hst : ∀ m : Nat, m ≤ 12 -> intDiagProdPrefixW18 12 prodLow m = intDiagProdPrefixW18 12 prodTrunc m := by
      intro m hm; induction m with
      | zero => rfl
      | succ m' ih =>
        have hm_lt : m' < 12 := hm
        simp only [intDiagProdPrefixW18, hm_lt, dite_true, ih (Nat.le_of_lt hm)]
        dsimp [prodLow]; rw [ite_false_of_w10 (Nat.lt_irrefl m')]
    exact hst 12 (Nat.le_refl 12)
  have hdiag_eq : ∀ m : Nat, m ≤ 12 ->
      ((natDiagProdModPW18 pNat apRows uCols m : Nat) : Int) =
        intDiagProdPrefixW18 12 prodTrunc m % p := by
    intro m hm; induction m with
    | zero => exact Int.natCast_emod 1 pNat
    | succ m' ih =>
      have hm_lt : m' < 12 := hm
      let fm : Fin 12 := ⟨m', hm_lt⟩
      simp only [natDiagProdModPW18, dotListsPrefixW18_eq]
      rw [Int.natCast_emod, Int.natCast_mul, Int.natCast_emod,
          ih (Nat.le_of_lt hm), hdot_eq fm fm (m' + 1) hm]
      simp only [intDiagProdPrefixW18, hm_lt, dite_true]
      exact (Int.mul_emod _ _ p).symm
  have hd_ap_diag : p ∣ (intDet 12 Ap - intDiagProdPrefixW18 12 prodTrunc 12) := by
    rw [← hdet_prod, ← hdet_low]; exact hd_low
  have hd_tot := hd_trans _ _ _ (hd_swaps cert.1 a0) hd_ap_diag
  rcases hd_tot with ⟨qt, hqt⟩
  intro hz_mod
  have hdiag_mod0 : intDiagProdPrefixW18 12 prodTrunc 12 % p = 0 := by
    have heq : intDiagProdPrefixW18 12 prodTrunc 12 =
        intDet 12 (matOf a0) + p * (-qt) := by
      rw [Int.mul_neg]; omega
    rw [heq, Int.add_emod, hz_mod, Int.zero_add, Int.mul_emod_right, Int.zero_emod]
  have hnat0_int : ((natDiagProdModPW18 pNat apRows uCols 12 : Nat) : Int) = ((0 : Nat) : Int) := by
    rw [hdiag_eq 12 (Nat.le_refl 12), hdiag_mod0]; rfl
  exact hdiag_nz (Int.ofNat.inj hnat0_int)

-- Lucas mod-3 closed form & period-9 invariance of `laurentInterpBinom n t % 3` (`t < 4`):
private def checkULModPNat12BoolW18 (pNat u w k : Nat)
    (cert : List (Nat × Nat) × List (List Nat)) : Bool :=
  let a0 := buildMat12NatW18 (fastApow12EntryModPNatW18 pNat u w k)
  let apRows := applySignedSwapsMat12NatW18 pNat cert.1 a0
  let uCols := buildMat12NatW18 (fun c r => uStrictNatValW18 cert.2 r c)
  allNatLoopW18 (fun r =>
    let row_r := natRowAtW18 apRows r
    allNatLoopW18 (fun c =>
      if Nat.ble (r + 1) c then
        dotListsPrefixW18 (c + 1) row_r (natRowAtW18 uCols c) % pNat == 0
      else true) 12) 12 &&
  (natDiagProdModPW18 pNat apRows uCols 12 != 0)

private theorem checkULModPNat12BoolW18_sound (pNat u w k : Nat) (hp : pNat ≥ 2)
    (cert : List (Nat × Nat) × List (List Nat))
    (h : checkULModPNat12BoolW18 pNat u w k cert = true) :
    intDet 12 (apow12KDivW18 u (w : Int) (k : Int)) % (pNat : Int) ≠ 0 := by
  let p : Int := (pNat : Int)
  have hp1 : pNat ≥ 1 := by omega
  let matOf (T : List (List Nat)) (i j : Fin 12) : Int := (natAt2DW18 T i.val j.val : Int)
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
    rcases int_mod_sub_dvd_w18 n pNat with ⟨q, hq⟩
    exact ⟨-q, by dsimp [p]; rw [Int.mul_neg]; omega⟩
  have hd_sub_r : ∀ a b : Nat, p ∣ (((a : Int) - (b : Int)) - (natSubModPW18 pNat a b : Int)) := by
    intro a b
    rcases natSubModPW18_dvd_int pNat a b hp1 with ⟨q, hq⟩
    exact ⟨-q, by dsimp [p]; rw [Int.mul_neg]; omega⟩
  let a0 := buildMat12NatW18 (fastApow12EntryModPNatW18 pNat u w k)
  let apRows := applySignedSwapsMat12NatW18 pNat cert.1 a0
  let uCols := buildMat12NatW18 (fun c r => uStrictNatValW18 cert.2 r c)
  have hd_A0 : p ∣ (intDet 12 (apow12KDivW18 u (w : Int) (k : Int)) - intDet 12 (matOf a0)) := by
    rw [← fastApow12KDivNatW18_eq u w k]
    apply intDet_congr_dvd p 12
    intro i j
    dsimp only [matOf, a0]
    rw [natAt2DW18_buildMat12 _ i.val j.val i.isLt j.isLt]
    unfold fastApow12KDivNatW18 fastApow12EntryModPNatW18
    simp only [powModFuelNatW18_all_eq]
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
        | 0 => (natSubModPW18 pNat sk w * natSubModPW18 pNat sk (2 * w)) % pNat
        | 1 => (((w + sk) % pNat) * natSubModPW18 pNat sk w) % pNat
        | _ => (((2 * w + sk) % pNat) * ((w + sk) % pNat)) % pNat
      have hd_qc : p ∣ (qCubicW18 r (w : Int) (sk : Int) - (qc_nat : Int)) := by
        dsimp only [qc_nat]
        rcases (by have := Nat.mod_lt i.val (by decide : 0 < 3); omega : r = 0 ∨ r = 1 ∨ r = 2) with hr | hr | hr
        · rw [hr]; dsimp only [qCubicW18]
          rw [show (2 : Int) * (w : Int) = ((2 * w : Nat) : Int) by simp [Int.natCast_mul]]
          exact hd_trans _ ((natSubModPW18 pNat sk w * natSubModPW18 pNat sk (2 * w) : Nat) : Int) _
            (by rw [Int.natCast_mul]; exact hd_mul _ _ _ _ (hd_sub_r sk w) (hd_sub_r sk (2 * w)))
            (hd_mod_r _)
        · rw [hr]; dsimp only [qCubicW18]
          rw [show (w : Int) + (sk : Int) = ((w + sk : Nat) : Int) by simp [Int.natCast_add]]
          exact hd_trans _ ((((w + sk) % pNat * natSubModPW18 pNat sk w : Nat) : Int)) _
            (by rw [Int.natCast_mul]; exact hd_mul _ _ _ _ (hd_mod_r (w + sk)) (hd_sub_r sk w))
            (hd_mod_r _)
        · rw [hr]; dsimp only [qCubicW18]
          rw [show (2 : Int) * (w : Int) + (sk : Int) = ((2 * w + sk : Nat) : Int) by simp [Int.natCast_add, Int.natCast_mul],
              show (w : Int) + (sk : Int) = ((w + sk : Nat) : Int) by simp [Int.natCast_add]]
          exact hd_trans _ ((((2 * w + sk) % pNat * ((w + sk) % pNat) : Nat) : Int)) _
            (by rw [Int.natCast_mul]; exact hd_mul _ _ _ _ (hd_mod_r _) (hd_mod_r _))
            (hd_mod_r _)
      let poly_nat : Nat := (s * qc_nat) % pNat
      have hd_sqc : p ∣ ((s : Int) * qCubicW18 r (w : Int) (sk : Int) - (poly_nat : Int)) :=
        hd_trans _ (((s * qc_nat : Nat) : Int)) _
          (by rw [Int.natCast_mul]; exact hd_mul (s : Int) (s : Int) _ _ ⟨0, by simp⟩ hd_qc)
          (hd_mod_r (s * qc_nat))
      change p ∣ ((s : Int) * qCubicW18 r (w : Int) (sk : Int) * E_int - (((poly_nat * E_nat) % pNat : Nat) : Int))
      exact hd_trans _ (((poly_nat * E_nat : Nat) : Int)) _
        (by rw [Int.natCast_mul]; exact hd_mul _ _ _ _ hd_sqc hd_E)
        (hd_mod_r (poly_nat * E_nat))
  have hraw_nz : intDet 12 (matOf a0) % p ≠ 0 :=
    checkRawMatULModP12BoolW18_sound pNat hp a0 cert h
  rcases hd_A0 with ⟨qt, hqt⟩
  intro hz_mod
  have hmat0 : intDet 12 (matOf a0) % p = 0 := by
    have heq : intDet 12 (matOf a0) =
        intDet 12 (apow12KDivW18 u (w : Int) (k : Int)) + p * (-qt) := by
      rw [Int.mul_neg]; omega
    rw [heq, Int.add_emod, hz_mod, Int.zero_add, Int.mul_emod_right, Int.zero_emod]
  exact hraw_nz hmat0

private def checkAllInvModPBoolW18 (pNat : Nat) : Nat -> Bool
  | 0 => true
  | x + 1 =>
    (if x == 0 then true else ((x * powModFuelNatW18 8 x (pNat - 2) pNat) % pNat == 1)) &&
      checkAllInvModPBoolW18 pNat x

private def checkAffRangeULModPBoolW18 (u pNat start : Nat) :
    Nat -> List (List (Nat × Nat) × List (List Nat)) -> Bool
  | 0, _ => true
  | cnt + 1, c :: cs =>
    checkULModPNat12BoolW18 pNat u start 1 c &&
      checkAffRangeULModPBoolW18 u pNat (start + 1) cnt cs
  | _, [] => false

private def iterNegModPW18 (pNat : Nat) : Nat -> Nat -> Nat
  | 0, v => v
  | k + 1, v => natSubModPW18 pNat 0 (iterNegModPW18 pNat k v)

private theorem iterNegModPW18_neg (pNat : Nat) :
    ∀ (cnt v : Nat),
      iterNegModPW18 pNat cnt (natSubModPW18 pNat 0 v) = iterNegModPW18 pNat (cnt + 1) v
  | 0, _ => rfl
  | cnt' + 1, v => congrArg (natSubModPW18 pNat 0) (iterNegModPW18_neg pNat cnt' v)

private def traceColSwapsW18 : List (Nat × Nat) -> Nat -> Nat × Nat
  | [], j => (j, 0)
  | (c1, c2) :: rest, j =>
    match traceColSwapsW18 rest j with
    | (j', cnt) =>
      if Nat.ble (c1 + 1) 12 && Nat.ble (c2 + 1) 12 && (c1 != c2) then
        if j' == c1 then (c2, cnt)
        else if j' == c2 then (c1, cnt + 1)
        else (j', cnt)
      else (j', cnt)

private theorem traceColSwapsW18_spec (pNat : Nat) :
    ∀ (swaps : List (Nat × Nat)) (M : List (List Nat)) (r j : Nat),
      r < 12 -> j < 12 ->
      (traceColSwapsW18 swaps j).1 < 12 ∧
      natAt2DW18 (applySignedSwapsMat12NatW18 pNat swaps M) r j =
        iterNegModPW18 pNat (traceColSwapsW18 swaps j).2
          (natAt2DW18 M r (traceColSwapsW18 swaps j).1)
  | [], _, _, _, _, hj => ⟨hj, rfl⟩
  | (c1, c2) :: rest, M, r, j, hr, hj => by
    unfold applySignedSwapsMat12NatW18 traceColSwapsW18
    rcases htr : traceColSwapsW18 rest j with ⟨j', cnt⟩
    dsimp only
    cases hcond : (Nat.ble (c1 + 1) 12 && Nat.ble (c2 + 1) 12 && (c1 != c2))
    · have hsw : swapOneMat12NatW18 pNat c1 c2 M = M := by
        unfold swapOneMat12NatW18; rw [hcond]; rfl
      rw [hsw]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rcases traceColSwapsW18_spec pNat rest M r j hr hj with ⟨hj', ih_eq⟩
      rw [htr] at hj' ih_eq
      exact ⟨hj', ih_eq⟩
    · simp only [↓reduceIte]
      let M' := swapOneMat12NatW18 pNat c1 c2 M
      rcases traceColSwapsW18_spec pNat rest M' r j hr hj with ⟨hj', ih_eq⟩
      rw [htr] at hj' ih_eq
      dsimp only at hj' ih_eq
      rcases bool_and_split hcond with ⟨hc12, _⟩
      rcases bool_and_split hc12 with ⟨hc1_b, hc2_b⟩
      have hc1 : c1 < 12 := Nat.ble_eq.mp hc1_b
      have hc2 : c2 < 12 := Nat.ble_eq.mp hc2_b
      have hM'_at : natAt2DW18 M' r j' =
          if j' == c1 then natAt2DW18 M r c2
          else if j' == c2 then natSubModPW18 pNat 0 (natAt2DW18 M r c1)
          else natAt2DW18 M r j' := by
        unfold M' swapOneMat12NatW18
        rw [hcond]; simp only [↓reduceIte]
        exact natAt2DW18_buildMat12 _ r j' hr hj'
      rw [hM'_at] at ih_eq
      cases he1 : (j' == c1)
      · cases he2 : (j' == c2)
        · simp only [he1, he2, Bool.false_eq_true, ↓reduceIte] at ih_eq ⊢
          exact ⟨hj', ih_eq⟩
        · simp only [he1, he2, Bool.false_eq_true, ↓reduceIte] at ih_eq ⊢
          rw [iterNegModPW18_neg] at ih_eq
          exact ⟨hc1, ih_eq⟩
      · simp only [he1, ↓reduceIte] at ih_eq ⊢
        exact ⟨hc2, ih_eq⟩

private theorem buildRow12NatW18_congr (f g : Nat -> Nat) (h : ∀ j : Nat, j < 12 -> f j = g j) :
    buildRow12NatW18 f = buildRow12NatW18 g := by
  unfold buildRow12NatW18
  rw [h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide),
      h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide),
      h 8 (by decide), h 9 (by decide), h 10 (by decide), h 11 (by decide)]

private theorem buildMat12NatW18_congr (f g : Nat -> Nat -> Nat)
    (h : ∀ r j : Nat, r < 12 -> j < 12 -> f r j = g r j) :
    buildMat12NatW18 f = buildMat12NatW18 g := by
  unfold buildMat12NatW18
  rw [buildRow12NatW18_congr _ _ (fun j hj => h 0 j (by decide) hj),
      buildRow12NatW18_congr _ _ (fun j hj => h 1 j (by decide) hj),
      buildRow12NatW18_congr _ _ (fun j hj => h 2 j (by decide) hj),
      buildRow12NatW18_congr _ _ (fun j hj => h 3 j (by decide) hj),
      buildRow12NatW18_congr _ _ (fun j hj => h 4 j (by decide) hj),
      buildRow12NatW18_congr _ _ (fun j hj => h 5 j (by decide) hj),
      buildRow12NatW18_congr _ _ (fun j hj => h 6 j (by decide) hj),
      buildRow12NatW18_congr _ _ (fun j hj => h 7 j (by decide) hj),
      buildRow12NatW18_congr _ _ (fun j hj => h 8 j (by decide) hj),
      buildRow12NatW18_congr _ _ (fun j hj => h 9 j (by decide) hj),
      buildRow12NatW18_congr _ _ (fun j hj => h 10 j (by decide) hj),
      buildRow12NatW18_congr _ _ (fun j hj => h 11 j (by decide) hj)]

private theorem applySignedSwaps_is_buildMat12W18 (pNat : Nat) :
    ∀ (swaps : List (Nat × Nat)) (f : Nat -> Nat -> Nat),
      ∃ g : Nat -> Nat -> Nat,
        applySignedSwapsMat12NatW18 pNat swaps (buildMat12NatW18 f) = buildMat12NatW18 g
  | [], f => ⟨f, rfl⟩
  | (c1, c2) :: rest, f => by
    unfold applySignedSwapsMat12NatW18 swapOneMat12NatW18
    cases (Nat.ble (c1 + 1) 12 && Nat.ble (c2 + 1) 12 && (c1 != c2)) <;>
      simp only [Bool.false_eq_true, ↓reduceIte] <;>
      exact applySignedSwaps_is_buildMat12W18 pNat rest _

private theorem applySignedSwaps_eq_tracedBuildMat12W18 (pNat : Nat)
    (swaps : List (Nat × Nat)) (f : Nat -> Nat -> Nat) :
    applySignedSwapsMat12NatW18 pNat swaps (buildMat12NatW18 f) =
      buildMat12NatW18 (fun r j =>
        match traceColSwapsW18 swaps j with
        | (j0, cnt) => iterNegModPW18 pNat cnt (f r j0)) := by
  rcases applySignedSwaps_is_buildMat12W18 pNat swaps f with ⟨g, hg⟩
  have hspec : ∀ r j : Nat, r < 12 -> j < 12 ->
      g r j = match traceColSwapsW18 swaps j with
              | (j0, cnt) => iterNegModPW18 pNat cnt (f r j0) := by
    intro r j hr hj
    rcases traceColSwapsW18_spec pNat swaps (buildMat12NatW18 f) r j hr hj with ⟨hj0, heq⟩
    rw [hg, natAt2DW18_buildMat12 g r j hr hj] at heq
    rcases htr : traceColSwapsW18 swaps j with ⟨j0, cnt⟩
    rw [htr] at hj0 heq
    dsimp only at hj0 heq ⊢
    rw [heq, natAt2DW18_buildMat12 f r j0 hr hj0]
  rw [hg]
  exact buildMat12NatW18_congr g _ hspec

private def fastApow12DirectModPW18 (pNat u w k rCol cCol : Nat) : Nat :=
  let r := rCol % 3; let s := rCol / 3
  let t := cCol % 4; let m := cCol / 4
  let E := ((2 ^ (r * (m * u))) % pNat * ((3 ^ (s * (m * u))) % pNat)) % pNat
  let sk := s * k
  let poly :=
    if Nat.ble (t + 1) 3 then ((r * w + sk) ^ t) % pNat
    else
      let qc :=
        match r with
        | 0 => (natSubModPW18 pNat sk w * natSubModPW18 pNat sk (2 * w)) % pNat
        | 1 => (((w + sk) % pNat) * natSubModPW18 pNat sk w) % pNat
        | _ => (((2 * w + sk) % pNat) * ((w + sk) % pNat)) % pNat
      (s * qc) % pNat
  (poly * E) % pNat

private theorem fastApow12DirectModPW18_eq (pNat u w k rCol cCol : Nat) :
    fastApow12DirectModPW18 pNat u w k rCol cCol =
      fastApow12EntryModPNatW18 pNat u w k rCol cCol := by
  unfold fastApow12DirectModPW18 fastApow12EntryModPNatW18
  simp only [powModFuelNatW18_all_eq]

private def dotDirect12W18 (f g : Nat -> Nat) : Nat -> Nat
  | 0 => 0
  | n + 1 =>
    dotDirect12W18 f g n +
      (let x := f n
       if x == 0 then 0 else x * g n)

private theorem dotDirect12W18_eq (f g : Nat -> Nat) :
    ∀ n : Nat, n ≤ 12 ->
      dotDirect12W18 f g n = dotPrefix12NatW18 (buildRow12NatW18 f) (buildRow12NatW18 g) n
  | 0, _ => rfl
  | n' + 1, hn => by
    have hn_lt : n' < 12 := hn
    simp only [dotDirect12W18, dotPrefix12NatW18,
               dotDirect12W18_eq f g n' (Nat.le_of_lt hn),
               natAt1DW18_buildRow12 f n' hn_lt, natAt1DW18_buildRow12 g n' hn_lt]
    apply congrArg (dotPrefix12NatW18 (buildRow12NatW18 f) (buildRow12NatW18 g) n' + ·)
    cases f n' <;> simp

private def natDiagDirectModPW18 (pNat : Nat) (apFn uFn : Nat -> Nat -> Nat) : Nat -> Nat
  | 0 => 1 % pNat
  | k + 1 =>
    let dk := dotDirect12W18 (apFn k) (fun n => uFn n k) (k + 1) % pNat
    (natDiagDirectModPW18 pNat apFn uFn k * dk) % pNat

private def checkULModPNat12FastBoolW18 (pNat u w k : Nat)
    (cert : List (Nat × Nat) × List (List Nat)) : Bool :=
  let apFn (r j : Nat) : Nat :=
    match traceColSwapsW18 cert.1 j with
    | (j0, cnt) =>
      iterNegModPW18 pNat cnt (fastApow12DirectModPW18 pNat u w k r j0)
  let uFn (n c : Nat) : Nat := uStrictNatValW18 cert.2 n c
  allNatLoopW18 (fun r =>
    allNatLoopW18 (fun c =>
      if Nat.ble (r + 1) c then
        dotDirect12W18 (apFn r) (fun n => uFn n c) (c + 1) % pNat == 0
      else true) 12) 12 &&
  (natDiagDirectModPW18 pNat apFn uFn 12 != 0)

private theorem allNatLoopW18_congr (p q : Nat -> Bool) :
    ∀ k : Nat, (∀ x : Nat, x < k -> p x = q x) -> allNatLoopW18 p k = allNatLoopW18 q k
  | 0, _ => rfl
  | k' + 1, h => by
    unfold allNatLoopW18
    rw [h k' (Nat.lt_succ_self k'), allNatLoopW18_congr p q k' (fun x hx => h x (Nat.lt_succ_of_lt hx))]

private theorem checkULModPNat12FastBoolW18_eq (pNat u w k : Nat)
    (cert : List (Nat × Nat) × List (List Nat)) :
    checkULModPNat12FastBoolW18 pNat u w k cert =
      checkULModPNat12BoolW18 pNat u w k cert := by
  unfold checkULModPNat12FastBoolW18 checkULModPNat12BoolW18
  dsimp only
  let apFn0 (r j : Nat) : Nat :=
    match traceColSwapsW18 cert.1 j with
    | (j0, cnt) => iterNegModPW18 pNat cnt (fastApow12DirectModPW18 pNat u w k r j0)
  let apFn1 (r j : Nat) : Nat :=
    match traceColSwapsW18 cert.1 j with
    | (j0, cnt) => iterNegModPW18 pNat cnt (fastApow12EntryModPNatW18 pNat u w k r j0)
  have hap01 : apFn0 = apFn1 := by
    funext r j; dsimp only [apFn0, apFn1]; rw [fastApow12DirectModPW18_eq]
  change (allNatLoopW18 (fun r => allNatLoopW18 (fun c =>
            if Nat.ble (r + 1) c then dotDirect12W18 (apFn0 r) (fun n => uStrictNatValW18 cert.2 n c) (c + 1) % pNat == 0
            else true) 12) 12 &&
          (natDiagDirectModPW18 pNat apFn0 (uStrictNatValW18 cert.2) 12 != 0)) = _
  rw [hap01, applySignedSwaps_eq_tracedBuildMat12W18 pNat cert.1 (fastApow12EntryModPNatW18 pNat u w k)]
  let apRows := buildMat12NatW18 apFn1
  let uCols := buildMat12NatW18 (fun c r => uStrictNatValW18 cert.2 r c)
  have hdot : ∀ (r c m : Nat), r < 12 -> c < 12 -> m ≤ 12 ->
      dotDirect12W18 (apFn1 r) (fun n => uStrictNatValW18 cert.2 n c) m =
        dotListsPrefixW18 m (natRowAtW18 apRows r) (natRowAtW18 uCols c) := by
    intro r c m hr hc hm
    rw [dotListsPrefixW18_eq, dotDirect12W18_eq _ _ m hm]
    dsimp only [apRows, uCols]
    rw [natRowAtW18_buildMat12 _ r hr, natRowAtW18_buildMat12 _ c hc]
  have hloop :
      allNatLoopW18 (fun r => allNatLoopW18 (fun c =>
        if Nat.ble (r + 1) c then dotDirect12W18 (apFn1 r) (fun n => uStrictNatValW18 cert.2 n c) (c + 1) % pNat == 0
        else true) 12) 12 =
      allNatLoopW18 (fun r =>
        let row_r := natRowAtW18 apRows r
        allNatLoopW18 (fun c =>
          if Nat.ble (r + 1) c then dotListsPrefixW18 (c + 1) row_r (natRowAtW18 uCols c) % pNat == 0
          else true) 12) 12 := by
    apply allNatLoopW18_congr _ _ 12; intro r hr
    apply allNatLoopW18_congr _ _ 12; intro c hc
    rw [hdot r c (c + 1) hr hc (by omega)]
  have hdiag : ∀ m : Nat, m ≤ 12 ->
      natDiagDirectModPW18 pNat apFn1 (uStrictNatValW18 cert.2) m =
        natDiagProdModPW18 pNat apRows uCols m := by
    intro m hm; induction m with
    | zero => rfl
    | succ m' ih =>
      have hm_lt : m' < 12 := hm
      simp only [natDiagDirectModPW18, natDiagProdModPW18,
                 ih (Nat.le_of_lt hm), hdot m' m' (m' + 1) hm_lt hm_lt hm]
  rw [hloop, hdiag 12 (Nat.le_refl 12)]

private def checkAffRangeULModPFastBoolW18 (u pNat start : Nat) :
    Nat -> List (List (Nat × Nat) × List (List Nat)) -> Bool
  | 0, _ => true
  | cnt + 1, c :: cs =>
    checkULModPNat12FastBoolW18 pNat u start 1 c &&
      checkAffRangeULModPFastBoolW18 u pNat (start + 1) cnt cs
  | _, [] => false

private theorem checkAffRangeULModPFastBoolW18_eq (u pNat : Nat) :
    ∀ (cnt start : Nat) (cs : List (List (Nat × Nat) × List (List Nat))),
      checkAffRangeULModPFastBoolW18 u pNat start cnt cs =
        checkAffRangeULModPBoolW18 u pNat start cnt cs
  | 0, _, _ => rfl
  | _ + 1, _, [] => rfl
  | cnt' + 1, start, c :: cs => by
    change (checkULModPNat12FastBoolW18 pNat u start 1 c && checkAffRangeULModPFastBoolW18 u pNat (start + 1) cnt' cs) =
      (checkULModPNat12BoolW18 pNat u start 1 c && checkAffRangeULModPBoolW18 u pNat (start + 1) cnt' cs)
    rw [checkULModPNat12FastBoolW18_eq, checkAffRangeULModPFastBoolW18_eq u pNat cnt' (start + 1) cs]

private def dropCertsW18 : Nat -> List (List (Nat × Nat) × List (List Nat)) ->
    List (List (Nat × Nat) × List (List Nat))
  | 0, cs => cs
  | _ + 1, [] => []
  | k + 1, _ :: cs => dropCertsW18 k cs

private theorem checkAffRangeULModPFastBoolW18_glue (u pNat : Nat) :
    ∀ (a b start : Nat) (cs : List (List (Nat × Nat) × List (List Nat))),
      checkAffRangeULModPFastBoolW18 u pNat start a cs = true ->
      checkAffRangeULModPFastBoolW18 u pNat (start + a) b (dropCertsW18 a cs) = true ->
      checkAffRangeULModPFastBoolW18 u pNat start (a + b) cs = true
  | 0, _, start, _, _, hb => by
    rw [Nat.zero_add]; rw [Nat.add_zero] at hb; exact hb
  | _ + 1, _, _, [], ha, _ => by cases ha
  | a' + 1, b, start, c :: cs, ha, hb => by
    rw [Nat.succ_add]
    change (checkULModPNat12FastBoolW18 pNat u start 1 c && checkAffRangeULModPFastBoolW18 u pNat (start + 1) a' cs) = true at ha
    change (checkULModPNat12FastBoolW18 pNat u start 1 c && checkAffRangeULModPFastBoolW18 u pNat (start + 1) (a' + b) cs) = true
    rcases bool_and_split ha with ⟨hc, hrest⟩
    rw [hc, Bool.true_and]
    apply checkAffRangeULModPFastBoolW18_glue u pNat a' b (start + 1) cs hrest
    have heq_st : (start + 1) + a' = start + (a' + 1) := by omega
    rw [heq_st]; exact hb

private theorem unpack_affRangeULModP_w18 (u pNat : Nat) (hp : pNat ≥ 2) :
    ∀ (cnt start : Nat) (cs : List (List (Nat × Nat) × List (List Nat))),
      checkAffRangeULModPBoolW18 u pNat start cnt cs = true ->
      ∀ t : Nat, start ≤ t -> t < start + cnt ->
        intDet 12 (apow12KDivW18 u (t : Int) 1) % (pNat : Int) ≠ 0
  | 0, _, _, _, _, hlo, hhi => by omega
  | cnt' + 1, start, [], hchk, _, _, _ => by cases hchk
  | cnt' + 1, start, c :: cs, hchk, t, hlo, hhi => by
    change (checkULModPNat12BoolW18 pNat u start 1 c && checkAffRangeULModPBoolW18 u pNat (start + 1) cnt' cs) = true at hchk
    rcases bool_and_split hchk with ⟨hcur, hrest⟩
    by_cases hteq : t = start
    · subst hteq
      exact checkULModPNat12BoolW18_sound pNat u t 1 hp c hcur
    · exact unpack_affRangeULModP_w18 u pNat hp cnt' (start + 1) cs hrest t (by omega) (by omega)

private def decodeSwapsW18 : Nat -> Nat -> List (Nat × Nat)
  | 0, _ => []
  | fuel + 1, pk =>
    let b := pk % 256
    if b == 0 then []
    else ((b / 16) - 1, (b % 16) - 1) :: decodeSwapsW18 fuel (pk / 256)

private def decodeUSeqRowW18 : Nat -> Nat -> List Nat × Nat
  | 0, cur => ([], cur)
  | k + 1, cur =>
    let (rest, nxt) := decodeUSeqRowW18 k (cur / 128)
    (cur % 128 :: rest, nxt)

private def decodeUSeqRowsW18 : List Nat -> Nat -> List (List Nat)
  | [], _ => []
  | len :: ls, cur =>
    let (row, nxt) := decodeUSeqRowW18 len cur
    row :: decodeUSeqRowsW18 ls nxt

private def decodeUCertW18 (pk : Nat × Nat) : List (Nat × Nat) × List (List Nat) :=
  (decodeSwapsW18 16 pk.1, decodeUSeqRowsW18 [11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1] pk.2)

private def sieveInfCertU2W18 : List (Nat × Nat) × List (List Nat) :=
  decodeUCertW18 (0x0, 0x118022c83460806a676a5a3806a41200214d15820601d5639192148049d16fcbb50afcda476740055b093377c75180848da8e0498c358400000)

private def sieveAffCertsU2C0W18 : List (List (Nat × Nat) × List (List Nat)) :=
  ([
  (0x9b896a563925, 0x141867000003e610391d000402608000840000d04001b08459b8842e408070e800000000000000000000000000000007c0000000000000000242),
  (0x795645, 0x50b7c34b281e0d32d0a1a0800070ac22ce52aa32a018038011a61b0401a01098a880040040068eb812b60007601423846cbb804014000308000),
  (0x0, 0xf9866c119164815076efdb8272c8997384d8086af9a027491f1a0c3da296445a2b52406846c6003628d9c2a508d980822d7371d0449f8400000),
  (0x0, 0x15285e15e2b20cda9354b9f2f3a3940640259b34cb0b8670edb297709f1f686949a5c18a0800840021e661134e11100802d22f56f45888400000),
  (0x0, 0x111308e0e1224b861e62cd28f6ef993842311101668c297f040b452b962d4699c0966ac52f681803e3c41b178261d807ef8e1754682028400000),
  (0x56, 0x128157046ad3cf441807059a71a50c2a761c81a528dc2c5c00e3a22f0d8c0e75a0654a81243e2c0235a145b652f04007c585c0741c8010000000),
  (0x0, 0xd0276c1db84459a9718dcf0470b979d34ada86007c03d62ac8ab6448e1868f1f9880ec293026403210c46c17a088807a3442f84189188400000),
  (0x0, 0x6be22a5ab83a5c6907499d215a91a3b4cdd6904c55bc104788a1100160248b9d2314ddc8f02440023608811046028078295b9160a0a58400000),
  (0x0, 0x928547dea608cd9100ed941f482db0a42913812444c8e0840b8000c1d81589120466f8f94708c01a12b8daa262df80768db8c52d5fb38400000),
  (0x0, 0x1a917a2e12720c82414895586226c2a93a61e1e767e02558e173446a981f0e5a1134821a1f0668008269d52816f9c0074684c00478b8b8400000),
  (0xbc, 0x52a8c80d686432f5851a2352312b71c8463360e4d32642d42a1cb4db758a94382065a93082402a0e50a1c543528072c01c050448b88400000),
  (0x0, 0x19b0070191e70644005e59fbf70c0f977485c892cc611f1aa942e6a0603666854a9830439b469c0215ed931d0081d0070f5f370091b198400000),
  (0x0, 0x99958b141028b1d9a72e55075c2dc8826853a8405878a2e28aa614141211cd8804788d83c385c0116c9913f32695006ec9f1d66e56398400000),
  (0x0, 0x8b0e915be46c5884522173435009963821440760923a541d1241ec4fa03430fad0c14429130003e6e883134e806806c890033c24cbc8400000),
  (0x0, 0x8ba36fdc9c44e1dba3add7b3390593f6cb81ac608d23376f9090463c21e6ca9b0c80b928c1254008784d0150a752006a6ce843c404058400000),
  (0x0, 0x1391cac19380cd0aa22a0c0642b922528d86bf162cf21645458c6418f09600892b0e904a9561000d00d093d00e57806871aa548888ae8400000),
  (0x0, 0x8c4a1909226b15ad2edc83112adeac409602b382c92612b49bd5655e3e48851834a0923574ec034820c63a0ed208066483266075d168400000)
  ] : List (Nat × Nat)).map decodeUCertW18
set_option maxRecDepth 65536 in
private theorem sieve_aff_u2_c0_fast_w18_s0 :
    checkAffRangeULModPFastBoolW18 2 67 0 4 (dropCertsW18 0 sieveAffCertsU2C0W18) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve_aff_u2_c0_fast_w18_s1 :
    checkAffRangeULModPFastBoolW18 2 67 4 4 (dropCertsW18 4 sieveAffCertsU2C0W18) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve_aff_u2_c0_fast_w18_s2 :
    checkAffRangeULModPFastBoolW18 2 67 8 4 (dropCertsW18 8 sieveAffCertsU2C0W18) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve_aff_u2_c0_fast_w18_s3 :
    checkAffRangeULModPFastBoolW18 2 67 12 4 (dropCertsW18 12 sieveAffCertsU2C0W18) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve_aff_u2_c0_fast_w18_s4 :
    checkAffRangeULModPFastBoolW18 2 67 16 1 (dropCertsW18 16 sieveAffCertsU2C0W18) = true := by decide
private theorem sieve_aff_u2_c0_fast_w18 :
    checkAffRangeULModPFastBoolW18 2 67 0 17 sieveAffCertsU2C0W18 = true := by
  have h0 : checkAffRangeULModPFastBoolW18 2 67 0 4 sieveAffCertsU2C0W18 = true := sieve_aff_u2_c0_fast_w18_s0
  have h1 : checkAffRangeULModPFastBoolW18 2 67 0 8 sieveAffCertsU2C0W18 = true :=
    checkAffRangeULModPFastBoolW18_glue 2 67 4 4 0 sieveAffCertsU2C0W18 h0 sieve_aff_u2_c0_fast_w18_s1
  have h2 : checkAffRangeULModPFastBoolW18 2 67 0 12 sieveAffCertsU2C0W18 = true :=
    checkAffRangeULModPFastBoolW18_glue 2 67 8 4 0 sieveAffCertsU2C0W18 h1 sieve_aff_u2_c0_fast_w18_s2
  have h3 : checkAffRangeULModPFastBoolW18 2 67 0 16 sieveAffCertsU2C0W18 = true :=
    checkAffRangeULModPFastBoolW18_glue 2 67 12 4 0 sieveAffCertsU2C0W18 h2 sieve_aff_u2_c0_fast_w18_s3
  have h4 : checkAffRangeULModPFastBoolW18 2 67 0 17 sieveAffCertsU2C0W18 = true :=
    checkAffRangeULModPFastBoolW18_glue 2 67 16 1 0 sieveAffCertsU2C0W18 h3 sieve_aff_u2_c0_fast_w18_s4
  exact h4
private theorem sieve_aff_u2_c0_ok_w18 :
    checkAffRangeULModPBoolW18 2 67 0 17 sieveAffCertsU2C0W18 = true :=
  (checkAffRangeULModPFastBoolW18_eq 2 67 17 0 sieveAffCertsU2C0W18).symm.trans sieve_aff_u2_c0_fast_w18

private def sieveAffCertsU2C1W18 : List (List (Nat × Nat) × List (List Nat)) :=
  ([
  (0x0, 0x170e563050664eda3054fcc2260c4db850cd9c252e60236d0089a6a8831d56ade060a85a8144f80262838ca302e430064e080404806838400000),
  (0x0, 0x93a5a7e0b182d968e6ab811a005d59f72c581a5700a015cb9d265acc73b66ad7a01c75a2610a002468c6092365ce006228d155d08a958400000),
  (0x9a89, 0x1828846c3805c0400d3e49620489e1426e2129562a92bd1a09728486d5a23e70a36125202e5a3801206cd00f5cd8b8060008992215b418400000),
  (0x0, 0x14a25cc542440450164a920ad40ad4a85cf18ac2e65f2b847543e142c7b47f01b395244984024c0285654f3520a9a005ea420608600a68400000),
  (0x0, 0x152c16ec99b729072244e0ab828cc0380a58ea34651c337a3cf13783531a460dfb54e957ab1ed800236dc6977084c005ca069414403348400000),
  (0x0, 0xb0b129473c10c103576f54bc06c0f306e0893380ecd3e24b820c12b60287c5112e4628b9962f00414ed1ab06e08e805ab9c0f50158958400000),
  (0x0, 0x1c896e58427489d1b718ddd305e14a045eb5b2528da0a926c15b320b86a45aad8c15c7cf16403c0362ae9f8f0ac498058213a902698138400000),
  (0x0, 0x9a32031b993c28a3e6235ca0642dda570819290c9440c430509342307a975042874cd5e356ee003456c169d7a84a80563830574dd1028400000),
  (0x0, 0x1891ccd9aa122158c18492252e79a8b26ac8827ec899a6c604382635b80366903602a883724bc018382531e2addb805438a2a5ea46ab8400000),
  (0x0, 0x2114223d31042e06bc748ca8e408d42b6ea1fae3c70d2a10615394635a08288c30548ad4a8804002234b49bb5279400521a1175065dab8400000),
  (0x0, 0x83e301101136aa101048c1350e283ba28c969b72acbab3e49591621d68d0675318425d43176dc0196221c420225480509168756612318400000),
  (0x0, 0x81e7b0124276cc987826612724cd0974614f332055c022c28a2474906b95250bbd5c14d16125800d1841cad46d89004e4c7af15056b98400000),
  (0x0, 0x1b0d04b44426e4172320a55408261f8e5410b0c2a9c828349610d1e587854a00e3f7498e0a6c9400246d0f384a48b004c2931d646d49e8400000),
  (0x0, 0x1a2e2ac530a748c0101c159877cd1fbc24d80355c0539a5284920847028438d9d06808e00d5c04013746dcb85435c804a8193836a4d228400000),
  (0x0, 0x81116598253c1503f41060b2168050430399848469f2b1621b8a7ccc1114a0d83a78387a0742803510ad2b87879a8048a4a040861c3b8400000),
  (0x0, 0x20aa2ed5e0c7e8943f5ee42ba4cfc40422a1402082a114101128a643cb823a84cb34614a0801040311c5de84101210046301ad00bddbf8400000),
  (0x0, 0xdb242d81260c357925acdc3082f9aad74106895acdc0000a41255c442b83cc550b81009102ec400f0ed9eb8324e0004410a2d140001a8400000)
  ] : List (Nat × Nat)).map decodeUCertW18
set_option maxRecDepth 65536 in
private theorem sieve_aff_u2_c1_fast_w18_s0 :
    checkAffRangeULModPFastBoolW18 2 67 17 4 (dropCertsW18 0 sieveAffCertsU2C1W18) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve_aff_u2_c1_fast_w18_s1 :
    checkAffRangeULModPFastBoolW18 2 67 21 4 (dropCertsW18 4 sieveAffCertsU2C1W18) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve_aff_u2_c1_fast_w18_s2 :
    checkAffRangeULModPFastBoolW18 2 67 25 4 (dropCertsW18 8 sieveAffCertsU2C1W18) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve_aff_u2_c1_fast_w18_s3 :
    checkAffRangeULModPFastBoolW18 2 67 29 4 (dropCertsW18 12 sieveAffCertsU2C1W18) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve_aff_u2_c1_fast_w18_s4 :
    checkAffRangeULModPFastBoolW18 2 67 33 1 (dropCertsW18 16 sieveAffCertsU2C1W18) = true := by decide
private theorem sieve_aff_u2_c1_fast_w18 :
    checkAffRangeULModPFastBoolW18 2 67 17 17 sieveAffCertsU2C1W18 = true := by
  have h0 : checkAffRangeULModPFastBoolW18 2 67 17 4 sieveAffCertsU2C1W18 = true := sieve_aff_u2_c1_fast_w18_s0
  have h1 : checkAffRangeULModPFastBoolW18 2 67 17 8 sieveAffCertsU2C1W18 = true :=
    checkAffRangeULModPFastBoolW18_glue 2 67 4 4 17 sieveAffCertsU2C1W18 h0 sieve_aff_u2_c1_fast_w18_s1
  have h2 : checkAffRangeULModPFastBoolW18 2 67 17 12 sieveAffCertsU2C1W18 = true :=
    checkAffRangeULModPFastBoolW18_glue 2 67 8 4 17 sieveAffCertsU2C1W18 h1 sieve_aff_u2_c1_fast_w18_s2
  have h3 : checkAffRangeULModPFastBoolW18 2 67 17 16 sieveAffCertsU2C1W18 = true :=
    checkAffRangeULModPFastBoolW18_glue 2 67 12 4 17 sieveAffCertsU2C1W18 h2 sieve_aff_u2_c1_fast_w18_s3
  have h4 : checkAffRangeULModPFastBoolW18 2 67 17 17 sieveAffCertsU2C1W18 = true :=
    checkAffRangeULModPFastBoolW18_glue 2 67 16 1 17 sieveAffCertsU2C1W18 h3 sieve_aff_u2_c1_fast_w18_s4
  exact h4
private theorem sieve_aff_u2_c1_ok_w18 :
    checkAffRangeULModPBoolW18 2 67 17 17 sieveAffCertsU2C1W18 = true :=
  (checkAffRangeULModPFastBoolW18_eq 2 67 17 17 sieveAffCertsU2C1W18).symm.trans sieve_aff_u2_c1_fast_w18

private def sieveAffCertsU2C2W18 : List (List (Nat × Nat) × List (List Nat)) :=
  ([
  (0x45, 0x1ca50aa45394081f2e84b1f10320e0c020e032a722de9d80f941b4029abc840062e4c308957a0188c22704a44e1400342d4f2d70383810108000),
  (0x0, 0x213f442d11e7ccc3a122b4a0320a83a648910022c8813922c9e8a545c0ad56f13312aaca9135040316441eb252e808040d858380299118400000),
  (0x56, 0x103e6c20cb706c82b502bd9a5122992d0e557c214ccd267000f180c3ce99646ddae44cd3c0725803370c0c0e66d44003e08cb90c557810000000),
  (0x0, 0x193482fc0b95c695b752bd0862a7038a2ca91a368097a44a50b1b640820238791a25c514970e040325235d30801c5003c90708267cf2f8400000),
  (0xbc, 0x95e3452918544081698811482489746c122d54595a004ca112041609b3eed4933e69811209401c1a9c41122bd6803a247842e8e0918400000),
  (0x0, 0x33d0255aa40e653403ce858a5828593300df1f3e8d2ba3e521202818f16067c69020cc3816058029403c59f06c9880383d93f3a2522f8400000),
  (0x0, 0x1322407592d188483d0f00696727c5a700252b784594ae64c4c3f2235d422059a09830803310dc0045cecc2b1424d0036c890032548928400000),
  (0x0, 0xd846a7c4206c893c27ae5b9b680150f645543a4cccc2746c929618243ac645d5bc363ddc2604001a7eb0cbe4c48d8034b4ab354710118400000),
  (0x0, 0x1300300598c6aa86866a157bc3c484b166807a60c94e336a6089a1c0ccb55e01f9f7808d1236bc00020a8e942c7060032705124c4072b8400000),
  (0x0, 0x11ac00818a92ae8292149448504140876081d0d8419634526803354396051284bae5afdd1320e003610a9396410570030589942c3cd298400000),
  (0x0, 0x1295380c3063a3d72008c569710657b3380538162d8291310418b1e198144eae1327ea989d6e3c03f22d001a52b98002efc6077ac95828400000),
  (0x0, 0xba1af4a092100b104509fa872a81400e71f2602bd7841eb863434398a626ec83c100182f58f0031730049c04393002c8d70b26fda158400000),
  (0x0, 0x162a36a4f2e6c1589e461521f6480d1c3ac94915061ba65c4021c1e44fa07230b0d60a808a66d8024404099078695802a260401674ab38400000),
  (0x0, 0x4a4686982a465d33b34298b844357bb4e0982b827520c286ca0c3aa4d02207c693020d493744c0055008297062c7802904abf3cdd7a88400000),
  (0x0, 0x13ac14991972904aac2a8193354a912d1449e951501e9824401b13ce86c258d4fb41221e3a0c3801c1841c0428a96002620b2f0aad8b38400000),
  (0x0, 0x161d30fd9804c7c38b74b1bb778d5c8b28e089732121136220b2c8248a8682a0c2d06390ad10a00164c600bb0ed138024c1d3f00c093b8400000),
  (0x0, 0x1c20505c61c4e6200a32682b53690a2b844059f20f1b98524c28e122c02e363c2292c2cd1b28f800660b4d174a71e8022353ae16acd308400000)
  ] : List (Nat × Nat)).map decodeUCertW18
set_option maxRecDepth 65536 in
private theorem sieve_aff_u2_c2_fast_w18_s0 :
    checkAffRangeULModPFastBoolW18 2 67 34 4 (dropCertsW18 0 sieveAffCertsU2C2W18) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve_aff_u2_c2_fast_w18_s1 :
    checkAffRangeULModPFastBoolW18 2 67 38 4 (dropCertsW18 4 sieveAffCertsU2C2W18) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve_aff_u2_c2_fast_w18_s2 :
    checkAffRangeULModPFastBoolW18 2 67 42 4 (dropCertsW18 8 sieveAffCertsU2C2W18) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve_aff_u2_c2_fast_w18_s3 :
    checkAffRangeULModPFastBoolW18 2 67 46 4 (dropCertsW18 12 sieveAffCertsU2C2W18) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve_aff_u2_c2_fast_w18_s4 :
    checkAffRangeULModPFastBoolW18 2 67 50 1 (dropCertsW18 16 sieveAffCertsU2C2W18) = true := by decide
private theorem sieve_aff_u2_c2_fast_w18 :
    checkAffRangeULModPFastBoolW18 2 67 34 17 sieveAffCertsU2C2W18 = true := by
  have h0 : checkAffRangeULModPFastBoolW18 2 67 34 4 sieveAffCertsU2C2W18 = true := sieve_aff_u2_c2_fast_w18_s0
  have h1 : checkAffRangeULModPFastBoolW18 2 67 34 8 sieveAffCertsU2C2W18 = true :=
    checkAffRangeULModPFastBoolW18_glue 2 67 4 4 34 sieveAffCertsU2C2W18 h0 sieve_aff_u2_c2_fast_w18_s1
  have h2 : checkAffRangeULModPFastBoolW18 2 67 34 12 sieveAffCertsU2C2W18 = true :=
    checkAffRangeULModPFastBoolW18_glue 2 67 8 4 34 sieveAffCertsU2C2W18 h1 sieve_aff_u2_c2_fast_w18_s2
  have h3 : checkAffRangeULModPFastBoolW18 2 67 34 16 sieveAffCertsU2C2W18 = true :=
    checkAffRangeULModPFastBoolW18_glue 2 67 12 4 34 sieveAffCertsU2C2W18 h2 sieve_aff_u2_c2_fast_w18_s3
  have h4 : checkAffRangeULModPFastBoolW18 2 67 34 17 sieveAffCertsU2C2W18 = true :=
    checkAffRangeULModPFastBoolW18_glue 2 67 16 1 34 sieveAffCertsU2C2W18 h3 sieve_aff_u2_c2_fast_w18_s4
  exact h4
private theorem sieve_aff_u2_c2_ok_w18 :
    checkAffRangeULModPBoolW18 2 67 34 17 sieveAffCertsU2C2W18 = true :=
  (checkAffRangeULModPFastBoolW18_eq 2 67 17 34 sieveAffCertsU2C2W18).symm.trans sieve_aff_u2_c2_fast_w18

private def sieveAffCertsU2C3W18 : List (List (Nat × Nat) × List (List Nat)) :=
  ([
  (0x9a, 0x17916c895800905398700d9a77c088c148edf345451d830a80cbd02c07a06640b06664d58c7eec0043c21db56e1410020806301101f238400000),
  (0x0, 0x1512604df9b06d029b4e40f36407dd0704b4cc204148912629d404b0932f6aa4b814e2c6011c100118061322261ca001ec412362c98398400000),
  (0x0, 0xb1c648c0b714344196abd7ab826d2a382ad24146e58246a2df8e14fc1066cd5c15525603f645400b7250db76c38f801c88f96247c7388400000),
  (0x0, 0x22a28cd2a04a40b0e2861f2c3c51f3402dc9b106fce001c00ab07ee5237265968a1cd5c1e4b0001c140863a7821b001a88da74c01a808400000),
  (0xbc, 0x1074c0d0d1cc1d986cfc8405a9162a48dc12e5a3d3aa6e5073114ec4a1284dd8f80ccea1765c04264800363e9cc8018a1fa7366462f8400000),
  (0x0, 0x6221829c8984d50936e19b8d30e950238794006804c2872c5f9d488572530f15357c000b43c9c023309c29a42bc48016e4cb9546c5128400000),
  (0x0, 0x1e923f08a2e4ed19b13e04c0a3078b1844edc2270746be48de0354621b80305d60b62260376c2402e1c085b81ec8f001489d3b6a14f8c8400000),
  (0x0, 0x11870599b1508210c1c9819478b53322cdc8081625d1d72f09bb3e08d054d04b365b01fae82680297008bbc0704580129428910985078400000),
  (0x0, 0x160e4480f0e78184847208eb70ab92b01c2c18284bcc02526d7ba1ee47a702f57a76af97a6548c01f361cc877ec420010853065504d288400000),
  (0x0, 0xea656ac62b12b0e8e82e87a482e4c1322345a876d0032509991f164100c582db8e827899420440413a91eb86e4df000ecdfa78444d9d8400000),
  (0x9b, 0xa22cf40002c415a1024c29e4e8d2a72adcb0866646973ec51820209f851cb00000091f362a640055cf593d52b99000cf08aa6cb12128400000),
  (0x0, 0x19bf5844e8a8018485130443934b8fbc1451a2342e869d3230b9a1f0989a6094e8a0300ea02690002183a0356ce9e000a3c2c26a995378400000),
  (0xbc, 0x271aed01348810a96aacc2544a133906640290e4d52c487d3bc846472e4c058ab58b5cb66e1802e4e8442374dc4000888e1d305cfa48400000),
  (0x0, 0x3b800ecd0e6e300b780d96af70a43ba72dc49406500a972352ad30c4ac27ec83050c9828d3e8402a1905b270a8d08006dd32182685368400000),
  (0x0, 0x1e190e4d7c10809cb10440ebe6e19fbd605cdb802bc53c68bd5a970a1f94749511708f932a7c6001f7c087ad7c5c80004ec996701c7948400000),
  (0x0, 0x114156000005a858196a9a0975c55ab300b80800000f00000159082d04af66599104a340b318740112a284816621000020000048000008400000)
  ] : List (Nat × Nat)).map decodeUCertW18
set_option maxRecDepth 65536 in
private theorem sieve_aff_u2_c3_fast_w18_s0 :
    checkAffRangeULModPFastBoolW18 2 67 51 4 (dropCertsW18 0 sieveAffCertsU2C3W18) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve_aff_u2_c3_fast_w18_s1 :
    checkAffRangeULModPFastBoolW18 2 67 55 4 (dropCertsW18 4 sieveAffCertsU2C3W18) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve_aff_u2_c3_fast_w18_s2 :
    checkAffRangeULModPFastBoolW18 2 67 59 4 (dropCertsW18 8 sieveAffCertsU2C3W18) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve_aff_u2_c3_fast_w18_s3 :
    checkAffRangeULModPFastBoolW18 2 67 63 4 (dropCertsW18 12 sieveAffCertsU2C3W18) = true := by decide
private theorem sieve_aff_u2_c3_fast_w18 :
    checkAffRangeULModPFastBoolW18 2 67 51 16 sieveAffCertsU2C3W18 = true := by
  have h0 : checkAffRangeULModPFastBoolW18 2 67 51 4 sieveAffCertsU2C3W18 = true := sieve_aff_u2_c3_fast_w18_s0
  have h1 : checkAffRangeULModPFastBoolW18 2 67 51 8 sieveAffCertsU2C3W18 = true :=
    checkAffRangeULModPFastBoolW18_glue 2 67 4 4 51 sieveAffCertsU2C3W18 h0 sieve_aff_u2_c3_fast_w18_s1
  have h2 : checkAffRangeULModPFastBoolW18 2 67 51 12 sieveAffCertsU2C3W18 = true :=
    checkAffRangeULModPFastBoolW18_glue 2 67 8 4 51 sieveAffCertsU2C3W18 h1 sieve_aff_u2_c3_fast_w18_s2
  have h3 : checkAffRangeULModPFastBoolW18 2 67 51 16 sieveAffCertsU2C3W18 = true :=
    checkAffRangeULModPFastBoolW18_glue 2 67 12 4 51 sieveAffCertsU2C3W18 h2 sieve_aff_u2_c3_fast_w18_s3
  exact h3
private theorem sieve_aff_u2_c3_ok_w18 :
    checkAffRangeULModPBoolW18 2 67 51 16 sieveAffCertsU2C3W18 = true :=
  (checkAffRangeULModPFastBoolW18_eq 2 67 16 51 sieveAffCertsU2C3W18).symm.trans sieve_aff_u2_c3_fast_w18

set_option maxRecDepth 65536 in
private theorem sieve_inf_and_inv_u2_fast_w18 :
    checkAllInvModPBoolW18 67 67 = true ∧
    checkULModPNat12FastBoolW18 67 2 1 0 sieveInfCertU2W18 = true := by decide
private theorem sieve_inf_and_inv_u2_ok_w18 :
    checkAllInvModPBoolW18 67 67 = true ∧
    checkULModPNat12BoolW18 67 2 1 0 sieveInfCertU2W18 = true :=
  ⟨sieve_inf_and_inv_u2_fast_w18.1,
   (checkULModPNat12FastBoolW18_eq 67 2 1 0 sieveInfCertU2W18).symm.trans sieve_inf_and_inv_u2_fast_w18.2⟩

private def sieveInfCertU3W18 : List (Nat × Nat) × List (List Nat) :=
  decodeUCertW18 (0x0, 0x9915420c9f2654aa95a3401a4c616a970ccba35c0cd0e3419a013850d9050b89955e08e94421402274194ae268d780744179940b50b57400000)

private def sieveAffCertsU3C0W18 : List (List (Nat × Nat) × List (List Nat)) :=
  ([
  (0x9b896a563925, 0xf201ae00001628e3538e002f38080007400001040061f74d15973ad40806480000000000000000000000000000000064000000000000000043a),
  (0x795645, 0x9916c888143c84a941019c800050fba4ea8531006418064013053ce402100e8f85320400c00e4294325dc0004000af743581f0400c8002e8000),
  (0x0, 0x1a19742d11f182071814245345e84eae3aa4b3a548001942d8e99120c3960abcda2226959c1440009586818f284da8072c55377488d057400000),
  (0x0, 0x11d1e856a11ebc187740c6951e90d1168399182e00e0026010b62e993b720587331c155b402d400940ccab00ac1b80700991a3c014007400000),
  (0x0, 0x8124440898624502c14419ad124dc0a461d6113ea40b91e4c310746458d1860d3a2eadaa0061002d0ee44084ac9c006e685b572096287400000),
  (0x0, 0x130a4045231702cb90243d2b95e7043a548d6a40401b2c3894eaf06045b4269c63726255071030038607460b5a790806c18a8a083cf967400000),
  (0x0, 0x13353e40a1f662d3a90634db13ad08324c790b80650d9764485036a64a894e3498520d859c067001c3abd7374031c806ab92083e904a97400000),
  (0x0, 0x2113a09b8a6c8981628b818610c439f0c650a932e84b51ed80135065a9b4ca8d264434bb3307401c024d3172019000684133262196057400000),
  (0x0, 0x2af2a414002a257186cbd99e5cb882e481dbba7280c0a18050924c78c931c90a8e60757266a0400d6e597014a44e0066b0a9b44c57ba7400000),
  (0x0, 0x1c2b1c8938408493374a7cfb112c9d1f4e4023010590906a7cb1b6a381926e998192240817264c0171eb078538b9300649062132ac31c7400000),
  (0x67, 0xdb5225c8265c04793544808218048932474039145dc1c56c438520788b270a8b8052b1734360c0083878422542d70062990b9047c80a7400000),
  (0x0, 0x8a7458e353a950833e1c9aa5a9d2ac12ac61e447c1a41240c8c60ad0a52cb1a0a5e94f1b24a4030582c0af6ed0780601dc226e5d92b7400000),
  (0x0, 0x140522197051048ea164e148002d95181645ba73a2562e2271b273259c2c0230a2a1095639441c03a2e450311c51d005e395ad1c3551f7400000),
  (0x0, 0x151864e142c127c136583d10c3400d38088148236a91300448111644c90f7058b172629cb70ccc02366d409f52b58805c059a0302dca97400000),
  (0x0, 0x4ad229cb076cc97aa2c20b1274e45173cc02305e211b65c85a095e7898e00a54921a91b321c5801874c990724b48005a7d8ac2e1469a7400000),
  (0x0, 0x9953e3dcb14a286ac1adc699307841d160828300b872e4ea1ab252c9b9640a86921431cb3345402d0ed14a3604058058a41175834a137400000),
  (0x0, 0x8a130356886ae030502455a056bca110ad0f8c56512b4622921d2c1868d44c8fa3461d405743c02118d41281a2c7005688f1f2a1c5317400000),
  (0x0, 0x10b50ae4e253061b1e4ce142702883b20ca989372ccf2c3e094952e98b21265c22502b12884e2402e60ac6af00e510054a909e383ce397400000),
  (0x0, 0x1510183c785429478c324ceb546a0aa0684039b62e822a24a932b4ead7ab56d13151490c0606c401c56a041c4e509805245b376c454917400000),
  (0x0, 0x1a2d3e54a1810cce306ca598d3e806b034cd1113c79cb908bc5a54ad8c385ea410e025d40810680011c709ba702490050544850209b8c7400000)
  ] : List (Nat × Nat)).map decodeUCertW18
set_option maxRecDepth 65536 in
private theorem sieve_aff_u3_c0_fast_w18_s0 :
    checkAffRangeULModPFastBoolW18 3 59 0 4 (dropCertsW18 0 sieveAffCertsU3C0W18) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve_aff_u3_c0_fast_w18_s1 :
    checkAffRangeULModPFastBoolW18 3 59 4 4 (dropCertsW18 4 sieveAffCertsU3C0W18) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve_aff_u3_c0_fast_w18_s2 :
    checkAffRangeULModPFastBoolW18 3 59 8 4 (dropCertsW18 8 sieveAffCertsU3C0W18) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve_aff_u3_c0_fast_w18_s3 :
    checkAffRangeULModPFastBoolW18 3 59 12 4 (dropCertsW18 12 sieveAffCertsU3C0W18) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve_aff_u3_c0_fast_w18_s4 :
    checkAffRangeULModPFastBoolW18 3 59 16 4 (dropCertsW18 16 sieveAffCertsU3C0W18) = true := by decide
private theorem sieve_aff_u3_c0_fast_w18 :
    checkAffRangeULModPFastBoolW18 3 59 0 20 sieveAffCertsU3C0W18 = true := by
  have h0 : checkAffRangeULModPFastBoolW18 3 59 0 4 sieveAffCertsU3C0W18 = true := sieve_aff_u3_c0_fast_w18_s0
  have h1 : checkAffRangeULModPFastBoolW18 3 59 0 8 sieveAffCertsU3C0W18 = true :=
    checkAffRangeULModPFastBoolW18_glue 3 59 4 4 0 sieveAffCertsU3C0W18 h0 sieve_aff_u3_c0_fast_w18_s1
  have h2 : checkAffRangeULModPFastBoolW18 3 59 0 12 sieveAffCertsU3C0W18 = true :=
    checkAffRangeULModPFastBoolW18_glue 3 59 8 4 0 sieveAffCertsU3C0W18 h1 sieve_aff_u3_c0_fast_w18_s2
  have h3 : checkAffRangeULModPFastBoolW18 3 59 0 16 sieveAffCertsU3C0W18 = true :=
    checkAffRangeULModPFastBoolW18_glue 3 59 12 4 0 sieveAffCertsU3C0W18 h2 sieve_aff_u3_c0_fast_w18_s3
  have h4 : checkAffRangeULModPFastBoolW18 3 59 0 20 sieveAffCertsU3C0W18 = true :=
    checkAffRangeULModPFastBoolW18_glue 3 59 16 4 0 sieveAffCertsU3C0W18 h3 sieve_aff_u3_c0_fast_w18_s4
  exact h4
private theorem sieve_aff_u3_c0_ok_w18 :
    checkAffRangeULModPBoolW18 3 59 0 20 sieveAffCertsU3C0W18 = true :=
  (checkAffRangeULModPFastBoolW18_eq 3 59 20 0 sieveAffCertsU3C0W18).symm.trans sieve_aff_u3_c0_fast_w18

private def sieveAffCertsU3C1W18 : List (List (Nat × Nat) × List (List Nat)) :=
  ([
  (0x9a, 0x140d547d4805a7173002e4c0f02c51a748bd12920616b9284d01c66b8f1f2cc50184e452184cb40191a111193234b804e7cd241c093a87400000),
  (0x0, 0x121c2e91a10504098140613a47000b2c1621b3a1a0138a6cb82b43c40e0060e9d346828f1c2a900122e8851742bd9004c61aab26c428d7400000),
  (0x0, 0x19064e694a322202b36a1c2936a8878d405cbb212e84b12204736187818f60a42280c7123002640255c092b310692804aa8499622953a7400000),
  (0x0, 0xc301a8c3032484e9052c56155ec089c0e3538e3a7158338406826868e0012cc41d066941c1c6c0032040b276838a004828c1c1ee0fab7400000),
  (0x0, 0xb274c3962028c8c8f28a53293680a9e2261298506c9aa26087ba1ab90077410c2a4839a3a16b8010089081000bce8046551004e454397400000),
  (0x0, 0x8294c5c3b254e8e0d340578a3ab9b3a4c0828e584d51658cc41e52944a1029062b525000f024401a4e904a1641d500445843120947887400000),
  (0x0, 0x1aa6814821044932926c8f8520bdb0a2a00aa60addd10042989d52c18a656bd99854c1b236ee403020a531420e5b00424131e00adcb17400000),
  (0x0, 0x15236eb49b74a2011358e5539405cc8a5010d84245c91874d0a1a5c7943032d58b94abd08c0ac003608c88202899a004028b28508c0877400000),
  (0x0, 0x11273080d231a5911130489990c447a15664590224d3820c2191906c452e34e923864d0409548c00d629cb1f6cd44003e2c80526e5ab37400000),
  (0x0, 0x99b34d412e58112081eb5b25147168864403b12ee548000ad2973284bae204099c300410f385002a1e6c31f5848c003c4110f22000107400000),
  (0x45, 0x1818488d68246c53b168d06093684c1b70890166ee5235667cf8e5455c9a740073260e59825a00a2a5cbd48630340233ad000f4a0908100e8000),
  (0x0, 0x10af140dd2416483142811d364cb1cb534dc18f0a04a041e24dae58319944818c1552e5c392c8c0156e05b181e8d98038a5b964cdd6327400000),
  (0x0, 0x16b35850b28022d3a34ad502c1a944b62e2c6915c28baa48c931e52e188a4c40da6582c4876ac001d744da2546b038036599094644b897400000),
  (0x0, 0xda274e999e7210e9a32ac1b670e4f016ce598026d831d6a6cf164810a1f6c09d1d6a8939460e40342eacfb54a18280340582268783207400000),
  (0x67, 0x101c6695c8944a159e4e5d01a66d831e268c0385059ab85ead5180add7355ea172e3a50b332a4400d48e53a556dc8803264a9c0a0c6107400000),
  (0x0, 0x837705c232401d6964a184333e6582c1ce471606c450628a062d2ce811720a44146069a2e42b80223c057050024f003039a1360d53937400000),
  (0x0, 0x10345ac049032c8ea2188531a2ec519230956b81c54d0c349868e48a8a1f4a74f28041d928386c0245c2093110dd3802e3921640bd0957400000),
  (0x0, 0xb1824c871c39a82324cba712a45124e7168f68a45160a900125ae5a1b544878c3618c174e6402156687875438b002c8d48b6095b177400000),
  (0xbc, 0x213405009589dcac1ee18b740b8f803c1822644609b75c2c7b010e01a22ed400506796343290031741952430744802a51a1a4e106b07400000),
  (0x0, 0x11324588aa16e45873cb46956cdd62130c58996a9150a1078bb802254b8600923a58689a356b400f1ae53af5c1d200283182820c599d7400000)
  ] : List (Nat × Nat)).map decodeUCertW18
set_option maxRecDepth 65536 in
private theorem sieve_aff_u3_c1_fast_w18_s0 :
    checkAffRangeULModPFastBoolW18 3 59 20 4 (dropCertsW18 0 sieveAffCertsU3C1W18) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve_aff_u3_c1_fast_w18_s1 :
    checkAffRangeULModPFastBoolW18 3 59 24 4 (dropCertsW18 4 sieveAffCertsU3C1W18) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve_aff_u3_c1_fast_w18_s2 :
    checkAffRangeULModPFastBoolW18 3 59 28 4 (dropCertsW18 8 sieveAffCertsU3C1W18) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve_aff_u3_c1_fast_w18_s3 :
    checkAffRangeULModPFastBoolW18 3 59 32 4 (dropCertsW18 12 sieveAffCertsU3C1W18) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve_aff_u3_c1_fast_w18_s4 :
    checkAffRangeULModPFastBoolW18 3 59 36 4 (dropCertsW18 16 sieveAffCertsU3C1W18) = true := by decide
private theorem sieve_aff_u3_c1_fast_w18 :
    checkAffRangeULModPFastBoolW18 3 59 20 20 sieveAffCertsU3C1W18 = true := by
  have h0 : checkAffRangeULModPFastBoolW18 3 59 20 4 sieveAffCertsU3C1W18 = true := sieve_aff_u3_c1_fast_w18_s0
  have h1 : checkAffRangeULModPFastBoolW18 3 59 20 8 sieveAffCertsU3C1W18 = true :=
    checkAffRangeULModPFastBoolW18_glue 3 59 4 4 20 sieveAffCertsU3C1W18 h0 sieve_aff_u3_c1_fast_w18_s1
  have h2 : checkAffRangeULModPFastBoolW18 3 59 20 12 sieveAffCertsU3C1W18 = true :=
    checkAffRangeULModPFastBoolW18_glue 3 59 8 4 20 sieveAffCertsU3C1W18 h1 sieve_aff_u3_c1_fast_w18_s2
  have h3 : checkAffRangeULModPFastBoolW18 3 59 20 16 sieveAffCertsU3C1W18 = true :=
    checkAffRangeULModPFastBoolW18_glue 3 59 12 4 20 sieveAffCertsU3C1W18 h2 sieve_aff_u3_c1_fast_w18_s3
  have h4 : checkAffRangeULModPFastBoolW18 3 59 20 20 sieveAffCertsU3C1W18 = true :=
    checkAffRangeULModPFastBoolW18_glue 3 59 16 4 20 sieveAffCertsU3C1W18 h3 sieve_aff_u3_c1_fast_w18_s4
  exact h4
private theorem sieve_aff_u3_c1_ok_w18 :
    checkAffRangeULModPBoolW18 3 59 20 20 sieveAffCertsU3C1W18 = true :=
  (checkAffRangeULModPFastBoolW18_eq 3 59 20 20 sieveAffCertsU3C1W18).symm.trans sieve_aff_u3_c1_fast_w18

private def sieveAffCertsU3C2W18 : List (List (Nat × Nat) × List (List Nat)) :=
  ([
  (0x0, 0x19906e707844e8c5330c894073a7dc3314e13945a04eb11e0961b3ee949b002daa65801a0336680281221b260a31480262dd363a296397400000),
  (0x0, 0x1aa10ac19a834410b4261438026749185cd139508c919b6c051a7268cea9485d6896681c8c4ec4016061d197147540024c421c2e802ba7400000),
  (0x0, 0x4374ec5a2646cd1320ac8db368516370698f972290f92563988524a8087207021f6a44d9d5c2400b12d481a14b0c8022b98ac36a482d7400000),
  (0x0, 0x17af503ce2c2845b0c08259b4325ceb2023c78858814a8586883528a0e2a40150af58c1520143c0250020d172e99680209172a224c7a17400000),
  (0x0, 0x15b740353b9302072a4e402a43485d110ab1392484539b3e31d293a4062b3e71c1d0e7170408540092014d1938898001e715ac2680e2f7400000),
  (0x0, 0x39d2444c83027cc9646e02933cc561f287d8aa6a4012c4e49522085db346050e022e9ceb15c5801a627c60054dd5801c01428703ca297400000),
  (0x0, 0x39d1445c0a7499cb91aa441948dca2a669580948c58aa1c386b122c540408c1d2132cc08242cc01e3860db0582c5001a84d0012456ad7400000),
  (0x0, 0x13b61c84ead0a481a1404520524b81203650c00189d10b5815387522000b18c84003291205281c02b14949193ad4080186892230c07b67400000),
  (0x0, 0xe8d18a802e54bc39908949a45475ba2266c5a32c89b1e3abd88f14d57381ca07b7380cb8438a402d106429352cd60016a52a60874f0c7400000),
  (0x0, 0x70d3c0d0ad049968842d0bb33ab13394e557b75a4412b08804921ecd4147080b06088d7b1260c026106d28310cc68014054387041b9b7400000),
  (0xbc, 0x130a643b640a8ea82a255b00a1489e2ac46113ab058e484cfb252c190a50106b154d159d5c4c01262418193a88a801244b945eb4ba87400000),
  (0x0, 0xe2d3ee4fb526599a330856b712e96ab2a41b2b1091c3064bda8208a8d06746c3393ae0c0d6c040352ac16210278f801048a1d042c48c7400000),
  (0x0, 0x1ba91c8c1b668e0f3768d148412a99a2663ce002e2929822dd89b347061944495b062b8f87147400f2e683a320e8d800e610b62a8d5047400000),
  (0x0, 0x6b73e8149e6c40eb43694b337038a891258d2b74dcc3a5e3c41074c01a4003403a2e7cd03487002b4c7d1022a4c1000cac9a1440462c7400000),
  (0x9b, 0xaa83ad000002504ad70e9012649500e32393950c9952f4a39a0d143c4234685a0d14d89a91c300302a9d21f40e8d000a01b152230b2d7400000),
  (0x0, 0x1289189ce2a2ea8a0610ac0922e04eb85808d9e5ce992116c42b3041cd035c3d5216ca9b874210034226d3276e4818008c5612106980a7400000),
  (0xbc, 0x3354616372681d23207d7322029d0556c841a68ddc2632609073cd96915040e3a3a9961140d400e16794083c682000624b0804551237400000),
  (0x0, 0x109938c8c82681030114545b8502019e2ea96ae2e4042b16a14126051d1b64b090524247122640008726da286ed030004585a964418137400000),
  (0x0, 0x198f6400000262d41f3280f8e14a170674280800000980000092c0c95ca05ea892d740c4b670140135444c096cc060002000004e000007400000)
  ] : List (Nat × Nat)).map decodeUCertW18
set_option maxRecDepth 65536 in
private theorem sieve_aff_u3_c2_fast_w18_s0 :
    checkAffRangeULModPFastBoolW18 3 59 40 4 (dropCertsW18 0 sieveAffCertsU3C2W18) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve_aff_u3_c2_fast_w18_s1 :
    checkAffRangeULModPFastBoolW18 3 59 44 4 (dropCertsW18 4 sieveAffCertsU3C2W18) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve_aff_u3_c2_fast_w18_s2 :
    checkAffRangeULModPFastBoolW18 3 59 48 4 (dropCertsW18 8 sieveAffCertsU3C2W18) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve_aff_u3_c2_fast_w18_s3 :
    checkAffRangeULModPFastBoolW18 3 59 52 4 (dropCertsW18 12 sieveAffCertsU3C2W18) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve_aff_u3_c2_fast_w18_s4 :
    checkAffRangeULModPFastBoolW18 3 59 56 3 (dropCertsW18 16 sieveAffCertsU3C2W18) = true := by decide
private theorem sieve_aff_u3_c2_fast_w18 :
    checkAffRangeULModPFastBoolW18 3 59 40 19 sieveAffCertsU3C2W18 = true := by
  have h0 : checkAffRangeULModPFastBoolW18 3 59 40 4 sieveAffCertsU3C2W18 = true := sieve_aff_u3_c2_fast_w18_s0
  have h1 : checkAffRangeULModPFastBoolW18 3 59 40 8 sieveAffCertsU3C2W18 = true :=
    checkAffRangeULModPFastBoolW18_glue 3 59 4 4 40 sieveAffCertsU3C2W18 h0 sieve_aff_u3_c2_fast_w18_s1
  have h2 : checkAffRangeULModPFastBoolW18 3 59 40 12 sieveAffCertsU3C2W18 = true :=
    checkAffRangeULModPFastBoolW18_glue 3 59 8 4 40 sieveAffCertsU3C2W18 h1 sieve_aff_u3_c2_fast_w18_s2
  have h3 : checkAffRangeULModPFastBoolW18 3 59 40 16 sieveAffCertsU3C2W18 = true :=
    checkAffRangeULModPFastBoolW18_glue 3 59 12 4 40 sieveAffCertsU3C2W18 h2 sieve_aff_u3_c2_fast_w18_s3
  have h4 : checkAffRangeULModPFastBoolW18 3 59 40 19 sieveAffCertsU3C2W18 = true :=
    checkAffRangeULModPFastBoolW18_glue 3 59 16 3 40 sieveAffCertsU3C2W18 h3 sieve_aff_u3_c2_fast_w18_s4
  exact h4
private theorem sieve_aff_u3_c2_ok_w18 :
    checkAffRangeULModPBoolW18 3 59 40 19 sieveAffCertsU3C2W18 = true :=
  (checkAffRangeULModPFastBoolW18_eq 3 59 19 40 sieveAffCertsU3C2W18).symm.trans sieve_aff_u3_c2_fast_w18

set_option maxRecDepth 65536 in
private theorem sieve_inf_and_inv_u3_fast_w18 :
    checkAllInvModPBoolW18 59 59 = true ∧
    checkULModPNat12FastBoolW18 59 3 1 0 sieveInfCertU3W18 = true := by decide
private theorem sieve_inf_and_inv_u3_ok_w18 :
    checkAllInvModPBoolW18 59 59 = true ∧
    checkULModPNat12BoolW18 59 3 1 0 sieveInfCertU3W18 = true :=
  ⟨sieve_inf_and_inv_u3_fast_w18.1,
   (checkULModPNat12FastBoolW18_eq 59 3 1 0 sieveInfCertU3W18).symm.trans sieve_inf_and_inv_u3_fast_w18.2⟩

private def sieveInfCertU4W18 : List (Nat × Nat) × List (List Nat) :=
  decodeUCertW18 (0x0, 0x9925049a0c5e78b110631d280e518222a30b8018bc0b432851b1605cb034a4c70362505b33c8c00b741101a20c448074a5b00721d11a7400000)

private def sieveAffCertsU4C0W18 : List (List (Nat × Nat) × List (List Nat)) :=
  ([
  (0x9b896a563925, 0x1bae70e00006288e1f18e0020620800074000330400d8a749d21f3a7c0801e94000000000000000000000000000000054000000000000000083a),
  (0x795645, 0xd296c3029c3cc18146419c800048faa4e81c3940b81802801a0f28e400100e8317600402800511a76a7dc00260130974413290401c8002e8000),
  (0x0, 0xcb75ad17b4228d2a80c558285e396132c280ae147021c3cbdd141cc8b0e485cf1d3a2d49e16d400732857b22ad110072501266c7ce8c7400000),
  (0x0, 0x99d224d92108e538016dd4a10e0140e4a6dcac406d19d5a1410646607b520c51071eb5a900a440043ed8cb10c0c18070dd23a2e787367400000),
  (0x0, 0x15396260d86380599a4e65d3172a09140648502168083944dc2a96ca0f383a9c12c42b50a10a70034501042824988806e84a955408c847400000),
  (0x0, 0x9556859215894ba000202a472dd4064a85ab6227561904c071a4888d0746e9ca816550933e6400a424c829429d8806c7d9b81c89c8b7400000),
  (0x0, 0xcaf72601a52e84eae389c80270801251845107082d5a3266d5851649394580c53306e5ca7024c0344a2849d68e8f806a71a0b1e614207400000),
  (0x0, 0x99a288ca932a517b4707108a0841c8848ad9ab2ea15211ea958a02a0f1a0a1469c1e48a992a6801b40283a538a918068a078020696117400000),
  (0x0, 0x19856e8522c12d5b8f502408f22e872b3ce578f4c391182c30022467039a1cdd6865ae5c126c1c0050cb5912527d300662d601308d2af7400000),
  (0x0, 0x9081cb5bb91ed8b0d387c91a084c8106841b066a3daba46e173020205ab0c883032c306850e3c00b1439ca462b0080642052e0a04c037400000),
  (0x0, 0x16b642dce1d0848f363a11b934e952a052d938960550145cb97166e2cf090c406083cc8886725401a66a040c3ed5b0062d9509349c68d7400000),
  (0x0, 0x5b432054a01401394040851f707861530a17896ca81a85e588a2464861014750110cc458c0ccc00326b072d1a1908060c4bac6e4c6257400000),
  (0x0, 0x102e28b04b06409510686c79a02c402e70a539214915981ee13ba581539b0e54f8b60292b114c40296485aa310796805ee14221e8d6037400000),
  (0x0, 0x265e3d7a2001cf8a0a9928c10e4cb80e09b0d5a4c3172ce51804e69185368d037505c4273c0c00c7438a8744812805c7cd0668912827400000),
  (0x0, 0xb03305869e5249c2704e00a56a446921ab041522555a714e40b66c2192c2a3d1173609a05189000c18899ab1c317805a40e881e518827400000),
  (0x0, 0x14871e8c33644300154a2d8a40298ca34ab0fa80a8d5175e5193a121ce8366b95325a05c9142740355c3c807300120058ad81d20906277400000),
  (0x0, 0xb855cd4037541960474d449d74aca825008c3a6a949370ee512b600898b00b9b8b1c5d73816b80104289c884024980561c31a5011a027400000),
  (0x0, 0x9f28d8b840e3c7110aad58b0a1d6802c083ac1c5988112140326e8cb0b06c583122002b46610036105598b3a202005450b2112e99367400000),
  (0x0, 0x1d1b1e2c3123c4081946914b318a022e324cab916d419b5a115b70e1c80f10cd29f54c4d9b52c000b5c00b0906c4f0052c952f6e807377400000),
  (0x0, 0xc26301c6853668c0472d43036688bb50e4db950099a103e11baa206c61314049b0225d030341403532481b35ed0800507d7100cace377400000)
  ] : List (Nat × Nat)).map decodeUCertW18
set_option maxRecDepth 65536 in
private theorem sieve_aff_u4_c0_fast_w18_s0 :
    checkAffRangeULModPFastBoolW18 4 59 0 4 (dropCertsW18 0 sieveAffCertsU4C0W18) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve_aff_u4_c0_fast_w18_s1 :
    checkAffRangeULModPFastBoolW18 4 59 4 4 (dropCertsW18 4 sieveAffCertsU4C0W18) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve_aff_u4_c0_fast_w18_s2 :
    checkAffRangeULModPFastBoolW18 4 59 8 4 (dropCertsW18 8 sieveAffCertsU4C0W18) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve_aff_u4_c0_fast_w18_s3 :
    checkAffRangeULModPFastBoolW18 4 59 12 4 (dropCertsW18 12 sieveAffCertsU4C0W18) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve_aff_u4_c0_fast_w18_s4 :
    checkAffRangeULModPFastBoolW18 4 59 16 4 (dropCertsW18 16 sieveAffCertsU4C0W18) = true := by decide
private theorem sieve_aff_u4_c0_fast_w18 :
    checkAffRangeULModPFastBoolW18 4 59 0 20 sieveAffCertsU4C0W18 = true := by
  have h0 : checkAffRangeULModPFastBoolW18 4 59 0 4 sieveAffCertsU4C0W18 = true := sieve_aff_u4_c0_fast_w18_s0
  have h1 : checkAffRangeULModPFastBoolW18 4 59 0 8 sieveAffCertsU4C0W18 = true :=
    checkAffRangeULModPFastBoolW18_glue 4 59 4 4 0 sieveAffCertsU4C0W18 h0 sieve_aff_u4_c0_fast_w18_s1
  have h2 : checkAffRangeULModPFastBoolW18 4 59 0 12 sieveAffCertsU4C0W18 = true :=
    checkAffRangeULModPFastBoolW18_glue 4 59 8 4 0 sieveAffCertsU4C0W18 h1 sieve_aff_u4_c0_fast_w18_s2
  have h3 : checkAffRangeULModPFastBoolW18 4 59 0 16 sieveAffCertsU4C0W18 = true :=
    checkAffRangeULModPFastBoolW18_glue 4 59 12 4 0 sieveAffCertsU4C0W18 h2 sieve_aff_u4_c0_fast_w18_s3
  have h4 : checkAffRangeULModPFastBoolW18 4 59 0 20 sieveAffCertsU4C0W18 = true :=
    checkAffRangeULModPFastBoolW18_glue 4 59 16 4 0 sieveAffCertsU4C0W18 h3 sieve_aff_u4_c0_fast_w18_s4
  exact h4
private theorem sieve_aff_u4_c0_ok_w18 :
    checkAffRangeULModPBoolW18 4 59 0 20 sieveAffCertsU4C0W18 = true :=
  (checkAffRangeULModPFastBoolW18_eq 4 59 20 0 sieveAffCertsU4C0W18).symm.trans sieve_aff_u4_c0_fast_w18

private def sieveAffCertsU4C1W18 : List (List (Nat × Nat) × List (List Nat)) :=
  ([
  (0x0, 0x9850248a874c406a76a397194aa5a0842c99aa3c3159808841924cc1aba00c1ba6149db2274500325ea4e0914d4d804ee84281e8db9a7400000),
  (0x0, 0xfae665dd003e80e932428e2e2e052380a54a276c9521616ad80804617b740d962f7229021484002f646568e22e59804ce03162c958107400000),
  (0x0, 0xc0e12914a55018f8908005b336191125e4cc376a35438329cd075ed442c309c49d6a8ccad1ae4002682599446317004a6cc09240d1147400000),
  (0x0, 0x70e7054204627dbba482502d1e1c216386c5953e545a33ce961f467cd35183c99b4680210443001932283971e0d6004844c225e60e817400000),
  (0x0, 0x17a466512b566349090adc69f4224f0b149400a3008e8944e9b1d1429b10368029f1034c892c6c038265802f1ad9a004675c843ac8c817400000),
  (0x0, 0x140d1054eb5688d0b304dd82f24d14a93e90d2914c0f821c14a89047908a3e149a9149c78026040033ec44254a95c8044e0a1136e56b67400000),
  (0x0, 0x1c20147470568b0f94502973a4e1890962bd8170e3d79d06a420000a170d3cb8f12449519f44b4003204941f1825800421d3271679c127400000),
  (0x9b, 0xc1a32cc0004a209940e8c1393a4809c02855216e952b800511a302e9a8b246c58b04dd8373ea4006604181a0e88a0040c82962c0c0277400000),
  (0x0, 0xb991a3011f140890e20301b254b411e2c440b414e48024cb971316d5317348428a0ac89865624020125472f561da803ed979e54e4a8d7400000),
  (0x0, 0x110552c8c9f26e15a0485501738904346cd0a901044f8000c530c56248b54c7c79e6a4539a30580092c6cf9f4ec94803cd0d0b360000a7400000),
  (0x45, 0x1a942a58515129958f34756a612b0aba2a7469c3040d240c6c5964644aad740011b02bc7243a00b005601c8712740123a68d83529870100e8000),
  (0x0, 0x148c2400b2f4a7580b424451b0c74aab0cb4c8016b08a71e4cea92a6868e705cb0a2e64e05162400e20e4e824cac3003800d1b52516287400000),
  (0x0, 0xb396c1d69936596ae6068c2724d0b2014d0cb446d8a1a021d80e5c2118e58d03ba688c4241ca400c34bc32a6c6538036013274c85d347400000),
  (0x0, 0x89248a0012269938c563dc826ea84af2c785964260ab440111150a8ce894eb9d2a32d842658b40381644da9188058034e0d114a1cdb77400000),
  (0x0, 0x15172c354940a315371ea038e729031132a80185e697ad242970c2ab58b7004152e74112356e040150461a2d1a201003258f0d16394b17400000),
  (0x0, 0x2a721070764e530d54d95133eb12b31e79d1066700b63605a0c4ee4fa42465d2e1e7c5ae4a6c00a103531912d8380309da98721503a7400000),
  (0x0, 0x183a40c09155c71a962c841236e4c8a35474822281d0ab6a5d3024000aa020282024a796b56a3000260c4c9e0c987802e90a9f32403247400000),
  (0x0, 0x198b12e881d724d7ab68604145c4c4a14a5da113674ba438d4c9c24d909106e962c1c3519a4ee400632e570248706802cac801465cf867400000),
  (0x0, 0x58102dc09e24e1b97385909666309271edc93556c4b3a24d0e0b5a20ca3421cf246625717124000e347921b6ec84002a287a748054877400000),
  (0x0, 0xc3148000b630780314cc173a60bdc9740314802c856217270e9a6095a8a408d1b34cbc30f52500133a20a9166e9000280121f1c6811f7400000)
  ] : List (Nat × Nat)).map decodeUCertW18
set_option maxRecDepth 65536 in
private theorem sieve_aff_u4_c1_fast_w18_s0 :
    checkAffRangeULModPFastBoolW18 4 59 20 4 (dropCertsW18 0 sieveAffCertsU4C1W18) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve_aff_u4_c1_fast_w18_s1 :
    checkAffRangeULModPFastBoolW18 4 59 24 4 (dropCertsW18 4 sieveAffCertsU4C1W18) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve_aff_u4_c1_fast_w18_s2 :
    checkAffRangeULModPFastBoolW18 4 59 28 4 (dropCertsW18 8 sieveAffCertsU4C1W18) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve_aff_u4_c1_fast_w18_s3 :
    checkAffRangeULModPFastBoolW18 4 59 32 4 (dropCertsW18 12 sieveAffCertsU4C1W18) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve_aff_u4_c1_fast_w18_s4 :
    checkAffRangeULModPFastBoolW18 4 59 36 4 (dropCertsW18 16 sieveAffCertsU4C1W18) = true := by decide
private theorem sieve_aff_u4_c1_fast_w18 :
    checkAffRangeULModPFastBoolW18 4 59 20 20 sieveAffCertsU4C1W18 = true := by
  have h0 : checkAffRangeULModPFastBoolW18 4 59 20 4 sieveAffCertsU4C1W18 = true := sieve_aff_u4_c1_fast_w18_s0
  have h1 : checkAffRangeULModPFastBoolW18 4 59 20 8 sieveAffCertsU4C1W18 = true :=
    checkAffRangeULModPFastBoolW18_glue 4 59 4 4 20 sieveAffCertsU4C1W18 h0 sieve_aff_u4_c1_fast_w18_s1
  have h2 : checkAffRangeULModPFastBoolW18 4 59 20 12 sieveAffCertsU4C1W18 = true :=
    checkAffRangeULModPFastBoolW18_glue 4 59 8 4 20 sieveAffCertsU4C1W18 h1 sieve_aff_u4_c1_fast_w18_s2
  have h3 : checkAffRangeULModPFastBoolW18 4 59 20 16 sieveAffCertsU4C1W18 = true :=
    checkAffRangeULModPFastBoolW18_glue 4 59 12 4 20 sieveAffCertsU4C1W18 h2 sieve_aff_u4_c1_fast_w18_s3
  have h4 : checkAffRangeULModPFastBoolW18 4 59 20 20 sieveAffCertsU4C1W18 = true :=
    checkAffRangeULModPFastBoolW18_glue 4 59 16 4 20 sieveAffCertsU4C1W18 h3 sieve_aff_u4_c1_fast_w18_s4
  exact h4
private theorem sieve_aff_u4_c1_ok_w18 :
    checkAffRangeULModPBoolW18 4 59 20 20 sieveAffCertsU4C1W18 = true :=
  (checkAffRangeULModPFastBoolW18_eq 4 59 20 20 sieveAffCertsU4C1W18).symm.trans sieve_aff_u4_c1_fast_w18

private def sieveAffCertsU4C2W18 : List (List (Nat × Nat) × List (List Nat)) :=
  ([
  (0x0, 0xa8a0095532021850310a1b3504a8bb602b15895024f991e81c0636092a5327c58c1a6d89d48140374a54607481d5802635200368961b7400000),
  (0x0, 0x1c0612202a410d4529521cd39625118a18e90066e143b53e5132454b07042edd8043a512aa62c0015468cca72294e8024b5d126618e277400000),
  (0x0, 0x138b32c8db41cb1d1038596303ed11b61ca938670b8b2340c502650752ac2ce54965c314905e1000c0a30aa54671b80220d1944860d8a7400000),
  (0x0, 0x152f4a89ab7643079122845374e8490f580491f563c1a71e4901f2e945ac6658f0a24717b322b80286a14b25280140020d4b306e516297400000),
  (0x0, 0x2a31e8539b54a8513208079b1458b9b640d739501c0a760b90895e8da0148616055e1db2768740140e30a8f26acb801e71399725058d7400000),
  (0x0, 0xeb43a05a28609158b621db8b04d58380a70628001991940d908d128539f1655632663d1023e9002e50c87a314b86001c4838d1088d857400000),
  (0x0, 0xf1a5a0100672a45ab001c48d2a3d1ac1859816582dca506616261edc21f260c7221ee9b1b480c004303011246b0b001a9552a0259c237400000),
  (0x0, 0x68700b47af5e797ae222db1274553b0405cc236e0c38b1ee0f2d6a2118c3e2519b5e54a0b64c400c64654210614700189980966c16037400000),
  (0x89, 0xab51c1ce8d3ab598070a411f64796a2549d00840b000a4488a8812e4a1e4e799b25cc581024cc02f2c346a974b8d00165949700c0c997400000),
  (0x0, 0x68d588131354e1a366a2048b56056124e842050a4c5994c5473674b938e4e857973a298ac685402016bd386068828014588155e88aa67400000),
  (0x0, 0xaa4129933346a9b98505c01d649d72e1ae90b42621b9524a8aa574b5617625160b7231a055e3c02836dc3b15a15d00127010006994917400000),
  (0x0, 0x129f3a519a0466dd1668259046684ea81c9d7a43c6c58660d569602d909f1c89cb9561578b5e1c016125dc34349ca80100d2805ed45867400000),
  (0x0, 0xe306c9529b2a449b750bd01158ddb114644f1710640945a640b70c55d055ed59085234f001468005567c3b61ee4c000ee8707729c7227400000),
  (0x0, 0xb1f46b8a326ee8602429c1b75e6c6866cb960a2ebd6800a0049156a5c874e51d2b5cbc202504c0042a1879848bce000c0c8151a01b007400000),
  (0x0, 0x148660394992e1439f62b1316423c21f1a2832c60c909f6cc57895a6139e4ccc0845011915446400f1a4c5b21e185000a04eab327028a7400000),
  (0x0, 0x21c200902c08505a502e44134a8c0964e848922eb901924d4017028cd1f329070a2040b19147002e3665d01607d500089c21c34894867400000),
  (0x9a, 0x1caa465cd0020945921e28381284da380098025383562c401982136717a92eac2b842142300a4400604c8db57275c0006143af1e3cdb57400000),
  (0x0, 0x1d1e16086a810ac72c7068eb9681c8001e7921b38255ac6cbd31d1694a9d564568f6c84b931ed40182c4919a22a8c80047890a1e3c28c7400000),
  (0x0, 0x1832480000058786316894d3016643aa422c08000000800000f1938d85134a0800454b0827088c0262808b904ebd900020000072000007400000)
  ] : List (Nat × Nat)).map decodeUCertW18
set_option maxRecDepth 65536 in
private theorem sieve_aff_u4_c2_fast_w18_s0 :
    checkAffRangeULModPFastBoolW18 4 59 40 4 (dropCertsW18 0 sieveAffCertsU4C2W18) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve_aff_u4_c2_fast_w18_s1 :
    checkAffRangeULModPFastBoolW18 4 59 44 4 (dropCertsW18 4 sieveAffCertsU4C2W18) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve_aff_u4_c2_fast_w18_s2 :
    checkAffRangeULModPFastBoolW18 4 59 48 4 (dropCertsW18 8 sieveAffCertsU4C2W18) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve_aff_u4_c2_fast_w18_s3 :
    checkAffRangeULModPFastBoolW18 4 59 52 4 (dropCertsW18 12 sieveAffCertsU4C2W18) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve_aff_u4_c2_fast_w18_s4 :
    checkAffRangeULModPFastBoolW18 4 59 56 3 (dropCertsW18 16 sieveAffCertsU4C2W18) = true := by decide
private theorem sieve_aff_u4_c2_fast_w18 :
    checkAffRangeULModPFastBoolW18 4 59 40 19 sieveAffCertsU4C2W18 = true := by
  have h0 : checkAffRangeULModPFastBoolW18 4 59 40 4 sieveAffCertsU4C2W18 = true := sieve_aff_u4_c2_fast_w18_s0
  have h1 : checkAffRangeULModPFastBoolW18 4 59 40 8 sieveAffCertsU4C2W18 = true :=
    checkAffRangeULModPFastBoolW18_glue 4 59 4 4 40 sieveAffCertsU4C2W18 h0 sieve_aff_u4_c2_fast_w18_s1
  have h2 : checkAffRangeULModPFastBoolW18 4 59 40 12 sieveAffCertsU4C2W18 = true :=
    checkAffRangeULModPFastBoolW18_glue 4 59 8 4 40 sieveAffCertsU4C2W18 h1 sieve_aff_u4_c2_fast_w18_s2
  have h3 : checkAffRangeULModPFastBoolW18 4 59 40 16 sieveAffCertsU4C2W18 = true :=
    checkAffRangeULModPFastBoolW18_glue 4 59 12 4 40 sieveAffCertsU4C2W18 h2 sieve_aff_u4_c2_fast_w18_s3
  have h4 : checkAffRangeULModPFastBoolW18 4 59 40 19 sieveAffCertsU4C2W18 = true :=
    checkAffRangeULModPFastBoolW18_glue 4 59 16 3 40 sieveAffCertsU4C2W18 h3 sieve_aff_u4_c2_fast_w18_s4
  exact h4
private theorem sieve_aff_u4_c2_ok_w18 :
    checkAffRangeULModPBoolW18 4 59 40 19 sieveAffCertsU4C2W18 = true :=
  (checkAffRangeULModPFastBoolW18_eq 4 59 19 40 sieveAffCertsU4C2W18).symm.trans sieve_aff_u4_c2_fast_w18

set_option maxRecDepth 65536 in
private theorem sieve_inf_and_inv_u4_fast_w18 :
    checkAllInvModPBoolW18 59 59 = true ∧
    checkULModPNat12FastBoolW18 59 4 1 0 sieveInfCertU4W18 = true := by decide
private theorem sieve_inf_and_inv_u4_ok_w18 :
    checkAllInvModPBoolW18 59 59 = true ∧
    checkULModPNat12BoolW18 59 4 1 0 sieveInfCertU4W18 = true :=
  ⟨sieve_inf_and_inv_u4_fast_w18.1,
   (checkULModPNat12FastBoolW18_eq 59 4 1 0 sieveInfCertU4W18).symm.trans sieve_inf_and_inv_u4_fast_w18.2⟩

private def sieveInfCertU5W18 : List (Nat × Nat) × List (List Nat) :=
  decodeUCertW18 (0x56, 0x4060e284020c2c10c0a0c28a0608581162c4010804002180030214004860800408102418c0c24009122c1890430580181418c142c4010000000)

private def sieveAffCertsU5C0W18 : List (List (Nat × Nat) × List (List Nat)) :=
  ([
  (0x9b896a563925, 0x30104280000a2828110280051008000180000c0400405180830c0c040800a1000000000000000000000000000000000c000000000000000030c),
  (0x795645, 0x7101010710001091818580001c087080430b14181800600381062c008003058c100400a000838718105000200501181c30c04002000230000),
  (0x0, 0x18a063058b0224107022c6040c0448418040811224180080060b14181070e08587142c284161400a060c103062c380160030612004801800000),
  (0x0, 0x6030e244810e20587001c50b0010003102c603042058a080c0830a08386161058412304820220002120000314304801404104020c48a1800000),
  (0x0, 0x8004082050a18208081c3000e2c5821800203001838516183040c18589142c4850e1848c002c0040414501081850012204820a201071800000),
  (0x0, 0x200101000018102860a141070420481002c48c002c60508146030620385160c30a022008816180000c302070430400102800200204881800000),
  (0x9a, 0x1090a102800c10282161050c1428501082c2000000000000408a0228289021840a08140051408006082058302245800e24281000000c1800000),
  (0x9a8945, 0x3820a1460014180051410607181c300021c4060e2c5850620386022008418005850630308060010a022c40812240020c2408c002c4810030000),
  (0x56, 0x4040c1018108003090404002180050210085850628284080018c10005070c0018312040090e18004041840902205800a243810e085810000000),
  (0x89, 0x30016205860c1c280020c384161010402141860218001103018a1008481161428c0a2858c062c008061c00218201800804282002c2811800000),
  (0x78, 0x8314300081818183080808a001800c180c107181800202241890414283180c00412204020820008140c2800020200061c08c182c6041800000),
  (0x0, 0x40210085881010004040c101161438a0a2c20118103880e3020204303840a2848b040c603141400106105060a1430004281810a143011800000),
  (0x0, 0x1830400000100420a122c189102430b1620080000050000006030c1858912080030218583081c000142008b062c600020000004000001800000)
  ] : List (Nat × Nat)).map decodeUCertW18
set_option maxRecDepth 65536 in
private theorem sieve_aff_u5_c0_fast_w18_s0 :
    checkAffRangeULModPFastBoolW18 5 13 0 4 (dropCertsW18 0 sieveAffCertsU5C0W18) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve_aff_u5_c0_fast_w18_s1 :
    checkAffRangeULModPFastBoolW18 5 13 4 4 (dropCertsW18 4 sieveAffCertsU5C0W18) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve_aff_u5_c0_fast_w18_s2 :
    checkAffRangeULModPFastBoolW18 5 13 8 4 (dropCertsW18 8 sieveAffCertsU5C0W18) = true := by decide
set_option maxRecDepth 65536 in
private theorem sieve_aff_u5_c0_fast_w18_s3 :
    checkAffRangeULModPFastBoolW18 5 13 12 1 (dropCertsW18 12 sieveAffCertsU5C0W18) = true := by decide
private theorem sieve_aff_u5_c0_fast_w18 :
    checkAffRangeULModPFastBoolW18 5 13 0 13 sieveAffCertsU5C0W18 = true := by
  have h0 : checkAffRangeULModPFastBoolW18 5 13 0 4 sieveAffCertsU5C0W18 = true := sieve_aff_u5_c0_fast_w18_s0
  have h1 : checkAffRangeULModPFastBoolW18 5 13 0 8 sieveAffCertsU5C0W18 = true :=
    checkAffRangeULModPFastBoolW18_glue 5 13 4 4 0 sieveAffCertsU5C0W18 h0 sieve_aff_u5_c0_fast_w18_s1
  have h2 : checkAffRangeULModPFastBoolW18 5 13 0 12 sieveAffCertsU5C0W18 = true :=
    checkAffRangeULModPFastBoolW18_glue 5 13 8 4 0 sieveAffCertsU5C0W18 h1 sieve_aff_u5_c0_fast_w18_s2
  have h3 : checkAffRangeULModPFastBoolW18 5 13 0 13 sieveAffCertsU5C0W18 = true :=
    checkAffRangeULModPFastBoolW18_glue 5 13 12 1 0 sieveAffCertsU5C0W18 h2 sieve_aff_u5_c0_fast_w18_s3
  exact h3
private theorem sieve_aff_u5_c0_ok_w18 :
    checkAffRangeULModPBoolW18 5 13 0 13 sieveAffCertsU5C0W18 = true :=
  (checkAffRangeULModPFastBoolW18_eq 5 13 13 0 sieveAffCertsU5C0W18).symm.trans sieve_aff_u5_c0_fast_w18

set_option maxRecDepth 65536 in
private theorem sieve_inf_and_inv_u5_fast_w18 :
    checkAllInvModPBoolW18 13 13 = true ∧
    checkULModPNat12FastBoolW18 13 5 1 0 sieveInfCertU5W18 = true := by decide
private theorem sieve_inf_and_inv_u5_ok_w18 :
    checkAllInvModPBoolW18 13 13 = true ∧
    checkULModPNat12BoolW18 13 5 1 0 sieveInfCertU5W18 = true :=
  ⟨sieve_inf_and_inv_u5_fast_w18.1,
   (checkULModPNat12FastBoolW18_eq 13 5 1 0 sieveInfCertU5W18).symm.trans sieve_inf_and_inv_u5_fast_w18.2⟩

private theorem det12_t4u3_nonzero_of_proj_sieve_w18 (u pNat : Nat) (hp : pNat ≥ 3)
    (hinv_b : checkAllInvModPBoolW18 pNat pNat = true)
    (hinf_nz : intDet 12 (apow12KDivW18 u 1 0) % (pNat : Int) ≠ 0)
    (haff_spec : ∀ t : Nat, t < pNat -> intDet 12 (apow12KDivW18 u (t : Int) 1) % (pNat : Int) ≠ 0)
    (W K : Nat) (hW : W ≥ 1) (hK : K ≥ 1) :
    intDet 12 (laurentTwoBaseT4U3Mat12 W K u) ≠ 0 := by
  let p : Int := (pNat : Int)
  have hinv_spec : ∀ x : Nat, x < pNat -> x ≠ 0 ->
      (x * powModFuelNatW18 8 x (pNat - 2) pNat) % pNat = 1 := by
    have hlp : ∀ n : Nat, n ≤ pNat -> checkAllInvModPBoolW18 pNat n = true ->
        ∀ x : Nat, x < n -> x ≠ 0 -> (x * powModFuelNatW18 8 x (pNat - 2) pNat) % pNat = 1 := by
      intro n hn; induction n with
      | zero => intros _ _ hlt; omega
      | succ n' ihn =>
        intro ha x hx hne
        unfold checkAllInvModPBoolW18 at ha
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
      dsimp [prod15, x15, inv15]; rw [← mul_pow_w18c x inv 15]; exact hp_d 15
    have hm1 : (prod15 : Int) % p = 1 := by
      dsimp [p]
      have hdm := congrArg (fun n : Nat => (n : Int)) (Nat.div_add_mod prod15 pNat)
      rw [hp15_1] at hdm
      rw [← hdm, Int.natCast_add, Int.natCast_mul, Int.add_comm, Int.add_mul_emod_self_left]
      exact Int.emod_eq_of_lt (by decide) (by omega)
    have h1p : (1 : Int) % p = 1 := Int.emod_eq_of_lt (by decide) (by dsimp [p]; omega)
    rw [intPowNat_natCast_w18 x 15] at hxv0
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
      p ∣ (intDet 12 (apow12KDivW18 u w1 k1) - intDet 12 (apow12KDivW18 u w2 k2)) := by
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
    intro i j; unfold apow12KDivW18; dsimp only
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
      have hqc : p ∣ (qCubicW18 (i.val % 3) w1 (s * k1) - qCubicW18 (i.val % 3) w2 (s * k2)) := by
        rcases (by have := Nat.mod_lt i.val (by decide : 0 < 3); omega : i.val % 3 = 0 ∨ i.val % 3 = 1 ∨ i.val % 3 = 2) with h | h | h
        · simp only [h, qCubicW18]
          exact hd_mul _ _ _ _ (hd_sub _ _ _ _ hsk hw)
            (hd_sub _ _ _ _ hsk (hd_mul 2 2 w1 w2 ⟨0, by simp⟩ hw))
        · simp only [h, qCubicW18]
          exact hd_mul _ _ _ _ (hd_add _ _ _ _ hw hsk) (hd_sub _ _ _ _ hsk hw)
        · simp only [h, qCubicW18]
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
  rw [hW_eq, hK_eq, det12_t4u3_homog18_w18 u g w' k'] at hz_det
  have hg18_pos : intPowNat (g : Int) 18 > 0 := by
    rw [intPowNat_natCast_w18 g 18]
    have := nat_pow_pos_of_pos g hg_pos 18
    omega
  have hdet_wk0 : intDet 12 (laurentTwoBaseT4U3Mat12 w' k' u) = 0 := by
    by_cases h0 : intDet 12 (laurentTwoBaseT4U3Mat12 w' k' u) = 0
    · exact h0
    · exact False.elim (Int.mul_ne_zero (by omega) h0 hz_det)
  have hapow0 := stirling_1728_det12_t4u3_u_w18 u w' k'
  rw [hdet_wk0, Int.mul_zero, (apow12_extract_k3_and_homog15_w18 u).1 (w' : Int) (k' : Int)] at hapow0
  have hk3_nz : intPowNat (k' : Int) 3 ≠ 0 := by
    rw [intPowNat_natCast_w18 k' 3]
    have := nat_pow_pos_of_pos k' hk'_pos 3
    omega
  have hkdiv0 : intDet 12 (apow12KDivW18 u (w' : Int) (k' : Int)) = 0 := by
    by_cases h0 : intDet 12 (apow12KDivW18 u (w' : Int) (k' : Int)) = 0
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
  have hm_wk : intDet 12 (apow12KDivW18 u (wm : Int) (km : Int)) % p = 0 := by
    rcases hmat_mod_congr (wm : Int) (w' : Int) (km : Int) (k' : Int)
      (int_mod_sub_dvd_w18 w' pNat) (int_mod_sub_dvd_w18 k' pNat) with ⟨q, hq⟩
    rw [hkdiv0, Int.sub_zero] at hq
    rw [hq, Int.mul_emod_right]
  by_cases hkm0 : km = 0
  · have hwm_ne : wm ≠ 0 := fun hw0 => hnot_both0 ⟨hw0, hkm0⟩
    let inv := powModFuelNatW18 8 wm (pNat - 2) pNat
    have hinv := hinv_spec wm hwm_lt hwm_ne
    rw [hkm0, show (wm : Int) = (wm : Int) * 1 by omega,
        show ((0 : Nat) : Int) = (wm : Int) * 0 by omega,
        (apow12_extract_k3_and_homog15_w18 u).2 1 0 (wm : Int)] at hm_wk
    exact hinf_nz (hcancel15 wm inv _ hinv hm_wk)
  · let inv := powModFuelNatW18 8 km (pNat - 2) pNat
    have hinv := hinv_spec km hkm_lt hkm0
    let t := (wm * inv) % pNat
    have ht_lt : t < pNat := Nat.mod_lt _ (by omega)
    have htkm_dvd : p ∣ ((km : Int) * (t : Int) - (wm : Int)) := by
      have hnat : (km * t) % pNat = wm := by
        dsimp [t]
        rw [Nat.mul_comm km, Nat.mod_mul_mod, Nat.mul_assoc wm inv km, Nat.mul_comm inv km,
            Nat.mul_mod wm (km * inv) pNat, hinv, Nat.mul_one, Nat.mod_mod, Nat.mod_eq_of_lt hwm_lt]
      have hsub := int_mod_sub_dvd_w18 (km * t) pNat
      rw [hnat] at hsub
      rcases hsub with ⟨q, hq⟩
      simp only [Int.natCast_mul] at hq
      exact ⟨-q, by dsimp [p]; rw [Int.mul_neg]; omega⟩
    rcases hmat_mod_congr ((km : Int) * (t : Int)) (wm : Int) ((km : Int) * 1) (km : Int)
      htkm_dvd ⟨0, by simp⟩ with ⟨qd, hqd⟩
    have htk_mod0 : intDet 12 (apow12KDivW18 u ((km : Int) * (t : Int)) ((km : Int) * 1)) % p = 0 := by
      have heq : intDet 12 (apow12KDivW18 u ((km : Int) * (t : Int)) ((km : Int) * 1)) =
          intDet 12 (apow12KDivW18 u (wm : Int) (km : Int)) + p * qd := by omega
      rw [heq, Int.add_emod, hm_wk, Int.zero_add, Int.mul_emod_right, Int.zero_emod]
    rw [(apow12_extract_k3_and_homog15_w18 u).2 (t : Int) 1 (km : Int)] at htk_mod0
    exact haff_spec t ht_lt (hcancel15 km inv _ hinv htk_mod0)

-- Tropical `2`-adic scaling & 12-step single-column-0 expansion for `∀ W, K, u : Nat`:
private theorem intDet_scale_row0_w18 (L : Nat) (c : Int) (A : Fin (L + 1) -> Fin (L + 1) -> Int) :
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

private theorem intDet_scale_row_w18 (c : Int) :
    ∀ (L r0 : Nat) (_hr : r0 < L) (A : Fin L -> Fin L -> Int),
      intDet L (fun i j => if i.val = r0 then c * A i j else A i j) = c * intDet L A
  | 0, _, hr, _ => by omega
  | m + 1, 0, _, A => intDet_scale_row0_w18 m c A
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
      rw [heq_s]; exact intDet_scale_row_w18 c m r' (by omega) (intSubMat A j)
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

private def delRowCol0W18 {L : Nat} (A : Fin (L + 1) -> Fin (L + 1) -> Int) (r0 : Fin (L + 1)) :
    Fin L -> Fin L -> Int :=
  fun r c => A (skipFinIdx r0 r) ⟨c.val + 1, Nat.succ_lt_succ c.isLt⟩

private theorem intDet_succ_single_col0_w18 :
    ∀ (L : Nat) (A : Fin (L + 1) -> Fin (L + 1) -> Int) (r0 : Fin (L + 1)),
      (∀ i : Fin (L + 1), i ≠ r0 -> A i ⟨0, Nat.zero_lt_succ L⟩ = 0) ->
      intDet (L + 1) A =
        (if r0.val % 2 = 0 then 1 else -1) * A r0 ⟨0, Nat.zero_lt_succ L⟩ *
          intDet L (delRowCol0W18 A r0)
  | 0, A, r0, _ => by
    have hr0 : r0 = ⟨0, Nat.zero_lt_one⟩ := Fin.ext (by omega)
    subst hr0
    simp [intDet, intSumFin, intSumPrefix]
  | m + 1, A, r0, hzero => by
    let z0 : Fin (m + 2) := ⟨0, Nat.zero_lt_succ (m + 1)⟩
    by_cases hr0_z : r0.val = 0
    · have hr0_eq : r0 = z0 := Fin.ext hr0_z
      subst hr0_eq
      have hsub_z : ∀ j : Fin (m + 2), j.val ≥ 1 -> intDet (m + 1) (intSubMat A j) = 0 := by
        intro j hj1
        have hd0 : (0 : Int) ∣ intDet (m + 1) (intSubMat A j) := by
          apply intDet_col_dvd 0 (m + 1) ⟨0, Nat.zero_lt_succ m⟩
          intro r; unfold intSubMat
          have hsk0 : skipFinIdx j ⟨0, Nat.zero_lt_succ m⟩ = z0 := by
            apply Fin.ext; simp [skipFinIdx, z0, show 0 < j.val by omega]
          rw [hsk0, hzero ⟨r.val + 1, Nat.succ_lt_succ r.isLt⟩
                (fun h => by have := congrArg Fin.val h; dsimp [z0] at this; omega)]
          exact ⟨0, rfl⟩
        rcases hd0 with ⟨_, hq⟩; rw [Int.zero_mul] at hq; exact hq
      conv => lhs; unfold intDet; unfold intSumFin
      have htrunc : ∀ k : Nat, 1 ≤ k -> k ≤ m + 2 ->
          intSumPrefix (m + 2) (fun j => (if j.val % 2 = 0 then 1 else -1) * A z0 j * intDet (m + 1) (intSubMat A j)) k =
            A z0 z0 * intDet (m + 1) (intSubMat A z0) := by
        intro k hk1 hkm; induction k with
        | zero => omega
        | succ k' ih =>
          have hk_lt : k' < m + 2 := hkm
          by_cases hk0 : k' = 0
          · subst hk0; simp [intSumPrefix, z0]
          · simp only [intSumPrefix, hk_lt, dite_true, ih (by omega) (Nat.le_of_lt hkm),
                       hsub_z ⟨k', hk_lt⟩ (by dsimp; omega), Int.mul_zero, Int.add_zero]
      have hmain := htrunc (m + 2) (by omega) (Nat.le_refl _)
      have hdel_eq : intSubMat A z0 = delRowCol0W18 A z0 := by
        funext r c; unfold intSubMat delRowCol0W18 skipFinIdx
        simp [z0]
      rw [hdel_eq] at hmain
      change intSumPrefix (m + 2) (fun j => (if j.val % 2 = 0 then 1 else -1) * A z0 j * intDet (m + 1) (intSubMat A j)) (m + 2) =
        (if z0.val % 2 = 0 then 1 else -1) * A z0 z0 * intDet (m + 1) (delRowCol0W18 A z0)
      rw [hmain]
      simp [z0]
    · have hr0_pos : r0.val ≥ 1 := by omega
      let r' : Fin (m + 1) := ⟨r0.val - 1, by omega⟩
      have hA00 : A z0 z0 = 0 := hzero z0 (fun h => hr0_z (congrArg Fin.val h).symm)
      have hsub_col : ∀ c : Fin (m + 1),
          intDet (m + 1) (intSubMat A ⟨c.val + 1, Nat.succ_lt_succ c.isLt⟩) =
            (if r'.val % 2 = 0 then 1 else -1) * A r0 z0 *
              intDet m (intSubMat (delRowCol0W18 A r0) c) := by
        intro c
        let jc : Fin (m + 2) := ⟨c.val + 1, Nat.succ_lt_succ c.isLt⟩
        have hsk_jc0 : skipFinIdx jc ⟨0, Nat.zero_lt_succ m⟩ = z0 := by
          apply Fin.ext; simp [skipFinIdx, jc, z0]
        have hz_sub : ∀ i' : Fin (m + 1), i' ≠ r' ->
            intSubMat A jc i' ⟨0, Nat.zero_lt_succ m⟩ = 0 := by
          intro i' hne
          unfold intSubMat; rw [hsk_jc0]
          exact hzero ⟨i'.val + 1, by omega⟩ (fun h => hne (Fin.ext (by
            have := congrArg Fin.val h; dsimp [r'] at *; omega)))
        rw [intDet_succ_single_col0_w18 m (intSubMat A jc) r' hz_sub]
        have hval_r' : intSubMat A jc r' ⟨0, Nat.zero_lt_succ m⟩ = A r0 z0 := by
          unfold intSubMat; rw [hsk_jc0]
          have hf : (⟨r'.val + 1, by omega⟩ : Fin (m + 2)) = r0 := Fin.ext (by dsimp [r']; omega)
          rw [hf]
        have hmat_eq : delRowCol0W18 (intSubMat A jc) r' = intSubMat (delRowCol0W18 A r0) c := by
          funext q d
          unfold delRowCol0W18 intSubMat
          have hrow : (⟨(skipFinIdx r' q).val + 1, by omega⟩ : Fin (m + 2)) =
              skipFinIdx r0 ⟨q.val + 1, by omega⟩ := by
            apply Fin.ext; unfold skipFinIdx
            by_cases hlt : q.val < r0.val - 1
            · have hlt2 : q.val + 1 < r0.val := by omega
              simp [r', hlt, hlt2]
            · have hnlt2 : ¬ (q.val + 1 < r0.val) := by omega
              simp [r', hlt, hnlt2]
          have hcol : skipFinIdx jc ⟨d.val + 1, by omega⟩ =
              ⟨(skipFinIdx c d).val + 1, by omega⟩ := by
            apply Fin.ext; unfold skipFinIdx
            by_cases hlt : d.val < c.val
            · have hlt2 : d.val + 1 < c.val + 1 := by omega
              simp [jc, hlt, hlt2]
            · have hnlt2 : ¬ (d.val + 1 < c.val + 1) := by omega
              simp [jc, hlt, hnlt2]
          rw [hrow, hcol]
        rw [hval_r', hmat_eq]
      conv => lhs; unfold intDet; unfold intSumFin
      conv => rhs; rhs; unfold intDet; unfold intSumFin
      have hst : ∀ k : Nat, k ≤ m + 1 ->
          intSumPrefix (m + 2) (fun j => (if j.val % 2 = 0 then 1 else -1) * A z0 j * intDet (m + 1) (intSubMat A j)) (k + 1) =
            (if r0.val % 2 = 0 then 1 else -1) * A r0 z0 *
              intSumPrefix (m + 1) (fun c => (if c.val % 2 = 0 then 1 else -1) * delRowCol0W18 A r0 ⟨0, Nat.zero_lt_succ m⟩ c * intDet m (intSubMat (delRowCol0W18 A r0) c)) k := by
        intro k hk; induction k with
        | zero =>
          simp only [intSumPrefix, Nat.zero_lt_succ, dite_true, Int.mul_zero]
          change 0 + 1 * A z0 z0 * _ = 0
          rw [hA00]; simp
        | succ k' ih =>
          have hk1_lt : k' + 1 < m + 2 := Nat.succ_lt_succ hk
          have hk_lt : k' < m + 1 := hk
          conv => lhs; unfold intSumPrefix
          simp only [hk1_lt, dite_true, ih (Nat.le_of_lt hk)]
          conv => rhs; rhs; unfold intSumPrefix
          simp only [hk_lt, dite_true, Int.mul_add]
          rw [hsub_col ⟨k', hk_lt⟩]
          have htop_c : delRowCol0W18 A r0 ⟨0, Nat.zero_lt_succ m⟩ ⟨k', hk_lt⟩ = A z0 ⟨k' + 1, hk1_lt⟩ := by
            unfold delRowCol0W18 skipFinIdx
            have h0lt : 0 < r0.val := hr0_pos
            simp [z0, h0lt]
          rw [htop_c]
          have hsgn : (if (k' + 1) % 2 = 0 then (1 : Int) else -1) * (if r'.val % 2 = 0 then 1 else -1) =
              (if r0.val % 2 = 0 then (1 : Int) else -1) * (if k' % 2 = 0 then 1 else -1) := by
            have hr_eq : r0.val = r'.val + 1 := by dsimp [r']; omega
            rw [hr_eq]
            rcases (by omega : k' % 2 = 0 ∨ k' % 2 = 1) with hk_p | hk_p <;>
            rcases (by omega : r'.val % 2 = 0 ∨ r'.val % 2 = 1) with hr_p | hr_p <;>
            (have h1 : (k' + 1) % 2 = (k' % 2 + 1) % 2 := Nat.add_mod k' 1 2;
             have h2 : (r'.val + 1) % 2 = (r'.val % 2 + 1) % 2 := Nat.add_mod r'.val 1 2;
             rw [h1, h2, hk_p, hr_p]; try decide)
          congr 1
          calc (if (k' + 1) % 2 = 0 then (1 : Int) else -1) * A z0 ⟨k' + 1, hk1_lt⟩ *
                 ((if r'.val % 2 = 0 then 1 else -1) * A r0 z0 * intDet m (intSubMat (delRowCol0W18 A r0) ⟨k', hk_lt⟩))
              = ((if (k' + 1) % 2 = 0 then (1 : Int) else -1) * (if r'.val % 2 = 0 then 1 else -1)) *
                  (A r0 z0 * A z0 ⟨k' + 1, hk1_lt⟩ * intDet m (intSubMat (delRowCol0W18 A r0) ⟨k', hk_lt⟩)) := by ac_rfl
            _ = ((if r0.val % 2 = 0 then (1 : Int) else -1) * (if k' % 2 = 0 then 1 else -1)) *
                  (A r0 z0 * A z0 ⟨k' + 1, hk1_lt⟩ * intDet m (intSubMat (delRowCol0W18 A r0) ⟨k', hk_lt⟩)) := by rw [hsgn]
            _ = (if r0.val % 2 = 0 then (1 : Int) else -1) * A r0 z0 *
                  ((if k' % 2 = 0 then 1 else -1) * A z0 ⟨k' + 1, hk1_lt⟩ * intDet m (intSubMat (delRowCol0W18 A r0) ⟨k', hk_lt⟩)) := by ac_rfl
      exact hst (m + 1) (Nat.le_refl _)

private def applyColOpsW18 (N : Nat) : List (Nat × Nat × Int) -> (Fin N -> Fin N -> Int) -> (Fin N -> Fin N -> Int)
  | [], M => M
  | (dst, src, coef) :: ops, M =>
    let M' :=
      if h : dst < N ∧ src < N ∧ src ≠ dst then
        fun i j => if j = ⟨dst, h.1⟩ then M i ⟨dst, h.1⟩ - coef * M i ⟨src, h.2.1⟩ else M i j
      else M
    applyColOpsW18 N ops M'

private theorem applyColOpsW18_det (N : Nat) :
    ∀ (ops : List (Nat × Nat × Int)) (M : Fin N -> Fin N -> Int),
      intDet N (applyColOpsW18 N ops M) = intDet N M
  | [], _ => rfl
  | (dst, src, coef) :: ops, M => by
    unfold applyColOpsW18
    by_cases h : dst < N ∧ src < N ∧ src ≠ dst
    · rw [dite_pos_w18 h, applyColOpsW18_det N ops]
      exact intDet_sub_col_mul_other N ⟨dst, h.1⟩ ⟨src, h.2.1⟩
        (fun heq => h.2.2 (congrArg Fin.val heq)) coef M
    · rw [dite_neg_w18 h, applyColOpsW18_det N ops]

private def tropActiveBoolW18 (r m : Nat) : Bool :=
  (r == 0 && m == 2) || (r == 1 && m == 2) || (r == 1 && m == 1) || (r == 2 && m == 1) || (r == 2 && m == 0)

private def tropRedPowMatW18 (w k C : Int) (i j : Fin 12) : Int :=
  let r := i.val % 3; let s := i.val / 3
  let t := j.val % 4; let m := j.val / 4
  if tropActiveBoolW18 r m then intPowNat ((r : Int) * w + (s : Int) * k) t * intPowNat C (s * m)
  else 0

private def tropColOpsListW18 (w k : Int) : List (Nat × Nat × Int) :=
  let blockOps (m : Nat) (A : Int) : List (Nat × Nat × Int) :=
    let c0 := 4 * m; let c1 := 4 * m + 1; let c2 := 4 * m + 2; let c3 := 4 * m + 3
    [(c1, c0, A), (c2, c0, A * A), (c2, c1, 2 * A),
     (c3, c0, A * A * A), (c3, c1, 3 * (A * A)), (c3, c2, 3 * A),
     (c2, c1, k), (c3, c1, k * k), (c3, c2, 3 * k),
     (c0, c3, -1), (c3, c0, 1), (c0, c3, -1),
     (c1, c2, 1), (c2, c1, -1), (c1, c2, 1)]
  blockOps 0 (2 * w) ++ blockOps 1 w ++ blockOps 2 0

private def stepVec4W18 : List (Nat × Nat × Int) -> (Int × Int × Int × Int) -> (Int × Int × Int × Int)
  | [], v => v
  | (d, s, c) :: tl, (v0, v1, v2, v3) =>
    let vs := match s with | 0 => v0 | 1 => v1 | 2 => v2 | _ => v3
    let v' := match d with
      | 0 => (v0 - c * vs, v1, v2, v3)
      | 1 => (v0, v1 - c * vs, v2, v3)
      | 2 => (v0, v1, v2 - c * vs, v3)
      | _ => (v0, v1, v2, v3 - c * vs)
    stepVec4W18 tl v'

private def relBlockOpsW18 (A k : Int) : List (Nat × Nat × Int) :=
  [(1, 0, A), (2, 0, A * A), (2, 1, 2 * A),
   (3, 0, A * A * A), (3, 1, 3 * (A * A)), (3, 2, 3 * A),
   (2, 1, k), (3, 1, k * k), (3, 2, 3 * k),
   (0, 3, -1), (3, 0, 1), (0, 3, -1),
   (1, 2, 1), (2, 1, -1), (1, 2, 1)]

private theorem stepVec4W18_relBlockOps (A y k E : Int) :
    stepVec4W18 (relBlockOpsW18 A k)
      (intPowNat (A + y) 0 * E, intPowNat (A + y) 1 * E,
       intPowNat (A + y) 2 * E, intPowNat (A + y) 3 * E) =
    ((y * (y - k) * (y - 2 * k)) * E, -(y * (y - k)) * E, y * E, -E) := by
  have he0 : intPowNat (A + y) 0 * E = E := by simp [intPowNat]
  have he1 : intPowNat (A + y) 1 * E = (A + y) * E := by simp [intPowNat]
  have hs1 : (A + y) * E - A * E = y * E := by rw [Int.add_mul]; omega
  have he2 : intPowNat (A + y) 2 * E = (A * A) * E + (2 * A) * (y * E) + (y * y) * E := by
    simp only [intPowNat, Int.mul_one]
    have hexp : (A + y) * (A + y) * E = A * A * E + A * y * E + y * A * E + (y * y) * E := by
      simp only [Int.add_mul, Int.mul_add]; ac_rfl
    rw [hexp,
        show y * A * E = A * y * E by ac_rfl,
        show (2 * A) * (y * E) = 2 * (A * y * E) by ac_rfl]
    omega
  have hs2 : ((A * A) * E + (2 * A) * (y * E) + (y * y) * E) - (A * A) * E - (2 * A) * (y * E) =
      (y * y) * E := by omega
  have he3 : intPowNat (A + y) 3 * E =
      (A * A * A) * E + (3 * (A * A)) * (y * E) + (3 * A) * ((y * y) * E) + (y * y * y) * E := by
    have hp3 : intPowNat (A + y) 3 * E = (A + y) * (intPowNat (A + y) 2 * E) := by
      simp only [intPowNat]; ac_rfl
    rw [hp3, he2]
    simp only [Int.add_mul, Int.mul_add]
    rw [show A * ((A * A) * E) = (A * A * A) * E by ac_rfl,
        show A * ((2 * A) * (y * E)) = 2 * ((A * A) * (y * E)) by ac_rfl,
        show y * ((A * A) * E) = (A * A) * (y * E) by ac_rfl,
        show (3 * (A * A)) * (y * E) = 3 * ((A * A) * (y * E)) by ac_rfl,
        show A * ((y * y) * E) = A * ((y * y) * E) from rfl,
        show y * ((2 * A) * (y * E)) = 2 * (A * ((y * y) * E)) by ac_rfl,
        show (3 * A) * ((y * y) * E) = 3 * (A * ((y * y) * E)) by ac_rfl,
        show y * ((y * y) * E) = (y * y * y) * E by ac_rfl]
    omega
  have hs3 : ((A * A * A) * E + (3 * (A * A)) * (y * E) + (3 * A) * ((y * y) * E) + (y * y * y) * E) -
      (A * A * A) * E - (3 * (A * A)) * (y * E) - (3 * A) * ((y * y) * E) = (y * y * y) * E := by omega
  have hk2 : (y * y) * E - k * (y * E) = (y * (y - k)) * E := by
    simp only [Int.mul_sub, Int.sub_mul]
    rw [show k * (y * E) = y * k * E by ac_rfl]
  have hk3 : (y * y * y) * E - (k * k) * (y * E) - (3 * k) * ((y * (y - k)) * E) =
      (y * (y - k) * (y - 2 * k)) * E := by
    have hrhs : (y * (y - k) * (y - 2 * k)) * E =
        (y * y * y) * E - 3 * (k * (y * y * E)) + 2 * (k * k * (y * E)) := by
      simp only [Int.mul_sub, Int.sub_mul]
      rw [show y * y * (2 * k) * E = 2 * (k * (y * y * E)) by ac_rfl,
          show y * k * y * E = k * (y * y * E) by ac_rfl,
          show y * k * (2 * k) * E = 2 * (k * k * (y * E)) by ac_rfl]
      omega
    have hlhs : (3 * k) * ((y * (y - k)) * E) =
        3 * (k * (y * y * E)) - 3 * (k * k * (y * E)) := by
      simp only [Int.mul_sub, Int.sub_mul]
      rw [show 3 * k * (y * y * E) = 3 * (k * (y * y * E)) by ac_rfl,
          show 3 * k * (y * k * E) = 3 * (k * k * (y * E)) by ac_rfl]
    rw [hrhs, hlhs]; omega
  have hsw03 : ∀ a b v1 v2 : Int,
      stepVec4W18 [(0, 3, -1), (3, 0, 1), (0, 3, -1), (1, 2, 1), (2, 1, -1), (1, 2, 1)] (a, v1, v2, b) =
        (b, -v2, v1, -a) := by
    intro a b v1 v2
    simp only [stepVec4W18]
    apply Prod.ext
    · dsimp only; omega
    · apply Prod.ext
      · dsimp only; omega
      · apply Prod.ext <;> (dsimp only; omega)
  have hstep_app : ∀ (xs ys : List (Nat × Nat × Int)) (v : Int × Int × Int × Int),
      stepVec4W18 (xs ++ ys) v = stepVec4W18 ys (stepVec4W18 xs v) := by
    intro xs; induction xs with
    | nil => intros; rfl
    | cons h tl ih =>
      rcases h with ⟨d, s, c⟩
      intro ys ⟨v0, v1, v2, v3⟩
      dsimp only [List.cons_append, stepVec4W18]
      exact ih ys _
  have hpart1 : stepVec4W18 [(1, 0, A), (2, 0, A * A), (2, 1, 2 * A)]
      (E, (A + y) * E, (A * A) * E + (2 * A) * (y * E) + (y * y) * E,
       (A * A * A) * E + (3 * (A * A)) * (y * E) + (3 * A) * ((y * y) * E) + (y * y * y) * E) =
    (E, y * E, (y * y) * E,
     (A * A * A) * E + (3 * (A * A)) * (y * E) + (3 * A) * ((y * y) * E) + (y * y * y) * E) := by
    simp only [stepVec4W18]
    rw [hs1, hs2]
  have hpart2 : stepVec4W18 [(3, 0, A * A * A), (3, 1, 3 * (A * A)), (3, 2, 3 * A)]
      (E, y * E, (y * y) * E,
       (A * A * A) * E + (3 * (A * A)) * (y * E) + (3 * A) * ((y * y) * E) + (y * y * y) * E) =
    (E, y * E, (y * y) * E, (y * y * y) * E) := by
    simp only [stepVec4W18]
    rw [hs3]
  have hpart3 : stepVec4W18 [(2, 1, k), (3, 1, k * k), (3, 2, 3 * k)]
      (E, y * E, (y * y) * E, (y * y * y) * E) =
    (E, y * E, (y * (y - k)) * E, (y * (y - k) * (y - 2 * k)) * E) := by
    simp only [stepVec4W18]
    rw [hk2, hk3]
  rw [he0, he1, he2, he3]
  have hrel_split : relBlockOpsW18 A k =
      [(1, 0, A), (2, 0, A * A), (2, 1, 2 * A)] ++
      ([(3, 0, A * A * A), (3, 1, 3 * (A * A)), (3, 2, 3 * A)] ++
       ([(2, 1, k), (3, 1, k * k), (3, 2, 3 * k)] ++
        [(0, 3, -1), (3, 0, 1), (0, 3, -1), (1, 2, 1), (2, 1, -1), (1, 2, 1)])) := rfl
  rw [hrel_split, hstep_app, hpart1, hstep_app, hpart2, hstep_app, hpart3,
      hsw03 E ((y * (y - k) * (y - 2 * k)) * E) (y * E) ((y * (y - k)) * E),
      Int.neg_mul (y * (y - k)) E]

private def fallPowValW18 (s : Nat) (k : Int) : Nat -> Int
  | 0 => (s : Int) * ((s : Int) - 1) * ((s : Int) - 2) * (k * k * k)
  | 1 => -((s : Int) * ((s : Int) - 1) * (k * k))
  | 2 => (s : Int) * k
  | _ => -1

private def tropBlkSpecPropW18 (k C : Int) (M_ab : Fin 12 -> Fin 12 -> Int) : Prop :=
  ∀ (i : Fin 12) (m t : Nat) (hmt : 4 * m + t < 12) (_ht4 : t < 4),
    let r := i.val % 3; let s := i.val / 3
    (m = 0 -> (r ≠ 2 -> M_ab i ⟨4 * m + t, hmt⟩ = 0) ∧
              (r = 2 -> M_ab i ⟨4 * m + t, hmt⟩ = fallPowValW18 s k t)) ∧
    (m = 1 -> (r = 0 -> M_ab i ⟨4 * m + t, hmt⟩ = 0) ∧
              (r = 1 -> M_ab i ⟨4 * m + t, hmt⟩ = fallPowValW18 s k t * intPowNat C s)) ∧
    (m = 2 -> (r = 0 -> M_ab i ⟨4 * m + t, hmt⟩ = fallPowValW18 s k t * intPowNat C (s * 2)))

private theorem tropBlkChar_w18 (w k C : Int) :
    tropBlkSpecPropW18 k C (applyColOpsW18 12 (tropColOpsListW18 w k) (tropRedPowMatW18 w k C)) := by
  let M_el := applyColOpsW18 12 (tropColOpsListW18 w k) (tropRedPowMatW18 w k C)
  have hblk_char : tropBlkSpecPropW18 k C M_el := by
    -- Bridge `applyColOpsW18` on shifted block `4 * m` to `stepVec4W18`:
    have hshift_sim : ∀ (m : Nat) (hm : m < 3) (i : Fin 12)
        (ops : List (Nat × Nat × Int)),
        (∀ op ∈ ops, op.1 < 4 ∧ op.2.1 < 4 ∧ op.2.1 ≠ op.1) ->
        ∀ (B : Fin 12 -> Fin 12 -> Int),
          let ops_sh := ops.map (fun x => (4 * m + x.1, 4 * m + x.2.1, x.2.2))
          let B' := applyColOpsW18 12 ops_sh B
          (∀ j : Fin 12, j.val / 4 ≠ m -> B' i j = B i j) ∧
          (B' i ⟨4 * m + 0, by omega⟩, B' i ⟨4 * m + 1, by omega⟩,
           B' i ⟨4 * m + 2, by omega⟩, B' i ⟨4 * m + 3, by omega⟩) =
            stepVec4W18 ops
              (B i ⟨4 * m + 0, by omega⟩, B i ⟨4 * m + 1, by omega⟩,
               B i ⟨4 * m + 2, by omega⟩, B i ⟨4 * m + 3, by omega⟩) := by
      intro m hm i ops; induction ops with
      | nil => intro _ B; exact ⟨fun _ _ => rfl, rfl⟩
      | cons hd tl ih =>
        rcases hd with ⟨d, s, c⟩
        intro hmem B
        have hhd := hmem (d, s, c) (List.Mem.head _)
        dsimp only at hhd
        have htl := fun op hop => hmem op (List.mem_cons_of_mem _ hop)
        rcases hhd with ⟨hd4, hs4, hne⟩
        have hguard : 4 * m + d < 12 ∧ 4 * m + s < 12 ∧ 4 * m + s ≠ 4 * m + d := by omega
        dsimp only [List.map]
        conv => lhs; unfold applyColOpsW18
        conv => rhs; lhs; unfold applyColOpsW18
        rw [dite_pos_w18 hguard]
        let B1 : Fin 12 -> Fin 12 -> Int := fun row col =>
          if col = ⟨4 * m + d, hguard.1⟩ then B row ⟨4 * m + d, hguard.1⟩ - c * B row ⟨4 * m + s, hguard.2.1⟩ else B row col
        rcases ih htl B1 with ⟨hout_tl, hvec_tl⟩
        refine ⟨?_, ?_⟩
        · intro j hjm
          change applyColOpsW18 12 (List.map (fun x => (4 * m + x.1, 4 * m + x.2.1, x.2.2)) tl) B1 i j = B i j
          rw [hout_tl j hjm]
          dsimp [B1]
          rw [ite_false_of_w10 (fun heq => hjm (by have := congrArg Fin.val heq; dsimp at this; omega))]
        · change (applyColOpsW18 12 (List.map (fun x => (4 * m + x.1, 4 * m + x.2.1, x.2.2)) tl) B1 i ⟨4 * m + 0, _⟩,
                  applyColOpsW18 12 (List.map (fun x => (4 * m + x.1, 4 * m + x.2.1, x.2.2)) tl) B1 i ⟨4 * m + 1, _⟩,
                  applyColOpsW18 12 (List.map (fun x => (4 * m + x.1, 4 * m + x.2.1, x.2.2)) tl) B1 i ⟨4 * m + 2, _⟩,
                  applyColOpsW18 12 (List.map (fun x => (4 * m + x.1, 4 * m + x.2.1, x.2.2)) tl) B1 i ⟨4 * m + 3, _⟩) = _
          rw [hvec_tl]
          dsimp only [stepVec4W18, B1]
          rcases (by omega : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3) with rfl | rfl | rfl | rfl <;>
          rcases (by omega : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3) with rfl | rfl | rfl | rfl
          all_goals (try omega)
          all_goals simp
    have hrel_valid : ∀ A : Int, ∀ op ∈ relBlockOpsW18 A k, op.1 < 4 ∧ op.2.1 < 4 ∧ op.2.1 ≠ op.1 := by
      intro A ⟨d, s, c⟩ hop
      dsimp only
      unfold relBlockOpsW18 at hop
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hop
      rcases hop with ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩ |
                      ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩ |
                      ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩ <;> decide
    have hind_blk : ∀ (m : Nat) (hm : m < 3) (A : Int) (B_in : Fin 12 -> Fin 12 -> Int),
        let ops_m := (relBlockOpsW18 A k).map (fun x => (4 * m + x.1, 4 * m + x.2.1, x.2.2))
        let B_out := applyColOpsW18 12 ops_m B_in
        (∀ (i j : Fin 12), j.val / 4 ≠ m -> B_out i j = B_in i j) ∧
        (∀ (i : Fin 12) (y E : Int),
          (∀ q : Nat, (hq : q < 4) -> B_in i ⟨4 * m + q, by omega⟩ = intPowNat (A + y) q * E) ->
          B_out i ⟨4 * m + 0, by omega⟩ = (y * (y - k) * (y - 2 * k)) * E ∧
          B_out i ⟨4 * m + 1, by omega⟩ = -(y * (y - k)) * E ∧
          B_out i ⟨4 * m + 2, by omega⟩ = y * E ∧
          B_out i ⟨4 * m + 3, by omega⟩ = -E) := by
      intro m hm A B_in; dsimp only
      refine ⟨fun i j hjm => (hshift_sim m hm i (relBlockOpsW18 A k) (hrel_valid A) B_in).1 j hjm, ?_⟩
      intro i y E hin
      have hvec := (hshift_sim m hm i (relBlockOpsW18 A k) (hrel_valid A) B_in).2
      rw [hin 0 (by decide), hin 1 (by decide), hin 2 (by decide), hin 3 (by decide),
          stepVec4W18_relBlockOps A y k E] at hvec
      injection hvec with e0 hrest1
      injection hrest1 with e1 hrest2
      injection hrest2 with e2 e3
      exact ⟨e0, e1, e2, e3⟩
    have happ_ops : ∀ (xs ys : List (Nat × Nat × Int)) (B : Fin 12 -> Fin 12 -> Int),
        applyColOpsW18 12 (xs ++ ys) B = applyColOpsW18 12 ys (applyColOpsW18 12 xs B) := by
      intro xs; induction xs with
      | nil => intros; rfl
      | cons _ tl ih => intros; simp [applyColOpsW18, ih]
    intro i m t hmt ht4; dsimp only
    let B0 := tropRedPowMatW18 w k C
    let ops0 := (relBlockOpsW18 (2 * w) k).map (fun x => (4 * 0 + x.1, 4 * 0 + x.2.1, x.2.2))
    let ops1 := (relBlockOpsW18 w k).map (fun x => (4 * 1 + x.1, 4 * 1 + x.2.1, x.2.2))
    let ops2 := (relBlockOpsW18 0 k).map (fun x => (4 * 2 + x.1, 4 * 2 + x.2.1, x.2.2))
    have hM_split : M_el = applyColOpsW18 12 ops2 (applyColOpsW18 12 ops1 (applyColOpsW18 12 ops0 B0)) := by
      have hlist : tropColOpsListW18 w k = ops0 ++ ops1 ++ ops2 := rfl
      dsimp [M_el, B0]
      rw [hlist, happ_ops, happ_ops]
    rcases hind_blk 0 (by decide) (2 * w) B0 with ⟨hout0, hin0⟩
    rcases hind_blk 1 (by decide) w (applyColOpsW18 12 ops0 B0) with ⟨hout1, hin1⟩
    rcases hind_blk 2 (by decide) 0 (applyColOpsW18 12 ops1 (applyColOpsW18 12 ops0 B0)) with ⟨hout2, hin2⟩
    have hfp : ∀ (s : Nat),
        let y := (s : Int) * k
        (y * (y - k) * (y - 2 * k) = fallPowValW18 s k 0) ∧
        (-(y * (y - k)) = fallPowValW18 s k 1) ∧
        (y = fallPowValW18 s k 2) ∧
        ((-1 : Int) = fallPowValW18 s k 3) := by
      intro s; dsimp [fallPowValW18]
      have hs1 : (s : Int) * k - k = ((s : Int) - 1) * k := by rw [Int.sub_mul, Int.one_mul]
      have hs2 : (s : Int) * k - 2 * k = ((s : Int) - 2) * k := by rw [Int.sub_mul]
      refine ⟨?_, ?_, rfl, rfl⟩
      · rw [hs1, hs2]; ac_rfl
      · rw [hs1]; congr 1; ac_rfl
    refine ⟨?_, ?_, ?_⟩
    · intro hm0; subst hm0
      have hj_pres : ∀ c : Fin 12, c.val / 4 = 0 ->
          M_el i c = applyColOpsW18 12 ops0 B0 i c := by
        intro c hc; rw [hM_split, hout2 i c (by omega), hout1 i c (by omega)]
      refine ⟨?_, ?_⟩
      · intro hr_ne2
        rw [hj_pres ⟨4 * 0 + t, hmt⟩ (by dsimp; omega)]
        have hz_in : ∀ q : Nat, (hq : q < 4) -> B0 i ⟨4 * 0 + q, by omega⟩ = intPowNat (2 * w + 0) q * 0 := by
          intro q hq; simp only [Int.mul_zero]; dsimp [B0, tropRedPowMatW18]
          have hact_f : tropActiveBoolW18 (i.val % 3) 0 = false := by
            rcases (by have := Nat.mod_lt i.val (by decide : 0 < 3); omega : i.val % 3 = 0 ∨ i.val % 3 = 1) with h | h <;>
            simp [tropActiveBoolW18, h]
          rw [show (4 * 0 + q) / 4 = 0 by omega, hact_f]; rfl
        rcases hin0 i 0 0 hz_in with ⟨e0, e1, e2, e3⟩
        dsimp only [ops0]
        rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3) with rfl | rfl | rfl | rfl
        · rw [e0]; simp
        · rw [e1]; simp
        · rw [e2]; simp
        · rw [e3]; simp
      · intro hr2
        change i.val % 3 = 2 at hr2
        rw [hj_pres ⟨4 * 0 + t, hmt⟩ (by dsimp; omega)]
        have hz_in : ∀ q : Nat, (hq : q < 4) ->
            B0 i ⟨4 * 0 + q, by omega⟩ = intPowNat (2 * w + ((i.val / 3 : Nat) : Int) * k) q * 1 := by
          intro q hq; dsimp only [B0, tropRedPowMatW18]
          have hact_t : tropActiveBoolW18 (i.val % 3) 0 = true := by simp [tropActiveBoolW18, hr2]
          rw [show (4 * 0 + q) / 4 = 0 by omega, show (4 * 0 + q) % 4 = q by omega, hact_t, hr2]
          simp only [reduceIte, Nat.mul_zero, intPowNat]
          rfl
        rcases hin0 i (((i.val / 3 : Nat) : Int) * k) 1 hz_in with ⟨e0, e1, e2, e3⟩
        rcases hfp (i.val / 3) with ⟨f0, f1, f2, f3⟩
        dsimp only [ops0]
        rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3) with rfl | rfl | rfl | rfl
        · rw [e0, Int.mul_one, f0]
        · rw [e1, Int.mul_one, f1]
        · rw [e2, Int.mul_one, f2]
        · rw [e3]; simp [f3]
    · intro hm1; subst hm1
      have hj_pres : ∀ c : Fin 12, c.val / 4 = 1 ->
          M_el i c = applyColOpsW18 12 ops1 (applyColOpsW18 12 ops0 B0) i c := by
        intro c hc; rw [hM_split, hout2 i c (by omega)]
      refine ⟨?_, ?_⟩
      · intro hr0
        change i.val % 3 = 0 at hr0
        rw [hj_pres ⟨4 * 1 + t, hmt⟩ (by dsimp; omega)]
        have hz_in : ∀ q : Nat, (hq : q < 4) ->
            applyColOpsW18 12 ops0 B0 i ⟨4 * 1 + q, by omega⟩ = intPowNat (w + 0) q * 0 := by
          intro q hq; simp only [Int.mul_zero]
          rw [hout0 i ⟨4 * 1 + q, by omega⟩ (by dsimp; omega)]
          dsimp only [B0, tropRedPowMatW18]
          have hact_f : tropActiveBoolW18 (i.val % 3) 1 = false := by simp [tropActiveBoolW18, hr0]
          rw [show (4 * 1 + q) / 4 = 1 by omega, hact_f]; rfl
        rcases hin1 i 0 0 hz_in with ⟨e0, e1, e2, e3⟩
        dsimp only [ops1]
        rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3) with rfl | rfl | rfl | rfl
        · rw [e0]; simp
        · rw [e1]; simp
        · rw [e2]; simp
        · rw [e3]; simp
      · intro hr1
        change i.val % 3 = 1 at hr1
        rw [hj_pres ⟨4 * 1 + t, hmt⟩ (by dsimp; omega)]
        have hz_in : ∀ q : Nat, (hq : q < 4) ->
            applyColOpsW18 12 ops0 B0 i ⟨4 * 1 + q, by omega⟩ =
              intPowNat (w + ((i.val / 3 : Nat) : Int) * k) q * intPowNat C (i.val / 3) := by
          intro q hq
          rw [hout0 i ⟨4 * 1 + q, by omega⟩ (by dsimp; omega)]
          dsimp only [B0, tropRedPowMatW18]
          have hact_t : tropActiveBoolW18 (i.val % 3) 1 = true := by simp [tropActiveBoolW18, hr1]
          rw [show (4 * 1 + q) / 4 = 1 by omega, show (4 * 1 + q) % 4 = q by omega, hact_t, hr1]
          simp only [reduceIte, Nat.mul_one]
          rw [show ((1 : Nat) : Int) * w = w from Int.one_mul w]
        rcases hin1 i (((i.val / 3 : Nat) : Int) * k) (intPowNat C (i.val / 3)) hz_in with ⟨e0, e1, e2, e3⟩
        rcases hfp (i.val / 3) with ⟨f0, f1, f2, f3⟩
        dsimp only [ops1]
        rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3) with rfl | rfl | rfl | rfl
        · rw [e0, f0]
        · rw [e1, f1]
        · rw [e2, f2]
        · rw [e3, ← f3, Int.neg_one_mul]
    · intro hm2; subst hm2
      intro hr0
      change i.val % 3 = 0 at hr0
      rw [hM_split]
      have hz_in : ∀ q : Nat, (hq : q < 4) ->
          applyColOpsW18 12 ops1 (applyColOpsW18 12 ops0 B0) i ⟨4 * 2 + q, by omega⟩ =
            intPowNat (0 + ((i.val / 3 : Nat) : Int) * k) q * intPowNat C (i.val / 3 * 2) := by
        intro q hq
        rw [hout1 i ⟨4 * 2 + q, by omega⟩ (by dsimp; omega),
            hout0 i ⟨4 * 2 + q, by omega⟩ (by dsimp; omega)]
        dsimp only [B0, tropRedPowMatW18]
        have hact_t : tropActiveBoolW18 (i.val % 3) 2 = true := by simp [tropActiveBoolW18, hr0]
        rw [show (4 * 2 + q) / 4 = 2 by omega, show (4 * 2 + q) % 4 = q by omega, hact_t, hr0]
        simp only [reduceIte]
        rw [show ((0 : Nat) : Int) * w = 0 from Int.zero_mul w]
      rcases hin2 i (((i.val / 3 : Nat) : Int) * k) (intPowNat C (i.val / 3 * 2)) hz_in with ⟨e0, e1, e2, e3⟩
      rcases hfp (i.val / 3) with ⟨f0, f1, f2, f3⟩
      dsimp only [ops2]
      rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3) with rfl | rfl | rfl | rfl
      · rw [e0, f0]
      · rw [e1, f1]
      · rw [e2, f2]
      · rw [e3, ← f3, Int.neg_one_mul]
  exact hblk_char

private def tropRowMapW18 : Nat -> List Nat
  | 0 => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
  | 1 => [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
  | 2 => [0, 1, 2, 3, 4, 5, 6, 7, 9, 10]
  | 3 => [0, 1, 2, 3, 4, 6, 7, 9, 10]
  | 4 => [0, 1, 3, 4, 6, 7, 9, 10]
  | 5 => [0, 1, 3, 4, 6, 7, 9]
  | 6 => [0, 1, 3, 4, 6, 9]
  | 7 => [0, 1, 3, 6, 9]
  | 8 => [0, 3, 6, 9]
  | 9 => [0, 3, 6]
  | 10 => [0, 3]
  | 11 => [0]
  | _ => []

private def tropSubStageRemW18 (M_ab : Fin 12 -> Fin 12 -> Int) (rem : Nat) (r c : Fin rem) : Int :=
  let st := 12 - rem
  let origR := (tropRowMapW18 st).getD r.val 0
  if h : origR < 12 ∧ st + c.val < 12 then M_ab ⟨origR, h.1⟩ ⟨st + c.val, h.2⟩ else 0

private theorem tropStepPeelW18 (M_ab : Fin 12 -> Fin 12 -> Int)
    (L st pivIdx origPiv : Nat) (_hL : L < 12) (hst_eq : 12 - (L + 1) = st)
    (hst : st < 12) (hpiv : pivIdx < L + 1) (horig : origPiv < 12) (val : Int)
    (hmap_p : (tropRowMapW18 st).getD pivIdx 0 = origPiv)
    (hmap_sk : ∀ q : Fin L, (tropRowMapW18 (st + 1)).getD q.val 0 = (tropRowMapW18 st).getD (skipFinIdx ⟨pivIdx, hpiv⟩ q).val 0)
    (hz_other : ∀ r : Fin (L + 1), r ≠ ⟨pivIdx, hpiv⟩ ->
      let or_v := (tropRowMapW18 st).getD r.val 0
      ∀ ho : or_v < 12, M_ab ⟨or_v, ho⟩ ⟨st, hst⟩ = 0)
    (hval_p : M_ab ⟨origPiv, horig⟩ ⟨st, hst⟩ = val) :
    intDet (L + 1) (tropSubStageRemW18 M_ab (L + 1)) =
      (if pivIdx % 2 = 0 then 1 else -1) * val * intDet L (tropSubStageRemW18 M_ab L) := by
  subst hst_eq
  let r0 : Fin (L + 1) := ⟨pivIdx, hpiv⟩
  have hz_A : ∀ i : Fin (L + 1), i ≠ r0 -> tropSubStageRemW18 M_ab (L + 1) i ⟨0, Nat.zero_lt_succ L⟩ = 0 := by
    intro i hne; unfold tropSubStageRemW18; dsimp only
    by_cases hb : (tropRowMapW18 (12 - (L + 1))).getD i.val 0 < 12 ∧ (12 - (L + 1)) + 0 < 12
    · rw [dite_pos_w18 hb, show (⟨(12 - (L + 1)) + 0, hb.2⟩ : Fin 12) = ⟨12 - (L + 1), hst⟩ from Fin.ext (Nat.add_zero _)]
      exact hz_other i hne hb.1
    · rw [dite_neg_w18 hb]
  rw [intDet_succ_single_col0_w18 L (tropSubStageRemW18 M_ab (L + 1)) r0 hz_A]
  have hpiv_val : tropSubStageRemW18 M_ab (L + 1) r0 ⟨0, Nat.zero_lt_succ L⟩ = val := by
    unfold tropSubStageRemW18; dsimp only [r0]
    have hb : (tropRowMapW18 (12 - (L + 1))).getD pivIdx 0 < 12 ∧ (12 - (L + 1)) + 0 < 12 := by
      rw [hmap_p]; exact ⟨horig, by omega⟩
    rw [dite_pos_w18 hb, ← hval_p,
        show (⟨(tropRowMapW18 (12 - (L + 1))).getD pivIdx 0, hb.1⟩ : Fin 12) = ⟨origPiv, horig⟩ from Fin.ext hmap_p,
        show (⟨(12 - (L + 1)) + 0, hb.2⟩ : Fin 12) = ⟨12 - (L + 1), hst⟩ from Fin.ext (Nat.add_zero _)]
  have hdel_eq : delRowCol0W18 (tropSubStageRemW18 M_ab (L + 1)) r0 = tropSubStageRemW18 M_ab L := by
    funext q d; unfold delRowCol0W18 tropSubStageRemW18; dsimp only [r0]
    have h12L : 12 - L = (12 - (L + 1)) + 1 := by omega
    have hadd : (12 - (L + 1)) + (d.val + 1) = ((12 - (L + 1)) + 1) + d.val := by omega
    simp only [h12L, hadd, ← hmap_sk q]
  dsimp only [r0] at hpiv_val ⊢
  rw [hpiv_val, hdel_eq]

private theorem tropCastRowW18 (M_ab : Fin 12 -> Fin 12 -> Int)
    (st idx v : Nat) (ho : (tropRowMapW18 st).getD idx 0 < 12) (hv : v < 12) (col : Fin 12)
    (heq : (tropRowMapW18 st).getD idx 0 = v) :
    M_ab ⟨(tropRowMapW18 st).getD idx 0, ho⟩ col = M_ab ⟨v, hv⟩ col :=
  congrArg (fun r_f => M_ab r_f col) (Fin.ext heq)

private theorem tropPeelBlock0_w18 (k C : Int) (M_ab : Fin 12 -> Fin 12 -> Int)
    (hblk : tropBlkSpecPropW18 k C M_ab) :
    intDet 12 (tropSubStageRemW18 M_ab 12) =
      12 * intPowNat k 6 * intDet 8 (tropSubStageRemW18 M_ab 8) := by
  have hel_m0_ne : ∀ (r_i : Nat) (hr : r_i < 12), r_i % 3 ≠ 2 -> ∀ (t : Nat) (ht : t < 4),
      M_ab ⟨r_i, hr⟩ ⟨t, by omega⟩ = 0 := by
    intro r_i hr hne t ht
    rw [show (⟨t, by omega⟩ : Fin 12) = ⟨4 * 0 + t, by omega⟩ from Fin.ext (Nat.zero_add t).symm]
    exact ((hblk ⟨r_i, hr⟩ 0 t (by omega) ht).1 rfl).1 hne
  have hel_m0_eq : ∀ (r_i : Nat) (hr : r_i < 12), r_i % 3 = 2 -> ∀ (t : Nat) (ht : t < 4),
      M_ab ⟨r_i, hr⟩ ⟨t, by omega⟩ = fallPowValW18 (r_i / 3) k t := by
    intro r_i hr heq t ht
    rw [show (⟨t, by omega⟩ : Fin 12) = ⟨4 * 0 + t, by omega⟩ from Fin.ext (Nat.zero_add t).symm]
    exact ((hblk ⟨r_i, hr⟩ 0 t (by omega) ht).1 rfl).2 heq
  have hfp00 : fallPowValW18 0 k 0 = 0 := Int.zero_mul _
  have hfp10 : fallPowValW18 1 k 0 = 0 := Int.zero_mul _
  have hfp20 : fallPowValW18 2 k 0 = 0 := Int.zero_mul _
  have hfp30 : fallPowValW18 3 k 0 = 6 * (k * k * k) := rfl
  have hfp01 : fallPowValW18 0 k 1 = 0 := by change -(0 * (k * k)) = 0; rw [Int.zero_mul]; rfl
  have hfp11 : fallPowValW18 1 k 1 = 0 := by change -(0 * (k * k)) = 0; rw [Int.zero_mul]; rfl
  have hfp21 : fallPowValW18 2 k 1 = -(2 * (k * k)) := rfl
  have hfp02 : fallPowValW18 0 k 2 = 0 := Int.zero_mul k
  have hfp12 : fallPowValW18 1 k 2 = k := Int.one_mul k
  have hfp03 : fallPowValW18 0 k 3 = -1 := rfl
  have p0 := tropStepPeelW18 M_ab 11 0 11 11 (by decide) rfl (by decide) (by decide) (by decide) (6 * (k * k * k)) rfl
    (fun ⟨qv, hq⟩ => by rcases (by omega : qv = 0 ∨ qv = 1 ∨ qv = 2 ∨ qv = 3 ∨ qv = 4 ∨ qv = 5 ∨ qv = 6 ∨ qv = 7 ∨ qv = 8 ∨ qv = 9 ∨ qv = 10) with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl)
    (fun r hne ho => by
      have hrv : r.val ≠ 11 := fun hv => hne (Fin.ext hv)
      rcases (by have := r.isLt; omega : r.val = 0 ∨ r.val = 1 ∨ r.val = 2 ∨ r.val = 3 ∨ r.val = 4 ∨ r.val = 5 ∨ r.val = 6 ∨ r.val = 7 ∨ r.val = 8 ∨ r.val = 9 ∨ r.val = 10) with h|h|h|h|h|h|h|h|h|h|h
      · rw [tropCastRowW18 M_ab 0 r.val 0 ho (by decide) _ (by rw [h]; rfl)]; exact hel_m0_ne 0 (by decide) (by decide) 0 (by decide)
      · rw [tropCastRowW18 M_ab 0 r.val 1 ho (by decide) _ (by rw [h]; rfl)]; exact hel_m0_ne 1 (by decide) (by decide) 0 (by decide)
      · rw [tropCastRowW18 M_ab 0 r.val 2 ho (by decide) _ (by rw [h]; rfl), hel_m0_eq 2 (by decide) rfl 0 (by decide)]; exact hfp00
      · rw [tropCastRowW18 M_ab 0 r.val 3 ho (by decide) _ (by rw [h]; rfl)]; exact hel_m0_ne 3 (by decide) (by decide) 0 (by decide)
      · rw [tropCastRowW18 M_ab 0 r.val 4 ho (by decide) _ (by rw [h]; rfl)]; exact hel_m0_ne 4 (by decide) (by decide) 0 (by decide)
      · rw [tropCastRowW18 M_ab 0 r.val 5 ho (by decide) _ (by rw [h]; rfl), hel_m0_eq 5 (by decide) rfl 0 (by decide)]; exact hfp10
      · rw [tropCastRowW18 M_ab 0 r.val 6 ho (by decide) _ (by rw [h]; rfl)]; exact hel_m0_ne 6 (by decide) (by decide) 0 (by decide)
      · rw [tropCastRowW18 M_ab 0 r.val 7 ho (by decide) _ (by rw [h]; rfl)]; exact hel_m0_ne 7 (by decide) (by decide) 0 (by decide)
      · rw [tropCastRowW18 M_ab 0 r.val 8 ho (by decide) _ (by rw [h]; rfl), hel_m0_eq 8 (by decide) rfl 0 (by decide)]; exact hfp20
      · rw [tropCastRowW18 M_ab 0 r.val 9 ho (by decide) _ (by rw [h]; rfl)]; exact hel_m0_ne 9 (by decide) (by decide) 0 (by decide)
      · rw [tropCastRowW18 M_ab 0 r.val 10 ho (by decide) _ (by rw [h]; rfl)]; exact hel_m0_ne 10 (by decide) (by decide) 0 (by decide))
    (by rw [hel_m0_eq 11 (by decide) rfl 0 (by decide)]; exact hfp30)
  have p1 := tropStepPeelW18 M_ab 10 1 8 8 (by decide) rfl (by decide) (by decide) (by decide) (-(2 * (k * k))) rfl
    (fun ⟨qv, hq⟩ => by rcases (by omega : qv = 0 ∨ qv = 1 ∨ qv = 2 ∨ qv = 3 ∨ qv = 4 ∨ qv = 5 ∨ qv = 6 ∨ qv = 7 ∨ qv = 8 ∨ qv = 9) with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl)
    (fun r hne ho => by
      have hrv : r.val ≠ 8 := fun hv => hne (Fin.ext hv)
      rcases (by have := r.isLt; omega : r.val = 0 ∨ r.val = 1 ∨ r.val = 2 ∨ r.val = 3 ∨ r.val = 4 ∨ r.val = 5 ∨ r.val = 6 ∨ r.val = 7 ∨ r.val = 9 ∨ r.val = 10) with h|h|h|h|h|h|h|h|h|h
      · rw [tropCastRowW18 M_ab 1 r.val 0 ho (by decide) _ (by rw [h]; rfl)]; exact hel_m0_ne 0 (by decide) (by decide) 1 (by decide)
      · rw [tropCastRowW18 M_ab 1 r.val 1 ho (by decide) _ (by rw [h]; rfl)]; exact hel_m0_ne 1 (by decide) (by decide) 1 (by decide)
      · rw [tropCastRowW18 M_ab 1 r.val 2 ho (by decide) _ (by rw [h]; rfl), hel_m0_eq 2 (by decide) rfl 1 (by decide)]; exact hfp01
      · rw [tropCastRowW18 M_ab 1 r.val 3 ho (by decide) _ (by rw [h]; rfl)]; exact hel_m0_ne 3 (by decide) (by decide) 1 (by decide)
      · rw [tropCastRowW18 M_ab 1 r.val 4 ho (by decide) _ (by rw [h]; rfl)]; exact hel_m0_ne 4 (by decide) (by decide) 1 (by decide)
      · rw [tropCastRowW18 M_ab 1 r.val 5 ho (by decide) _ (by rw [h]; rfl), hel_m0_eq 5 (by decide) rfl 1 (by decide)]; exact hfp11
      · rw [tropCastRowW18 M_ab 1 r.val 6 ho (by decide) _ (by rw [h]; rfl)]; exact hel_m0_ne 6 (by decide) (by decide) 1 (by decide)
      · rw [tropCastRowW18 M_ab 1 r.val 7 ho (by decide) _ (by rw [h]; rfl)]; exact hel_m0_ne 7 (by decide) (by decide) 1 (by decide)
      · rw [tropCastRowW18 M_ab 1 r.val 9 ho (by decide) _ (by rw [h]; rfl)]; exact hel_m0_ne 9 (by decide) (by decide) 1 (by decide)
      · rw [tropCastRowW18 M_ab 1 r.val 10 ho (by decide) _ (by rw [h]; rfl)]; exact hel_m0_ne 10 (by decide) (by decide) 1 (by decide))
    (by rw [hel_m0_eq 8 (by decide) rfl 1 (by decide)]; exact hfp21)
  have p2 := tropStepPeelW18 M_ab 9 2 5 5 (by decide) rfl (by decide) (by decide) (by decide) k rfl
    (fun ⟨qv, hq⟩ => by rcases (by omega : qv = 0 ∨ qv = 1 ∨ qv = 2 ∨ qv = 3 ∨ qv = 4 ∨ qv = 5 ∨ qv = 6 ∨ qv = 7 ∨ qv = 8) with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl)
    (fun r hne ho => by
      have hrv : r.val ≠ 5 := fun hv => hne (Fin.ext hv)
      rcases (by have := r.isLt; omega : r.val = 0 ∨ r.val = 1 ∨ r.val = 2 ∨ r.val = 3 ∨ r.val = 4 ∨ r.val = 6 ∨ r.val = 7 ∨ r.val = 8 ∨ r.val = 9) with h|h|h|h|h|h|h|h|h
      · rw [tropCastRowW18 M_ab 2 r.val 0 ho (by decide) _ (by rw [h]; rfl)]; exact hel_m0_ne 0 (by decide) (by decide) 2 (by decide)
      · rw [tropCastRowW18 M_ab 2 r.val 1 ho (by decide) _ (by rw [h]; rfl)]; exact hel_m0_ne 1 (by decide) (by decide) 2 (by decide)
      · rw [tropCastRowW18 M_ab 2 r.val 2 ho (by decide) _ (by rw [h]; rfl), hel_m0_eq 2 (by decide) rfl 2 (by decide)]; exact hfp02
      · rw [tropCastRowW18 M_ab 2 r.val 3 ho (by decide) _ (by rw [h]; rfl)]; exact hel_m0_ne 3 (by decide) (by decide) 2 (by decide)
      · rw [tropCastRowW18 M_ab 2 r.val 4 ho (by decide) _ (by rw [h]; rfl)]; exact hel_m0_ne 4 (by decide) (by decide) 2 (by decide)
      · rw [tropCastRowW18 M_ab 2 r.val 6 ho (by decide) _ (by rw [h]; rfl)]; exact hel_m0_ne 6 (by decide) (by decide) 2 (by decide)
      · rw [tropCastRowW18 M_ab 2 r.val 7 ho (by decide) _ (by rw [h]; rfl)]; exact hel_m0_ne 7 (by decide) (by decide) 2 (by decide)
      · rw [tropCastRowW18 M_ab 2 r.val 9 ho (by decide) _ (by rw [h]; rfl)]; exact hel_m0_ne 9 (by decide) (by decide) 2 (by decide)
      · rw [tropCastRowW18 M_ab 2 r.val 10 ho (by decide) _ (by rw [h]; rfl)]; exact hel_m0_ne 10 (by decide) (by decide) 2 (by decide))
    (by rw [hel_m0_eq 5 (by decide) rfl 2 (by decide)]; exact hfp12)
  have p3 := tropStepPeelW18 M_ab 8 3 2 2 (by decide) rfl (by decide) (by decide) (by decide) (-1) rfl
    (fun ⟨qv, hq⟩ => by rcases (by omega : qv = 0 ∨ qv = 1 ∨ qv = 2 ∨ qv = 3 ∨ qv = 4 ∨ qv = 5 ∨ qv = 6 ∨ qv = 7) with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl)
    (fun r hne ho => by
      have hrv : r.val ≠ 2 := fun hv => hne (Fin.ext hv)
      rcases (by have := r.isLt; omega : r.val = 0 ∨ r.val = 1 ∨ r.val = 3 ∨ r.val = 4 ∨ r.val = 5 ∨ r.val = 6 ∨ r.val = 7 ∨ r.val = 8) with h|h|h|h|h|h|h|h
      · rw [tropCastRowW18 M_ab 3 r.val 0 ho (by decide) _ (by rw [h]; rfl)]; exact hel_m0_ne 0 (by decide) (by decide) 3 (by decide)
      · rw [tropCastRowW18 M_ab 3 r.val 1 ho (by decide) _ (by rw [h]; rfl)]; exact hel_m0_ne 1 (by decide) (by decide) 3 (by decide)
      · rw [tropCastRowW18 M_ab 3 r.val 3 ho (by decide) _ (by rw [h]; rfl)]; exact hel_m0_ne 3 (by decide) (by decide) 3 (by decide)
      · rw [tropCastRowW18 M_ab 3 r.val 4 ho (by decide) _ (by rw [h]; rfl)]; exact hel_m0_ne 4 (by decide) (by decide) 3 (by decide)
      · rw [tropCastRowW18 M_ab 3 r.val 6 ho (by decide) _ (by rw [h]; rfl)]; exact hel_m0_ne 6 (by decide) (by decide) 3 (by decide)
      · rw [tropCastRowW18 M_ab 3 r.val 7 ho (by decide) _ (by rw [h]; rfl)]; exact hel_m0_ne 7 (by decide) (by decide) 3 (by decide)
      · rw [tropCastRowW18 M_ab 3 r.val 9 ho (by decide) _ (by rw [h]; rfl)]; exact hel_m0_ne 9 (by decide) (by decide) 3 (by decide)
      · rw [tropCastRowW18 M_ab 3 r.val 10 ho (by decide) _ (by rw [h]; rfl)]; exact hel_m0_ne 10 (by decide) (by decide) 3 (by decide))
    (by rw [hel_m0_eq 2 (by decide) rfl 3 (by decide)]; exact hfp03)
  have hk6 : (k * k * k) * (k * k) * k = intPowNat k 6 := by simp only [intPowNat, Int.mul_one]; ac_rfl
  generalize intDet 12 (tropSubStageRemW18 M_ab 12) = D12,
             intDet 11 (tropSubStageRemW18 M_ab 11) = D11,
             intDet 10 (tropSubStageRemW18 M_ab 10) = D10,
             intDet 9 (tropSubStageRemW18 M_ab 9) = D9,
             intDet 8 (tropSubStageRemW18 M_ab 8) = D8 at p0 p1 p2 p3 ⊢
  rw [p0, p1, p2, p3]
  simp only [↓reduceIte, Int.one_mul, Int.mul_neg, Int.neg_mul, Int.neg_neg]
  rw [← hk6, show (12 : Int) = 6 * 2 by decide]; ac_rfl

private theorem tropPeelBlock1_w18 (k C : Int) (M_ab : Fin 12 -> Fin 12 -> Int)
    (hblk : tropBlkSpecPropW18 k C M_ab) :
    intDet 8 (tropSubStageRemW18 M_ab 8) =
      12 * intPowNat C 6 * intPowNat k 6 * intDet 4 (tropSubStageRemW18 M_ab 4) := by
  have hel_m1_r0 : ∀ (r_i : Nat) (hr : r_i < 12), r_i % 3 = 0 -> ∀ (t : Nat) (ht : t < 4),
      M_ab ⟨r_i, hr⟩ ⟨4 + t, by omega⟩ = 0 :=
    fun r_i hr heq t ht => ((hblk ⟨r_i, hr⟩ 1 t (by omega) ht).2.1 rfl).1 heq
  have hel_m1_r1 : ∀ (r_i : Nat) (hr : r_i < 12), r_i % 3 = 1 -> ∀ (t : Nat) (ht : t < 4),
      M_ab ⟨r_i, hr⟩ ⟨4 + t, by omega⟩ = fallPowValW18 (r_i / 3) k t * intPowNat C (r_i / 3) :=
    fun r_i hr heq t ht => ((hblk ⟨r_i, hr⟩ 1 t (by omega) ht).2.1 rfl).2 heq
  have hfp00 : fallPowValW18 0 k 0 = 0 := Int.zero_mul _
  have hfp10 : fallPowValW18 1 k 0 = 0 := Int.zero_mul _
  have hfp20 : fallPowValW18 2 k 0 = 0 := Int.zero_mul _
  have hfp30 : fallPowValW18 3 k 0 = 6 * (k * k * k) := rfl
  have hfp01 : fallPowValW18 0 k 1 = 0 := by change -(0 * (k * k)) = 0; rw [Int.zero_mul]; rfl
  have hfp11 : fallPowValW18 1 k 1 = 0 := by change -(0 * (k * k)) = 0; rw [Int.zero_mul]; rfl
  have hfp21 : fallPowValW18 2 k 1 = -(2 * (k * k)) := rfl
  have hfp02 : fallPowValW18 0 k 2 = 0 := Int.zero_mul k
  have hfp12 : fallPowValW18 1 k 2 = k := Int.one_mul k
  have hfp03 : fallPowValW18 0 k 3 = -1 := rfl
  have p4 := tropStepPeelW18 M_ab 7 4 7 10 (by decide) rfl (by decide) (by decide) (by decide) (6 * (k * k * k) * intPowNat C 3) rfl
    (fun ⟨qv, hq⟩ => by rcases (by omega : qv = 0 ∨ qv = 1 ∨ qv = 2 ∨ qv = 3 ∨ qv = 4 ∨ qv = 5 ∨ qv = 6) with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl)
    (fun r hne ho => by
      have hrv : r.val ≠ 7 := fun hv => hne (Fin.ext hv)
      rcases (by have := r.isLt; omega : r.val = 0 ∨ r.val = 1 ∨ r.val = 2 ∨ r.val = 3 ∨ r.val = 4 ∨ r.val = 5 ∨ r.val = 6) with h|h|h|h|h|h|h
      · rw [tropCastRowW18 M_ab 4 r.val 0 ho (by decide) _ (by rw [h]; rfl)]; exact hel_m1_r0 0 (by decide) rfl 0 (by decide)
      · rw [tropCastRowW18 M_ab 4 r.val 1 ho (by decide) _ (by rw [h]; rfl), hel_m1_r1 1 (by decide) rfl 0 (by decide), show (1 / 3 : Nat) = 0 from rfl, hfp00, Int.zero_mul]
      · rw [tropCastRowW18 M_ab 4 r.val 3 ho (by decide) _ (by rw [h]; rfl)]; exact hel_m1_r0 3 (by decide) rfl 0 (by decide)
      · rw [tropCastRowW18 M_ab 4 r.val 4 ho (by decide) _ (by rw [h]; rfl), hel_m1_r1 4 (by decide) rfl 0 (by decide), show (4 / 3 : Nat) = 1 from rfl, hfp10, Int.zero_mul]
      · rw [tropCastRowW18 M_ab 4 r.val 6 ho (by decide) _ (by rw [h]; rfl)]; exact hel_m1_r0 6 (by decide) rfl 0 (by decide)
      · rw [tropCastRowW18 M_ab 4 r.val 7 ho (by decide) _ (by rw [h]; rfl), hel_m1_r1 7 (by decide) rfl 0 (by decide), show (7 / 3 : Nat) = 2 from rfl, hfp20, Int.zero_mul]
      · rw [tropCastRowW18 M_ab 4 r.val 9 ho (by decide) _ (by rw [h]; rfl)]; exact hel_m1_r0 9 (by decide) rfl 0 (by decide))
    (by rw [hel_m1_r1 10 (by decide) rfl 0 (by decide), show (10 / 3 : Nat) = 3 from rfl, hfp30])
  have p5 := tropStepPeelW18 M_ab 6 5 5 7 (by decide) rfl (by decide) (by decide) (by decide) (-(2 * (k * k)) * intPowNat C 2) rfl
    (fun ⟨qv, hq⟩ => by rcases (by omega : qv = 0 ∨ qv = 1 ∨ qv = 2 ∨ qv = 3 ∨ qv = 4 ∨ qv = 5) with rfl|rfl|rfl|rfl|rfl|rfl <;> rfl)
    (fun r hne ho => by
      have hrv : r.val ≠ 5 := fun hv => hne (Fin.ext hv)
      rcases (by have := r.isLt; omega : r.val = 0 ∨ r.val = 1 ∨ r.val = 2 ∨ r.val = 3 ∨ r.val = 4 ∨ r.val = 6) with h|h|h|h|h|h
      · rw [tropCastRowW18 M_ab 5 r.val 0 ho (by decide) _ (by rw [h]; rfl)]; exact hel_m1_r0 0 (by decide) rfl 1 (by decide)
      · rw [tropCastRowW18 M_ab 5 r.val 1 ho (by decide) _ (by rw [h]; rfl), hel_m1_r1 1 (by decide) rfl 1 (by decide), show (1 / 3 : Nat) = 0 from rfl, hfp01, Int.zero_mul]
      · rw [tropCastRowW18 M_ab 5 r.val 3 ho (by decide) _ (by rw [h]; rfl)]; exact hel_m1_r0 3 (by decide) rfl 1 (by decide)
      · rw [tropCastRowW18 M_ab 5 r.val 4 ho (by decide) _ (by rw [h]; rfl), hel_m1_r1 4 (by decide) rfl 1 (by decide), show (4 / 3 : Nat) = 1 from rfl, hfp11, Int.zero_mul]
      · rw [tropCastRowW18 M_ab 5 r.val 6 ho (by decide) _ (by rw [h]; rfl)]; exact hel_m1_r0 6 (by decide) rfl 1 (by decide)
      · rw [tropCastRowW18 M_ab 5 r.val 9 ho (by decide) _ (by rw [h]; rfl)]; exact hel_m1_r0 9 (by decide) rfl 1 (by decide))
    (by rw [hel_m1_r1 7 (by decide) rfl 1 (by decide), show (7 / 3 : Nat) = 2 from rfl, hfp21])
  have p6 := tropStepPeelW18 M_ab 5 6 3 4 (by decide) rfl (by decide) (by decide) (by decide) (k * intPowNat C 1) rfl
    (fun ⟨qv, hq⟩ => by rcases (by omega : qv = 0 ∨ qv = 1 ∨ qv = 2 ∨ qv = 3 ∨ qv = 4) with rfl|rfl|rfl|rfl|rfl <;> rfl)
    (fun r hne ho => by
      have hrv : r.val ≠ 3 := fun hv => hne (Fin.ext hv)
      rcases (by have := r.isLt; omega : r.val = 0 ∨ r.val = 1 ∨ r.val = 2 ∨ r.val = 4 ∨ r.val = 5) with h|h|h|h|h
      · rw [tropCastRowW18 M_ab 6 r.val 0 ho (by decide) _ (by rw [h]; rfl)]; exact hel_m1_r0 0 (by decide) rfl 2 (by decide)
      · rw [tropCastRowW18 M_ab 6 r.val 1 ho (by decide) _ (by rw [h]; rfl), hel_m1_r1 1 (by decide) rfl 2 (by decide), show (1 / 3 : Nat) = 0 from rfl, hfp02, Int.zero_mul]
      · rw [tropCastRowW18 M_ab 6 r.val 3 ho (by decide) _ (by rw [h]; rfl)]; exact hel_m1_r0 3 (by decide) rfl 2 (by decide)
      · rw [tropCastRowW18 M_ab 6 r.val 6 ho (by decide) _ (by rw [h]; rfl)]; exact hel_m1_r0 6 (by decide) rfl 2 (by decide)
      · rw [tropCastRowW18 M_ab 6 r.val 9 ho (by decide) _ (by rw [h]; rfl)]; exact hel_m1_r0 9 (by decide) rfl 2 (by decide))
    (by rw [hel_m1_r1 4 (by decide) rfl 2 (by decide), show (4 / 3 : Nat) = 1 from rfl, hfp12])
  have p7 := tropStepPeelW18 M_ab 4 7 1 1 (by decide) rfl (by decide) (by decide) (by decide) (-1) rfl
    (fun ⟨qv, hq⟩ => by rcases (by omega : qv = 0 ∨ qv = 1 ∨ qv = 2 ∨ qv = 3) with rfl|rfl|rfl|rfl <;> rfl)
    (fun r hne ho => by
      have hrv : r.val ≠ 1 := fun hv => hne (Fin.ext hv)
      rcases (by have := r.isLt; omega : r.val = 0 ∨ r.val = 2 ∨ r.val = 3 ∨ r.val = 4) with h|h|h|h
      · rw [tropCastRowW18 M_ab 7 r.val 0 ho (by decide) _ (by rw [h]; rfl)]; exact hel_m1_r0 0 (by decide) rfl 3 (by decide)
      · rw [tropCastRowW18 M_ab 7 r.val 3 ho (by decide) _ (by rw [h]; rfl)]; exact hel_m1_r0 3 (by decide) rfl 3 (by decide)
      · rw [tropCastRowW18 M_ab 7 r.val 6 ho (by decide) _ (by rw [h]; rfl)]; exact hel_m1_r0 6 (by decide) rfl 3 (by decide)
      · rw [tropCastRowW18 M_ab 7 r.val 9 ho (by decide) _ (by rw [h]; rfl)]; exact hel_m1_r0 9 (by decide) rfl 3 (by decide))
    (by rw [hel_m1_r1 1 (by decide) rfl 3 (by decide), show (1 / 3 : Nat) = 0 from rfl, hfp03]; rfl)
  have hk6 : (k * k * k) * (k * k) * k = intPowNat k 6 := by simp only [intPowNat, Int.mul_one]; ac_rfl
  have hC6 : intPowNat C 3 * intPowNat C 2 * intPowNat C 1 = intPowNat C 6 := by
    rw [← intPowNat_add C 3 2, ← intPowNat_add C 5 1]
  generalize intDet 8 (tropSubStageRemW18 M_ab 8) = D8,
             intDet 7 (tropSubStageRemW18 M_ab 7) = D7,
             intDet 6 (tropSubStageRemW18 M_ab 6) = D6,
             intDet 5 (tropSubStageRemW18 M_ab 5) = D5,
             intDet 4 (tropSubStageRemW18 M_ab 4) = D4 at p4 p5 p6 p7 ⊢
  rw [p4, p5, p6, p7]
  simp only [Int.mul_neg, Int.neg_mul, Int.neg_neg]
  rw [← hk6, ← hC6, show (12 : Int) = 6 * 2 by decide]; ac_rfl

private theorem tropPeelBlock2_w18 (k C : Int) (M_ab : Fin 12 -> Fin 12 -> Int)
    (hblk : tropBlkSpecPropW18 k C M_ab) :
    intDet 4 (tropSubStageRemW18 M_ab 4) = 12 * intPowNat C 12 * intPowNat k 6 := by
  have hel_m2_r0 : ∀ (r_i : Nat) (hr : r_i < 12), r_i % 3 = 0 -> ∀ (t : Nat) (ht : t < 4),
      M_ab ⟨r_i, hr⟩ ⟨8 + t, by omega⟩ = fallPowValW18 (r_i / 3) k t * intPowNat C (r_i / 3 * 2) :=
    fun r_i hr heq t ht => (hblk ⟨r_i, hr⟩ 2 t (by omega) ht).2.2 rfl heq
  have hfp00 : fallPowValW18 0 k 0 = 0 := Int.zero_mul _
  have hfp10 : fallPowValW18 1 k 0 = 0 := Int.zero_mul _
  have hfp20 : fallPowValW18 2 k 0 = 0 := Int.zero_mul _
  have hfp30 : fallPowValW18 3 k 0 = 6 * (k * k * k) := rfl
  have hfp01 : fallPowValW18 0 k 1 = 0 := by change -(0 * (k * k)) = 0; rw [Int.zero_mul]; rfl
  have hfp11 : fallPowValW18 1 k 1 = 0 := by change -(0 * (k * k)) = 0; rw [Int.zero_mul]; rfl
  have hfp21 : fallPowValW18 2 k 1 = -(2 * (k * k)) := rfl
  have hfp02 : fallPowValW18 0 k 2 = 0 := Int.zero_mul k
  have hfp12 : fallPowValW18 1 k 2 = k := Int.one_mul k
  have hfp03 : fallPowValW18 0 k 3 = -1 := rfl
  have p8 := tropStepPeelW18 M_ab 3 8 3 9 (by decide) rfl (by decide) (by decide) (by decide) (6 * (k * k * k) * intPowNat C 6) rfl
    (fun ⟨qv, hq⟩ => by rcases (by omega : qv = 0 ∨ qv = 1 ∨ qv = 2) with rfl|rfl|rfl <;> rfl)
    (fun r hne ho => by
      have hrv : r.val ≠ 3 := fun hv => hne (Fin.ext hv)
      rcases (by have := r.isLt; omega : r.val = 0 ∨ r.val = 1 ∨ r.val = 2) with h|h|h
      · rw [tropCastRowW18 M_ab 8 r.val 0 ho (by decide) _ (by rw [h]; rfl), hel_m2_r0 0 (by decide) rfl 0 (by decide), show (0 / 3 : Nat) = 0 from rfl, hfp00, Int.zero_mul]
      · rw [tropCastRowW18 M_ab 8 r.val 3 ho (by decide) _ (by rw [h]; rfl), hel_m2_r0 3 (by decide) rfl 0 (by decide), show (3 / 3 : Nat) = 1 from rfl, hfp10, Int.zero_mul]
      · rw [tropCastRowW18 M_ab 8 r.val 6 ho (by decide) _ (by rw [h]; rfl), hel_m2_r0 6 (by decide) rfl 0 (by decide), show (6 / 3 : Nat) = 2 from rfl, hfp20, Int.zero_mul])
    (by rw [hel_m2_r0 9 (by decide) rfl 0 (by decide), show (9 / 3 : Nat) = 3 from rfl, hfp30])
  have p9 := tropStepPeelW18 M_ab 2 9 2 6 (by decide) rfl (by decide) (by decide) (by decide) (-(2 * (k * k)) * intPowNat C 4) rfl
    (fun ⟨qv, hq⟩ => by rcases (by omega : qv = 0 ∨ qv = 1) with rfl|rfl <;> rfl)
    (fun r hne ho => by
      have hrv : r.val ≠ 2 := fun hv => hne (Fin.ext hv)
      rcases (by have := r.isLt; omega : r.val = 0 ∨ r.val = 1) with h|h
      · rw [tropCastRowW18 M_ab 9 r.val 0 ho (by decide) _ (by rw [h]; rfl), hel_m2_r0 0 (by decide) rfl 1 (by decide), show (0 / 3 : Nat) = 0 from rfl, hfp01, Int.zero_mul]
      · rw [tropCastRowW18 M_ab 9 r.val 3 ho (by decide) _ (by rw [h]; rfl), hel_m2_r0 3 (by decide) rfl 1 (by decide), show (3 / 3 : Nat) = 1 from rfl, hfp11, Int.zero_mul])
    (by rw [hel_m2_r0 6 (by decide) rfl 1 (by decide), show (6 / 3 : Nat) = 2 from rfl, hfp21])
  have p10 := tropStepPeelW18 M_ab 1 10 1 3 (by decide) rfl (by decide) (by decide) (by decide) (k * intPowNat C 2) rfl
    (fun ⟨qv, hq⟩ => by cases qv with | zero => rfl | succ _ => omega)
    (fun r hne ho => by
      have h0 : r.val = 0 := by have hrv : r.val ≠ 1 := fun hv => hne (Fin.ext hv); have := r.isLt; omega
      rw [tropCastRowW18 M_ab 10 r.val 0 ho (by decide) _ (by rw [h0]; rfl), hel_m2_r0 0 (by decide) rfl 2 (by decide), show (0 / 3 : Nat) = 0 from rfl, hfp02, Int.zero_mul])
    (by rw [hel_m2_r0 3 (by decide) rfl 2 (by decide), show (3 / 3 : Nat) = 1 from rfl, hfp12])
  have p11 := tropStepPeelW18 M_ab 0 11 0 0 (by decide) rfl (by decide) (by decide) (by decide) (-1) rfl
    (fun q => Fin.elim0 q)
    (fun r hne _ => False.elim (hne (Fin.ext (by have := r.isLt; omega))))
    (by rw [hel_m2_r0 0 (by decide) rfl 3 (by decide), show (0 / 3 : Nat) = 0 from rfl, hfp03]; rfl)
  have hend0 : intDet 0 (tropSubStageRemW18 M_ab 0) = 1 := rfl
  have hk6 : (k * k * k) * (k * k) * k = intPowNat k 6 := by simp only [intPowNat, Int.mul_one]; ac_rfl
  have hC12 : intPowNat C 6 * intPowNat C 4 * intPowNat C 2 = intPowNat C 12 := by
    rw [← intPowNat_add C 6 4, ← intPowNat_add C 10 2]
  rw [hend0] at p11
  generalize intDet 4 (tropSubStageRemW18 M_ab 4) = D4,
             intDet 3 (tropSubStageRemW18 M_ab 3) = D3,
             intDet 2 (tropSubStageRemW18 M_ab 2) = D2,
             intDet 1 (tropSubStageRemW18 M_ab 1) = D1 at p8 p9 p10 p11 ⊢
  rw [p8, p9, p10, p11]
  simp only [↓reduceIte, Int.one_mul, Int.mul_one, Int.mul_neg, Int.neg_mul, Int.neg_neg]
  rw [← hk6, ← hC12, show (12 : Int) = 6 * 2 by decide]; ac_rfl

private theorem tropPeelDet12_w18 (k C : Int) (M_ab : Fin 12 -> Fin 12 -> Int)
    (hblk : tropBlkSpecPropW18 k C M_ab) :
    intDet 12 M_ab = 1728 * intPowNat C 18 * intPowNat k 18 := by
  have hst12 : tropSubStageRemW18 M_ab 12 = M_ab := by
    funext r c
    have hget0 : (tropRowMapW18 0).getD r.val 0 = r.val := by
      rcases (by have := r.isLt; omega :
        r.val = 0 ∨ r.val = 1 ∨ r.val = 2 ∨ r.val = 3 ∨ r.val = 4 ∨ r.val = 5 ∨
        r.val = 6 ∨ r.val = 7 ∨ r.val = 8 ∨ r.val = 9 ∨ r.val = 10 ∨ r.val = 11) with
        hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr | hr <;> (rw [hr]; decide)
    dsimp only [tropSubStageRemW18]
    change (if h : (tropRowMapW18 0).getD r.val 0 < 12 ∧ 0 + c.val < 12 then M_ab ⟨(tropRowMapW18 0).getD r.val 0, h.1⟩ ⟨0 + c.val, h.2⟩ else 0) = M_ab r c
    have hg : (tropRowMapW18 0).getD r.val 0 < 12 ∧ 0 + c.val < 12 := by rw [hget0]; exact ⟨r.isLt, by omega⟩
    rw [dite_pos_w18 hg]
    congr 1; exact Fin.ext hget0; exact Fin.ext (Nat.zero_add c.val)
  have hb0 := tropPeelBlock0_w18 k C M_ab hblk
  have hb1 := tropPeelBlock1_w18 k C M_ab hblk
  have hb2 := tropPeelBlock2_w18 k C M_ab hblk
  rw [hst12] at hb0
  generalize intDet 12 M_ab = D12,
             intDet 8 (tropSubStageRemW18 M_ab 8) = D8,
             intDet 4 (tropSubStageRemW18 M_ab 4) = D4 at hb0 hb1 hb2 ⊢
  rw [hb0, hb1, hb2]
  have hC18 : intPowNat C 6 * intPowNat C 12 = intPowNat C 18 := (intPowNat_add C 6 12).symm
  have hk18 : intPowNat k 6 * (intPowNat k 6 * intPowNat k 6) = intPowNat k 18 := by
    rw [← intPowNat_add k 6 6, ← intPowNat_add k 6 12]
  rw [← hC18, ← hk18, show (1728 : Int) = 12 * (12 * 12) by decide]
  ac_rfl

private theorem tropRedPowMat_det_w18 (w k C : Int) :
    intDet 12 (tropRedPowMatW18 w k C) = 1728 * intPowNat C 18 * intPowNat k 18 := by
  rw [← applyColOpsW18_det 12 (tropColOpsListW18 w k) (tropRedPowMatW18 w k C)]
  exact tropPeelDet12_w18 k C _ (tropBlkChar_w18 w k C)

private def bColTropW18 (m : Nat) : Nat := match m with | 0 => 3 | 1 => 1 | _ => 0
private def aRowTropW18 (r : Nat) : Nat := match r with | 0 => 0 | 1 => 2 | _ => 3

private def colPrefExpTropW18 (u : Nat) : Nat -> Nat
  | 0 => 0
  | c + 1 => bColTropW18 (c / 4) * u + colPrefExpTropW18 u c

private def rowPrefExpTropW18 (u : Nat) : Nat -> Nat
  | 0 => 0
  | r + 1 => aRowTropW18 (r % 3) * u + rowPrefExpTropW18 u r

private theorem det12_t4u3_2adic_congr_w18 (W K u : Nat) :
    Int.ofNat (2 ^ (5 * u)) ∣
      (intDet 12 (laurentTwoBaseT4U3Mat12 W K u) -
        Int.ofNat (2 ^ (4 * u) * 3 ^ (18 * u) * K ^ 18)) := by
  have hmul_ofNat : ∀ a b : Nat, Int.ofNat (a * b) = Int.ofNat a * Int.ofNat b := Int.natCast_mul
  let bCol := bColTropW18
  let aRow := aRowTropW18
  let M_trop : Fin 12 -> Fin 12 -> Int := fun i j =>
    let r := i.val % 3; let s := i.val / 3
    let t := j.val % 4; let m := j.val / 4
    let e2 := (r * m + bCol m - aRow r) * u
    Int.ofNat (laurentInterpBinom (r * W + s * K) t * (2 ^ e2 * 3 ^ (s * (m * u))))
  let colPrefExp := colPrefExpTropW18 u
  let rowPrefExp := rowPrefExpTropW18 u
  let M_col (c_done : Nat) (i j : Fin 12) : Int :=
    if j.val < c_done then Int.ofNat (2 ^ (bCol (j.val / 4) * u)) * laurentTwoBaseT4U3Mat12 W K u i j
    else laurentTwoBaseT4U3Mat12 W K u i j
  have hcol_ind : ∀ n : Nat, n ≤ 12 ->
      intDet 12 (M_col n) = Int.ofNat (2 ^ colPrefExp n) * intDet 12 (M_col 0) := by
    intro n; induction n with
    | zero => intro _; rw [show Int.ofNat (2 ^ colPrefExp 0) = 1 from rfl, Int.one_mul]
    | succ n' ih =>
      intro hn
      let jn : Fin 12 := ⟨n', hn⟩
      have heq_c : M_col (n' + 1) = (fun i j =>
          if j = jn then Int.ofNat (2 ^ (bCol (n' / 4) * u)) * M_col n' i jn else M_col n' i j) := by
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
  let M_row (r_done : Nat) (i j : Fin 12) : Int :=
    if i.val < r_done then Int.ofNat (2 ^ (aRow (i.val % 3) * u)) * M_trop i j
    else M_trop i j
  have hrow_ind : ∀ n : Nat, n ≤ 12 ->
      intDet 12 (M_row n) = Int.ofNat (2 ^ rowPrefExp n) * intDet 12 (M_row 0) := by
    intro n; induction n with
    | zero => intro _; rw [show Int.ofNat (2 ^ rowPrefExp 0) = 1 from rfl, Int.one_mul]
    | succ n' ih =>
      intro hn
      have heq_r : M_row (n' + 1) = (fun i j =>
          if i.val = n' then Int.ofNat (2 ^ (aRow (n' % 3) * u)) * M_row n' i j else M_row n' i j) := by
        funext i j
        by_cases hi : i.val = n'
        · dsimp [M_row]; rw [ite_true_of_w10 (by omega : i.val < n' + 1), ite_true_of_w10 hi,
                              ite_false_of_w10 (by omega : ¬ (i.val < n')), hi]
        · dsimp [M_row]; rw [ite_false_of_w10 hi]
          by_cases hlt : i.val < n'
          · rw [ite_true_of_w10 (by omega), ite_true_of_w10 hlt]
          · rw [ite_false_of_w10 (by omega), ite_false_of_w10 hlt]
      rw [heq_r, intDet_scale_row_w18 _ 12 n' hn, ih (Nat.le_of_lt hn), ← Int.mul_assoc,
          ← hmul_ofNat, ← Nat.pow_add]; rfl
  have hMcol_eq_Mrow : M_col 12 = M_row 12 := by
    funext i j
    dsimp only [M_col, M_row]
    rw [ite_true_of_w10 j.isLt, ite_true_of_w10 i.isLt]
    dsimp only [M_trop]; unfold laurentTwoBaseT4U3Mat12 laurentInterpMat laurentInterpEntry
      laurentRowsTwoBase12 laurentColsT4U3_12
    dsimp only
    have hl_eq : Int.ofNat (laurentInterpBinom (i.val % 3 * W + i.val / 3 * K) (j.val % 4) *
        2 ^ (i.val % 3 * (j.val / 4 * u)) * 3 ^ (i.val / 3 * (j.val / 4 * u))) =
      ((laurentInterpBinom (i.val % 3 * W + i.val / 3 * K) (j.val % 4) *
        2 ^ (i.val % 3 * (j.val / 4 * u)) * 3 ^ (i.val / 3 * (j.val / 4 * u)) : Nat) : Int) := rfl
    rw [← hl_eq, ← hmul_ofNat, ← hmul_ofNat]
    apply congrArg Int.ofNat
    have hexp_eq : aRow (i.val % 3) * u + (i.val % 3 * (j.val / 4) + bCol (j.val / 4) - aRow (i.val % 3)) * u =
        bCol (j.val / 4) * u + i.val % 3 * (j.val / 4 * u) := by
      have hge : aRow (i.val % 3) ≤ i.val % 3 * (j.val / 4) + bCol (j.val / 4) := by
        rcases (by have := Nat.mod_lt i.val (by decide : 0 < 3); omega : i.val % 3 = 0 ∨ i.val % 3 = 1 ∨ i.val % 3 = 2) with hr | hr | hr <;>
        rcases (by have := j.isLt; omega : j.val / 4 = 0 ∨ j.val / 4 = 1 ∨ j.val / 4 = 2) with hm | hm | hm <;>
        simp [aRow, bCol, bColTropW18, aRowTropW18, hr, hm]
      have h1 : aRow (i.val % 3) + (i.val % 3 * (j.val / 4) + bCol (j.val / 4) - aRow (i.val % 3)) =
          bCol (j.val / 4) + i.val % 3 * (j.val / 4) := by omega
      calc aRow (i.val % 3) * u + (i.val % 3 * (j.val / 4) + bCol (j.val / 4) - aRow (i.val % 3)) * u
          = (aRow (i.val % 3) + (i.val % 3 * (j.val / 4) + bCol (j.val / 4) - aRow (i.val % 3))) * u := (Nat.add_mul _ _ _).symm
        _ = (bCol (j.val / 4) + i.val % 3 * (j.val / 4)) * u := by rw [h1]
        _ = bCol (j.val / 4) * u + i.val % 3 * (j.val / 4 * u) := by rw [Nat.add_mul, Nat.mul_assoc]
    calc 2 ^ (bCol (j.val / 4) * u) *
           (laurentInterpBinom (i.val % 3 * W + i.val / 3 * K) (j.val % 4) *
             2 ^ (i.val % 3 * (j.val / 4 * u)) * 3 ^ (i.val / 3 * (j.val / 4 * u)))
        = laurentInterpBinom (i.val % 3 * W + i.val / 3 * K) (j.val % 4) *
            (2 ^ (bCol (j.val / 4) * u) * 2 ^ (i.val % 3 * (j.val / 4 * u))) *
            3 ^ (i.val / 3 * (j.val / 4 * u)) := by ac_rfl
      _ = laurentInterpBinom (i.val % 3 * W + i.val / 3 * K) (j.val % 4) *
            2 ^ (bCol (j.val / 4) * u + i.val % 3 * (j.val / 4 * u)) *
            3 ^ (i.val / 3 * (j.val / 4 * u)) := by rw [← Nat.pow_add]
      _ = laurentInterpBinom (i.val % 3 * W + i.val / 3 * K) (j.val % 4) *
            (2 ^ (aRow (i.val % 3) * u) * 2 ^ ((i.val % 3 * (j.val / 4) + bCol (j.val / 4) - aRow (i.val % 3)) * u)) *
            3 ^ (i.val / 3 * (j.val / 4 * u)) := by rw [← hexp_eq, Nat.pow_add]
      _ = 2 ^ (aRow (i.val % 3) * u) *
            (laurentInterpBinom (i.val % 3 * W + i.val / 3 * K) (j.val % 4) *
              (2 ^ ((i.val % 3 * (j.val / 4) + bCol (j.val / 4) - aRow (i.val % 3)) * u) *
               3 ^ (i.val / 3 * (j.val / 4 * u)))) := by ac_rfl
  have hcol12_exp : colPrefExp 12 = 16 * u := by
    simp [colPrefExp, colPrefExpTropW18, bColTropW18]; omega
  have hrow12_exp : rowPrefExp 12 = 20 * u := by
    simp [rowPrefExp, rowPrefExpTropW18, aRowTropW18]; omega
  have hc0 : M_col 0 = laurentTwoBaseT4U3Mat12 W K u := by funext i j; simp [M_col]
  have hr0 : M_row 0 = M_trop := by funext i j; simp [M_row]
  have hscale_rel : intDet 12 (laurentTwoBaseT4U3Mat12 W K u) =
      Int.ofNat (2 ^ (4 * u)) * intDet 12 M_trop := by
    have heq12 := hcol_ind 12 (Nat.le_refl 12)
    rw [hMcol_eq_Mrow, hrow_ind 12 (Nat.le_refl 12), hcol12_exp, hrow12_exp, hc0, hr0] at heq12
    have h20 : Int.ofNat (2 ^ (20 * u)) = Int.ofNat (2 ^ (16 * u)) * Int.ofNat (2 ^ (4 * u)) := by
      rw [← hmul_ofNat, ← Nat.pow_add, show 16 * u + 4 * u = 20 * u by omega]
    rw [h20, Int.mul_assoc] at heq12
    have hp16_nz : Int.ofNat (2 ^ (16 * u)) ≠ 0 := by
      intro hz; injection hz with h0
      have hp := nat_pow_pos_of_pos 2 (by decide) (16 * u); omega
    exact Int.eq_of_mul_eq_mul_left hp16_nz heq12.symm
  let B_red : Fin 12 -> Fin 12 -> Int := fun i j =>
    let r := i.val % 3; let s := i.val / 3
    let t := j.val % 4; let m := j.val / 4
    if tropActiveBoolW18 r m then
      Int.ofNat (laurentInterpBinom (r * W + s * K) t * 3 ^ (s * (m * u)))
    else 0
  have hdvd_trop_red : Int.ofNat (2 ^ u) ∣ (intDet 12 M_trop - intDet 12 B_red) := by
    apply intDet_congr_dvd (Int.ofNat (2 ^ u)) 12
    intro i j
    change Int.ofNat (2 ^ u) ∣
      (Int.ofNat (laurentInterpBinom (i.val % 3 * W + i.val / 3 * K) (j.val % 4) *
        (2 ^ ((i.val % 3 * (j.val / 4) + bColTropW18 (j.val / 4) - aRowTropW18 (i.val % 3)) * u) *
         3 ^ (i.val / 3 * (j.val / 4 * u)))) -
       if tropActiveBoolW18 (i.val % 3) (j.val / 4) then
         Int.ofNat (laurentInterpBinom (i.val % 3 * W + i.val / 3 * K) (j.val % 4) *
           3 ^ (i.val / 3 * (j.val / 4 * u)))
       else 0)
    rcases (by have := Nat.mod_lt i.val (by decide : 0 < 3); omega : i.val % 3 = 0 ∨ i.val % 3 = 1 ∨ i.val % 3 = 2) with hr | hr | hr <;>
    rcases (by have := j.isLt; omega : j.val / 4 = 0 ∨ j.val / 4 = 1 ∨ j.val / 4 = 2) with hm | hm | hm
    · -- (0, 0)
      rw [hr, hm, show tropActiveBoolW18 0 0 = false from rfl]
      simp only [Bool.false_eq_true, ↓reduceIte, bColTropW18, aRowTropW18, Int.sub_zero]
      exact ⟨Int.ofNat (laurentInterpBinom (i.val / 3 * K) (j.val % 4) * 2 ^ (2 * u)),
        by rw [← hmul_ofNat]; apply congrArg Int.ofNat
           simp only [Nat.zero_mul, Nat.mul_zero, Nat.zero_add, Nat.pow_zero, Nat.mul_one]
           rw [show 3 * u = u + 2 * u by omega, Nat.pow_add 2 u (2 * u)]
           ac_rfl⟩
    · -- (0, 1)
      rw [hr, hm, show tropActiveBoolW18 0 1 = false from rfl]
      simp only [Bool.false_eq_true, ↓reduceIte, bColTropW18, aRowTropW18, Int.sub_zero]
      exact ⟨Int.ofNat (laurentInterpBinom (i.val / 3 * K) (j.val % 4) * 3 ^ (i.val / 3 * u)),
        by rw [← hmul_ofNat]; apply congrArg Int.ofNat
           simp only [Nat.zero_mul, Nat.zero_add, Nat.one_mul]
           ac_rfl⟩
    · -- (0, 2): active
      rw [hr, hm, show tropActiveBoolW18 0 2 = true from rfl]
      simp only [↓reduceIte, bColTropW18, aRowTropW18]
      have he02 : Int.ofNat (laurentInterpBinom (0 * W + i.val / 3 * K) (j.val % 4) * (2 ^ ((0 * 2 + 0 - 0) * u) * 3 ^ (i.val / 3 * (2 * u)))) =
          Int.ofNat (laurentInterpBinom (0 * W + i.val / 3 * K) (j.val % 4) * 3 ^ (i.val / 3 * (2 * u))) := by
        apply congrArg Int.ofNat; rw [show (0 * 2 + 0 - 0) * u = 0 by omega, Nat.pow_zero, Nat.one_mul]
      rw [he02, Int.sub_self]; exact ⟨0, (Int.mul_zero _).symm⟩
    · -- (1, 0)
      rw [hr, hm, show tropActiveBoolW18 1 0 = false from rfl]
      simp only [Bool.false_eq_true, ↓reduceIte, bColTropW18, aRowTropW18, Int.sub_zero]
      exact ⟨Int.ofNat (laurentInterpBinom (W + i.val / 3 * K) (j.val % 4)),
        by rw [← hmul_ofNat]; apply congrArg Int.ofNat
           simp only [Nat.zero_mul, Nat.mul_zero, Nat.one_mul, Nat.pow_zero, Nat.mul_one]
           ac_rfl⟩
    · -- (1, 1): active
      rw [hr, hm, show tropActiveBoolW18 1 1 = true from rfl]
      have he11 : (1 * 1 + bColTropW18 1 - aRowTropW18 1) * u = 0 := by simp [bColTropW18, aRowTropW18]
      simp only [↓reduceIte, he11, Nat.pow_zero, Nat.one_mul]
      rw [Int.sub_self]; exact ⟨0, (Int.mul_zero _).symm⟩
    · -- (1, 2): active
      rw [hr, hm, show tropActiveBoolW18 1 2 = true from rfl]
      have he12 : (1 * 2 + bColTropW18 2 - aRowTropW18 1) * u = 0 := by simp [bColTropW18, aRowTropW18]
      simp only [↓reduceIte, he12, Nat.pow_zero, Nat.one_mul]
      rw [Int.sub_self]; exact ⟨0, (Int.mul_zero _).symm⟩
    · -- (2, 0): active
      rw [hr, hm, show tropActiveBoolW18 2 0 = true from rfl]
      simp only [↓reduceIte, bColTropW18, aRowTropW18]
      have he20 : Int.ofNat (laurentInterpBinom (2 * W + i.val / 3 * K) (j.val % 4) * (2 ^ ((2 * 0 + 3 - 3) * u) * 3 ^ (i.val / 3 * (0 * u)))) =
          Int.ofNat (laurentInterpBinom (2 * W + i.val / 3 * K) (j.val % 4) * 3 ^ (i.val / 3 * (0 * u))) := by
        apply congrArg Int.ofNat; rw [show (2 * 0 + 3 - 3) * u = 0 by omega, Nat.pow_zero, Nat.one_mul]
      rw [he20, Int.sub_self]; exact ⟨0, (Int.mul_zero _).symm⟩
    · -- (2, 1): active
      rw [hr, hm, show tropActiveBoolW18 2 1 = true from rfl]
      simp only [↓reduceIte, bColTropW18, aRowTropW18]
      have he21 : Int.ofNat (laurentInterpBinom (2 * W + i.val / 3 * K) (j.val % 4) * (2 ^ ((2 * 1 + 1 - 3) * u) * 3 ^ (i.val / 3 * (1 * u)))) =
          Int.ofNat (laurentInterpBinom (2 * W + i.val / 3 * K) (j.val % 4) * 3 ^ (i.val / 3 * (1 * u))) := by
        apply congrArg Int.ofNat; rw [show (2 * 1 + 1 - 3) * u = 0 by omega, Nat.pow_zero, Nat.one_mul]
      rw [he21, Int.sub_self]; exact ⟨0, (Int.mul_zero _).symm⟩
    · -- (2, 2)
      rw [hr, hm, show tropActiveBoolW18 2 2 = false from rfl]
      simp only [Bool.false_eq_true, ↓reduceIte, bColTropW18, aRowTropW18, Int.sub_zero]
      exact ⟨Int.ofNat (laurentInterpBinom (2 * W + i.val / 3 * K) (j.val % 4) * 3 ^ (i.val / 3 * (2 * u))),
        by rw [← hmul_ofNat]; apply congrArg Int.ofNat
           rw [show (2 * 2 + 0 - 3) * u = u by omega]; ac_rfl⟩
  have hpow_nat : ∀ (n d : Nat), intPowNat (Int.ofNat n) d = Int.ofNat (n ^ d) := intPowNat_natCast_w18
  have hB_red_det : intDet 12 B_red = Int.ofNat (3 ^ (18 * u) * K ^ 18) := by
    let eFn (i : Fin 12) (m : Nat) : Int :=
      if tropActiveBoolW18 (i.val % 3) m then Int.ofNat (3 ^ (i.val / 3 * (m * u))) else 0
    have hB_eq : B_red = (fun i j => ((laurentInterpBinom (i.val % 3 * W + i.val / 3 * K) (j.val % 4) : Nat) : Int) * eFn i (j.val / 4)) := by
      funext i j; dsimp only [B_red, eFn]
      by_cases ha : tropActiveBoolW18 (i.val % 3) (j.val / 4) = true
      · rw [ite_true_of_w10 ha, ite_true_of_w10 ha]; rfl
      · simp [ha]
    have hpow_eq : (fun i j : Fin 12 => intPowNat ((i.val % 3 * W + i.val / 3 * K : Nat) : Int) (j.val % 4) * eFn i (j.val / 4)) =
        tropRedPowMatW18 (Int.ofNat W) (Int.ofNat K) (Int.ofNat (3 ^ u)) := by
      funext i j; dsimp only [eFn, tropRedPowMatW18]
      by_cases ha : tropActiveBoolW18 (i.val % 3) (j.val / 4) = true
      · rw [ite_true_of_w10 ha, ite_true_of_w10 ha, hpow_nat (3 ^ u) (i.val / 3 * (j.val / 4))]
        apply congrArg (intPowNat _ (j.val % 4) * ·)
        apply congrArg Int.ofNat
        rw [pow_pow_eq_mul_w5 3 u (i.val / 3 * (j.val / 4))]
        apply congrArg (3 ^ ·)
        ac_rfl
      · simp [ha]
    have h1728 : 1728 * intDet 12 B_red = 1728 * Int.ofNat (3 ^ (18 * u) * K ^ 18) := by
      rw [hB_eq, stirling_3blk_1728_w18
            (fun i => i.val % 3 * W + i.val / 3 * K)
            eFn,
          hpow_eq, tropRedPowMat_det_w18,
          hpow_nat (3 ^ u) 18, hpow_nat K 18, Int.mul_assoc 1728, ← hmul_ofNat]
      apply congrArg (1728 * ·); apply congrArg Int.ofNat
      rw [pow_pow_eq_mul_w5 3 u 18, Nat.mul_comm u 18]
    exact Int.eq_of_mul_eq_mul_left (by decide : (1728 : Int) ≠ 0) h1728
  rw [hB_red_det] at hdvd_trop_red
  rcases hdvd_trop_red with ⟨q_u, hq_u⟩
  refine ⟨q_u, ?_⟩
  have hcast_5u : Int.ofNat (2 ^ (5 * u)) = Int.ofNat (2 ^ (4 * u)) * Int.ofNat (2 ^ u) := by
    rw [show 5 * u = 4 * u + u by omega, Nat.pow_add, hmul_ofNat]
  have hcast_rhs : Int.ofNat (2 ^ (4 * u) * 3 ^ (18 * u) * K ^ 18) =
      Int.ofNat (2 ^ (4 * u)) * Int.ofNat (3 ^ (18 * u) * K ^ 18) := by
    rw [Nat.mul_assoc, hmul_ofNat]
  rw [hscale_rel, hcast_5u, hcast_rhs]
  calc Int.ofNat (2 ^ (4 * u)) * intDet 12 M_trop -
         Int.ofNat (2 ^ (4 * u)) * Int.ofNat (3 ^ (18 * u) * K ^ 18)
      = Int.ofNat (2 ^ (4 * u)) * (intDet 12 M_trop - Int.ofNat (3 ^ (18 * u) * K ^ 18)) :=
          (Int.mul_sub _ _ _).symm
    _ = Int.ofNat (2 ^ (4 * u)) * (Int.ofNat (2 ^ u) * q_u) := by rw [hq_u]
    _ = (Int.ofNat (2 ^ (4 * u)) * Int.ofNat (2 ^ u)) * q_u := (Int.mul_assoc _ _ _).symm

-- 3-Adic Newton-Polygon / Tropical Matrix Congruence & Mod-3 Period-9 Non-Vanishing:

private def aRow3TropW18 (s : Nat) : Nat := match s with | 0 => 3 | 1 => 1 | _ => 0
private def bCol3TropW18 (m : Nat) : Nat := match m with | 0 => 0 | 1 => 2 | _ => 3

private def trop3ActiveBoolW18 (s m : Nat) : Bool :=
  (s * m + aRow3TropW18 s == bCol3TropW18 m)

private def rowPrefExp3TropW18 (u : Nat) : Nat -> Nat
  | 0 => 0
  | r + 1 => aRow3TropW18 (r / 3) * u + rowPrefExp3TropW18 u r

private def colPrefExp3TropW18 (u : Nat) : Nat -> Nat
  | 0 => 0
  | c + 1 => bCol3TropW18 (c / 4) * u + colPrefExp3TropW18 u c

/-- Leading `3 ^ (8 * u)` Newton-polygon / tropical integer matrix of `laurentTwoBaseT4U3Mat12 W K u`. -/
def laurentTrop3Mat12 (W K u : Nat) (i j : Fin 12) : Int :=
  let r := i.val % 3; let s := i.val / 3
  let t := j.val % 4; let m := j.val / 4
  if trop3ActiveBoolW18 s m then
    Int.ofNat (laurentInterpBinom (r * W + s * K) t * 2 ^ (r * (m * u)))
  else 0

private theorem det12_t4u3_3adic_congr_w18 (W K u : Nat) :
    Int.ofNat (3 ^ (9 * u)) ∣
      (intDet 12 (laurentTwoBaseT4U3Mat12 W K u) -
        Int.ofNat (3 ^ (8 * u)) * intDet 12 (laurentTrop3Mat12 W K u)) := by
  have hmul_ofNat : ∀ a b : Nat, Int.ofNat (a * b) = Int.ofNat a * Int.ofNat b := Int.natCast_mul
  let aRow := aRow3TropW18
  let bCol := bCol3TropW18
  let M_trop3 : Fin 12 -> Fin 12 -> Int := fun i j =>
    let r := i.val % 3; let s := i.val / 3
    let t := j.val % 4; let m := j.val / 4
    let e3 := (s * m + aRow s - bCol m) * u
    Int.ofNat (laurentInterpBinom (r * W + s * K) t * (2 ^ (r * (m * u)) * 3 ^ e3))
  let rowPrefExp := rowPrefExp3TropW18 u
  let colPrefExp := colPrefExp3TropW18 u
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
      rw [heq_r, intDet_scale_row_w18 _ 12 n' hn, ih (Nat.le_of_lt hn), ← Int.mul_assoc,
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
        simp [aRow, bCol, aRow3TropW18, bCol3TropW18, hs, hm]
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
    simp [rowPrefExp, rowPrefExp3TropW18, aRow3TropW18]; omega
  have hcol12_exp : colPrefExp 12 = 20 * u := by
    simp [colPrefExp, colPrefExp3TropW18, bCol3TropW18]; omega
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
  have hdvd_trop3 : Int.ofNat (3 ^ u) ∣ (intDet 12 M_trop3 - intDet 12 (laurentTrop3Mat12 W K u)) := by
    apply intDet_congr_dvd (Int.ofNat (3 ^ u)) 12
    intro i j
    change Int.ofNat (3 ^ u) ∣
      (Int.ofNat (laurentInterpBinom (i.val % 3 * W + i.val / 3 * K) (j.val % 4) *
        (2 ^ (i.val % 3 * (j.val / 4 * u)) *
         3 ^ ((i.val / 3 * (j.val / 4) + aRow3TropW18 (i.val / 3) - bCol3TropW18 (j.val / 4)) * u))) -
       if trop3ActiveBoolW18 (i.val / 3) (j.val / 4) then
         Int.ofNat (laurentInterpBinom (i.val % 3 * W + i.val / 3 * K) (j.val % 4) *
           2 ^ (i.val % 3 * (j.val / 4 * u)))
       else 0)
    by_cases hact : trop3ActiveBoolW18 (i.val / 3) (j.val / 4) = true
    · rw [ite_true_of_w10 hact]
      have he0 : (i.val / 3 * (j.val / 4) + aRow3TropW18 (i.val / 3) - bCol3TropW18 (j.val / 4)) * u = 0 := by
        unfold trop3ActiveBoolW18 at hact
        have heq := beq_iff_eq.mp hact
        rw [show i.val / 3 * (j.val / 4) + aRow3TropW18 (i.val / 3) - bCol3TropW18 (j.val / 4) = 0 by omega,
            Nat.zero_mul]
      rw [he0, Nat.pow_zero, Nat.mul_one, Int.sub_self]
      exact ⟨0, (Int.mul_zero _).symm⟩
    · rw [ite_false_of_w10 hact, Int.sub_zero]
      have hpos_gap : i.val / 3 * (j.val / 4) + aRow3TropW18 (i.val / 3) - bCol3TropW18 (j.val / 4) ≥ 1 := by
        unfold trop3ActiveBoolW18 at hact
        rcases (by have := i.isLt; omega : i.val / 3 = 0 ∨ i.val / 3 = 1 ∨ i.val / 3 = 2 ∨ i.val / 3 = 3) with
          hs | hs | hs | hs <;>
        rcases (by have := j.isLt; omega : j.val / 4 = 0 ∨ j.val / 4 = 1 ∨ j.val / 4 = 2) with hm | hm | hm <;>
        (rw [hs, hm] at hact ⊢; simp [aRow3TropW18, bCol3TropW18] at hact ⊢)
      let eg := i.val / 3 * (j.val / 4) + aRow3TropW18 (i.val / 3) - bCol3TropW18 (j.val / 4)
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
    rw [show 9 * u = 8 * u + u by omega, Nat.pow_add, hmul_ofNat]
  rw [hscale_rel, hcast_9u, ← Int.mul_sub, hq3, ← Int.mul_assoc]

private theorem binom_mod3_lucas_and_period9_w18 :
    (∀ n : Nat,
      laurentInterpBinom n 0 % 3 = 1 ∧
      laurentInterpBinom n 1 % 3 = n % 3 ∧
      laurentInterpBinom n 2 % 3 = (if n % 3 == 2 then 1 else 0) ∧
      laurentInterpBinom n 3 % 3 = (n / 3) % 3) ∧
    (∀ (n t : Nat), t < 4 -> laurentInterpBinom n t % 3 = laurentInterpBinom (n % 9) t % 3) := by
  have hluc : ∀ n : Nat,
      laurentInterpBinom n 0 % 3 = 1 ∧
      laurentInterpBinom n 1 % 3 = n % 3 ∧
      laurentInterpBinom n 2 % 3 = (if n % 3 == 2 then 1 else 0) ∧
      laurentInterpBinom n 3 % 3 = (n / 3) % 3 := by
    intro n; induction n with
    | zero => decide
    | succ n' ih =>
      rcases ih with ⟨h0, h1, h2, h3⟩
      have hm3_lt : n' % 3 < 3 := Nat.mod_lt n' (by decide)
      have hdm3 := (Nat.div_add_mod n' 3).symm
      refine ⟨rfl, ?_, ?_, ?_⟩
      · change (laurentInterpBinom n' 0 + laurentInterpBinom n' 1) % 3 = (n' + 1) % 3
        rw [Nat.add_mod, h0, h1]; omega
      · change (laurentInterpBinom n' 1 + laurentInterpBinom n' 2) % 3 =
          if (n' + 1) % 3 == 2 then 1 else 0
        rw [Nat.add_mod, h1, h2]
        rcases (by omega : n' % 3 = 0 ∨ n' % 3 = 1 ∨ n' % 3 = 2) with hr | hr | hr
        · have hs : (n' + 1) % 3 = 1 := by omega
          rw [hr, hs]; rfl
        · have hs : (n' + 1) % 3 = 2 := by omega
          rw [hr, hs]; rfl
        · have hs : (n' + 1) % 3 = 0 := by omega
          rw [hr, hs]; rfl
      · change (laurentInterpBinom n' 2 + laurentInterpBinom n' 3) % 3 = ((n' + 1) / 3) % 3
        rw [Nat.add_mod, h2, h3]
        rcases (by omega : n' % 3 = 0 ∨ n' % 3 = 1 ∨ n' % 3 = 2) with hr | hr | hr
        · have hd_eq : (n' + 1) / 3 = n' / 3 := by omega
          rw [hr, hd_eq]; simp
        · have hd_eq : (n' + 1) / 3 = n' / 3 := by omega
          rw [hr, hd_eq]; simp
        · have hd_eq : (n' + 1) / 3 = n' / 3 + 1 := by omega
          rw [hr, hd_eq]; simp [Nat.add_comm 1 (n' / 3 % 3), Nat.add_mod]
  refine ⟨hluc, fun n t ht => ?_⟩
  have hmod3_9 : (n % 9) % 3 = n % 3 := Nat.mod_mod_of_dvd n (by decide : 3 ∣ 9)
  have hdiv3_9 : ((n % 9) / 3) % 3 = (n / 3) % 3 := by
    have hdm9 := (Nat.div_add_mod n 9).symm
    have hr9 : n % 9 < 9 := Nat.mod_lt n (by decide)
    have hd_split : n / 3 = 3 * (n / 9) + (n % 9) / 3 := by omega
    rw [hd_split, Nat.mul_add_mod_self_left]
  rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2 ∨ t = 3) with rfl | rfl | rfl | rfl
  · rw [(hluc n).1, (hluc (n % 9)).1]
  · rw [(hluc n).2.1, (hluc (n % 9)).2.1, hmod3_9]
  · rw [(hluc n).2.2.1, (hluc (n % 9)).2.2.1, hmod3_9]
  · rw [(hluc n).2.2.2, (hluc (n % 9)).2.2.2, hdiv3_9]

private def trop3Mod3EntryW18 (uPar w0 k0 rCol cCol : Nat) : Nat :=
  let r := rCol % 3; let s := rCol / 3
  let t := cCol % 4; let m := cCol / 4
  if trop3ActiveBoolW18 s m then
    let x := if uPar == 0 then 1 else 2
    (laurentInterpBinom (r * w0 + s * k0) t * (x ^ (r * m))) % 3
  else 0

-- O(1) Lucas-reduced fast entry (avoids exponential Pascal recursion in kernel `decide`!):
private def lucasBinomMod3FastW18 (n : Nat) : Nat -> Nat
  | 0 => 1
  | 1 => n % 3
  | 2 => if n % 3 == 2 then 1 else 0
  | _ => (n / 3) % 3

private def trop3Mod3FastEntryW18 (uPar w0 k0 rCol cCol : Nat) : Nat :=
  let r := rCol % 3; let s := rCol / 3
  let t := cCol % 4; let m := cCol / 4
  if trop3ActiveBoolW18 s m then
    let x := if uPar == 0 then 1 else 2
    (lucasBinomMod3FastW18 (r * w0 + s * k0) t * (x ^ (r * m))) % 3
  else 0

private theorem trop3Mod3FastEntryW18_eq (uPar w0 k0 rCol cCol : Nat) :
    trop3Mod3FastEntryW18 uPar w0 k0 rCol cCol = trop3Mod3EntryW18 uPar w0 k0 rCol cCol := by
  unfold trop3Mod3FastEntryW18 trop3Mod3EntryW18
  dsimp only
  by_cases hact : trop3ActiveBoolW18 (rCol / 3) (cCol / 4) = true
  · rw [ite_true_of_w10 hact, ite_true_of_w10 hact]
    let n := rCol % 3 * w0 + rCol / 3 * k0
    have hluc := binom_mod3_lucas_and_period9_w18.1 n
    have ht_lt : cCol % 4 < 4 := Nat.mod_lt cCol (by decide)
    rcases (by omega : cCol % 4 = 0 ∨ cCol % 4 = 1 ∨ cCol % 4 = 2 ∨ cCol % 4 = 3) with h | h | h | h
    · rw [h]; simp only [lucasBinomMod3FastW18]
      rw [Nat.mul_mod 1, Nat.mul_mod (laurentInterpBinom _ 0), hluc.1]
    · rw [h]; simp only [lucasBinomMod3FastW18]
      rw [Nat.mul_mod (_ % 3), Nat.mod_mod, Nat.mul_mod (laurentInterpBinom _ 1), hluc.2.1]
    · rw [h]; simp only [lucasBinomMod3FastW18]
      conv => lhs; rw [Nat.mul_mod]
      conv => rhs; rw [Nat.mul_mod, hluc.2.2.1]
      cases ((rCol % 3 * w0 + rCol / 3 * k0) % 3 == 2) <;> rfl
    · rw [h]; simp only [lucasBinomMod3FastW18]
      rw [Nat.mul_mod (_ % 3), Nat.mod_mod, Nat.mul_mod (laurentInterpBinom _ 3), hluc.2.2.2]
  · rw [ite_false_of_w10 hact, ite_false_of_w10 hact]

private def checkRawFnULModPFastBoolW18 (pNat : Nat) (f0 : Nat -> Nat -> Nat)
    (cert : List (Nat × Nat) × List (List Nat)) : Bool :=
  let apFn (r j : Nat) : Nat :=
    match traceColSwapsW18 cert.1 j with
    | (j0, cnt) => iterNegModPW18 pNat cnt (f0 r j0)
  let uFn (n c : Nat) : Nat := uStrictNatValW18 cert.2 n c
  allNatLoopW18 (fun r =>
    allNatLoopW18 (fun c =>
      if Nat.ble (r + 1) c then
        dotDirect12W18 (apFn r) (fun n => uFn n c) (c + 1) % pNat == 0
      else true) 12) 12 &&
  (natDiagDirectModPW18 pNat apFn uFn 12 != 0)

private theorem checkRawFnULModPFastBoolW18_eq (pNat : Nat) (f0 f1 : Nat -> Nat -> Nat)
    (hf : f0 = f1) (cert : List (Nat × Nat) × List (List Nat)) :
    checkRawFnULModPFastBoolW18 pNat f0 cert =
      checkRawMatULModP12BoolW18 pNat (buildMat12NatW18 f1) cert := by
  subst hf
  unfold checkRawFnULModPFastBoolW18 checkRawMatULModP12BoolW18
  dsimp only
  let apFn (r j : Nat) : Nat :=
    match traceColSwapsW18 cert.1 j with
    | (j0, cnt) => iterNegModPW18 pNat cnt (f0 r j0)
  rw [applySignedSwaps_eq_tracedBuildMat12W18 pNat cert.1 f0]
  let apRows := buildMat12NatW18 apFn
  let uCols := buildMat12NatW18 (fun c r => uStrictNatValW18 cert.2 r c)
  have hdot : ∀ (r c m : Nat), r < 12 -> c < 12 -> m ≤ 12 ->
      dotDirect12W18 (apFn r) (fun n => uStrictNatValW18 cert.2 n c) m =
        dotListsPrefixW18 m (natRowAtW18 apRows r) (natRowAtW18 uCols c) := by
    intro r c m hr hc hm
    rw [dotListsPrefixW18_eq, dotDirect12W18_eq _ _ m hm]
    dsimp only [apRows, uCols]
    rw [natRowAtW18_buildMat12 _ r hr, natRowAtW18_buildMat12 _ c hc]
  have hloop :
      allNatLoopW18 (fun r => allNatLoopW18 (fun c =>
        if Nat.ble (r + 1) c then dotDirect12W18 (apFn r) (fun n => uStrictNatValW18 cert.2 n c) (c + 1) % pNat == 0
        else true) 12) 12 =
      allNatLoopW18 (fun r =>
        let row_r := natRowAtW18 apRows r
        allNatLoopW18 (fun c =>
          if Nat.ble (r + 1) c then dotListsPrefixW18 (c + 1) row_r (natRowAtW18 uCols c) % pNat == 0
          else true) 12) 12 := by
    apply allNatLoopW18_congr _ _ 12; intro r hr
    apply allNatLoopW18_congr _ _ 12; intro c hc
    rw [hdot r c (c + 1) hr hc (by omega)]
  have hdiag : ∀ m : Nat, m ≤ 12 ->
      natDiagDirectModPW18 pNat apFn (uStrictNatValW18 cert.2) m =
        natDiagProdModPW18 pNat apRows uCols m := by
    intro m hm; induction m with
    | zero => rfl
    | succ m' ih =>
      have hm_lt : m' < 12 := hm
      simp only [natDiagDirectModPW18, natDiagProdModPW18,
                 ih (Nat.le_of_lt hm), hdot m' m' (m' + 1) hm_lt hm_lt hm]
  rw [hloop, hdiag 12 (Nat.le_refl 12)]

private def dropPairsW18 : Nat -> List (Nat × Nat) -> List (Nat × Nat)
  | 0, ps => ps
  | _ + 1, [] => []
  | k + 1, _ :: ps => dropPairsW18 k ps

private def checkTrop3PairsFastBoolW18 (uPar : Nat) :
    Nat -> List (Nat × Nat) -> List (List (Nat × Nat) × List (List Nat)) -> Bool
  | 0, _, _ => true
  | cnt + 1, (w0, k0) :: ps, c :: cs =>
    checkRawFnULModPFastBoolW18 3 (trop3Mod3FastEntryW18 uPar w0 k0) c &&
      checkTrop3PairsFastBoolW18 uPar cnt ps cs
  | _, _, _ => false

private theorem checkTrop3PairsFastBoolW18_glue (uPar : Nat) :
    ∀ (a b : Nat) (ps : List (Nat × Nat)) (cs : List (List (Nat × Nat) × List (List Nat))),
      checkTrop3PairsFastBoolW18 uPar a ps cs = true ->
      checkTrop3PairsFastBoolW18 uPar b (dropPairsW18 a ps) (dropCertsW18 a cs) = true ->
      checkTrop3PairsFastBoolW18 uPar (a + b) ps cs = true
  | 0, _, _, _, _, hb => by rw [Nat.zero_add]; exact hb
  | _ + 1, _, [], _, ha, _ => by cases ha
  | _ + 1, _, _ :: _, [], ha, _ => by cases ha
  | a' + 1, b, (w0, k0) :: ps, c :: cs, ha, hb => by
    rw [Nat.succ_add]
    change (checkRawFnULModPFastBoolW18 3 (trop3Mod3FastEntryW18 uPar w0 k0) c &&
      checkTrop3PairsFastBoolW18 uPar a' ps cs) = true at ha
    rcases bool_and_split ha with ⟨hc, hrest⟩
    change (checkRawFnULModPFastBoolW18 3 (trop3Mod3FastEntryW18 uPar w0 k0) c &&
      checkTrop3PairsFastBoolW18 uPar (a' + b) ps cs) = true
    rw [hc, Bool.true_and]
    exact checkTrop3PairsFastBoolW18_glue uPar a' b ps cs hrest hb

private theorem unpack_trop3Pairs_sound_w18 (uPar : Nat) :
    ∀ (ps : List (Nat × Nat)) (cs : List (List (Nat × Nat) × List (List Nat))),
      checkTrop3PairsFastBoolW18 uPar ps.length ps cs = true ->
      ∀ (w0 k0 : Nat), (w0, k0) ∈ ps ->
        intDet 12 (fun i j =>
          (natAt2DW18 (buildMat12NatW18 (trop3Mod3EntryW18 uPar w0 k0)) i.val j.val : Int)) % 3 ≠ 0
  | [], _, _, _, _, hmem => by cases hmem
  | (_, _) :: _, [], hchk, _, _, _ => by cases hchk
  | (w_h, k_h) :: ps, c :: cs, hchk, w0, k0, hmem => by
    change (checkRawFnULModPFastBoolW18 3 (trop3Mod3FastEntryW18 uPar w_h k_h) c &&
      checkTrop3PairsFastBoolW18 uPar ps.length ps cs) = true at hchk
    rcases bool_and_split hchk with ⟨hcur, hrest⟩
    rcases List.mem_cons.mp hmem with heq | htl
    · injection heq with hw hk; subst hw; subst hk
      rw [checkRawFnULModPFastBoolW18_eq 3 _ _
            (funext fun r => funext fun c0 => trop3Mod3FastEntryW18_eq uPar w0 k0 r c0) c] at hcur
      exact checkRawMatULModP12BoolW18_sound 3 (by decide) _ c hcur
    · exact unpack_trop3Pairs_sound_w18 uPar ps cs hrest w0 k0 htl

private def trop3EvenPairsW18 : List (Nat × Nat) :=
  [(1,1), (1,2), (1,4), (1,5), (1,7), (1,8), (2,1), (2,2), (2,4), (2,5), (2,7), (2,8),
   (4,1), (4,2), (4,4), (4,5), (4,7), (4,8), (5,1), (5,2), (5,4), (5,5), (5,7), (5,8),
   (7,1), (7,2), (7,4), (7,5), (7,7), (7,8), (8,1), (8,2), (8,4), (8,5), (8,7), (8,8)]

private def trop3OddPairsW18 : List (Nat × Nat) :=
  [(1,1), (1,2), (1,7), (1,8), (2,2), (2,4), (2,5), (2,7), (4,1), (4,4), (4,5), (4,8),
   (5,1), (5,4), (5,5), (5,8), (7,2), (7,4), (7,5), (7,7), (8,1), (8,2), (8,7), (8,8)]

private theorem trop3_pairs_loop_cert_w18 :
    allNatLoopW18 (fun w0 =>
      allNatLoopW18 (fun k0 =>
        (if w0 % 3 != 0 && k0 % 3 != 0 then decide ((w0, k0) ∈ trop3EvenPairsW18) else true) &&
        (if w0 % 3 != 0 && k0 % 3 != 0 && (k0 + 5 * w0) % 9 != 0 && (k0 + 4 * w0) % 9 != 0 then
           decide ((w0, k0) ∈ trop3OddPairsW18) else true)) 9) 9 = true := by decide

private theorem trop3_even_and_odd_pairs_mem_w18 :
    (∀ (w0 k0 : Fin 9), w0.val % 3 ≠ 0 -> k0.val % 3 ≠ 0 ->
       (w0.val, k0.val) ∈ trop3EvenPairsW18) ∧
    (∀ (w0 k0 : Fin 9), w0.val % 3 ≠ 0 -> k0.val % 3 ≠ 0 ->
       (k0.val + 5 * w0.val) % 9 ≠ 0 -> (k0.val + 4 * w0.val) % 9 ≠ 0 ->
       (w0.val, k0.val) ∈ trop3OddPairsW18) := by
  constructor
  · intro w0 k0 hw3 hk3
    have hw_b := allNatLoopW18_spec _ 9 trop3_pairs_loop_cert_w18 w0.val w0.isLt
    have hk_b := allNatLoopW18_spec _ 9 hw_b k0.val k0.isLt
    rcases bool_and_split hk_b with ⟨hev, _⟩
    have hc : (w0.val % 3 != 0 && k0.val % 3 != 0) = true := by
      rw [bne_iff_ne.mpr hw3, bne_iff_ne.mpr hk3]; rfl
    rw [hc] at hev; simp only [↓reduceIte] at hev
    exact of_decide_eq_true hev
  · intro w0 k0 hw3 hk3 hm5 hm4
    have hw_b := allNatLoopW18_spec _ 9 trop3_pairs_loop_cert_w18 w0.val w0.isLt
    have hk_b := allNatLoopW18_spec _ 9 hw_b k0.val k0.isLt
    rcases bool_and_split hk_b with ⟨_, hod⟩
    have hc : (w0.val % 3 != 0 && k0.val % 3 != 0 &&
        (k0.val + 5 * w0.val) % 9 != 0 && (k0.val + 4 * w0.val) % 9 != 0) = true := by
      rw [bne_iff_ne.mpr hw3, bne_iff_ne.mpr hk3, bne_iff_ne.mpr hm5, bne_iff_ne.mpr hm4]; rfl
    rw [hc] at hod; simp only [↓reduceIte] at hod
    exact of_decide_eq_true hod

private def trop3EvenCertsW18 : List (List (Nat × Nat) × List (List Nat)) :=
  ([
  (0xbcac89796756453b2a19, 0x81020808002080000000080020000004001000008001000400002080000000000000000000000000000000000000000000000000000),
  (0x6756453b2a19, 0x1000404100020008002081020008001000400000000000004080040010000040000000000000000000000000000000000000000000000000000),
  (0xab6756453b2a19, 0x10000100040800100040800400080040800004000810008002000408002080000000000000000000000000000000000000000000000000000),
  (0xbc89786756453b2a19, 0x408002040000004040800208101000408000000000004102020008100040000000000000000000000000000000000000000000000000000),
  (0xab6756453b2a19, 0x20008101040800202040800400080020800004001010008000000000002080000000000000000000000000000000000000000000000000000),
  (0x6756453b2a19, 0x800200000000808000001010204101000400000000000004000000000000040000000000000000000000000000000000000000000000000000),
  (0xbc786756453b2a19, 0x20404001020010204040020008000040008200001000200081000400200080020000000000000004000000000000020000000000000000000),
  (0xac896756453b2a19, 0x1000000081040010004000800400001000000004041000008002000800002040000400000000000000080000000000020000000000000000000),
  (0xab6756453b2a19, 0x8082020008202080010000001040400000041010000100020808000081000000000000000200000000000000020000000000000000000),
  (0x786756453b2a19, 0x404100040410004040810004000000000102040800208000000000002041000000000000000200000000000000020000000000000000000),
  (0x6756453b2a19, 0x1020000000000400200000810208080040400202001010000000000000000081000000000000000200000000000000020000000000000000000),
  (0x6756453b2a19, 0x1020400102040408200080800204000000000102041010008002040410002041000000000000000200000000000000020000000000000000000),
  (0xab786756453b2a19, 0x820008080040408004041020000101020010100000000008000000000002080000000000000000200000000000000000000000000000000000),
  (0xbc896756453b2a19, 0x10404101040000004000820408102040000104040800004102040800000040000000000000000004000000000000000000000000000000000),
  (0xac896756453b2a19, 0x800000080040408002080800200082020000000040000008001040400002080000000000000000000080000000000000000000000000000000),
  (0x786756453b2a19, 0x800200000000010100081020004102040008002040800404000000000000040000000000000000200000000000000000000000000000000000),
  (0xab6756453b2a19, 0x10000082040410100081000200101040800100000000008001040408002080000000000000000200000000000000000000000000000000000),
  (0x6756453b2a19, 0x1020004100020010102080810008002020400200041020004080020810000040000000000000000200000000000000000000000000000000000),
  (0xab796756453b2a19, 0x1000008100020008204081000000001040400100080820000100020808000081000000000000000000000000000000020000000000000000000),
  (0x6756453b2a19, 0x1020200101040410200081000404000000000004040820008002020410002041000000000000000000000000000000020000000000000000000),
  (0x6756453b2a19, 0x1020000000000400200001020408080040400204000820000000000000000081000000000000000000000000000000020000000000000000000),
  (0xac89796756453b2a19, 0x800000080040008002000000000001000000002080800008002020800002040000400000000000000000000000000020000000000000000000),
  (0xbc6756453b2a19, 0x10404002040400104001010408000020400102001020000081000810000080020000000000000000000000000000020000000000000000000),
  (0x6756453b2a19, 0x10204100040410102081000404000000000004041020008000000000002041000000000000000000000000000000020000000000000000000),
  (0xab8a786756453b2a19, 0x10000081000008004040810400102040410204081010408001020410102080000000000000000100000000000000000000000000000000000),
  (0x9a896756453b2a19, 0x800400080000000100001010404101000000004040000004000000000000040000000000000000100000000000000000000000000000000000),
  (0xab8a6756453b2a19, 0x1020008081020008002080810400100000000204000000008000000000002080000000000000000100000000000000000000000000000000000),
  (0x9a796756453b2a19, 0x1010404080020010102080020008002020400100080810004080020810000040000000000000000100000000000000000000000000000000000),
  (0xbcac8a6756453b2a19, 0x4081040010004080820200102000000004040000008002040000002080000000000000000000040000000000000000000000000000000),
  (0xbc9a896756453b2a19, 0x20208100040000004001010208101000000202040000004102020000000040000000000000000002000000000000000000000000000000000),
  (0x9a89786756453b2a19, 0x1000008000000000200040010208080020408200000000000000000000000081000000000000000100000000000000020000000000000000000),
  (0x8a6756453b2a19, 0x10404100040000002081020404000000000200000000008000000000002041000000000000000100000000000000020000000000000000000),
  (0xbc9a6756453b2a19, 0x20000100040400104001000208000020400004000000000081000810000080020000000000000002000000000000020000000000000000000),
  (0x8a786756453b2a19, 0x1000400102040000004040820404000000000200000000008002040408202041000000000000000100000000000000020000000000000000000),
  (0xab9a6756453b2a19, 0x1000008000020008102081010000001020400200000000000100020408000081000000000000000100000000000000020000000000000000000),
  (0xbcac8a6756453b2a19, 0x8080000010004041010200001000000000080000008001020000002040000400000000000000040000000000020000000000000000000)
  ] : List (Nat × Nat)).map decodeUCertW18

private def trop3OddCertsW18 : List (List (Nat × Nat) × List (List Nat)) :=
  ([
  (0xbcac89796756453b2a19, 0x82020810002080000000081020000004081000008001020400002080000000000000000000000000000000000000000000000000000),
  (0x6756453b2a19, 0x1000404102040010002080020008002000400100000000004100020010000040000000000000000000000000000000000000000000000000000),
  (0x896756453b2a19, 0x800408101040810002040010408101020000202081000008000000000002080000000000000000000000000000000000000000000000000000),
  (0x6756453b2a19, 0x1000200000000808000001010204101000400000000000004000000000000040000000000000000000000000000000000000000000000000000),
  (0xac896756453b2a19, 0x1000000082040008004001000400001000000004001000008002040800002040000400000000000000080000000000020000000000000000000),
  (0x9b6756453b2a19, 0x800200000040008002041010008001000400000040010000080020008000081000000000000000200000000000000020000000000000000000),
  (0x786756453b2a19, 0x810004081040800202041010000000000000202080800208000000000002041000000000000000200000000000000020000000000000000000),
  (0x6756453b2a19, 0x810000000000400200000810208080040400202001010000000000000000081000000000000000200000000000000020000000000000000000),
  (0x786756453b2a19, 0x820208102040800102041020008101020010100000000008000000000002080000000000000000200000000000000000000000000000000000),
  (0xac896756453b2a19, 0x800000080040410002081000200082020000000040000008001040400002080000000000000000000080000000000000000000000000000000),
  (0x786756453b2a19, 0x1000200000000010100081020004102040008002040800404000000000000040000000000000000200000000000000000000000000000000000),
  (0x6756453b2a19, 0x1020004102040010202080010008002040400200040820004100020410000040000000000000000200000000000000000000000000000000000),
  (0x9b796756453b2a19, 0x810400000040010204080820008002040400200040820000080040808000081000000000000000000000000000000020000000000000000000),
  (0x6756453b2a19, 0x810000000000400200001020408080040400204000820000000000000000081000000000000000000000000000000020000000000000000000),
  (0xac89796756453b2a19, 0x800000080040010002000000000001000000002080800008002020800002040000400000000000000000000000000020000000000000000000),
  (0x896756453b2a19, 0x820208101020408002040010200000000000004040800008000000000002041000000000000000000000000000000020000000000000000000),
  (0x9a896756453b2a19, 0x1000400080000000100001010404101000000004040000004000000000000040000000000000000100000000000000000000000000000000000),
  (0x6756453b2a19, 0x810008102020410002040010208101000800004040020008000000000002080000000000000000100000000000000000000000000000000000),
  (0x796756453b2a19, 0x1010208080040010202081000008002040400000081010004100020410000040000000000000000100000000000000000000000000000000000),
  (0xbcac8a6756453b2a19, 0x4082040008004081020200102000000004040000008002040000002080000000000000000000040000000000000000000000000000000),
  (0x9a89786756453b2a19, 0x800004000000000200040010208080020408200000000000000000000000081000000000000000100000000000000020000000000000000000),
  (0x6756453b2a19, 0x800404081020410002040020200000000000100000000008000000000002041000000000000000100000000000000020000000000000000000),
  (0x9b6756453b2a19, 0x820000000040010202040820008002040400100000000000080040808000081000000000000000100000000000000020000000000000000000),
  (0xbcac8a6756453b2a19, 0x8080000008004040810200001000000000080000008001020000002040000400000000000000040000000000020000000000000000000)
  ] : List (Nat × Nat)).map decodeUCertW18

set_option maxRecDepth 65536 in
private theorem trop3_ev_s0_w18 :
    checkTrop3PairsFastBoolW18 0 6 (dropPairsW18 0 trop3EvenPairsW18) (dropCertsW18 0 trop3EvenCertsW18) = true := by decide
set_option maxRecDepth 65536 in
private theorem trop3_ev_s1_w18 :
    checkTrop3PairsFastBoolW18 0 6 (dropPairsW18 6 trop3EvenPairsW18) (dropCertsW18 6 trop3EvenCertsW18) = true := by decide
set_option maxRecDepth 65536 in
private theorem trop3_ev_s2_w18 :
    checkTrop3PairsFastBoolW18 0 6 (dropPairsW18 12 trop3EvenPairsW18) (dropCertsW18 12 trop3EvenCertsW18) = true := by decide
set_option maxRecDepth 65536 in
private theorem trop3_ev_s3_w18 :
    checkTrop3PairsFastBoolW18 0 6 (dropPairsW18 18 trop3EvenPairsW18) (dropCertsW18 18 trop3EvenCertsW18) = true := by decide
set_option maxRecDepth 65536 in
private theorem trop3_ev_s4_w18 :
    checkTrop3PairsFastBoolW18 0 6 (dropPairsW18 24 trop3EvenPairsW18) (dropCertsW18 24 trop3EvenCertsW18) = true := by decide
set_option maxRecDepth 65536 in
private theorem trop3_ev_s5_w18 :
    checkTrop3PairsFastBoolW18 0 6 (dropPairsW18 30 trop3EvenPairsW18) (dropCertsW18 30 trop3EvenCertsW18) = true := by decide

private theorem trop3_ev_all36_ok_w18 :
    checkTrop3PairsFastBoolW18 0 trop3EvenPairsW18.length trop3EvenPairsW18 trop3EvenCertsW18 = true := by
  have h1 := checkTrop3PairsFastBoolW18_glue 0 6 6 trop3EvenPairsW18 trop3EvenCertsW18 trop3_ev_s0_w18 trop3_ev_s1_w18
  have h2 := checkTrop3PairsFastBoolW18_glue 0 12 6 trop3EvenPairsW18 trop3EvenCertsW18 h1 trop3_ev_s2_w18
  have h3 := checkTrop3PairsFastBoolW18_glue 0 18 6 trop3EvenPairsW18 trop3EvenCertsW18 h2 trop3_ev_s3_w18
  have h4 := checkTrop3PairsFastBoolW18_glue 0 24 6 trop3EvenPairsW18 trop3EvenCertsW18 h3 trop3_ev_s4_w18
  exact checkTrop3PairsFastBoolW18_glue 0 30 6 trop3EvenPairsW18 trop3EvenCertsW18 h4 trop3_ev_s5_w18

set_option maxRecDepth 65536 in
private theorem trop3_od_s0_w18 :
    checkTrop3PairsFastBoolW18 1 6 (dropPairsW18 0 trop3OddPairsW18) (dropCertsW18 0 trop3OddCertsW18) = true := by decide
set_option maxRecDepth 65536 in
private theorem trop3_od_s1_w18 :
    checkTrop3PairsFastBoolW18 1 6 (dropPairsW18 6 trop3OddPairsW18) (dropCertsW18 6 trop3OddCertsW18) = true := by decide
set_option maxRecDepth 65536 in
private theorem trop3_od_s2_w18 :
    checkTrop3PairsFastBoolW18 1 6 (dropPairsW18 12 trop3OddPairsW18) (dropCertsW18 12 trop3OddCertsW18) = true := by decide
set_option maxRecDepth 65536 in
private theorem trop3_od_s3_w18 :
    checkTrop3PairsFastBoolW18 1 6 (dropPairsW18 18 trop3OddPairsW18) (dropCertsW18 18 trop3OddCertsW18) = true := by decide

private theorem trop3_od_all24_ok_w18 :
    checkTrop3PairsFastBoolW18 1 trop3OddPairsW18.length trop3OddPairsW18 trop3OddCertsW18 = true := by
  have h1 := checkTrop3PairsFastBoolW18_glue 1 6 6 trop3OddPairsW18 trop3OddCertsW18 trop3_od_s0_w18 trop3_od_s1_w18
  have h2 := checkTrop3PairsFastBoolW18_glue 1 12 6 trop3OddPairsW18 trop3OddCertsW18 h1 trop3_od_s2_w18
  exact checkTrop3PairsFastBoolW18_glue 1 18 6 trop3OddPairsW18 trop3OddCertsW18 h2 trop3_od_s3_w18

private def ray4WCertU7W18 : List (Nat × Nat) × List (List Nat) := decodeUCertW18 (0x9a, 0x185021840008200830608182062800a040c3020c0c102062430802182811208108122028a0a10002001c1070000080140c30912244021400000)
private def ray4WCertU9W18 : List (Nat × Nat) × List (List Nat) := decodeUCertW18 (0x56, 0x30304246080e201060624400080830a0a24608161c40b040028514080040620203082050b101800200100031224100181838208246010000000)
private def ray4WCertU11W18 : List (Nat × Nat) × List (List Nat) := decodeUCertW18 (0x9a, 0x1051c2440000188100a405851a1458d16183002000610083c7001a3450e1a345091a00387140400e062c681163448020147810a046822000000)
private def ray4WCertU13W18 : List (Nat × Nat) × List (List Nat) := decodeUCertW18 (0x9a, 0x205021028010183080c04089022418a042020404003841224108100448a10243070200282080c001001c4050a080801404501081c1021400000)
private def ray4WCertU15W18 : List (Nat × Nat) × List (List Nat) := decodeUCertW18 (0x78, 0x3030424608041830c083058a003050c000428a082c603101c40114104820e184850200505002000b02200880620580181c50700282861800000)
private def ray4WCertU17W18 : List (Nat × Nat) × List (List Nat) := decodeUCertW18 (0x9a, 0x185021840008200830608182062800a040c3020c0c102062430802182811208108122028a0a10002001c1070000080140c30912244021400000)
private def ray4WCertU19W18 : List (Nat × Nat) × List (List Nat) := decodeUCertW18 (0x0, 0x2181c58a1410480120460b18204031800007061010414084891618008122c486101828a160800402002051228080183060c142418b1800000)
private def ray4WCertU21W18 : List (Nat × Nat) × List (List Nat) := decodeUCertW18 (0x56, 0x30304246080e201060624400080830a0a24608161c40b040028514080040620203082050b101800200100031224100181838208246010000000)
private def ray4WCertU23W18 : List (Nat × Nat) × List (List Nat) := decodeUCertW18 (0x9a, 0x205021028010183080c04089022418a042020404003841224108100448a10243070200282080c001001c4050a080801404501081c1021400000)
private def ray4WCertU25W18 : List (Nat × Nat) × List (List Nat) := decodeUCertW18 (0x0, 0x208201018a10246091e0848f1a14189082458e1c1020c20408030e283090a203850a1800f0e2000f1a1800c1a24400204000318140812000000)
private def ray4WCertU27W18 : List (Nat × Nat) × List (List Nat) := decodeUCertW18 (0x9a, 0x185021840008200830608182062800a040c3020c0c102062430802182811208108122028a0a10002001c1070000080140c30912244021400000)
private def ray4WCertU29W18 : List (Nat × Nat) × List (List Nat) := decodeUCertW18 (0x78, 0x8c02280061818201080850c002c00c0630408142c00606281890e182830604004181c402021c006020c58000200801820189181c5031800000)
private def ray4WCertU31W18 : List (Nat × Nat) × List (List Nat) := decodeUCertW18 (0x0, 0x2181c58a1410480120460b18204031800007061010414084891618008122c486101828a160800402002051228080183060c142418b1800000)
private def ray4WCertU33W18 : List (Nat × Nat) × List (List Nat) := decodeUCertW18 (0x9a, 0x205021028010183080c04089022418a042020404003841224108100448a10243070200282080c001001c4050a080801404501081c1021400000)
private def ray4WCertU35W18 : List (Nat × Nat) × List (List Nat) := decodeUCertW18 (0xbc, 0x2040c7100a3880d061058c0c0818f1040009063810d141c30c1c0440f1c107071c386090404004160820a1e2448020140041c1038a2000000)

set_option maxRecDepth 65536 in
private theorem ray_4w_grp0_fast_w18 :
    checkULModPNat12FastBoolW18 11 7 1 4 ray4WCertU7W18 &&
    checkULModPNat12FastBoolW18 13 9 1 4 ray4WCertU9W18 &&
    checkULModPNat12FastBoolW18 17 11 1 4 ray4WCertU11W18 = true := by decide

set_option maxRecDepth 65536 in
private theorem ray_4w_grp1_fast_w18 :
    checkULModPNat12FastBoolW18 11 13 1 4 ray4WCertU13W18 &&
    checkULModPNat12FastBoolW18 13 15 1 4 ray4WCertU15W18 &&
    checkULModPNat12FastBoolW18 11 17 1 4 ray4WCertU17W18 = true := by decide

set_option maxRecDepth 65536 in
private theorem ray_4w_grp2_fast_w18 :
    checkULModPNat12FastBoolW18 13 19 1 4 ray4WCertU19W18 &&
    checkULModPNat12FastBoolW18 13 21 1 4 ray4WCertU21W18 &&
    checkULModPNat12FastBoolW18 11 23 1 4 ray4WCertU23W18 = true := by decide

set_option maxRecDepth 65536 in
private theorem ray_4w_grp3_fast_w18 :
    checkULModPNat12FastBoolW18 17 25 1 4 ray4WCertU25W18 &&
    checkULModPNat12FastBoolW18 11 27 1 4 ray4WCertU27W18 &&
    checkULModPNat12FastBoolW18 13 29 1 4 ray4WCertU29W18 = true := by decide

set_option maxRecDepth 65536 in
private theorem ray_4w_grp4_fast_w18 :
    checkULModPNat12FastBoolW18 13 31 1 4 ray4WCertU31W18 &&
    checkULModPNat12FastBoolW18 11 33 1 4 ray4WCertU33W18 &&
    checkULModPNat12FastBoolW18 17 35 1 4 ray4WCertU35W18 = true := by decide

private theorem laurentTrop3Mat12_mod3_eq_entry_w18 (W K u : Nat) :
    (3 : Int) ∣
      (intDet 12 (laurentTrop3Mat12 W K u) -
        intDet 12 (fun i j =>
          (natAt2DW18 (buildMat12NatW18 (trop3Mod3EntryW18 (u % 2) (W % 9) (K % 9))) i.val j.val : Int))) := by
  have hp2_even : ∀ q : Nat, 2 ^ (2 * q) % 3 = 1 := by
    intro q; induction q with
    | zero => rfl
    | succ q' ih => rw [Nat.mul_succ, Nat.pow_add, Nat.mul_mod, ih]
  apply intDet_congr_dvd 3 12
  intro i j
  rw [natAt2DW18_buildMat12 _ i.val j.val i.isLt j.isLt]
  unfold laurentTrop3Mat12 trop3Mod3EntryW18
  dsimp only
  by_cases hact : trop3ActiveBoolW18 (i.val / 3) (j.val / 4) = true
  · rw [ite_true_of_w10 hact, ite_true_of_w10 hact]
    let r := i.val % 3; let s := i.val / 3
    let t := j.val % 4; let m := j.val / 4
    have ht_lt : t < 4 := Nat.mod_lt j.val (by decide)
    have hbin_9 : laurentInterpBinom (r * W + s * K) t % 3 =
        laurentInterpBinom (r * (W % 9) + s * (K % 9)) t % 3 := by
      have hm9 : (r * W + s * K) % 9 = (r * (W % 9) + s * (K % 9)) % 9 := by
        rw [Nat.add_mod, Nat.mul_mod r W 9, Nat.mul_mod s K 9,
            Nat.add_mod (r * (W % 9)) (s * (K % 9)) 9,
            Nat.mul_mod r (W % 9) 9, Nat.mul_mod s (K % 9) 9, Nat.mod_mod, Nat.mod_mod]
      rw [binom_mod3_lucas_and_period9_w18.2 (r * W + s * K) t ht_lt,
          binom_mod3_lucas_and_period9_w18.2 (r * (W % 9) + s * (K % 9)) t ht_lt, hm9]
    have hp2_par : 2 ^ (r * (m * u)) % 3 =
        ((if u % 2 == 0 then 1 else 2) ^ (r * m)) % 3 := by
      have hdm2 := (Nat.div_add_mod u 2).symm
      by_cases hev : u % 2 = 0
      · have hb : (u % 2 == 0) = true := beq_iff_eq.mpr hev
        rw [hb]; simp only [↓reduceIte, Nat.one_pow]
        have hu2 : u = 2 * (u / 2) := by omega
        have hexp : r * (m * u) = 2 * (r * m * (u / 2)) := by
          calc r * (m * u) = r * (m * (2 * (u / 2))) := by rw [← hu2]
            _ = 2 * (r * m * (u / 2)) := by ac_rfl
        rw [hexp]; exact hp2_even _
      · have hod : u % 2 = 1 := by omega
        have hb : (u % 2 == 0) = false := beq_false_of_ne hev
        rw [hb]; simp only [Bool.false_eq_true, ↓reduceIte]
        have hexp : r * (m * u) = 2 * (r * m * (u / 2)) + r * m := by
          conv => lhs; rw [hdm2, hod, Nat.mul_add, Nat.mul_add]
          ac_rfl
        rw [hexp, Nat.pow_add, Nat.mul_mod, hp2_even _, Nat.one_mul, Nat.mod_mod]
    have hprod_m3 : (laurentInterpBinom (r * W + s * K) t * 2 ^ (r * (m * u))) % 3 =
        (laurentInterpBinom (r * (W % 9) + s * (K % 9)) t *
          (if u % 2 == 0 then 1 else 2) ^ (r * m)) % 3 := by
      rw [Nat.mul_mod, hbin_9, hp2_par, ← Nat.mul_mod]
    rcases int_mod_sub_dvd_w18 (laurentInterpBinom (r * W + s * K) t * 2 ^ (r * (m * u))) 3 with ⟨q, hq⟩
    refine ⟨-q, ?_⟩
    rw [hprod_m3] at hq
    have hofNat_eq : ∀ n : Nat, Int.ofNat n = (n : Int) := fun _ => rfl
    rw [hofNat_eq, Int.mul_neg]
    dsimp only [r, s, t, m] at hq
    omega
  · rw [ite_false_of_w10 hact, ite_false_of_w10 hact]; exact ⟨0, by simp⟩

/--
  Theorem W18.2b (`laurent_12x12_t4u3_u2_to_5_nonvanishing_and_2adic_zero_horizon`,
  `zero custom axioms`):
  Rank-3 Order-4 `12 × 12` `(T = 4, U = 3)` Multi-`u` Global Non-Vanishing, `(2, 3)`-Adic
  Newton-Polygon Matrix Congruences, Exact Resonant-Ray `K = 4 * W` Uniqueness, & Finite
  `binBitLength` Multi-`u` Zero-Multiplicity Horizon:
  1. Collatz-cone `(W = 5, K = 8)` `u = 2 > 0` vs `u = 5 < 0` sign-flip (`3^5 < 2^8 ∧ 3 * 8 ≤ 5 * 5`);
  2. Global ZERO-FREE non-vanishing across ALL `W, K ≥ 1` for EVERY `u ∈ {2, 3, 4, 5}`, PLUS exact
     all-`u ≥ 1` resonant-ray characterization `det_12(W, 4 * W, u) = 0 ↔ u = 1`;
  3. Universal `∀ W, K, u : Nat` `(2, 3)`-adic Chu–Vandermonde / Newton-polygon tropical congruences:
     `2^(5 * u) ∣ (det_12(W, K, u) - 2^(4 * u) * 3^(18 * u) * K^18)` AND
     `3^(9 * u) ∣ (det_12(W, K, u) - 3^(8 * u) * det_12(laurentTrop3Mat12 W K u))`;
  4. Unconditional `(2, 3)`-adic **all-`u` / all-even-`u` / non-resonant odd-`u`** non-vanishing and
     explicit logarithmic `binBitLength` multi-`u` zero-horizon across ALL `W, K, u ≥ 1`:
     - `(K / gcd(W, K)) % 2 = 1 -> det_12(W, K, u) ≠ 0` (all `u ≥ 1`);
     - `u % 2 = 0 ∧ (W / gcd) % 3 ≠ 0 ∧ (K / gcd) % 3 ≠ 0 -> det_12(W, K, u) ≠ 0` (all even `u ≥ 2`);
     - `u % 2 = 1 ∧ (W / gcd) % 3 ≠ 0 ∧ (K / gcd) % 3 ≠ 0 ∧ (K / gcd + 5 * (W / gcd)) % 9 ≠ 0 ∧ (K / gcd + 4 * (W / gcd)) % 9 ≠ 0 -> det_12(W, K, u) ≠ 0` (all odd `u ≥ 1`);
     - `det_12(W, K, u) = 0 -> (u = 1 ∧ K = 4 * W) ∨ (u ≥ 6 ∧ K ≠ 4 * W ∧ 2 ^ ((u + 17) / 18) ≤ K / gcd(W, K) ∧ u < 18 * binBitLength (K / gcd(W, K)))`
     (`Branch P3.3`, witness `LAURENT_12X12_T4U3_5_8_U5_FLIP_AND_RECT_ODD_U3_OVERLAP`, `W18_H2`).
-/
theorem laurent_12x12_t4u3_u2_to_5_nonvanishing_and_2adic_zero_horizon :
    (intDet 12 (laurentTwoBaseT4U3Mat12 5 8 2) =
       7670713343317232068959875928780963840000 ∧
     intDet 12 (laurentTwoBaseT4U3Mat12 5 8 2) > 0 ∧
     intDet 12 (laurentTwoBaseT4U3Mat12 5 8 5) =
       -1672565616913273357156942646537077388479879261317516242714101291766003701276115016188065480704 ∧
     intDet 12 (laurentTwoBaseT4U3Mat12 5 8 5) < 0) ∧
    ((∀ (W K u : Nat), W ≥ 1 -> K ≥ 1 -> 2 ≤ u -> u ≤ 5 ->
        intDet 12 (laurentTwoBaseT4U3Mat12 W K u) ≠ 0) ∧
     (∀ (W u : Nat), W ≥ 1 -> u ≥ 1 ->
        (intDet 12 (laurentTwoBaseT4U3Mat12 W (4 * W) u) = 0 ↔ u = 1))) ∧
    ((∀ (W K u : Nat),
        Int.ofNat (2 ^ (5 * u)) ∣
          (intDet 12 (laurentTwoBaseT4U3Mat12 W K u) -
            Int.ofNat (2 ^ (4 * u) * 3 ^ (18 * u) * K ^ 18))) ∧
     (∀ (W K u : Nat),
        Int.ofNat (3 ^ (9 * u)) ∣
          (intDet 12 (laurentTwoBaseT4U3Mat12 W K u) -
            Int.ofNat (3 ^ (8 * u)) * intDet 12 (laurentTrop3Mat12 W K u)))) ∧
    (∀ (W K u : Nat), W ≥ 1 -> K ≥ 1 -> u ≥ 1 ->
      let g := Nat.gcd W K
      let w' := W / g
      let k' := K / g
      (k' % 2 = 1 -> intDet 12 (laurentTwoBaseT4U3Mat12 W K u) ≠ 0) ∧
      (u % 2 = 0 -> w' % 3 ≠ 0 -> k' % 3 ≠ 0 ->
        intDet 12 (laurentTwoBaseT4U3Mat12 W K u) ≠ 0) ∧
      (u % 2 = 1 -> w' % 3 ≠ 0 -> k' % 3 ≠ 0 ->
        (k' + 5 * w') % 9 ≠ 0 -> (k' + 4 * w') % 9 ≠ 0 ->
        intDet 12 (laurentTwoBaseT4U3Mat12 W K u) ≠ 0) ∧
      (intDet 12 (laurentTwoBaseT4U3Mat12 W K u) = 0 ->
        (u = 1 ∧ K = 4 * W) ∨
        (u ≥ 6 ∧ K ≠ 4 * W ∧ 2 ^ ((u + 17) / 18) ≤ k' ∧ u < 18 * binBitLength k'))) := by
  have hd582 : intDet 12 (laurentTwoBaseT4U3Mat12 5 8 2) = 7670713343317232068959875928780963840000 := by
    rw [← fastMat12T4U3FnW18_eq]; exact checkULDet12BoolW18_sound _ _ _ t4u3_582_cert_w18
  have hd585 : intDet 12 (laurentTwoBaseT4U3Mat12 5 8 5) =
      -1672565616913273357156942646537077388479879261317516242714101291766003701276115016188065480704 := by
    rw [← fastMat12T4U3FnW18_eq]; exact checkULDet12BoolW18_sound _ _ _ t4u3_585_cert_w18
  have hu2_5_nz : ∀ (W K u : Nat), W ≥ 1 -> K ≥ 1 -> 2 ≤ u -> u ≤ 5 ->
      intDet 12 (laurentTwoBaseT4U3Mat12 W K u) ≠ 0 := by
    intro W K u hW hK hu2 hu5
    rcases (by omega : u = 2 ∨ u = 3 ∨ u = 4 ∨ u = 5) with rfl | rfl | rfl | rfl
    · rcases sieve_inf_and_inv_u2_ok_w18 with ⟨hinv, hinf⟩
      exact det12_t4u3_nonzero_of_proj_sieve_w18 2 67 (by decide) hinv
        (checkULModPNat12BoolW18_sound 67 2 1 0 (by decide) _ hinf)
        (fun t ht => by
          by_cases h17 : t < 17
          · exact unpack_affRangeULModP_w18 2 67 (by decide) 17 0 _ sieve_aff_u2_c0_ok_w18 t (by omega) h17
          · by_cases h34 : t < 34
            · exact unpack_affRangeULModP_w18 2 67 (by decide) 17 17 _ sieve_aff_u2_c1_ok_w18 t (by omega) h34
            · by_cases h51 : t < 51
              · exact unpack_affRangeULModP_w18 2 67 (by decide) 17 34 _ sieve_aff_u2_c2_ok_w18 t (by omega) h51
              · exact unpack_affRangeULModP_w18 2 67 (by decide) 16 51 _ sieve_aff_u2_c3_ok_w18 t (by omega) (by omega))
        W K hW hK
    · rcases sieve_inf_and_inv_u3_ok_w18 with ⟨hinv, hinf⟩
      exact det12_t4u3_nonzero_of_proj_sieve_w18 3 59 (by decide) hinv
        (checkULModPNat12BoolW18_sound 59 3 1 0 (by decide) _ hinf)
        (fun t ht => by
          by_cases h20 : t < 20
          · exact unpack_affRangeULModP_w18 3 59 (by decide) 20 0 _ sieve_aff_u3_c0_ok_w18 t (by omega) h20
          · by_cases h40 : t < 40
            · exact unpack_affRangeULModP_w18 3 59 (by decide) 20 20 _ sieve_aff_u3_c1_ok_w18 t (by omega) h40
            · exact unpack_affRangeULModP_w18 3 59 (by decide) 19 40 _ sieve_aff_u3_c2_ok_w18 t (by omega) (by omega))
        W K hW hK
    · rcases sieve_inf_and_inv_u4_ok_w18 with ⟨hinv, hinf⟩
      exact det12_t4u3_nonzero_of_proj_sieve_w18 4 59 (by decide) hinv
        (checkULModPNat12BoolW18_sound 59 4 1 0 (by decide) _ hinf)
        (fun t ht => by
          by_cases h20 : t < 20
          · exact unpack_affRangeULModP_w18 4 59 (by decide) 20 0 _ sieve_aff_u4_c0_ok_w18 t (by omega) h20
          · by_cases h40 : t < 40
            · exact unpack_affRangeULModP_w18 4 59 (by decide) 20 20 _ sieve_aff_u4_c1_ok_w18 t (by omega) h40
            · exact unpack_affRangeULModP_w18 4 59 (by decide) 19 40 _ sieve_aff_u4_c2_ok_w18 t (by omega) (by omega))
        W K hW hK
    · rcases sieve_inf_and_inv_u5_ok_w18 with ⟨hinv, hinf⟩
      exact det12_t4u3_nonzero_of_proj_sieve_w18 5 13 (by decide) hinv
        (checkULModPNat12BoolW18_sound 13 5 1 0 (by decide) _ hinf)
        (fun t ht => unpack_affRangeULModP_w18 5 13 (by decide) 13 0 _ sieve_aff_u5_c0_ok_w18 t (by omega) ht)
        W K hW hK
  -- Helper: if `laurentTrop3Mat12 w' k' u % 3 ≠ 0` and `u ≥ 1`, then `det_12(w', k', u) ≠ 0`:
  have htrop3_nz : ∀ (w' k' u : Nat), u ≥ 1 ->
      intDet 12 (fun i j =>
        (natAt2DW18 (buildMat12NatW18 (trop3Mod3EntryW18 (u % 2) (w' % 9) (k' % 9))) i.val j.val : Int)) % 3 ≠ 0 ->
      intDet 12 (laurentTwoBaseT4U3Mat12 w' k' u) ≠ 0 := by
    have hmul_ofNat : ∀ a b : Nat, Int.ofNat (a * b) = Int.ofNat a * Int.ofNat b := Int.natCast_mul
    intro w' k' u hu1 hm3_nz hz
    rcases det12_t4u3_3adic_congr_w18 w' k' u with ⟨q3, hq3⟩
    rw [hz, Int.zero_sub] at hq3
    have hcast_9 : Int.ofNat (3 ^ (9 * u)) = Int.ofNat (3 ^ (8 * u)) * Int.ofNat (3 ^ u) := by
      rw [show 9 * u = 8 * u + u by omega, Nat.pow_add, hmul_ofNat]
    rw [hcast_9, Int.mul_assoc] at hq3
    have hp8_nz : Int.ofNat (3 ^ (8 * u)) ≠ 0 := by
      intro h0; injection h0 with hn0
      have := nat_pow_pos_of_pos 3 (by decide) (8 * u); omega
    have hneg_eq : -(intDet 12 (laurentTrop3Mat12 w' k' u)) = Int.ofNat (3 ^ u) * q3 :=
      Int.eq_of_mul_eq_mul_left hp8_nz (by rw [← Int.mul_neg] at hq3; exact hq3)
    have h3_dvd_trop : (3 : Int) ∣ intDet 12 (laurentTrop3Mat12 w' k' u) := by
      have h3_pow : (3 : Int) ∣ Int.ofNat (3 ^ u) := by
        rw [show u = 1 + (u - 1) by omega, Nat.pow_add, Nat.pow_one, hmul_ofNat]
        exact ⟨_, rfl⟩
      rcases h3_pow with ⟨c3, hc3⟩
      refine ⟨-(c3 * q3), ?_⟩
      rw [hc3, Int.mul_assoc] at hneg_eq
      rw [Int.mul_neg]; omega
    rcases h3_dvd_trop with ⟨qa, hqa⟩
    rcases laurentTrop3Mat12_mod3_eq_entry_w18 w' k' u with ⟨qb, hqb⟩
    have h3_entry : (3 : Int) ∣
        intDet 12 (fun i j =>
          (natAt2DW18 (buildMat12NatW18 (trop3Mod3EntryW18 (u % 2) (w' % 9) (k' % 9))) i.val j.val : Int)) :=
      ⟨qa - qb, by rw [Int.mul_sub]; omega⟩
    exact hm3_nz (Int.emod_eq_zero_of_dvd h3_entry)
  have htrop3_even : ∀ (w' k' u : Nat), u ≥ 1 -> u % 2 = 0 -> w' % 3 ≠ 0 -> k' % 3 ≠ 0 ->
      intDet 12 (laurentTwoBaseT4U3Mat12 w' k' u) ≠ 0 := by
    intro w' k' u hu1 hev hw3 hk3
    apply htrop3_nz w' k' u hu1
    rw [hev]
    have hw9_3 : (w' % 9) % 3 ≠ 0 := by rwa [Nat.mod_mod_of_dvd w' (by decide : 3 ∣ 9)]
    have hk9_3 : (k' % 9) % 3 ≠ 0 := by rwa [Nat.mod_mod_of_dvd k' (by decide : 3 ∣ 9)]
    have hmem := trop3_even_and_odd_pairs_mem_w18.1 ⟨w' % 9, Nat.mod_lt w' (by decide)⟩
      ⟨k' % 9, Nat.mod_lt k' (by decide)⟩ hw9_3 hk9_3
    exact unpack_trop3Pairs_sound_w18 0 trop3EvenPairsW18 trop3EvenCertsW18 trop3_ev_all36_ok_w18
      (w' % 9) (k' % 9) hmem
  have htrop3_odd : ∀ (w' k' u : Nat), u ≥ 1 -> u % 2 = 1 -> w' % 3 ≠ 0 -> k' % 3 ≠ 0 ->
      (k' + 5 * w') % 9 ≠ 0 -> (k' + 4 * w') % 9 ≠ 0 ->
      intDet 12 (laurentTwoBaseT4U3Mat12 w' k' u) ≠ 0 := by
    intro w' k' u hu1 hod hw3 hk3 hn5 hn4
    apply htrop3_nz w' k' u hu1
    rw [hod]
    have hw9_3 : (w' % 9) % 3 ≠ 0 := by rwa [Nat.mod_mod_of_dvd w' (by decide : 3 ∣ 9)]
    have hk9_3 : (k' % 9) % 3 ≠ 0 := by rwa [Nat.mod_mod_of_dvd k' (by decide : 3 ∣ 9)]
    have hm5 : (k' % 9 + 5 * (w' % 9)) % 9 ≠ 0 := by
      have : (k' % 9 + 5 * (w' % 9)) % 9 = (k' + 5 * w') % 9 := by
        rw [Nat.add_mod k' (5 * w') 9, Nat.mul_mod 5 w' 9,
            Nat.add_mod (k' % 9) (5 * (w' % 9)) 9, Nat.mul_mod 5 (w' % 9) 9, Nat.mod_mod]
      rwa [this]
    have hm4 : (k' % 9 + 4 * (w' % 9)) % 9 ≠ 0 := by
      have : (k' % 9 + 4 * (w' % 9)) % 9 = (k' + 4 * w') % 9 := by
        rw [Nat.add_mod k' (4 * w') 9, Nat.mul_mod 4 w' 9,
            Nat.add_mod (k' % 9) (4 * (w' % 9)) 9, Nat.mul_mod 4 (w' % 9) 9, Nat.mod_mod]
      rwa [this]
    have hmem := trop3_even_and_odd_pairs_mem_w18.2 ⟨w' % 9, Nat.mod_lt w' (by decide)⟩
      ⟨k' % 9, Nat.mod_lt k' (by decide)⟩ hw9_3 hk9_3 hm5 hm4
    exact unpack_trop3Pairs_sound_w18 1 trop3OddPairsW18 trop3OddCertsW18 trop3_od_all24_ok_w18
      (w' % 9) (k' % 9) hmem
  -- Helper: `2`-adic + `binBitLength` bound on primitive `(w', k')` whenever `det_12(w', k', u) = 0`:
  have h2adic_prim : ∀ (w' k' u : Nat), k' ≥ 1 -> u ≥ 1 ->
      intDet 12 (laurentTwoBaseT4U3Mat12 w' k' u) = 0 ->
      k' % 2 = 0 ∧ 2 ^ ((u + 17) / 18) ≤ k' ∧ u < 18 * binBitLength k' := by
    intro w' k' u hk'_pos hu1 hz'
    rcases det12_t4u3_2adic_congr_w18 w' k' u with ⟨q, hq⟩
    rw [hz', Int.zero_sub] at hq
    have hnat_dvd : 2 ^ (5 * u) ∣ 2 ^ (4 * u) * (3 ^ (18 * u) * k' ^ 18) := by
      refine ⟨q.natAbs, ?_⟩
      have habs := congrArg Int.natAbs hq
      rw [Int.natAbs_neg, Int.natAbs_mul] at habs
      dsimp only [Int.natAbs] at habs
      rwa [Nat.mul_assoc (2 ^ (4 * u))] at habs
    rcases hnat_dvd with ⟨c_q, hc_q⟩
    rw [show 5 * u = 4 * u + u by omega, Nat.pow_add 2 (4 * u) u, Nat.mul_assoc] at hc_q
    have h2u_dvd_prod : 2 ^ u ∣ 3 ^ (18 * u) * k' ^ 18 :=
      ⟨c_q, Nat.eq_of_mul_eq_mul_left (nat_pow_pos_of_pos 2 (by decide) (4 * u)) hc_q⟩
    have hcop_2_3 : Nat.Coprime (2 ^ u) (3 ^ (18 * u)) := by
      have hc23 : Nat.Coprime 2 3 := by decide
      exact (hc23.pow_left u).pow_right (18 * u)
    have hd : 2 ^ u ∣ k' ^ 18 := hcop_2_3.dvd_of_dvd_mul_left h2u_dvd_prod
    have hv2_decomp : ∀ (fuel n : Nat), n ≥ 1 -> n ≤ fuel ->
        ∃ v odd_n : Nat, n = 2 ^ v * odd_n ∧ odd_n % 2 = 1 ∧ odd_n ≥ 1 := by
      intro fuel; induction fuel with
      | zero => intros _ h1 h0; omega
      | succ f' ih =>
        intro n hn1 hnf
        by_cases hodd : n % 2 = 1
        · exact ⟨0, n, by simp, hodd, hn1⟩
        · let nh := n / 2
          have h2nh : n = 2 * nh := by have := Nat.div_add_mod n 2; omega
          rcases ih nh (by omega) (by omega) with ⟨v, odd_n, hnh, ho1, ho_pos⟩
          exact ⟨v + 1, odd_n, by rw [h2nh, hnh, Nat.pow_succ]; ac_rfl, ho1, ho_pos⟩
    rcases hv2_decomp k' k' hk'_pos (Nat.le_refl k') with ⟨v, odd_k, hk_fac, hodd_k, hodd_pos⟩
    rw [hk_fac, mul_pow_w18c (2 ^ v) odd_k 18, pow_pow_eq_mul_w5 2 v 18] at hd
    have hcop_2_odd : Nat.Coprime (2 ^ u) (odd_k ^ 18) := by
      have hc : Nat.Coprime 2 odd_k := by
        rw [Nat.coprime_iff_gcd_eq_one]
        have hg2 : Nat.gcd 2 odd_k ≤ 2 := Nat.le_of_dvd (by decide) (Nat.gcd_dvd_left _ _)
        have hgp : Nat.gcd 2 odd_k ≥ 1 := Nat.gcd_pos_of_pos_left _ (by decide)
        have hgd := Nat.gcd_dvd_right 2 odd_k
        by_cases h1 : Nat.gcd 2 odd_k = 1
        · exact h1
        · have he2 : Nat.gcd 2 odd_k = 2 := by omega
          rw [he2] at hgd; rcases hgd with ⟨q0, hq0⟩; omega
      exact (hc.pow_left u).pow_right 18
    have h2u_dvd_18v : 2 ^ u ∣ 2 ^ (v * 18) := hcop_2_odd.dvd_of_dvd_mul_right hd
    have hu_le_18v : u ≤ v * 18 := by
      by_cases hle : u ≤ v * 18
      · exact hle
      · exfalso
        have hlt_pow : 2 ^ (v * 18) < 2 ^ u := by
          have h1 : 2 ^ (v * 18) < 2 ^ (v * 18 + 1) := by
            rw [Nat.pow_succ]; have := nat_pow_pos_of_pos 2 (by decide) (v * 18); omega
          exact Nat.lt_of_lt_of_le h1 (nat_pow_mono_exp_pos 2 (v * 18 + 1) u (by decide) (by omega))
        have hle_pow := Nat.le_of_dvd (nat_pow_pos_of_pos 2 (by decide) _) h2u_dvd_18v
        omega
    have hv_ge1 : v ≥ 1 := by omega
    have hkev : k' % 2 = 0 := by
      rw [hk_fac, show v = 1 + (v - 1) by omega, Nat.pow_add, Nat.pow_one, Nat.mul_assoc]
      exact Nat.mul_mod_right 2 _
    have h2v_le_k : 2 ^ v ≤ k' := by rw [hk_fac]; exact Nat.le_mul_of_pos_right _ hodd_pos
    have hceil_le : 2 ^ ((u + 17) / 18) ≤ k' :=
      Nat.le_trans (nat_pow_mono_exp_pos 2 ((u + 17) / 18) v (by decide) (by omega)) h2v_le_k
    have hbl_ge : v + 1 ≤ binBitLength k' := by
      have hm_bl := binBitLength_mono (2 ^ v) k' h2v_le_k
      rwa [(binBitLength_pow2_and_pred v).1] at hm_bl
    exact ⟨hkev, hceil_le, by omega⟩
  -- Global resonant-ray uniqueness `det_12(W, 4 * W, u) = 0 ↔ u = 1`:
  have hray_1_4_nz_u : ∀ u : Nat, u ≥ 2 -> intDet 12 (laurentTwoBaseT4U3Mat12 1 4 u) ≠ 0 := by
    intro u hu2 hz14
    by_cases hle5 : u ≤ 5
    · exact hu2_5_nz 1 4 u (by decide) (by decide) hu2 hle5 hz14
    · by_cases hev : u % 2 = 0
      · exact htrop3_even 1 4 u (by omega) hev (by decide) (by decide) hz14
      · rcases h2adic_prim 1 4 u (by decide) (by omega) hz14 with ⟨_, hceil4, _⟩
        have hu_le36 : u ≤ 36 := by
          by_cases h36 : u ≤ 36
          · exact h36
          · exfalso
            have hm3 : 3 ≤ (u + 17) / 18 := by omega
            have h8 := Nat.le_trans (nat_pow_mono_exp_pos 2 3 ((u + 17) / 18) (by decide) hm3) hceil4
            omega
        have hapow_nz_of_ul : ∀ (pNat : Nat) (cert : List (Nat × Nat) × List (List Nat)),
            pNat ≥ 2 ->
            checkULModPNat12FastBoolW18 pNat u 1 4 cert = true ->
            False := by
          intro pNat cert hp hok
          rw [checkULModPNat12FastBoolW18_eq] at hok
          have hmod_nz := checkULModPNat12BoolW18_sound pNat u 1 4 hp cert hok
          have hst := stirling_1728_det12_t4u3_u_w18 u 1 4
          have hk3 := (apow12_extract_k3_and_homog15_w18 u).1 (1 : Int) (4 : Int)
          change Int.ofNat 1728 * intDet 12 (laurentTwoBaseT4U3Mat12 1 4 u) =
            intDet 12 (apow12UW18 u (1 : Int) (4 : Int)) at hst
          rw [hz14, Int.mul_zero, hk3] at hst
          have hap0 : intDet 12 (apow12KDivW18 u (1 : Int) (4 : Int)) = 0 :=
            Int.eq_of_mul_eq_mul_left (by decide : intPowNat 4 3 ≠ 0) (by rw [Int.mul_zero]; exact hst.symm)
          change intDet 12 (apow12KDivW18 u (1 : Int) (4 : Int)) % (pNat : Int) ≠ 0 at hmod_nz
          rw [hap0, Int.zero_emod] at hmod_nz
          exact hmod_nz rfl
        rcases bool_and_split ray_4w_grp0_fast_w18 with ⟨hcg0, hc11⟩
        rcases bool_and_split hcg0 with ⟨hc7, hc9⟩
        rcases bool_and_split ray_4w_grp1_fast_w18 with ⟨hcg1, hc17⟩
        rcases bool_and_split hcg1 with ⟨hc13, hc15⟩
        rcases bool_and_split ray_4w_grp2_fast_w18 with ⟨hcg2, hc23⟩
        rcases bool_and_split hcg2 with ⟨hc19, hc21⟩
        rcases bool_and_split ray_4w_grp3_fast_w18 with ⟨hcg3, hc29⟩
        rcases bool_and_split hcg3 with ⟨hc25, hc27⟩
        rcases bool_and_split ray_4w_grp4_fast_w18 with ⟨hcg4, hc35⟩
        rcases bool_and_split hcg4 with ⟨hc31, hc33⟩
        rcases (by omega : u = 7 ∨ u = 9 ∨ u = 11 ∨ u = 13 ∨ u = 15 ∨ u = 17 ∨ u = 19 ∨ u = 21 ∨ u = 23 ∨ u = 25 ∨ u = 27 ∨ u = 29 ∨ u = 31 ∨ u = 33 ∨ u = 35) with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact hapow_nz_of_ul 11 ray4WCertU7W18 (by decide) hc7
        · exact hapow_nz_of_ul 13 ray4WCertU9W18 (by decide) hc9
        · exact hapow_nz_of_ul 17 ray4WCertU11W18 (by decide) hc11
        · exact hapow_nz_of_ul 11 ray4WCertU13W18 (by decide) hc13
        · exact hapow_nz_of_ul 13 ray4WCertU15W18 (by decide) hc15
        · exact hapow_nz_of_ul 11 ray4WCertU17W18 (by decide) hc17
        · exact hapow_nz_of_ul 13 ray4WCertU19W18 (by decide) hc19
        · exact hapow_nz_of_ul 13 ray4WCertU21W18 (by decide) hc21
        · exact hapow_nz_of_ul 11 ray4WCertU23W18 (by decide) hc23
        · exact hapow_nz_of_ul 17 ray4WCertU25W18 (by decide) hc25
        · exact hapow_nz_of_ul 11 ray4WCertU27W18 (by decide) hc27
        · exact hapow_nz_of_ul 13 ray4WCertU29W18 (by decide) hc29
        · exact hapow_nz_of_ul 13 ray4WCertU31W18 (by decide) hc31
        · exact hapow_nz_of_ul 11 ray4WCertU33W18 (by decide) hc33
        · exact hapow_nz_of_ul 17 ray4WCertU35W18 (by decide) hc35
  have hray_4W_iff : ∀ (W u : Nat), W ≥ 1 -> u ≥ 1 ->
      (intDet 12 (laurentTwoBaseT4U3Mat12 W (4 * W) u) = 0 ↔ u = 1) := by
    intro W u hW hu1
    have hhom := det12_t4u3_homog18_w18 u W 1 4
    rw [Nat.mul_one, Nat.mul_comm W 4] at hhom
    constructor
    · intro hz
      by_cases hu_eq1 : u = 1
      · exact hu_eq1
      · exfalso
        rw [hhom] at hz
        have hw18_pos : intPowNat (W : Int) 18 > 0 := by
          rw [intPowNat_natCast_w18 W 18]
          have := nat_pow_pos_of_pos W hW 18; omega
        exact Int.mul_ne_zero (by omega) (hray_1_4_nz_u u (by omega)) hz
    · rintro rfl
      exact (laurent_12x12_t4u3_cone_flip_and_exact_u1_zero_locus.2.2.2.2 W (4 * W) hW (by omega)).1.mpr rfl
  refine ⟨⟨hd582, by rw [hd582]; decide, hd585, by rw [hd585]; decide⟩,
          ⟨hu2_5_nz, hray_4W_iff⟩,
          ⟨det12_t4u3_2adic_congr_w18, det12_t4u3_3adic_congr_w18⟩, ?_⟩
  intro W K u hW hK hu1; dsimp only
  let g := Nat.gcd W K
  have hg_pos : g ≥ 1 := Nat.gcd_pos_of_pos_left K hW
  let w' := W / g
  let k' := K / g
  have hW_eq : W = g * w' := by rw [Nat.mul_comm]; exact (Nat.div_mul_cancel (Nat.gcd_dvd_left W K)).symm
  have hK_eq : K = g * k' := by rw [Nat.mul_comm]; exact (Nat.div_mul_cancel (Nat.gcd_dvd_right W K)).symm
  have hk'_pos : k' ≥ 1 := Nat.div_pos (Nat.le_of_dvd hK (Nat.gcd_dvd_right W K)) hg_pos
  have hz_to_prim : intDet 12 (laurentTwoBaseT4U3Mat12 W K u) = 0 ->
      intDet 12 (laurentTwoBaseT4U3Mat12 w' k' u) = 0 := by
    intro hz
    rw [hW_eq, hK_eq, det12_t4u3_homog18_w18 u g w' k'] at hz
    have hg18_pos : intPowNat (g : Int) 18 > 0 := by
      rw [intPowNat_natCast_w18 g 18]
      have := nat_pow_pos_of_pos g hg_pos 18; omega
    by_cases h0 : intDet 12 (laurentTwoBaseT4U3Mat12 w' k' u) = 0
    · exact h0
    · exact False.elim (Int.mul_ne_zero (by omega) h0 hz)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hk_odd hz
    have hev := (h2adic_prim w' k' u hk'_pos hu1 (hz_to_prim hz)).1
    dsimp only [k', g] at hk_odd hev
    rw [hk_odd] at hev
    cases hev
  · intro hev hw3 hk3 hz
    exact htrop3_even w' k' u hu1 hev hw3 hk3 (hz_to_prim hz)
  · intro hod hw3 hk3 hn5 hn4 hz
    exact htrop3_odd w' k' u hu1 hod hw3 hk3 hn5 hn4 (hz_to_prim hz)
  · intro hz
    by_cases hu_eq1 : u = 1
    · left
      subst hu_eq1
      exact ⟨rfl, (laurent_12x12_t4u3_cone_flip_and_exact_u1_zero_locus.2.2.2.2 W K hW hK).1.mp hz⟩
    · right
      have hu_ge6 : u ≥ 6 := by
        by_cases hle5 : u ≤ 5
        · exact False.elim (hu2_5_nz W K u hW hK (by omega) hle5 hz)
        · omega
      have hne_4W : K ≠ 4 * W := by
        intro heq4
        rw [heq4] at hz
        exact hu_eq1 ((hray_4W_iff W u hW hu1).mp hz)
      rcases h2adic_prim w' k' u hk'_pos hu1 (hz_to_prim hz) with ⟨_, hceil_le, hbl_lt⟩
      exact ⟨hu_ge6, hne_4W, hceil_le, hbl_lt⟩

-- ----------------------------------------------------------------------------
end CollatzFormal
