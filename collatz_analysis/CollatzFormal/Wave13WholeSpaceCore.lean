/-
  CollatzFormal/Wave13WholeSpaceCore.lean
  Wave 13 Whole-Space Mathematical & CS Proof Loop (Core — Fronts A & B):
  1. Front A — Positive-Subdiagonal `d = 2` Matrix Commutator Lock (`A 1 0 ≥ 1, B 1 0 ≥ 1,
     A * B ≥ B * A -> A 0 1 = B 0 1 = 0 ∨ A * B = B * A` + Entrywise Determinant Non-Monotonicity
     Certificate), Complete Collapse of `∀ d ≥ 1` Lower-Triangular (`M_s 0 0 ≥ 1`), `d = 2`
     Positive-Diagonal Upper-Triangular (`M_s 0 0 ≥ 1, M_s 1 1 ≥ 1`), and `d = 2` Unit-Diagonal
     Full-Rank Non-Triangular (`M_s = [[1, b_s], [c_s, 1]]`, `det = 1 - b_s * c_s ≠ 0`) `ω^k`
     Hofbauer–Waldmann Matrix Towers on `TwoSided(2 × 3)` `c39` & `TwoSided(2 × 6)` `c78`,
     End-to-End `.L`-to-`.R` Coupled Syracuse Homomorphism (`2^a * dp2GlobalOddVal u2 =
     3 * dp2GlobalOddVal u1 + 1`) & Unconditional `1`- and `2`-Cycle Freedom of `leftAnchoredDP2Step`,
     Universal Mersenne Finite-Feature Ranking Impossibility (`∀ M_feat ≥ 1`), & `M1` Mod-`p`
     Separation Certificate (Branch P4.3)
  2. Front B — Universal Second-Order Three-Block `(U = 3)` Mixed-Newton Confluent Divisibility
     `2^((3*(T*(T-1)/2) + T^2)*u) * (2^u - 1)^(3*T^2) * (2^u + 1)^(T^2) ∣ intDet (3*T) M0` &
     Strict Confluent-Reduced Majorant Bound Beating `intDet_natAbs_le_fact_mul_colProd`,
     Rectangular `U > T` `6 × 6` `(T = 2, U = 3)` Row-Side `2^((2W+K)u) * (2^(W*u) - 1)^3`
     Vandermonde Divisibility vs Square `9 × 9` `(T = 3, U = 3)` `(3, 5, 1)` Non-Divisibility by `7`,
     Complete Diophantine Zero Classification & Universal Multi-`u` Zero-Multiplicity `≤ 1` on
     Rank-2 `6 × 6` `(T = 3, U = 2)`, & Universal `m`-Block Brox Carry Telescoping Bound +
     Cross-Block Companion-Prime Archimedean Squeeze (Branches P3.3 & P3.4)

  Zero `sorry`, zero `native_decide`, zero custom axioms.
-/

import CollatzFormal.Wave12WholeSpace

namespace CollatzFormal

-- ============================================================================
-- SECTION 1: Front A (Branch P4.3) — Positive-Subdiagonal `d = 2` Commutator Lock,
--            Lower-Triangular / Pos-Diag Upper-Tri / Unit-Diag Full-Rank Collapse
--            on `c39` & `c78`, `.L`-to-`.R` Coupled `DP2` Syracuse Homomorphism &
--            `1/2`-Cycle Freedom, & Finite-Feature Ranking Impossibility
-- ============================================================================

-- ----------------------------------------------------------------------------
-- Section 1A: Positive-Subdiagonal `d = 2` Commutator Lock & Det Drop
-- ----------------------------------------------------------------------------

def detDropMatLhs (_ _ : Fin 2) : Nat := 2

def detDropMatRhs (i j : Fin 2) : Nat :=
  if i.val = j.val then 2 else 0

private abbrev fin2_0 : Fin 2 := ⟨0, by decide⟩
private abbrev fin2_1 : Fin 2 := ⟨1, by decide⟩

private theorem natMatMul_two_expand (A B : Fin 2 -> Fin 2 -> Nat) (i j : Fin 2) :
    natMatMul 2 A B i j =
      A i ⟨0, by decide⟩ * B ⟨0, by decide⟩ j + A i ⟨1, by decide⟩ * B ⟨1, by decide⟩ j := by
  change (0 + A i ⟨0, by decide⟩ * B ⟨0, by decide⟩ j) +
    A i ⟨1, by decide⟩ * B ⟨1, by decide⟩ j = _
  rw [Nat.zero_add]

private theorem natMatVec_two_expand (M : Fin 2 -> Fin 2 -> Nat) (r : Fin 2 -> Nat) (i : Fin 2) :
    natMatVec 2 M r i =
      M i ⟨0, by decide⟩ * r ⟨0, by decide⟩ + M i ⟨1, by decide⟩ * r ⟨1, by decide⟩ := by
  change (0 + M i ⟨0, by decide⟩ * r ⟨0, by decide⟩) +
    M i ⟨1, by decide⟩ * r ⟨1, by decide⟩ = _
  rw [Nat.zero_add]

/--
  Theorem W13.1a (`natMat2_pos_subdiag_commutator_lock`, choice-free `zero custom axioms`):
  Entrywise Determinant Non-Monotonicity & Universal Positive-Subdiagonal `d = 2` Commutator Lock
  (`Branch P4.3`, `W13_H1`):
  1. **Entrywise Orientation Breaks Determinant Monotonicity (`A ≥ B`, `det A < det B`)**:
     `detDropMatLhs = [[2, 2], [2, 2]]` and `detDropMatRhs = [[2, 0], [0, 2]]` satisfy entrywise
     `detDropMatLhs i j ≥ detDropMatRhs i j`, YET `intDet 2 detDropMatLhs = 0 < 4 = intDet 2 detDropMatRhs`!
  2. **Universal Positive-Subdiagonal `R8` Commutator Dichotomy (`A 1 0 ≥ 1, B 1 0 ≥ 1, A * B ≥ B * A`)**:
     For ANY `A, B : Fin 2 -> Fin 2 -> Nat` with `A 1 0 ≥ 1`, `B 1 0 ≥ 1`, and entrywise
     `natMatMul 2 A B i j ≥ natMatMul 2 B A i j` (as required on `R8 : [41, 23] -> [23, 41]` in `c39`
     and `[83, 47] -> [47, 83]` in `c78`):
     - Off-diagonal product lock: `A 0 1 * B 1 0 = B 0 1 * A 1 0`;
     - Complete dichotomy: EITHER both matrices are lower-triangular (`A 0 1 = 0 ∧ B 0 1 = 0`),
       OR both are genuinely non-triangular (`A 0 1 ≥ 1 ∧ B 0 1 ≥ 1`) AND **commute identically**
       (`∀ i j : Fin 2, natMatMul 2 A B i j = natMatMul 2 B A i j`, zero strict commutator drop in ANY
       entry!) with exact trace-gap proportionality `B 1 0 * A 0 0 + A 1 0 * B 1 1 = A 1 0 * B 0 0 + B 1 0 * A 1 1`!
-/
theorem natMat2_pos_subdiag_commutator_lock :
    ((∀ i j : Fin 2, detDropMatLhs i j ≥ detDropMatRhs i j) ∧
     intDet 2 (fun i j => (detDropMatLhs i j : Int)) = 0 ∧
     intDet 2 (fun i j => (detDropMatRhs i j : Int)) = 4) ∧
    (∀ (A B : Fin 2 -> Fin 2 -> Nat),
      let z0 : Fin 2 := ⟨0, by decide⟩
      let z1 : Fin 2 := ⟨1, by decide⟩
      A z1 z0 ≥ 1 -> B z1 z0 ≥ 1 ->
      (∀ i j : Fin 2, natMatMul 2 A B i j ≥ natMatMul 2 B A i j) ->
      A z0 z1 * B z1 z0 = B z0 z1 * A z1 z0 ∧
      ((A z0 z1 = 0 ∧ B z0 z1 = 0) ∨
       (A z0 z1 ≥ 1 ∧ B z0 z1 ≥ 1 ∧
        (∀ i j : Fin 2, natMatMul 2 A B i j = natMatMul 2 B A i j) ∧
        B z1 z0 * A z0 z0 + A z1 z0 * B z1 z1 = A z1 z0 * B z0 z0 + B z1 z0 * A z1 z1))) := by
  refine ⟨⟨by decide, by decide, by decide⟩, ?_⟩
  intro A B
  dsimp only
  intro hA10 hB10 hge
  have hdiag0 := natMatMul_commutator_diag_eq.2.1 2 A B hge fin2_0
  have hdiag1 := natMatMul_commutator_diag_eq.2.1 2 A B hge fin2_1
  rw [natMatMul_two_expand A B fin2_0 fin2_0, natMatMul_two_expand B A fin2_0 fin2_0] at hdiag0
  have ha00_comm : A fin2_0 fin2_0 * B fin2_0 fin2_0 = B fin2_0 fin2_0 * A fin2_0 fin2_0 :=
    Nat.mul_comm _ _
  have hoff_eq : A fin2_0 fin2_1 * B fin2_1 fin2_0 = B fin2_0 fin2_1 * A fin2_1 fin2_0 := by
    dsimp only [fin2_0, fin2_1] at *
    omega
  refine ⟨hoff_eq, ?_⟩
  by_cases ha01 : A fin2_0 fin2_1 = 0
  · left
    rw [ha01, Nat.zero_mul] at hoff_eq
    rcases Nat.mul_eq_zero.mp hoff_eq.symm with hb01 | ha10_z
    · exact ⟨ha01, hb01⟩
    · dsimp only [fin2_0, fin2_1] at *; omega
  · right
    have ha01_pos : A fin2_0 fin2_1 ≥ 1 := by dsimp only [fin2_0, fin2_1] at *; omega
    have hb01_pos : B fin2_0 fin2_1 ≥ 1 := by
      by_cases hb0 : B fin2_0 fin2_1 = 0
      · rw [hb0, Nat.zero_mul] at hoff_eq
        rcases Nat.mul_eq_zero.mp hoff_eq with h1 | h2 <;> (dsimp only [fin2_0, fin2_1] at *; omega)
      · dsimp only [fin2_0, fin2_1] at *; omega
    have h01 := hge fin2_0 fin2_1
    have h10 := hge fin2_1 fin2_0
    rw [natMatMul_two_expand A B fin2_0 fin2_1, natMatMul_two_expand B A fin2_0 fin2_1] at h01
    rw [natMatMul_two_expand A B fin2_1 fin2_0, natMatMul_two_expand B A fin2_1 fin2_0] at h10
    have hm01 : A fin2_1 fin2_0 * (B fin2_0 fin2_0 * A fin2_0 fin2_1 + B fin2_0 fin2_1 * A fin2_1 fin2_1) ≤
        A fin2_1 fin2_0 * (A fin2_0 fin2_0 * B fin2_0 fin2_1 + A fin2_0 fin2_1 * B fin2_1 fin2_1) :=
      Nat.mul_le_mul_left (A fin2_1 fin2_0) h01
    have hlhs_rw : A fin2_1 fin2_0 * (B fin2_0 fin2_0 * A fin2_0 fin2_1 + B fin2_0 fin2_1 * A fin2_1 fin2_1) =
        A fin2_0 fin2_1 * (A fin2_1 fin2_0 * B fin2_0 fin2_0 + B fin2_1 fin2_0 * A fin2_1 fin2_1) := by
      calc
        A fin2_1 fin2_0 * (B fin2_0 fin2_0 * A fin2_0 fin2_1 + B fin2_0 fin2_1 * A fin2_1 fin2_1)
            = A fin2_0 fin2_1 * (A fin2_1 fin2_0 * B fin2_0 fin2_0) + (B fin2_0 fin2_1 * A fin2_1 fin2_0) * A fin2_1 fin2_1 := by
              rw [Nat.mul_add]; congr 1 <;> ac_rfl
        _ = A fin2_0 fin2_1 * (A fin2_1 fin2_0 * B fin2_0 fin2_0) + (A fin2_0 fin2_1 * B fin2_1 fin2_0) * A fin2_1 fin2_1 := by rw [← hoff_eq]
        _ = A fin2_0 fin2_1 * (A fin2_1 fin2_0 * B fin2_0 fin2_0 + B fin2_1 fin2_0 * A fin2_1 fin2_1) := by
              rw [Nat.mul_add]; congr 1; ac_rfl
    have hrhs_rw : A fin2_1 fin2_0 * (A fin2_0 fin2_0 * B fin2_0 fin2_1 + A fin2_0 fin2_1 * B fin2_1 fin2_1) =
        A fin2_0 fin2_1 * (B fin2_1 fin2_0 * A fin2_0 fin2_0 + A fin2_1 fin2_0 * B fin2_1 fin2_1) := by
      calc
        A fin2_1 fin2_0 * (A fin2_0 fin2_0 * B fin2_0 fin2_1 + A fin2_0 fin2_1 * B fin2_1 fin2_1)
            = (B fin2_0 fin2_1 * A fin2_1 fin2_0) * A fin2_0 fin2_0 + A fin2_0 fin2_1 * (A fin2_1 fin2_0 * B fin2_1 fin2_1) := by
              rw [Nat.mul_add]; congr 1 <;> ac_rfl
        _ = (A fin2_0 fin2_1 * B fin2_1 fin2_0) * A fin2_0 fin2_0 + A fin2_0 fin2_1 * (A fin2_1 fin2_0 * B fin2_1 fin2_1) := by rw [← hoff_eq]
        _ = A fin2_0 fin2_1 * (B fin2_1 fin2_0 * A fin2_0 fin2_0 + A fin2_1 fin2_0 * B fin2_1 fin2_1) := by
              rw [Nat.mul_add]; congr 1; ac_rfl
    rw [hlhs_rw, hrhs_rw] at hm01
    have h10_rev : A fin2_1 fin2_0 * B fin2_0 fin2_0 + B fin2_1 fin2_0 * A fin2_1 fin2_1 ≤
        B fin2_1 fin2_0 * A fin2_0 fin2_0 + A fin2_1 fin2_0 * B fin2_1 fin2_1 := by
      by_cases hgt : B fin2_1 fin2_0 * A fin2_0 fin2_0 + A fin2_1 fin2_0 * B fin2_1 fin2_1 <
          A fin2_1 fin2_0 * B fin2_0 fin2_0 + B fin2_1 fin2_0 * A fin2_1 fin2_1
      · exfalso
        have hlt_m := Nat.mul_lt_mul_of_pos_left hgt (by omega : 0 < A fin2_0 fin2_1)
        exact absurd hlt_m (Nat.not_lt_of_ge hm01)
      · omega
    have hc_a11 : A fin2_1 fin2_1 * B fin2_1 fin2_0 = B fin2_1 fin2_0 * A fin2_1 fin2_1 :=
      Nat.mul_comm _ _
    have hc_b11 : B fin2_1 fin2_1 * A fin2_1 fin2_0 = A fin2_1 fin2_0 * B fin2_1 fin2_1 :=
      Nat.mul_comm _ _
    have h10_eq : A fin2_1 fin2_0 * B fin2_0 fin2_0 + A fin2_1 fin2_1 * B fin2_1 fin2_0 =
        B fin2_1 fin2_0 * A fin2_0 fin2_0 + B fin2_1 fin2_1 * A fin2_1 fin2_0 := by
      dsimp only [fin2_0, fin2_1] at *; omega
    have htr_gap : B fin2_1 fin2_0 * A fin2_0 fin2_0 + A fin2_1 fin2_0 * B fin2_1 fin2_1 =
        A fin2_1 fin2_0 * B fin2_0 fin2_0 + B fin2_1 fin2_0 * A fin2_1 fin2_1 := by
      dsimp only [fin2_0, fin2_1] at *; omega
    have h01_eq : A fin2_0 fin2_0 * B fin2_0 fin2_1 + A fin2_0 fin2_1 * B fin2_1 fin2_1 =
        B fin2_0 fin2_0 * A fin2_0 fin2_1 + B fin2_0 fin2_1 * A fin2_1 fin2_1 := by
      have hm_eq : A fin2_1 fin2_0 * (A fin2_0 fin2_0 * B fin2_0 fin2_1 + A fin2_0 fin2_1 * B fin2_1 fin2_1) =
          A fin2_1 fin2_0 * (B fin2_0 fin2_0 * A fin2_0 fin2_1 + B fin2_0 fin2_1 * A fin2_1 fin2_1) := by
        rw [hlhs_rw, hrhs_rw, htr_gap]
      exact Nat.eq_of_mul_eq_mul_left (by dsimp only [fin2_0, fin2_1] at *; omega : 0 < A fin2_1 fin2_0) hm_eq
    refine ⟨ha01_pos, hb01_pos, ?_, htr_gap⟩
    intro i j
    rcases (by have := i.isLt; omega : i.val = 0 ∨ i.val = 1) with hi | hi <;>
    rcases (by have := j.isLt; omega : j.val = 0 ∨ j.val = 1) with hj | hj
    · rw [show i = fin2_0 from Fin.ext hi, show j = fin2_0 from Fin.ext hj]
      exact natMatMul_commutator_diag_eq.2.1 2 A B hge fin2_0
    · rw [show i = fin2_0 from Fin.ext hi, show j = fin2_1 from Fin.ext hj,
          natMatMul_two_expand A B fin2_0 fin2_1, natMatMul_two_expand B A fin2_0 fin2_1]
      exact h01_eq
    · rw [show i = fin2_1 from Fin.ext hi, show j = fin2_0 from Fin.ext hj,
          natMatMul_two_expand A B fin2_1 fin2_0, natMatMul_two_expand B A fin2_1 fin2_0]
      exact h10_eq
    · rw [show i = fin2_1 from Fin.ext hi, show j = fin2_1 from Fin.ext hj]
      exact natMatMul_commutator_diag_eq.2.1 2 A B hge fin2_1

-- ----------------------------------------------------------------------------
-- Section 1B: Lower-Triangular (`∀ d ≥ 1`), Pos-Diag Upper-Triangular (`d = 2`),
--             & Unit-Diagonal Full-Rank Non-Triangular (`d = 2`) Collapse on `c39` & `c78`
-- ----------------------------------------------------------------------------

/-- `∀ d ≥ 1` lower-triangular (positive top-left `M_s 0 0 ≥ 1`, zero top-row off-diagonals `M_s 0 j = 0`
    for `j > 0`, arbitrary lower rows!) `ω^k` Hofbauer–Waldmann matrix tower. -/
def GenOmegaLowerTriPosTopMatTower (N d : Nat) (hd : d ≥ 1) :
    Nat -> List (List (Fin N) × List (Fin N)) -> Prop
  | 0, rules => rules = []
  | k + 1, rules =>
    rules = [] ∨
    ∃ (rem : List (List (Fin N) × List (Fin N)))
      (M : Fin N -> Fin d -> Fin d -> Nat) (v : Fin N -> Fin d -> Nat),
      (∀ s : Fin N, M s ⟨0, hd⟩ ⟨0, hd⟩ ≥ 1) ∧
      (∀ (s : Fin N) (j : Fin d), j.val > 0 -> M s ⟨0, hd⟩ j = 0) ∧
      (∀ r ∈ rules,
        (∀ i j : Fin d, evalFinWordMat N d M r.1 i j ≥ evalFinWordMat N d M r.2 i j) ∧
        (∀ i : Fin d, evalFinWordVec N d M v r.1 i ≥ evalFinWordVec N d M v r.2 i)) ∧
      (∀ r ∈ rules,
        ¬ (evalFinWordVec N d M v r.1 ⟨0, hd⟩ > evalFinWordVec N d M v r.2 ⟨0, hd⟩) -> r ∈ rem) ∧
      GenOmegaLowerTriPosTopMatTower N d hd k rem

/-- `d = 2` positive-diagonal upper-triangular (`M_s 0 0 ≥ 1, M_s 1 1 ≥ 1, M_s 1 0 = 0`, arbitrary
    `M_s 0 1 ≥ 0`) `ω^k` Hofbauer–Waldmann matrix tower. -/
def GenOmegaPosDiagUpperTri2DMatTower (N : Nat) :
    Nat -> List (List (Fin N) × List (Fin N)) -> Prop
  | 0, rules => rules = []
  | k + 1, rules =>
    rules = [] ∨
    ∃ (rem : List (List (Fin N) × List (Fin N)))
      (M : Fin N -> Fin 2 -> Fin 2 -> Nat) (v : Fin N -> Fin 2 -> Nat),
      (∀ s : Fin N, M s ⟨0, by decide⟩ ⟨0, by decide⟩ ≥ 1 ∧ M s ⟨1, by decide⟩ ⟨1, by decide⟩ ≥ 1) ∧
      (∀ s : Fin N, M s ⟨1, by decide⟩ ⟨0, by decide⟩ = 0) ∧
      (∀ r ∈ rules,
        (∀ i j : Fin 2, evalFinWordMat N 2 M r.1 i j ≥ evalFinWordMat N 2 M r.2 i j) ∧
        (∀ i : Fin 2, evalFinWordVec N 2 M v r.1 i ≥ evalFinWordVec N 2 M v r.2 i)) ∧
      (∀ r ∈ rules,
        ¬ (evalFinWordVec N 2 M v r.1 ⟨0, by decide⟩ >
            evalFinWordVec N 2 M v r.2 ⟨0, by decide⟩) -> r ∈ rem) ∧
      GenOmegaPosDiagUpperTri2DMatTower N k rem

/-- `d = 2` unit-diagonal full-rank-capable non-triangular (`M_s = [[1, b_s], [c_s, 1]]` with
    simultaneous `b_s, c_s ≥ 0`, including full-rank `det(M_s) = 1 - b_s * c_s ≠ 0` when `b_s * c_s ≥ 2`)
    `ω^k` Hofbauer–Waldmann matrix tower. -/
def GenOmegaUnitDiagFullRank2DMatTower (N : Nat) :
    Nat -> List (List (Fin N) × List (Fin N)) -> Prop
  | 0, rules => rules = []
  | k + 1, rules =>
    rules = [] ∨
    ∃ (rem : List (List (Fin N) × List (Fin N)))
      (M : Fin N -> Fin 2 -> Fin 2 -> Nat) (v : Fin N -> Fin 2 -> Nat),
      (∀ s : Fin N, M s ⟨0, by decide⟩ ⟨0, by decide⟩ = 1 ∧ M s ⟨1, by decide⟩ ⟨1, by decide⟩ = 1) ∧
      (∀ r ∈ rules,
        (∀ i j : Fin 2, evalFinWordMat N 2 M r.1 i j ≥ evalFinWordMat N 2 M r.2 i j) ∧
        (∀ i : Fin 2, evalFinWordVec N 2 M v r.1 i ≥ evalFinWordVec N 2 M v r.2 i)) ∧
      (∀ r ∈ rules,
        ¬ (evalFinWordVec N 2 M v r.1 ⟨0, by decide⟩ >
            evalFinWordVec N 2 M v r.2 ⟨0, by decide⟩) -> r ∈ rem) ∧
      GenOmegaUnitDiagFullRank2DMatTower N k rem

private theorem bool_or_split_w13 {a b : Bool} (h : (a || b) = true) : a = true ∨ b = true := by
  cases a <;> cases b <;> simp at h ⊢

private theorem natSumPrefix_eq_of_le_and_sum_eq_w13 (d : Nat) (f g : Fin d -> Nat)
    (hle : ∀ i : Fin d, g i ≤ f i) :
    ∀ k : Nat, k ≤ d ->
      natSumPrefix d f k ≤ natSumPrefix d g k ->
      ∀ (i : Fin d), i.val < k -> f i = g i
  | 0, _, _, _, hi => by omega
  | k + 1, hk, hsum, i, hi => by
    have hk_lt : k < d := hk
    simp only [natSumPrefix, hk_lt, dite_true] at hsum
    have hpre_ge : natSumPrefix d g k ≤ natSumPrefix d f k :=
      natSumPrefix_mono_w5 d g f hle k
    have hcur_ge : g ⟨k, hk_lt⟩ ≤ f ⟨k, hk_lt⟩ := hle ⟨k, hk_lt⟩
    have hpre_le : natSumPrefix d f k ≤ natSumPrefix d g k := by omega
    have hcur_eq : f ⟨k, hk_lt⟩ = g ⟨k, hk_lt⟩ := by omega
    by_cases hik : i.val = k
    · have hif : i = ⟨k, hk_lt⟩ := Fin.ext hik
      rwa [hif]
    · exact natSumPrefix_eq_of_le_and_sum_eq_w13 d f g hle k (Nat.le_of_lt hk) hpre_le i (by omega)

private theorem mul_pow_w13 (a b : Nat) : ∀ n : Nat, (a * b) ^ n = a ^ n * b ^ n
  | 0 => rfl
  | n + 1 => by
    rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, mul_pow_w13 a b n]
    ac_rfl

private theorem pow_mono_base_w13 (a b : Nat) (hle : a ≤ b) : ∀ n : Nat, a ^ n ≤ b ^ n
  | 0 => Nat.le_refl 1
  | n + 1 => Nat.mul_le_mul (pow_mono_base_w13 a b hle n) hle

private def prodFinWordW13 (N : Nat) (m : Fin N -> Nat) : List (Fin N) -> Nat
  | [] => 1
  | s :: rest => m s * prodFinWordW13 N m rest

private theorem evalFinAffine1D_fst_w13 (N : Nat) (m v : Fin N -> Nat) :
    ∀ w : List (Fin N), (evalFinAffine1D N m v w).1 = prodFinWordW13 N m w
  | [] => rfl
  | _ :: rest => by simp [evalFinAffine1D, prodFinWordW13, evalFinAffine1D_fst_w13 N m v rest]

private theorem prodFinWord_pos_w13 (N : Nat) (m : Fin N -> Nat) (hm : ∀ s : Fin N, m s ≥ 1) :
    ∀ w : List (Fin N), prodFinWordW13 N m w ≥ 1
  | [] => Nat.le_refl 1
  | s :: rest => Nat.mul_le_mul (hm s) (prodFinWord_pos_w13 N m hm rest)

private def weightedProdLhsW13 (N : Nat) (m : Fin N -> Nat) :
    List (List (Fin N) × List (Fin N)) -> List Nat -> Nat
  | [], _ => 1
  | _, [] => 1
  | r :: rs, u :: us => (prodFinWordW13 N m r.1) ^ u * weightedProdLhsW13 N m rs us

private def weightedProdRhsW13 (N : Nat) (m : Fin N -> Nat) :
    List (List (Fin N) × List (Fin N)) -> List Nat -> Nat
  | [], _ => 1
  | _, [] => 1
  | r :: rs, u :: us => (prodFinWordW13 N m r.2) ^ u * weightedProdRhsW13 N m rs us

private theorem prodFinWord_eq_sym_pow_prefix_w13 (N : Nat) (m : Fin N -> Nat) :
    ∀ w : List (Fin N),
      prodFinWordW13 N m w = colBoundProdPrefix N (fun s => (m s) ^ countFinOcc N s w) N
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
    simp only [prodFinWordW13, prodFinWord_eq_sym_pow_prefix_w13 N m rest]
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

private theorem colBoundProdPrefix_pow_mul_w13 (N : Nat) (m : Fin N -> Nat)
    (f g : Fin N -> Nat) (u : Nat) :
    ∀ k : Nat, k ≤ N ->
      (colBoundProdPrefix N (fun s => (m s) ^ f s) k) ^ u *
        colBoundProdPrefix N (fun s => (m s) ^ g s) k =
      colBoundProdPrefix N (fun s => (m s) ^ (u * f s + g s)) k
  | 0, _ => by simp [colBoundProdPrefix]
  | k + 1, hk => by
    have hk_lt : k < N := hk
    simp only [colBoundProdPrefix, hk_lt, dite_true]
    rw [mul_pow_w13 _ _ u,
        pow_pow_eq_mul_w5 (m ⟨k, hk_lt⟩) (f ⟨k, hk_lt⟩) u,
        Nat.mul_comm (f ⟨k, hk_lt⟩) u]
    have ih := colBoundProdPrefix_pow_mul_w13 N m f g u k (Nat.le_of_lt hk)
    calc
      ((colBoundProdPrefix N (fun s => (m s) ^ f s) k) ^ u * (m ⟨k, hk_lt⟩) ^ (u * f ⟨k, hk_lt⟩)) *
          (colBoundProdPrefix N (fun s => (m s) ^ g s) k * (m ⟨k, hk_lt⟩) ^ g ⟨k, hk_lt⟩)
          = ((colBoundProdPrefix N (fun s => (m s) ^ f s) k) ^ u *
              colBoundProdPrefix N (fun s => (m s) ^ g s) k) *
            ((m ⟨k, hk_lt⟩) ^ (u * f ⟨k, hk_lt⟩) * (m ⟨k, hk_lt⟩) ^ g ⟨k, hk_lt⟩) := by ac_rfl
      _ = colBoundProdPrefix N (fun s => (m s) ^ (u * f s + g s)) k *
            (m ⟨k, hk_lt⟩) ^ (u * f ⟨k, hk_lt⟩ + g ⟨k, hk_lt⟩) := by
            rw [ih, ← Nat.pow_add]

private theorem weightedProd_eq_sym_pow_w13 (N : Nat) (m : Fin N -> Nat) :
    ∀ (rules : List (List (Fin N) × List (Fin N))) (mults : List Nat),
      weightedProdLhsW13 N m rules mults =
        colBoundProdPrefix N (fun s => (m s) ^ weightedSymLhsSum N s rules mults) N ∧
      weightedProdRhsW13 N m rules mults =
        colBoundProdPrefix N (fun s => (m s) ^ weightedSymRhsSum N s rules mults) N
  | [], _ => by
    have hz : ∀ k : Nat, k ≤ N -> colBoundProdPrefix N (fun _ => 1) k = 1 := by
      intro k hk; induction k with
      | zero => rfl
      | succ k' ih =>
        have hk'_lt : k' < N := hk
        simp only [colBoundProdPrefix, hk'_lt, dite_true]
        rw [ih (Nat.le_of_lt hk), Nat.mul_one]
    refine ⟨?_, ?_⟩ <;> simpa [weightedProdLhsW13, weightedProdRhsW13, weightedSymLhsSum, weightedSymRhsSum]
      using (hz N (Nat.le_refl N)).symm
  | _ :: _, [] => by
    have hz : ∀ k : Nat, k ≤ N -> colBoundProdPrefix N (fun _ => 1) k = 1 := by
      intro k hk; induction k with
      | zero => rfl
      | succ k' ih =>
        have hk'_lt : k' < N := hk
        simp only [colBoundProdPrefix, hk'_lt, dite_true]
        rw [ih (Nat.le_of_lt hk), Nat.mul_one]
    refine ⟨?_, ?_⟩ <;> simpa [weightedProdLhsW13, weightedProdRhsW13, weightedSymLhsSum, weightedSymRhsSum]
      using (hz N (Nat.le_refl N)).symm
  | r0 :: rs, u0 :: us => by
    rcases weightedProd_eq_sym_pow_w13 N m rs us with ⟨hl, hr⟩
    refine ⟨?_, ?_⟩
    · simp only [weightedProdLhsW13, hl, prodFinWord_eq_sym_pow_prefix_w13 N m r0.1]
      exact colBoundProdPrefix_pow_mul_w13 N m _ _ u0 N (Nat.le_refl N)
    · simp only [weightedProdRhsW13, hr, prodFinWord_eq_sym_pow_prefix_w13 N m r0.2]
      exact colBoundProdPrefix_pow_mul_w13 N m _ _ u0 N (Nat.le_refl N)

private theorem colBoundProdPrefix_mono_pos_w13 (N : Nat) (f g : Fin N -> Nat)
    (hpos : ∀ s : Fin N, f s ≥ 1) (hle : ∀ s : Fin N, f s ≤ g s) :
    ∀ k : Nat, k ≤ N ->
      colBoundProdPrefix N f k ≥ 1 ∧
      colBoundProdPrefix N f k ≤ colBoundProdPrefix N g k ∧
      (colBoundProdPrefix N f k = colBoundProdPrefix N g k ->
        ∀ (s : Fin N), s.val < k -> f s = g s)
  | 0, _ => ⟨Nat.le_refl 1, Nat.le_refl 1, fun _ _ hs => by omega⟩
  | k + 1, hk => by
    have hk_lt : k < N := hk
    rcases colBoundProdPrefix_mono_pos_w13 N f g hpos hle k (Nat.le_of_lt hk) with ⟨hp, hm, heq_imp⟩
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
    · have hsf : s = ⟨k, hk_lt⟩ := Fin.ext hsk
      rwa [hsf]
    · exact heq_imp ha1_eq s (by omega)

private theorem syzygy_forces_parikh_and_prod_eq_w13
    (N : Nat) (rules : List (List (Fin N) × List (Fin N))) (mults : List Nat)
    (hsyz : checkPositiveParikhSyzygyFastBool N rules mults = true) :
    (∀ wt : Fin N -> Nat,
      (∀ r ∈ rules, evalFinParikh N wt r.1 ≥ evalFinParikh N wt r.2) ->
      ∀ r ∈ rules, evalFinParikh N wt r.1 = evalFinParikh N wt r.2) ∧
    (∀ m : Fin N -> Nat,
      (∀ s : Fin N, m s ≥ 1) ->
      (∀ r ∈ rules, prodFinWordW13 N m r.1 ≥ prodFinWordW13 N m r.2) ->
      ∀ r ∈ rules, prodFinWordW13 N m r.1 = prodFinWordW13 N m r.2) := by
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
  refine ⟨?_, ?_⟩
  · intro wt hweak
    rcases weightedParikh_eq_sum_sym N wt rules mults with ⟨hl_sum, hr_sum⟩
    have htot_le : weightedParikhLhs N wt rules mults ≤ weightedParikhRhs N wt rules mults := by
      rw [hl_sum, hr_sum]
      exact natSumPrefix_mono_w5 N _ _ (fun s => Nat.mul_le_mul_left (wt s) (hsym_le s)) N
    exact weightedParikh_strict_of_mem N wt rules mults hlen hpos_m hweak htot_le
  · intro m hm1 hweak
    have hprod_ge : ∀ (rs : List (List (Fin N) × List (Fin N))) (us : List Nat),
        rs.length = us.length ->
        checkAllPosNatList us = true ->
        (∀ r ∈ rs, prodFinWordW13 N m r.1 ≥ prodFinWordW13 N m r.2) ->
        weightedProdRhsW13 N m rs us ≥ 1 ∧
        weightedProdLhsW13 N m rs us ≥ weightedProdRhsW13 N m rs us ∧
        (weightedProdLhsW13 N m rs us = weightedProdRhsW13 N m rs us ->
          ∀ r ∈ rs, prodFinWordW13 N m r.1 = prodFinWordW13 N m r.2) := by
      intro rs; induction rs with
      | nil =>
        intro _ _ _ _
        exact ⟨by simp [weightedProdRhsW13], by simp [weightedProdLhsW13, weightedProdRhsW13],
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
          simp only [weightedProdLhsW13, weightedProdRhsW13]
          have hp_r2 := prodFinWord_pos_w13 N m hm1 r0.2
          have hpu_pos := nat_pow_pos_of_pos (prodFinWordW13 N m r0.2) hp_r2 u0
          have hw0 := hw r0 List.mem_cons_self
          have hpu_ge := pow_mono_base_w13 (prodFinWordW13 N m r0.2) (prodFinWordW13 N m r0.1) hw0 u0
          refine ⟨Nat.mul_le_mul hpu_pos hr_pos, Nat.mul_le_mul hpu_ge hge_tl, ?_⟩
          intro heq_mul r hr_mem
          have h1_eq : (prodFinWordW13 N m r0.1) ^ u0 = (prodFinWordW13 N m r0.2) ^ u0 := by
            by_cases hne : (prodFinWordW13 N m r0.1) ^ u0 = (prodFinWordW13 N m r0.2) ^ u0
            · exact hne
            · exfalso
              have hlt : (prodFinWordW13 N m r0.2) ^ u0 < (prodFinWordW13 N m r0.1) ^ u0 := by omega
              have hm1_lt := Nat.mul_lt_mul_of_pos_right hlt
                (Nat.lt_of_lt_of_le Nat.zero_lt_one hr_pos)
              have hm2_le := Nat.mul_le_mul_left ((prodFinWordW13 N m r0.1) ^ u0) hge_tl
              exact Nat.ne_of_lt (Nat.lt_of_lt_of_le hm1_lt hm2_le) heq_mul.symm
          have h2_eq : weightedProdLhsW13 N m rt ut = weightedProdRhsW13 N m rt ut := by
            rw [h1_eq] at heq_mul
            exact Nat.eq_of_mul_eq_mul_left (by omega) heq_mul
          cases hr_mem with
          | head =>
            by_cases hbase : prodFinWordW13 N m r0.1 = prodFinWordW13 N m r0.2
            · exact hbase
            · exfalso
              have hgt : prodFinWordW13 N m r0.2 < prodFinWordW13 N m r0.1 := by omega
              have hpow_lt : (prodFinWordW13 N m r0.2) ^ u0 < (prodFinWordW13 N m r0.1) ^ u0 := by
                rw [show u0 = (u0 - 1) + 1 by omega, Nat.pow_succ, Nat.pow_succ]
                have hm_b := pow_mono_base_w13 _ _ hw0 (u0 - 1)
                have hm_p := nat_pow_pos_of_pos _ hp_r2 (u0 - 1)
                have h1 := Nat.mul_le_mul_right (prodFinWordW13 N m r0.2) hm_b
                have h2 := Nat.mul_lt_mul_of_pos_left hgt
                  (Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_trans hm_p hm_b))
                exact Nat.lt_of_le_of_lt h1 h2
              omega
          | tail _ htl => exact heq_tl h2_eq r htl
    rcases hprod_ge rules mults hlen hpos_m hweak with ⟨_, htot_ge, htot_imp⟩
    rcases weightedProd_eq_sym_pow_w13 N m rules mults with ⟨hl_sym, hr_sym⟩
    have hsym_pow_le : ∀ s : Fin N,
        (m s) ^ weightedSymLhsSum N s rules mults ≤ (m s) ^ weightedSymRhsSum N s rules mults :=
      fun s => nat_pow_mono_exp_pos (m s) _ _ (hm1 s) (hsym_le s)
    have hsym_pow_pos : ∀ s : Fin N, (m s) ^ weightedSymLhsSum N s rules mults ≥ 1 :=
      fun s => nat_pow_pos_of_pos (m s) (hm1 s) _
    rcases colBoundProdPrefix_mono_pos_w13 N _ _ hsym_pow_pos hsym_pow_le N (Nat.le_refl N) with
      ⟨_, htot_le_sym, _⟩
    rw [← hl_sym, ← hr_sym] at htot_le_sym
    exact htot_imp (by omega)

private theorem weightedParikh_eq_of_all_eq_w13 (N : Nat) (wt : Fin N -> Nat) :
    ∀ (rs : List (List (Fin N) × List (Fin N))) (us : List Nat),
      (∀ r ∈ rs, evalFinParikh N wt r.1 = evalFinParikh N wt r.2) ->
      weightedParikhLhs N wt rs us = weightedParikhRhs N wt rs us
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | r0 :: rt, u0 :: ut, heq => by
    simp only [weightedParikhLhs, weightedParikhRhs, heq r0 List.mem_cons_self,
      weightedParikh_eq_of_all_eq_w13 N wt rt ut (fun r hr => heq r (List.mem_cons_of_mem r0 hr))]

private theorem weightedProd_eq_of_all_eq_w13 (N : Nat) (m : Fin N -> Nat) :
    ∀ (rs : List (List (Fin N) × List (Fin N))) (us : List Nat),
      (∀ r ∈ rs, prodFinWordW13 N m r.1 = prodFinWordW13 N m r.2) ->
      weightedProdLhsW13 N m rs us = weightedProdRhsW13 N m rs us
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | r0 :: rt, u0 :: ut, heq => by
    simp only [weightedProdLhsW13, weightedProdRhsW13, heq r0 List.mem_cons_self,
      weightedProd_eq_of_all_eq_w13 N m rt ut (fun r hr => heq r (List.mem_cons_of_mem r0 hr))]

private theorem checkInteriorAnnihilationPairsAux_sound_w13 (M N : Nat)
    (rules : List (List (Fin N) × List (Fin N))) :
    ∀ (ps ns : List (Nat × Nat)) (idx : Nat),
      ps.length = ns.length ->
      checkInteriorAnnihilationPairsAux M N rules idx ps ns = true ->
      ∀ k : Nat, k < ps.length ->
        let p := getPairAtW11 ps k
        let n := getPairAtW11 ns k
        p.1 + n.2 ≤ p.2 + n.1 ∧
        (idx + k ≥ 4 * M -> symAppearsInRulesBool N (idx + k) rules = true -> p.1 + n.2 < p.2 + n.1)
  | [], _, _, _, _, _, hk => by simp at hk
  | _ :: _, [], _, hlen, _, _, _ => by simp at hlen
  | _ :: _, _ :: _, idx, _, hb, 0, _ => by
    unfold checkInteriorAnnihilationPairsAux at hb
    rcases bool_and_split hb with ⟨hb1, _⟩
    rcases bool_and_split hb1 with ⟨hle_b, hlt_b⟩
    simp only [getPairAtW11, Nat.add_zero]
    refine ⟨of_decide_eq_true hle_b, ?_⟩
    intro hge4 hact
    have hcond : (decide (idx ≥ 4 * M) && symAppearsInRulesBool N idx rules) = true := by
      rw [decide_eq_true hge4, hact]; rfl
    rw [hcond] at hlt_b
    exact of_decide_eq_true hlt_b
  | _ :: ps, _ :: ns, idx, hlen, hb, k + 1, hk => by
    unfold checkInteriorAnnihilationPairsAux at hb
    rcases bool_and_split hb with ⟨_, hrest⟩
    have ih := checkInteriorAnnihilationPairsAux_sound_w13 M N rules ps ns (idx + 1)
      (by simp at hlen; omega) hrest k (by simp at hk; omega)
    simpa [getPairAtW11, show idx + 1 + k = idx + (k + 1) by omega] using ih

private theorem signed_annihilation_forces_interior_zero_and_one_w13 (M : Nat)
    (rules : List (List (Fin (14 * M)) × List (Fin (14 * M))))
    (posMults negMults : List Nat)
    (hann : checkSignedInteriorAnnihilationBool M rules posMults negMults = true) :
    (∀ wt : Fin (14 * M) -> Nat,
      (∀ r ∈ rules, evalFinParikh (14 * M) wt r.1 = evalFinParikh (14 * M) wt r.2) ->
      ∀ s : Fin (14 * M), s.val ≥ 4 * M -> symAppearsInRulesBool (14 * M) s.val rules = true ->
        wt s = 0) ∧
    (∀ m : Fin (14 * M) -> Nat,
      (∀ s : Fin (14 * M), m s ≥ 1) ->
      (∀ r ∈ rules, prodFinWordW13 (14 * M) m r.1 = prodFinWordW13 (14 * M) m r.2) ->
      ∀ s : Fin (14 * M), s.val ≥ 4 * M -> symAppearsInRulesBool (14 * M) s.val rules = true ->
        m s = 1) := by
  rcases accumSymCountsW11_spec (14 * M) rules posMults with ⟨hlen_p, hget_p⟩
  rcases accumSymCountsW11_spec (14 * M) rules negMults with ⟨hlen_n, hget_n⟩
  let A_cnt : Fin (14 * M) -> Nat := fun s =>
    weightedSymLhsSum (14 * M) s rules posMults + weightedSymRhsSum (14 * M) s rules negMults
  let B_cnt : Fin (14 * M) -> Nat := fun s =>
    weightedSymRhsSum (14 * M) s rules posMults + weightedSymLhsSum (14 * M) s rules negMults
  have hAB : ∀ s : Fin (14 * M),
      A_cnt s ≤ B_cnt s ∧
      (s.val ≥ 4 * M -> symAppearsInRulesBool (14 * M) s.val rules = true -> A_cnt s < B_cnt s) := by
    intro s
    have hsnd := checkInteriorAnnihilationPairsAux_sound_w13 M (14 * M) rules
      (accumSymCountsW11 (14 * M) rules posMults) (accumSymCountsW11 (14 * M) rules negMults) 0
      (hlen_p.trans hlen_n.symm) hann s.val (by rw [hlen_p]; exact s.isLt)
    simp only [Nat.zero_add, hget_p s, hget_n s] at hsnd
    exact hsnd
  refine ⟨?_, ?_⟩
  · intro wt heq s hs_ge hs_act
    have hp_eq := weightedParikh_eq_of_all_eq_w13 (14 * M) wt rules posMults heq
    have hn_eq := weightedParikh_eq_of_all_eq_w13 (14 * M) wt rules negMults heq
    rcases weightedParikh_eq_sum_sym (14 * M) wt rules posMults with ⟨hl_p, hr_p⟩
    rcases weightedParikh_eq_sum_sym (14 * M) wt rules negMults with ⟨hl_n, hr_n⟩
    have hsum_add : ∀ k : Nat, k ≤ 14 * M ->
        natSumPrefix (14 * M) (fun x => wt x * weightedSymLhsSum (14 * M) x rules posMults) k +
          natSumPrefix (14 * M) (fun x => wt x * weightedSymRhsSum (14 * M) x rules negMults) k =
        natSumPrefix (14 * M) (fun x => wt x * A_cnt x) k := by
      intro k hk; induction k with
      | zero => rfl
      | succ k' ih =>
        have hk'_lt : k' < 14 * M := hk
        simp only [natSumPrefix, hk'_lt, dite_true]
        rw [← ih (Nat.le_of_lt hk)]
        dsimp only [A_cnt]
        rw [Nat.mul_add]
        omega
    have hsum_addB : ∀ k : Nat, k ≤ 14 * M ->
        natSumPrefix (14 * M) (fun x => wt x * weightedSymRhsSum (14 * M) x rules posMults) k +
          natSumPrefix (14 * M) (fun x => wt x * weightedSymLhsSum (14 * M) x rules negMults) k =
        natSumPrefix (14 * M) (fun x => wt x * B_cnt x) k := by
      intro k hk; induction k with
      | zero => rfl
      | succ k' ih =>
        have hk'_lt : k' < 14 * M := hk
        simp only [natSumPrefix, hk'_lt, dite_true]
        rw [← ih (Nat.le_of_lt hk)]
        dsimp only [B_cnt]
        rw [Nat.mul_add]
        omega
    have htot_eq : natSumPrefix (14 * M) (fun x => wt x * A_cnt x) (14 * M) =
        natSumPrefix (14 * M) (fun x => wt x * B_cnt x) (14 * M) := by
      rw [← hsum_add (14 * M) (Nat.le_refl _), ← hsum_addB (14 * M) (Nat.le_refl _),
          ← hl_p, ← hr_p, ← hl_n, ← hr_n, hp_eq, hn_eq]
    have hterm_eq : wt s * B_cnt s = wt s * A_cnt s :=
      natSumPrefix_eq_of_le_and_sum_eq_w13 (14 * M)
        (fun x => wt x * B_cnt x) (fun x => wt x * A_cnt x)
        (fun x => Nat.mul_le_mul_left (wt x) (hAB x).1) (14 * M) (Nat.le_refl _)
        (Nat.le_of_eq htot_eq.symm) s s.isLt
    have hlt_s := (hAB s).2 hs_ge hs_act
    by_cases hwt0 : wt s = 0
    · exact hwt0
    · exfalso
      have hm_lt := Nat.mul_lt_mul_of_pos_left hlt_s (Nat.pos_of_ne_zero hwt0)
      exact Nat.ne_of_lt hm_lt hterm_eq.symm
  · intro m hm1 heq s hs_ge hs_act
    have hp_eq := weightedProd_eq_of_all_eq_w13 (14 * M) m rules posMults heq
    have hn_eq := weightedProd_eq_of_all_eq_w13 (14 * M) m rules negMults heq
    rcases weightedProd_eq_sym_pow_w13 (14 * M) m rules posMults with ⟨hl_p, hr_p⟩
    rcases weightedProd_eq_sym_pow_w13 (14 * M) m rules negMults with ⟨hl_n, hr_n⟩
    have hprod_mul : ∀ (f g : Fin (14 * M) -> Nat) (k : Nat), k ≤ 14 * M ->
        colBoundProdPrefix (14 * M) (fun x => (m x) ^ f x) k *
          colBoundProdPrefix (14 * M) (fun x => (m x) ^ g x) k =
        colBoundProdPrefix (14 * M) (fun x => (m x) ^ (f x + g x)) k := by
      intro f g k hk
      simpa using colBoundProdPrefix_pow_mul_w13 (14 * M) m f g 1 k hk
    have htot_eq : colBoundProdPrefix (14 * M) (fun x => (m x) ^ A_cnt x) (14 * M) =
        colBoundProdPrefix (14 * M) (fun x => (m x) ^ B_cnt x) (14 * M) := by
      rw [← hprod_mul _ _ (14 * M) (Nat.le_refl _), ← hprod_mul _ _ (14 * M) (Nat.le_refl _),
          ← hl_p, ← hr_p, ← hl_n, ← hr_n, hp_eq, hn_eq]
    rcases colBoundProdPrefix_mono_pos_w13 (14 * M)
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
        conv => lhs; rw [hexp]
        exact Nat.pow_add (m s) (A_cnt s) (B_cnt s - A_cnt s)
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

private theorem evalFinAffine1D_all_int_w13 (M : Nat) (m v : Fin (14 * M) -> Nat) :
    ∀ w : List (Fin (14 * M)),
      (∀ s ∈ w, m s = 1) ->
      evalFinAffine1D (14 * M) m v w = (1, evalFinParikh (14 * M) v w)
  | [], _ => rfl
  | s :: rest, hall => by
    have hs1 : m s = 1 := hall s List.mem_cons_self
    have ih := evalFinAffine1D_all_int_w13 M m v rest (fun x hx => hall x (List.mem_cons_of_mem s hx))
    simp [evalFinAffine1D, evalFinParikh, hs1, ih]

private theorem evalFinAffine1D_right_or_int_w13 (M : Nat) (m v : Fin (14 * M) -> Nat) :
    ∀ w : List (Fin (14 * M)),
      checkWordRightOrIntBool M w = true ->
      (∀ s ∈ w, s.val ≥ 4 * M -> m s = 1) ->
      (evalFinAffine1D (14 * M) m v w).2 = evalFinParikh (14 * M) v w
  | [], _, _ => rfl
  | [_], _, _ => by simp [evalFinAffine1D, evalFinParikh]
  | s :: s2 :: rest, hb, hint => by
    rcases bool_and_split hb with ⟨hs_ge, hrest⟩
    have hs1 : m s = 1 := hint s List.mem_cons_self (of_decide_eq_true hs_ge)
    have ih := evalFinAffine1D_right_or_int_w13 M m v (s2 :: rest) hrest
      (fun x hx => hint x (List.mem_cons_of_mem s hx))
    change v s + m s * (evalFinAffine1D (14 * M) m v (s2 :: rest)).2 =
      v s + evalFinParikh (14 * M) v (s2 :: rest)
    rw [hs1, Nat.one_mul, ih]

private theorem parikh_int_scale_w13 (M c : Nat) (v wt : Fin (14 * M) -> Nat) :
    ∀ w : List (Fin (14 * M)),
      (∀ s ∈ w, wt s = c * v s) ->
      evalFinParikh (14 * M) wt w = c * evalFinParikh (14 * M) v w
  | [], _ => by simp [evalFinParikh]
  | s :: rest, hall => by
    simp only [evalFinParikh, hall s List.mem_cons_self,
      parikh_int_scale_w13 M c v wt rest (fun x hx => hall x (List.mem_cons_of_mem s hx)),
      Nat.mul_add]

private theorem hasTwoToOneRuleBool_sound_w13 (N : Nat) (a b c : Fin N) :
    ∀ rs : List (List (Fin N) × List (Fin N)),
      hasTwoToOneRuleBool N a.val b.val c.val rs = true -> ([a, b], [c]) ∈ rs
  | [], h => by cases h
  | (l, r) :: rs, h => by
    unfold hasTwoToOneRuleBool at h
    rcases bool_or_split_w13 h with h0 | htl
    · rcases of_decide_eq_true h0 with ⟨hl, hr⟩
      have hl_eq : l = [a, b] := by
        cases l with
        | nil => simp at hl
        | cons x1 tl1 =>
          cases tl1 with
          | nil => simp at hl
          | cons x2 tl2 =>
            cases tl2 with
            | nil =>
              simp only [List.map_cons, List.map_nil, List.cons.injEq] at hl
              rw [Fin.ext hl.1, Fin.ext hl.2.1]
            | cons _ _ => simp at hl
      have hr_eq : r = [c] := by
        cases r with
        | nil => simp at hr
        | cons y1 tl1 =>
          cases tl1 with
          | nil =>
            simp only [List.map_cons, List.map_nil, List.cons.injEq] at hr
            rw [Fin.ext hr.1]
          | cons _ _ => simp at hr
      rw [hl_eq, hr_eq]
      exact List.Mem.head _
    · exact List.mem_cons_of_mem _ (hasTwoToOneRuleBool_sound_w13 N a b c rs htl)

private theorem lowerTriPosTop_eq_affine1d (N d : Nat) (hd : d ≥ 1)
    (M : Fin N -> Fin d -> Fin d -> Nat) (v : Fin N -> Fin d -> Nat)
    (h0j : ∀ (s : Fin N) (j : Fin d), j.val > 0 -> M s ⟨0, hd⟩ j = 0) :
    ∀ w : List (Fin N),
      evalFinWordMat N d M w ⟨0, hd⟩ ⟨0, hd⟩ =
        (evalFinAffine1D N (fun s => M s ⟨0, hd⟩ ⟨0, hd⟩) (fun s => v s ⟨0, hd⟩) w).1 ∧
      evalFinWordVec N d M v w ⟨0, hd⟩ =
        (evalFinAffine1D N (fun s => M s ⟨0, hd⟩ ⟨0, hd⟩) (fun s => v s ⟨0, hd⟩) w).2
  | [] => by simp [evalFinWordMat, evalFinWordVec, evalFinAffine1D, natMatId]
  | s :: rest => by
    rcases lowerTriPosTop_eq_affine1d N d hd M v h0j rest with ⟨hm_ih, hv_ih⟩
    refine ⟨?_, ?_⟩
    · simp only [evalFinWordMat, evalFinAffine1D, natMatMul]
      unfold natSumFin
      have h1 : natSumPrefix d
          (fun k => M s ⟨0, hd⟩ k * evalFinWordMat N d M rest k ⟨0, hd⟩) d =
          M s ⟨0, hd⟩ ⟨0, hd⟩ * evalFinWordMat N d M rest ⟨0, hd⟩ ⟨0, hd⟩ := by
        have hst : ∀ m : Nat, 1 ≤ m -> m ≤ d ->
            natSumPrefix d (fun k => M s ⟨0, hd⟩ k * evalFinWordMat N d M rest k ⟨0, hd⟩) m =
              M s ⟨0, hd⟩ ⟨0, hd⟩ * evalFinWordMat N d M rest ⟨0, hd⟩ ⟨0, hd⟩ := by
          intro m hm1 hmd; induction m with
          | zero => omega
          | succ m' ihm =>
            cases m' with
            | zero =>
              have h0d : 0 < d := hd
              simp only [natSumPrefix, h0d, dite_true, Nat.zero_add]
            | succ r =>
              have hr1 : r + 1 < d := hmd
              conv => lhs; unfold natSumPrefix
              simp only [hr1, dite_true]
              rw [ihm (by omega) (Nat.le_of_lt hmd), h0j s ⟨r + 1, hr1⟩ (Nat.succ_pos r),
                  Nat.zero_mul, Nat.add_zero]
        exact hst d hd (Nat.le_refl d)
      rw [h1, hm_ih]
    · simp only [evalFinWordVec, evalFinAffine1D, natMatVec]
      unfold natSumFin
      have h2 : natSumPrefix d
          (fun k => M s ⟨0, hd⟩ k * evalFinWordVec N d M v rest k) d =
          M s ⟨0, hd⟩ ⟨0, hd⟩ * evalFinWordVec N d M v rest ⟨0, hd⟩ := by
        have hst : ∀ m : Nat, 1 ≤ m -> m ≤ d ->
            natSumPrefix d (fun k => M s ⟨0, hd⟩ k * evalFinWordVec N d M v rest k) m =
              M s ⟨0, hd⟩ ⟨0, hd⟩ * evalFinWordVec N d M v rest ⟨0, hd⟩ := by
          intro m hm1 hmd; induction m with
          | zero => omega
          | succ m' ihm =>
            cases m' with
            | zero =>
              have h0d : 0 < d := hd
              simp only [natSumPrefix, h0d, dite_true, Nat.zero_add]
            | succ r =>
              have hr1 : r + 1 < d := hmd
              conv => lhs; unfold natSumPrefix
              simp only [hr1, dite_true]
              rw [ihm (by omega) (Nat.le_of_lt hmd), h0j s ⟨r + 1, hr1⟩ (Nat.succ_pos r),
                  Nat.zero_mul, Nat.add_zero]
        exact hst d hd (Nat.le_refl d)
      rw [h2, hv_ih]

private theorem upperTri2D_bot_eq_affine1d (N : Nat)
    (M : Fin N -> Fin 2 -> Fin 2 -> Nat) (v : Fin N -> Fin 2 -> Nat)
    (h10 : ∀ s : Fin N, M s ⟨1, by decide⟩ ⟨0, by decide⟩ = 0) :
    ∀ w : List (Fin N),
      evalFinWordMat N 2 M w ⟨1, by decide⟩ ⟨0, by decide⟩ = 0 ∧
      evalFinWordMat N 2 M w ⟨1, by decide⟩ ⟨1, by decide⟩ =
        (evalFinAffine1D N (fun s => M s ⟨1, by decide⟩ ⟨1, by decide⟩)
          (fun s => v s ⟨1, by decide⟩) w).1 ∧
      evalFinWordVec N 2 M v w ⟨1, by decide⟩ =
        (evalFinAffine1D N (fun s => M s ⟨1, by decide⟩ ⟨1, by decide⟩)
          (fun s => v s ⟨1, by decide⟩) w).2
  | [] => by simp [evalFinWordMat, evalFinWordVec, evalFinAffine1D, natMatId]
  | s :: rest => by
    rcases upperTri2D_bot_eq_affine1d N M v h10 rest with ⟨h10_ih, h11_ih, hv1_ih⟩
    refine ⟨?_, ?_, ?_⟩
    · simp only [evalFinWordMat]
      rw [natMatMul_two_expand, h10 s, h10_ih, Nat.zero_mul, Nat.mul_zero]
    · simp only [evalFinWordMat, evalFinAffine1D]
      rw [natMatMul_two_expand, h10 s, Nat.zero_mul, Nat.zero_add, h11_ih]
    · simp only [evalFinWordVec, evalFinAffine1D]
      rw [natMatVec_two_expand, h10 s, Nat.zero_mul, Nat.zero_add, hv1_ih]

private theorem upperTri2D_mat01_all_int (N : Nat)
    (M : Fin N -> Fin 2 -> Fin 2 -> Nat)
    (h10 : ∀ s : Fin N, M s ⟨1, by decide⟩ ⟨0, by decide⟩ = 0) :
    ∀ w : List (Fin N),
      (∀ s ∈ w, M s ⟨0, by decide⟩ ⟨0, by decide⟩ = 1 ∧ M s ⟨1, by decide⟩ ⟨1, by decide⟩ = 1) ->
      evalFinWordMat N 2 M w ⟨0, by decide⟩ ⟨0, by decide⟩ = 1 ∧
      evalFinWordMat N 2 M w ⟨1, by decide⟩ ⟨1, by decide⟩ = 1 ∧
      evalFinWordMat N 2 M w ⟨0, by decide⟩ ⟨1, by decide⟩ =
        evalFinParikh N (fun s => M s ⟨0, by decide⟩ ⟨1, by decide⟩) w
  | [], _ => by simp [evalFinWordMat, evalFinParikh, natMatId]
  | s :: rest, hall => by
    rcases hall s List.mem_cons_self with ⟨ha1, he1⟩
    rcases upperTri2D_mat01_all_int N M h10 rest
      (fun x hx => hall x (List.mem_cons_of_mem s hx)) with ⟨hm00, hm11, hm01⟩
    rcases upperTri2D_bot_eq_affine1d N M (fun _ _ => 0) h10 rest with ⟨hm10, _, _⟩
    refine ⟨?_, ?_, ?_⟩
    · simp only [evalFinWordMat]
      rw [natMatMul_two_expand, ha1, hm00, hm10, Nat.mul_zero, Nat.add_zero, Nat.one_mul]
    · simp only [evalFinWordMat]
      rw [natMatMul_two_expand, h10 s, he1, hm11, Nat.zero_mul, Nat.zero_add, Nat.one_mul]
    · simp only [evalFinWordMat, evalFinParikh]
      rw [natMatMul_two_expand, ha1, hm01, hm11, Nat.one_mul, Nat.mul_one, Nat.add_comm]

private theorem upperTri2D_mat01_right_or_int (M_mod : Nat)
    (mat : Fin (14 * M_mod) -> Fin 2 -> Fin 2 -> Nat)
    (h10 : ∀ s : Fin (14 * M_mod), mat s ⟨1, by decide⟩ ⟨0, by decide⟩ = 0)
    (E_R : Nat) :
    ∀ w : List (Fin (14 * M_mod)),
      checkWordRightOrIntBool M_mod w = true ->
      (∀ s ∈ w, s.val ≥ 4 * M_mod ->
        mat s ⟨0, by decide⟩ ⟨0, by decide⟩ = 1 ∧ mat s ⟨1, by decide⟩ ⟨1, by decide⟩ = 1) ->
      (∀ s ∈ w, 2 * M_mod ≤ s.val -> s.val < 4 * M_mod -> mat s ⟨1, by decide⟩ ⟨1, by decide⟩ = E_R) ->
      (∀ s ∈ w, 2 * M_mod ≤ s.val -> s.val < 4 * M_mod -> evalFinWordMat (14 * M_mod) 2 mat w ⟨1, by decide⟩ ⟨1, by decide⟩ = E_R) ∧
      (evalFinWordMat (14 * M_mod) 2 mat w ⟨1, by decide⟩ ⟨1, by decide⟩ = 1 ∨
       evalFinWordMat (14 * M_mod) 2 mat w ⟨1, by decide⟩ ⟨1, by decide⟩ = E_R) ∧
      ((∀ s ∈ w, s.val ≥ 4 * M_mod) ->
        evalFinWordMat (14 * M_mod) 2 mat w ⟨0, by decide⟩ ⟨1, by decide⟩ =
          evalFinParikh (14 * M_mod) (fun s => mat s ⟨0, by decide⟩ ⟨1, by decide⟩) w) ∧
      ((∃ r_sym ∈ w, 2 * M_mod ≤ r_sym.val ∧ r_sym.val < 4 * M_mod) ->
        evalFinWordMat (14 * M_mod) 2 mat w ⟨0, by decide⟩ ⟨1, by decide⟩ =
          evalFinParikh (14 * M_mod) (fun s =>
            if s.val < 4 * M_mod then mat s ⟨0, by decide⟩ ⟨1, by decide⟩
            else E_R * mat s ⟨0, by decide⟩ ⟨1, by decide⟩) w)
  | [], _, _, _ => by
    refine ⟨fun _ hs => False.elim (List.not_mem_nil hs), Or.inl rfl, fun _ => rfl, ?_⟩
    rintro ⟨_, hrest⟩
    exact False.elim (List.not_mem_nil hrest.1)
  | [s], hb, hint, hR => by
    have hs2M : s.val ≥ 2 * M_mod := of_decide_eq_true hb
    have hm11_s : evalFinWordMat (14 * M_mod) 2 mat [s] ⟨1, by decide⟩ ⟨1, by decide⟩ =
        mat s ⟨1, by decide⟩ ⟨1, by decide⟩ := by
      simp only [evalFinWordMat]
      rw [natMatMul_two_expand]; simp [natMatId]
    have hm01_s : evalFinWordMat (14 * M_mod) 2 mat [s] ⟨0, by decide⟩ ⟨1, by decide⟩ =
        mat s ⟨0, by decide⟩ ⟨1, by decide⟩ := by
      simp only [evalFinWordMat]
      rw [natMatMul_two_expand]; simp [natMatId]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x hx hx2 hx4
      simp only [List.mem_singleton] at hx; subst hx
      rw [hm11_s]; exact hR x List.mem_cons_self hx2 hx4
    · by_cases hs4 : s.val ≥ 4 * M_mod
      · left; rw [hm11_s]; exact (hint s List.mem_cons_self hs4).2
      · right; rw [hm11_s]; exact hR s List.mem_cons_self hs2M (by omega)
    · intro _; rw [hm01_s]; simp only [evalFinParikh, Nat.add_zero]
    · rintro ⟨r_sym, hrm, _, hr4⟩
      simp only [List.mem_singleton] at hrm; subst hrm
      rw [hm01_s]
      simp only [evalFinParikh, Nat.add_zero, ite_true_of_w10 hr4]
  | s :: s2 :: tl, hb, hint, hR => by
    rcases bool_and_split hb with ⟨hs4_b, hrest⟩
    have hs4 : s.val ≥ 4 * M_mod := of_decide_eq_true hs4_b
    rcases hint s List.mem_cons_self hs4 with ⟨ha1, he1⟩
    rcases upperTri2D_mat01_right_or_int M_mod mat h10 E_R (s2 :: tl) hrest
      (fun x hx => hint x (List.mem_cons_of_mem s hx))
      (fun x hx => hR x (List.mem_cons_of_mem s hx)) with ⟨ih_R11, ih_11or, ih_int, ih_R01⟩
    have hm11_step : evalFinWordMat (14 * M_mod) 2 mat (s :: s2 :: tl) ⟨1, by decide⟩ ⟨1, by decide⟩ =
        evalFinWordMat (14 * M_mod) 2 mat (s2 :: tl) ⟨1, by decide⟩ ⟨1, by decide⟩ := by
      change natMatMul 2 (mat s) (evalFinWordMat (14 * M_mod) 2 mat (s2 :: tl)) ⟨1, by decide⟩ ⟨1, by decide⟩ = _
      rw [natMatMul_two_expand, h10 s, he1, Nat.zero_mul, Nat.zero_add, Nat.one_mul]
    have hm01_step : evalFinWordMat (14 * M_mod) 2 mat (s :: s2 :: tl) ⟨0, by decide⟩ ⟨1, by decide⟩ =
        evalFinWordMat (14 * M_mod) 2 mat (s2 :: tl) ⟨0, by decide⟩ ⟨1, by decide⟩ +
          mat s ⟨0, by decide⟩ ⟨1, by decide⟩ *
            evalFinWordMat (14 * M_mod) 2 mat (s2 :: tl) ⟨1, by decide⟩ ⟨1, by decide⟩ := by
      change natMatMul 2 (mat s) (evalFinWordMat (14 * M_mod) 2 mat (s2 :: tl)) ⟨0, by decide⟩ ⟨1, by decide⟩ = _
      rw [natMatMul_two_expand, ha1, Nat.one_mul]
    refine ⟨?_, hm11_step ▸ ih_11or, ?_, ?_⟩
    · intro x hx hx2 hx4
      cases hx with
      | head => omega
      | tail _ htl => rw [hm11_step]; exact ih_R11 x htl hx2 hx4
    · intro hall4
      have htl4 : ∀ x ∈ s2 :: tl, x.val ≥ 4 * M_mod :=
        fun x hx => hall4 x (List.mem_cons_of_mem s hx)
      have hm11_1 : evalFinWordMat (14 * M_mod) 2 mat (s2 :: tl) ⟨1, by decide⟩ ⟨1, by decide⟩ = 1 :=
        (upperTri2D_mat01_all_int (14 * M_mod) mat h10 (s2 :: tl)
          (fun x hx => hint x (List.mem_cons_of_mem s hx) (htl4 x hx))).2.1
      rw [hm01_step, ih_int htl4, hm11_1, Nat.mul_one]
      change _ = mat s ⟨0, by decide⟩ ⟨1, by decide⟩ +
        evalFinParikh (14 * M_mod) (fun x => mat x ⟨0, by decide⟩ ⟨1, by decide⟩) (s2 :: tl)
      omega
    · rintro ⟨r_sym, hrm, hr2, hr4⟩
      have hrm_tl : r_sym ∈ s2 :: tl := by
        cases hrm with
        | head => omega
        | tail _ htl => exact htl
      have hm11_E : evalFinWordMat (14 * M_mod) 2 mat (s2 :: tl) ⟨1, by decide⟩ ⟨1, by decide⟩ = E_R :=
        ih_R11 r_sym hrm_tl hr2 hr4
      rw [hm01_step, ih_R01 ⟨r_sym, hrm_tl, hr2, hr4⟩, hm11_E]
      have hnot4 : ¬ (s.val < 4 * M_mod) := by omega
      change _ = (if s.val < 4 * M_mod then _ else E_R * mat s ⟨0, by decide⟩ ⟨1, by decide⟩) +
        evalFinParikh (14 * M_mod) _ (s2 :: tl)
      rw [ite_false_of_w10 hnot4, Nat.mul_comm (mat s _ _) E_R, Nat.add_comm]

-- Helper: filter rules by positive multiplicity (`u > 0`) for sub-core syzygy certificates:
def filterRulesByPosMults {α : Type} : List α -> List Nat -> List α
  | [], _ => []
  | _, [] => []
  | _ :: rs, 0 :: ms => filterRulesByPosMults rs ms
  | r :: rs, (_ + 1) :: ms => r :: filterRulesByPosMults rs ms

def filterPosMults : List Nat -> List Nat
  | [] => []
  | 0 :: ms => filterPosMults ms
  | (u + 1) :: ms => (u + 1) :: filterPosMults ms

private theorem mem_of_mem_filterRulesByPosMults {α : Type} :
    ∀ (rs : List α) (ms : List Nat) (r : α),
      r ∈ filterRulesByPosMults rs ms -> r ∈ rs
  | [], _, _, hr => by cases hr
  | _ :: _, [], _, hr => by cases hr
  | r0 :: rs, 0 :: ms, r, hr =>
    List.mem_cons_of_mem r0 (mem_of_mem_filterRulesByPosMults rs ms r hr)
  | r0 :: rs, (_ + 1) :: ms, r, hr => by
    cases hr with
    | head => exact List.Mem.head _
    | tail _ htl => exact List.mem_cons_of_mem r0 (mem_of_mem_filterRulesByPosMults rs ms r htl)

-- Check that every `.R` symbol (`2*M ≤ s < 4*M`) in `rules` lies in `{2*M, 3*M}` and `allGe4MBool` matches:
def checkOnlyR0SymsBool (M : Nat) : List (List (Fin (14 * M)) × List (Fin (14 * M))) -> Bool
  | [] => true
  | (l, r) :: rs =>
    let okSym : Fin (14 * M) -> Bool := fun s =>
      if 2 * M ≤ s.val ∧ s.val < 4 * M then decide (s.val = 2 * M ∨ s.val = 3 * M) else true
    l.all okSym && r.all okSym && decide (allGe4MBool M l = allGe4MBool M r) &&
      checkOnlyR0SymsBool M rs

private theorem checkOnlyR0SymsBool_sound (M : Nat) :
    ∀ (rules : List (List (Fin (14 * M)) × List (Fin (14 * M)))),
      checkOnlyR0SymsBool M rules = true ->
      ∀ r ∈ rules,
        allGe4MBool M r.1 = allGe4MBool M r.2 ∧
        ∀ s : Fin (14 * M), (s ∈ r.1 ∨ s ∈ r.2) ->
          2 * M ≤ s.val -> s.val < 4 * M -> (s.val = 2 * M ∨ s.val = 3 * M)
  | [], _, _, hr => by cases hr
  | (l0, r0) :: rs, hb, r, hr => by
    unfold checkOnlyR0SymsBool at hb
    rcases bool_and_split hb with ⟨hlr_eq, hrs⟩
    rcases bool_and_split hlr_eq with ⟨hlr, hge_eq⟩
    rcases bool_and_split hlr with ⟨hl_all, hr_all⟩
    cases hr with
    | head =>
      refine ⟨of_decide_eq_true hge_eq, ?_⟩
      intro s hmem h2 h4
      have hok : (if 2 * M ≤ s.val ∧ s.val < 4 * M then decide (s.val = 2 * M ∨ s.val = 3 * M) else true) = true := by
        rcases hmem with hl | hr_m
        · exact List.all_eq_true.mp hl_all s hl
        · exact List.all_eq_true.mp hr_all s hr_m
      rw [ite_true_of_w10 ⟨h2, h4⟩] at hok
      exact of_decide_eq_true hok
    | tail _ htl =>
      exact checkOnlyR0SymsBool_sound M rs hrs r htl

-- Check that active interior symbols of `fullCore` also appear in `subCore`:
def checkSameActiveIntBool (M : Nat)
    (fullCore subCore : List (List (Fin (14 * M)) × List (Fin (14 * M)))) : Bool :=
  let rec loop : Nat -> Bool
    | 0 => true
    | k + 1 =>
      (if k ≥ 4 * M && symAppearsInRulesBool (14 * M) k fullCore then
         symAppearsInRulesBool (14 * M) k subCore
       else true) && loop k
  loop (14 * M)

private theorem checkSameActiveIntBool_sound (M : Nat)
    (fullCore subCore : List (List (Fin (14 * M)) × List (Fin (14 * M))))
    (hb : checkSameActiveIntBool M fullCore subCore = true) :
    ∀ s : Fin (14 * M), s.val ≥ 4 * M ->
      symAppearsInRulesBool (14 * M) s.val fullCore = true ->
      symAppearsInRulesBool (14 * M) s.val subCore = true := by
  unfold checkSameActiveIntBool at hb
  have hloop : ∀ n : Nat, checkSameActiveIntBool.loop M fullCore subCore n = true ->
      ∀ k : Nat, k < n -> k ≥ 4 * M ->
        symAppearsInRulesBool (14 * M) k fullCore = true ->
        symAppearsInRulesBool (14 * M) k subCore = true := by
    intro n; induction n with
    | zero => intros _ _ hk; omega
    | succ n' ih =>
      intro hn k hk hge4 hact
      unfold checkSameActiveIntBool.loop at hn
      rcases bool_and_split hn with ⟨hcur, hprev⟩
      by_cases hkn : k = n'
      · subst hkn
        rw [show (decide (k ≥ 4 * M) && symAppearsInRulesBool (14 * M) k fullCore) = true by
              rw [decide_eq_true hge4, hact]; rfl] at hcur
        exact hcur
      · exact ih hprev k (by omega) hge4 hact
  intro s hs4 hact
  exact hloop (14 * M) hb s.val s.isLt hs4 hact

-- Check rule length `|lhs| = 2` and `1 ≤ |rhs| ≤ 3` across all rules:
def checkAllRulesLen2To123Bool {N : Nat} : List (List (Fin N) × List (Fin N)) -> Bool
  | [] => true
  | (l, r) :: rs =>
    decide (l.length = 2 ∧ 1 ≤ r.length ∧ r.length ≤ 3) && checkAllRulesLen2To123Bool rs

private theorem checkAllRulesLen2To123Bool_sound {N : Nat} :
    ∀ rs : List (List (Fin N) × List (Fin N)),
      checkAllRulesLen2To123Bool rs = true ->
      ∀ r ∈ rs, r.1.length = 2 ∧ 1 ≤ r.2.length ∧ r.2.length ≤ 3
  | [], _, _, hr => by cases hr
  | r0 :: rs, hb, r, hr => by
    rcases bool_and_split hb with ⟨h0, hrs⟩
    cases hr with
    | head => exact of_decide_eq_true h0
    | tail _ htl => exact checkAllRulesLen2To123Bool_sound rs hrs r htl

-- Unit-diagonal `[[1, b_s], [c_s, 1]]` 2-letter exact & 1/2/3-letter lower-bound Parikh lemma:
private theorem unitDiag2D_mat_parikh_bounds (N : Nat)
    (M : Fin N -> Fin 2 -> Fin 2 -> Nat)
    (hdiag1 : ∀ s : Fin N, M s ⟨0, by decide⟩ ⟨0, by decide⟩ = 1 ∧ M s ⟨1, by decide⟩ ⟨1, by decide⟩ = 1) :
    (∀ (w : List (Fin N)), w.length = 2 ->
      evalFinWordMat N 2 M w ⟨0, by decide⟩ ⟨1, by decide⟩ =
        evalFinParikh N (fun s => M s ⟨0, by decide⟩ ⟨1, by decide⟩) w ∧
      evalFinWordMat N 2 M w ⟨1, by decide⟩ ⟨0, by decide⟩ =
        evalFinParikh N (fun s => M s ⟨1, by decide⟩ ⟨0, by decide⟩) w) ∧
    (∀ (w : List (Fin N)), 1 ≤ w.length -> w.length ≤ 3 ->
      evalFinWordMat N 2 M w ⟨0, by decide⟩ ⟨1, by decide⟩ ≥
        evalFinParikh N (fun s => M s ⟨0, by decide⟩ ⟨1, by decide⟩) w ∧
      evalFinWordMat N 2 M w ⟨1, by decide⟩ ⟨0, by decide⟩ ≥
        evalFinParikh N (fun s => M s ⟨1, by decide⟩ ⟨0, by decide⟩) w) := by
  have h1 : ∀ x : Fin N,
      evalFinWordMat N 2 M [x] fin2_0 fin2_0 = 1 ∧
      evalFinWordMat N 2 M [x] fin2_1 fin2_1 = 1 ∧
      evalFinWordMat N 2 M [x] fin2_0 fin2_1 = M x fin2_0 fin2_1 ∧
      evalFinWordMat N 2 M [x] fin2_1 fin2_0 = M x fin2_1 fin2_0 := by
    intro x
    rcases hdiag1 x with ⟨hx0, hx1⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · change natMatMul 2 (M x) (natMatId 2) fin2_0 fin2_0 = 1
      rw [natMatMul_two_expand, hx0]; rfl
    · change natMatMul 2 (M x) (natMatId 2) fin2_1 fin2_1 = 1
      rw [natMatMul_two_expand, hx1]; rfl
    · change natMatMul 2 (M x) (natMatId 2) fin2_0 fin2_1 = _
      rw [natMatMul_two_expand]
      change M x fin2_0 fin2_0 * 0 + M x fin2_0 fin2_1 * 1 = _
      omega
    · change natMatMul 2 (M x) (natMatId 2) fin2_1 fin2_0 = _
      rw [natMatMul_two_expand]
      change M x fin2_1 fin2_0 * 1 + M x fin2_1 fin2_1 * 0 = _
      omega
  have h2 : ∀ x y : Fin N,
      evalFinWordMat N 2 M [x, y] fin2_0 fin2_0 = 1 + M x fin2_0 fin2_1 * M y fin2_1 fin2_0 ∧
      evalFinWordMat N 2 M [x, y] fin2_1 fin2_1 = 1 + M x fin2_1 fin2_0 * M y fin2_0 fin2_1 ∧
      evalFinWordMat N 2 M [x, y] fin2_0 fin2_1 = M x fin2_0 fin2_1 + M y fin2_0 fin2_1 ∧
      evalFinWordMat N 2 M [x, y] fin2_1 fin2_0 = M x fin2_1 fin2_0 + M y fin2_1 fin2_0 := by
    intro x y
    rcases hdiag1 x with ⟨hx0, hx1⟩
    rcases h1 y with ⟨hy00, hy11, hy01, hy10⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · change natMatMul 2 (M x) (evalFinWordMat N 2 M [y]) fin2_0 fin2_0 = _
      rw [natMatMul_two_expand, hx0, hy00, hy10, Nat.one_mul]
    · change natMatMul 2 (M x) (evalFinWordMat N 2 M [y]) fin2_1 fin2_1 = _
      rw [natMatMul_two_expand, hx1, hy11, hy01, Nat.one_mul, Nat.add_comm]
    · change natMatMul 2 (M x) (evalFinWordMat N 2 M [y]) fin2_0 fin2_1 = _
      rw [natMatMul_two_expand, hx0, hy01, hy11, Nat.one_mul, Nat.mul_one, Nat.add_comm]
    · change natMatMul 2 (M x) (evalFinWordMat N 2 M [y]) fin2_1 fin2_0 = _
      rw [natMatMul_two_expand, hx1, hy10, hy00, Nat.one_mul, Nat.mul_one]
  refine ⟨?_, ?_⟩
  · intro w hw2
    cases w with
    | nil => simp at hw2
    | cons x tl1 =>
      cases tl1 with
      | nil => simp at hw2
      | cons y tl2 =>
        cases tl2 with
        | cons _ _ => simp at hw2
        | nil =>
          rcases h2 x y with ⟨_, _, h01, h10⟩
          simp only [evalFinParikh, Nat.add_zero]
          exact ⟨h01, h10⟩
  · intro w hge1 hle3
    cases w with
    | nil => simp at hge1
    | cons x tl1 =>
      cases tl1 with
      | nil =>
        rcases h1 x with ⟨_, _, h01, h10⟩
        simp only [evalFinParikh, Nat.add_zero]
        exact ⟨Nat.le_of_eq h01.symm, Nat.le_of_eq h10.symm⟩
      | cons y tl2 =>
        cases tl2 with
        | nil =>
          rcases h2 x y with ⟨_, _, h01, h10⟩
          simp only [evalFinParikh, Nat.add_zero]
          exact ⟨Nat.le_of_eq h01.symm, Nat.le_of_eq h10.symm⟩
        | cons z tl3 =>
          cases tl3 with
          | cons _ _ => simp at hle3
          | nil =>
            rcases hdiag1 x with ⟨hx0, hx1⟩
            rcases h2 y z with ⟨hyz00, hyz11, hyz01, hyz10⟩
            have h3_01 : evalFinWordMat N 2 M [x, y, z] fin2_0 fin2_1 =
                M y fin2_0 fin2_1 + M z fin2_0 fin2_1 +
                  M x fin2_0 fin2_1 * (1 + M y fin2_1 fin2_0 * M z fin2_0 fin2_1) := by
              change natMatMul 2 (M x) (evalFinWordMat N 2 M [y, z]) fin2_0 fin2_1 = _
              rw [natMatMul_two_expand, hx0, hyz01, hyz11, Nat.one_mul]
            have h3_10 : evalFinWordMat N 2 M [x, y, z] fin2_1 fin2_0 =
                M x fin2_1 fin2_0 * (1 + M y fin2_0 fin2_1 * M z fin2_1 fin2_0) +
                  (M y fin2_1 fin2_0 + M z fin2_1 fin2_0) := by
              change natMatMul 2 (M x) (evalFinWordMat N 2 M [y, z]) fin2_1 fin2_0 = _
              rw [natMatMul_two_expand, hx1, hyz00, hyz10, Nat.one_mul]
            rw [Nat.mul_add (M x fin2_0 fin2_1), Nat.mul_one] at h3_01
            rw [Nat.mul_add (M x fin2_1 fin2_0), Nat.mul_one] at h3_10
            simp only [evalFinParikh, Nat.add_zero]
            change evalFinWordMat N 2 M [x, y, z] fin2_0 fin2_1 ≥
                M x fin2_0 fin2_1 + (M y fin2_0 fin2_1 + M z fin2_0 fin2_1) ∧
              evalFinWordMat N 2 M [x, y, z] fin2_1 fin2_0 ≥
                M x fin2_1 fin2_0 + (M y fin2_1 fin2_0 + M z fin2_1 fin2_0)
            rw [h3_01, h3_10]
            omega

-- Evaluate `evalFinWordVec N 2 M v w` when all interior symbols `s.val ≥ 4 * M_mod` in `w` have `M s = I_2`:
private theorem idInt2D_vec_eval (M_mod : Nat)
    (mat : Fin (14 * M_mod) -> Fin 2 -> Fin 2 -> Nat)
    (v : Fin (14 * M_mod) -> Fin 2 -> Nat) :
    (∀ w : List (Fin (14 * M_mod)),
      (∀ s ∈ w, ∀ i j : Fin 2, mat s i j = natMatId 2 i j) ->
      ∀ i : Fin 2, evalFinWordVec (14 * M_mod) 2 mat v w i = evalFinParikh (14 * M_mod) (fun s => v s i) w) ∧
    (∀ w : List (Fin (14 * M_mod)),
      checkWordRightOrIntBool M_mod w = true ->
      (∀ s ∈ w, s.val ≥ 4 * M_mod -> ∀ i j : Fin 2, mat s i j = natMatId 2 i j) ->
      ∀ i : Fin 2, evalFinWordVec (14 * M_mod) 2 mat v w i = evalFinParikh (14 * M_mod) (fun s => v s i) w) := by
  have hint_fn : ∀ w : List (Fin (14 * M_mod)),
      (∀ s ∈ w, ∀ i j : Fin 2, mat s i j = natMatId 2 i j) ->
      ∀ i : Fin 2, evalFinWordVec (14 * M_mod) 2 mat v w i = evalFinParikh (14 * M_mod) (fun s => v s i) w := by
    intro w; induction w with
    | nil => intro _ _; rfl
    | cons s rest ih =>
      intro hall i
      have hs_id := hall s List.mem_cons_self
      have ih_r := ih (fun x hx => hall x (List.mem_cons_of_mem s hx))
      simp only [evalFinWordVec, evalFinParikh]
      rw [natMatVec_two_expand, hs_id i ⟨0, by decide⟩, hs_id i ⟨1, by decide⟩,
          ih_r ⟨0, by decide⟩, ih_r ⟨1, by decide⟩]
      rcases (by have := i.isLt; omega : i.val = 0 ∨ i.val = 1) with hi | hi
      · rw [show i = ⟨0, by decide⟩ from Fin.ext hi]; simp [natMatId]
      · rw [show i = ⟨1, by decide⟩ from Fin.ext hi]; simp [natMatId]
  refine ⟨hint_fn, ?_⟩
  intro w; induction w with
  | nil => intros; rfl
  | cons s rest ih =>
    cases rest with
    | nil =>
      intros _ _ i
      simp only [evalFinWordVec, evalFinParikh]
      rw [natMatVec_two_expand]; simp
    | cons s2 tl =>
      intro hb hint i
      rcases bool_and_split hb with ⟨hs4_b, hrest⟩
      have hs_id := hint s List.mem_cons_self (of_decide_eq_true hs4_b)
      have ih_r := ih hrest (fun x hx => hint x (List.mem_cons_of_mem s hx))
      change v s i + natMatVec 2 (mat s) (evalFinWordVec (14 * M_mod) 2 mat v (s2 :: tl)) i =
        v s i + evalFinParikh (14 * M_mod) (fun x => v x i) (s2 :: tl)
      rw [natMatVec_two_expand, hs_id i ⟨0, by decide⟩, hs_id i ⟨1, by decide⟩,
          ih_r ⟨0, by decide⟩, ih_r ⟨1, by decide⟩]
      rcases (by have := i.isLt; omega : i.val = 0 ∨ i.val = 1) with hi | hi
      · rw [show i = ⟨0, by decide⟩ from Fin.ext hi]; simp [natMatId]
      · rw [show i = ⟨1, by decide⟩ from Fin.ext hi]; simp [natMatId]

-- Certificates for `c39` (`M = 3`) and `c78` (`M = 6`) in Wave 13:
def syzC39R0Only : List Nat :=
  [2, 4, 2, 4, 24, 2, 2, 2, 14, 10, 14, 10, 12, 2, 10, 2, 10, 2, 10, 10,
   20, 20, 14, 2, 2, 9, 7, 0, 0, 12, 0, 0, 6, 0, 0, 6, 0, 0, 6]

def posMultsC39R0Only : List Nat :=
  [2, 4, 0, 4, 24, 2, 0, 41, 27, 13, 29, 13, 14, 4, 0, 11, 12, 2, 15, 19,
   7, 9, 27, 3, 2, 9, 7, 0, 0, 12, 0, 0, 6, 0, 0, 6, 0, 0, 6]

def negMultsC39R0Only : List Nat :=
  [0, 0, 37, 0, 0, 0, 11, 0, 0, 0, 0, 0, 0, 0, 15, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def syzC39L0Only : List Nat :=
  [4, 8, 0, 0, 26, 4, 0, 0, 14, 10, 14, 10, 12, 2, 10, 2, 10, 2, 10, 10,
   20, 20, 14, 2, 2, 9, 7, 4, 4, 4, 2, 2, 2, 2, 2, 2, 2, 2, 2]

def syzC39L1Only : List Nat :=
  [0, 0, 4, 8, 0, 0, 26, 4, 14, 10, 14, 10, 12, 2, 10, 2, 10, 2, 10, 10,
   20, 20, 14, 2, 2, 9, 7, 4, 4, 4, 2, 2, 2, 2, 2, 2, 2, 2, 2]

def syzC78R0Only : List Nat :=
  [1, 2, 1, 2, 1, 2, 1, 2, 63, 1, 2, 1, 1, 1, 2, 1, 7, 10, 32, 1,
   39, 1, 3, 7, 2, 30, 8, 33, 1, 1, 1, 2, 6, 8, 1, 5, 1, 4, 8, 37,
   7, 36, 44, 1, 1, 29, 34, 1, 1, 14, 29, 44, 16, 1,
   0, 0, 0, 0, 0, 26, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 20]

def posMultsC78R0Only : List Nat :=
  [2, 4, 2, 4, 0, 0, 2, 73, 126, 2, 4, 2, 59, 21, 0, 52, 25, 0, 73, 3,
   101, 4, 7, 0, 3, 67, 0, 66, 53, 0, 0, 0, 21, 21, 0, 39, 2, 0, 60, 74,
   0, 57, 91, 16, 8, 46, 72, 0, 2, 28, 58, 88, 32, 2,
   0, 0, 0, 0, 0, 52, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 40]

def negMultsC78R0Only : List Nat :=
  [0, 0, 0, 0, 78, 76, 0, 0, 0, 0, 0, 0, 0, 0, 57, 0, 0, 18, 0, 0,
   0, 0, 0, 27, 0, 0, 40, 0, 0, 47, 4, 40, 0, 0, 44, 0, 0, 23, 0, 0,
   24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def syzC78L0Only : List Nat :=
  [2, 4, 2, 4, 0, 0, 0, 0, 64, 2, 4, 2, 0, 0, 0, 0, 7, 10, 32, 1,
   39, 1, 3, 7, 2, 30, 8, 33, 1, 1, 1, 2, 6, 8, 1, 5, 1, 4, 8, 37,
   7, 36, 44, 1, 1, 29, 34, 1, 1, 14, 29, 44, 16, 1,
   2, 2, 2, 2, 2, 16, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 15]

def syzC78L1Only : List Nat :=
  [0, 0, 0, 0, 2, 4, 2, 4, 0, 0, 0, 0, 64, 2, 4, 2, 7, 10, 32, 1,
   39, 1, 3, 7, 2, 30, 8, 33, 1, 1, 1, 2, 6, 8, 1, 5, 1, 4, 8, 37,
   7, 36, 44, 1, 1, 29, 34, 1, 1, 14, 29, 44, 16, 1,
   2, 2, 2, 2, 2, 16, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 15]

def checkNoL1RulesBool (M : Nat) : List (List (Fin (14 * M)) × List (Fin (14 * M))) -> Bool
  | [] => true
  | (l, r) :: rs =>
    l.all (fun s => decide (¬ (M ≤ s.val ∧ s.val < 2 * M))) &&
    r.all (fun s => decide (¬ (M ≤ s.val ∧ s.val < 2 * M))) &&
    checkNoL1RulesBool M rs

def checkNoL0RulesBool (M : Nat) : List (List (Fin (14 * M)) × List (Fin (14 * M))) -> Bool
  | [] => true
  | (l, r) :: rs =>
    l.all (fun s => decide (¬ (s.val < M))) &&
    r.all (fun s => decide (¬ (s.val < M))) &&
    checkNoL0RulesBool M rs

private theorem checkNoL1RulesBool_sound (M : Nat) :
    ∀ rs : List (List (Fin (14 * M)) × List (Fin (14 * M))),
      checkNoL1RulesBool M rs = true ->
      ∀ r ∈ rs, ∀ s : Fin (14 * M), (s ∈ r.1 ∨ s ∈ r.2) -> ¬ (M ≤ s.val ∧ s.val < 2 * M)
  | [], _, _, hr => by cases hr
  | (l0, r0) :: rs, hb, r, hr => by
    unfold checkNoL1RulesBool at hb
    rcases bool_and_split hb with ⟨hlr, hrs⟩
    rcases bool_and_split hlr with ⟨hl_a, hr_a⟩
    cases hr with
    | head =>
      intro s hmem
      rcases hmem with hl | hr_m
      · exact of_decide_eq_true (List.all_eq_true.mp hl_a s hl)
      · exact of_decide_eq_true (List.all_eq_true.mp hr_a s hr_m)
    | tail _ htl => exact checkNoL1RulesBool_sound M rs hrs r htl

private theorem checkNoL0RulesBool_sound (M : Nat) :
    ∀ rs : List (List (Fin (14 * M)) × List (Fin (14 * M))),
      checkNoL0RulesBool M rs = true ->
      ∀ r ∈ rs, ∀ s : Fin (14 * M), (s ∈ r.1 ∨ s ∈ r.2) -> ¬ (s.val < M)
  | [], _, _, hr => by cases hr
  | (l0, r0) :: rs, hb, r, hr => by
    unfold checkNoL0RulesBool at hb
    rcases bool_and_split hb with ⟨hlr, hrs⟩
    rcases bool_and_split hlr with ⟨hl_a, hr_a⟩
    cases hr with
    | head =>
      intro s hmem
      rcases hmem with hl | hr_m
      · exact of_decide_eq_true (List.all_eq_true.mp hl_a s hl)
      · exact of_decide_eq_true (List.all_eq_true.mp hr_a s hr_m)
    | tail _ htl => exact checkNoL0RulesBool_sound M rs hrs r htl

def hasTwoToTwoRuleBool (N : Nat) (a b c d : Nat) : List (List (Fin N) × List (Fin N)) -> Bool
  | [] => false
  | (l, r) :: rs =>
    decide (l.map Fin.val = [a, b] ∧ r.map Fin.val = [c, d]) || hasTwoToTwoRuleBool N a b c d rs

private theorem hasTwoToTwoRuleBool_sound (N : Nat) (a b c d : Fin N) :
    ∀ rs : List (List (Fin N) × List (Fin N)),
      hasTwoToTwoRuleBool N a.val b.val c.val d.val rs = true -> ([a, b], [c, d]) ∈ rs
  | [], h => by cases h
  | (l, r) :: rs, h => by
    unfold hasTwoToTwoRuleBool at h
    rcases bool_or_split_w13 h with h0 | htl
    · rcases of_decide_eq_true h0 with ⟨hl, hr⟩
      have hl_eq : l = [a, b] := by
        cases l with
        | nil => simp at hl
        | cons x1 t1 =>
          cases t1 with
          | nil => simp at hl
          | cons x2 t2 =>
            cases t2 with
            | nil =>
              simp only [List.map_cons, List.map_nil, List.cons.injEq] at hl
              rw [Fin.ext hl.1, Fin.ext hl.2.1]
            | cons _ _ => simp at hl
      have hr_eq : r = [c, d] := by
        cases r with
        | nil => simp at hr
        | cons y1 t1 =>
          cases t1 with
          | nil => simp at hr
          | cons y2 t2 =>
            cases t2 with
            | nil =>
              simp only [List.map_cons, List.map_nil, List.cons.injEq] at hr
              rw [Fin.ext hr.1, Fin.ext hr.2.1]
            | cons _ _ => simp at hr
      rw [hl_eq, hr_eq]; exact List.Mem.head _
    · exact List.mem_cons_of_mem _ (hasTwoToTwoRuleBool_sound N a b c d rs htl)

-- Master 2D collapse theorem for positive-diagonal upper-triangular & unit-diagonal full-rank towers:
private theorem twosided_w13_2d_collapse_master (M : Nat)
    (core : List (List (Fin (14 * M)) × List (Fin (14 * M))))
    (syz posMults negMults syzR0 posR0 negR0 syzL0 syzL1 : List Nat)
    (l0Ref l1Ref r0Ref r1Ref r9L r9R : Fin (14 * M))
    (hsyz : checkPositiveParikhSyzygyFastBool (14 * M) core syz = true)
    (hann : checkSignedInteriorAnnihilationBool M core posMults negMults = true)
    (hshape : checkAllRulesShapeBool M core = true)
    (hlen123 : checkAllRulesLen2To123Bool core = true)
    (hne_core : core ≠ [])
    (hsyzR0 : checkPositiveParikhSyzygyFastBool (14 * M)
      (filterRulesByPosMults core syzR0) (filterPosMults syzR0) = true)
    (hannR0 : checkSignedInteriorAnnihilationBool M
      (filterRulesByPosMults core syzR0)
      (filterRulesByPosMults posR0 syzR0) (filterRulesByPosMults negR0 syzR0) = true)
    (honlyR0 : checkOnlyR0SymsBool M (filterRulesByPosMults core syzR0) = true)
    (hsameIntR0 : checkSameActiveIntBool M core (filterRulesByPosMults core syzR0) = true)
    (hr9_mem : ([r9L, r0Ref], [r9R, r1Ref]) ∈ core)
    (hr_vals : r0Ref.val = 2 * M ∧ r1Ref.val = 3 * M ∧ r9L.val ≥ 4 * M ∧ r9R.val ≥ 4 * M)
    (hsyzL0 : checkPositiveParikhSyzygyFastBool (14 * M)
      (filterRulesByPosMults core syzL0) (filterPosMults syzL0) = true)
    (hnoL1 : checkNoL1RulesBool M (filterRulesByPosMults core syzL0) = true)
    (hsyzL1 : checkPositiveParikhSyzygyFastBool (14 * M)
      (filterRulesByPosMults core syzL1) (filterPosMults syzL1) = true)
    (hnoL0 : checkNoL0RulesBool M (filterRulesByPosMults core syzL1) = true)
    (hcoverL01 : ∀ r ∈ core,
      r ∈ filterRulesByPosMults core syzL0 ∨ r ∈ filterRulesByPosMults core syzL1)
    (hL_eq_prod : ∀ m : Fin (14 * M) -> Nat,
      (∀ r ∈ core, prodFinWordW13 (14 * M) m r.1 = prodFinWordW13 (14 * M) m r.2) ->
      (∀ s : Fin (14 * M), s.val ≥ 4 * M -> symAppearsInRulesBool (14 * M) s.val core = true -> m s = 1) ->
      ∀ (r : List (Fin (14 * M)) × List (Fin (14 * M))), r ∈ core ->
        (∀ s : Fin (14 * M), (s ∈ r.1 ∨ s ∈ r.2) -> s.val < M -> m s = m l0Ref) ∧
        (∀ s : Fin (14 * M), (s ∈ r.1 ∨ s ∈ r.2) -> M ≤ s.val -> s.val < 2 * M -> m s = m l1Ref))
    (hL_eq_par : ∀ b : Fin (14 * M) -> Nat,
      (∀ r ∈ core, evalFinParikh (14 * M) b r.1 = evalFinParikh (14 * M) b r.2) ->
      (∀ s : Fin (14 * M), s.val ≥ 4 * M -> symAppearsInRulesBool (14 * M) s.val core = true -> b s = 0) ->
      ∀ (r : List (Fin (14 * M)) × List (Fin (14 * M))), r ∈ core ->
        (∀ s : Fin (14 * M), (s ∈ r.1 ∨ s ∈ r.2) -> s.val < M -> b s = b l0Ref) ∧
        (∀ s : Fin (14 * M), (s ∈ r.1 ∨ s ∈ r.2) -> M ≤ s.val -> s.val < 2 * M -> b s = b l1Ref)) :
    (∀ k : Nat, ¬ GenOmegaPosDiagUpperTri2DMatTower (14 * M) k core) ∧
    (∀ k : Nat, ¬ GenOmegaUnitDiagFullRank2DMatTower (14 * M) k core) := by
  let N := 14 * M
  let z0 : Fin 2 := ⟨0, by decide⟩
  let z1 : Fin 2 := ⟨1, by decide⟩
  rcases syzygy_forces_parikh_and_prod_eq_w13 N core syz hsyz with ⟨hpar_eq_all, hprod_eq_all⟩
  rcases signed_annihilation_forces_interior_zero_and_one_w13 M core posMults negMults hann with
    ⟨hpar_int_zero, hprod_int_one⟩
  have hshape_all := checkAllRulesShapeBool_sound M core hshape
  have hlen_all := checkAllRulesLen2To123Bool_sound core hlen123
  -- Helper: any 1D-affine `(a, u)` (`a s ≥ 1`) weakly orienting `core` has `= ` on all rules AND `u s = 0` on active interior:
  have haff_eq_and_int0 : ∀ (a u : Fin N -> Nat),
      (∀ s : Fin N, a s ≥ 1) ->
      (∀ r ∈ core,
        (evalFinAffine1D N a u r.1).1 ≥ (evalFinAffine1D N a u r.2).1 ∧
        (evalFinAffine1D N a u r.1).2 ≥ (evalFinAffine1D N a u r.2).2) ->
      (∀ r ∈ core, (evalFinAffine1D N a u r.1).2 = (evalFinAffine1D N a u r.2).2) ∧
      (∀ s : Fin N, s.val ≥ 4 * M -> symAppearsInRulesBool N s.val core = true -> u s = 0) := by
    intro a u ha1 hweak
    have hprod_eq : ∀ r ∈ core, prodFinWordW13 N a r.1 = prodFinWordW13 N a r.2 :=
      hprod_eq_all a ha1 (fun r hr => by
        rw [← evalFinAffine1D_fst_w13 N a u r.1, ← evalFinAffine1D_fst_w13 N a u r.2]
        exact (hweak r hr).1)
    have hint1 : ∀ s : Fin N, s.val ≥ 4 * M -> symAppearsInRulesBool N s.val core = true -> a s = 1 :=
      hprod_int_one a ha1 hprod_eq
    have hL_c := hL_eq_prod a hprod_eq hint1
    let A0 := a l0Ref
    let A1 := a l1Ref
    have hA0_pos : A0 ≥ 1 := ha1 l0Ref
    have hA1_pos : A1 ≥ 1 := ha1 l1Ref
    let wt : Fin N -> Nat := fun s =>
      if s.val < M then A1 * u s
      else if s.val < 2 * M then A0 * u s
      else (A0 * A1) * u s
    have hrel : ∀ r ∈ core,
        evalFinParikh N wt r.1 ≥ evalFinParikh N wt r.2 ∧
        (evalFinParikh N wt r.1 = evalFinParikh N wt r.2 ->
          (evalFinAffine1D N a u r.1).2 = (evalFinAffine1D N a u r.2).2) := by
      intro r hr
      have hsh := hshape_all r hr
      unfold checkRuleTwoSidedShapeBool at hsh
      rcases bool_or_split_w13 hsh with hL_case | hR_case
      · cases hl1 : r.1 with
        | nil => rw [hl1] at hL_case; simp at hL_case
        | cons l0 lint =>
          cases hr1 : r.2 with
          | nil => rw [hl1, hr1] at hL_case; simp at hL_case
          | cons r0 rint =>
            rw [hl1, hr1] at hL_case; dsimp only at hL_case
            have hw2 := (hweak r hr).2; rw [hl1, hr1] at hw2
            rcases bool_or_split_w13 hL_case with hq0 | hq1
            · rcases bool_and_split hq0 with ⟨hb0, hrint_b⟩
              rcases bool_and_split hb0 with ⟨hlr_b, hlint_b⟩
              rcases of_decide_eq_true hlr_b with ⟨hl0_lt, hr0_lt⟩
              have hl0_a : a l0 = A0 := (hL_c r hr).1 l0 (Or.inl (hl1 ▸ List.Mem.head _)) hl0_lt
              have hr0_a : a r0 = A0 := (hL_c r hr).1 r0 (Or.inr (hr1 ▸ List.Mem.head _)) hr0_lt
              have hli1 : ∀ x ∈ lint, a x = 1 := fun x hx =>
                hint1 x (allGe4MBool_sound M lint hlint_b x hx)
                  (symAppearsInRulesBool_of_mem_lhs N x core r hr (hl1 ▸ List.mem_cons_of_mem l0 hx))
              have hri1 : ∀ x ∈ rint, a x = 1 := fun x hx =>
                hint1 x (allGe4MBool_sound M rint hrint_b x hx)
                  (symAppearsInRulesBool_of_mem_rhs N x core r hr (hr1 ▸ List.mem_cons_of_mem r0 hx))
              have hal : (evalFinAffine1D N a u (l0 :: lint)).2 = u l0 + A0 * evalFinParikh N u lint := by
                dsimp only [evalFinAffine1D]; rw [hl0_a, evalFinAffine1D_all_int_w13 M a u lint hli1]
              have har : (evalFinAffine1D N a u (r0 :: rint)).2 = u r0 + A0 * evalFinParikh N u rint := by
                dsimp only [evalFinAffine1D]; rw [hr0_a, evalFinAffine1D_all_int_w13 M a u rint hri1]
              have hpl : evalFinParikh N wt (l0 :: lint) = A1 * (u l0 + A0 * evalFinParikh N u lint) := by
                simp only [evalFinParikh]
                have hwl0 : wt l0 = A1 * u l0 := by dsimp [wt]; rw [ite_true_of_w10 hl0_lt]
                have hwli : evalFinParikh N wt lint = (A0 * A1) * evalFinParikh N u lint :=
                  parikh_int_scale_w13 M (A0 * A1) u wt lint (fun x hx => by
                    have hx_ge := allGe4MBool_sound M lint hlint_b x hx
                    dsimp [wt]; rw [ite_false_of_w10 (by omega), ite_false_of_w10 (by omega)])
                rw [hwl0, hwli, Nat.mul_add, ← Nat.mul_assoc A1 A0, Nat.mul_comm A1 A0]
              have hpr : evalFinParikh N wt (r0 :: rint) = A1 * (u r0 + A0 * evalFinParikh N u rint) := by
                simp only [evalFinParikh]
                have hwr0 : wt r0 = A1 * u r0 := by dsimp [wt]; rw [ite_true_of_w10 hr0_lt]
                have hwri : evalFinParikh N wt rint = (A0 * A1) * evalFinParikh N u rint :=
                  parikh_int_scale_w13 M (A0 * A1) u wt rint (fun x hx => by
                    have hx_ge := allGe4MBool_sound M rint hrint_b x hx
                    dsimp [wt]; rw [ite_false_of_w10 (by omega), ite_false_of_w10 (by omega)])
                rw [hwr0, hwri, Nat.mul_add, ← Nat.mul_assoc A1 A0, Nat.mul_comm A1 A0]
              rw [hpl, hpr]; rw [hal, har] at hw2 ⊢
              exact ⟨Nat.mul_le_mul_left A1 hw2, fun heq => Nat.eq_of_mul_eq_mul_left (by omega) heq⟩
            · rcases bool_and_split hq1 with ⟨hb1, hrint_b⟩
              rcases bool_and_split hb1 with ⟨hlr_b, hlint_b⟩
              rcases of_decide_eq_true hlr_b with ⟨hl0_ge, hl0_lt, hr0_ge, hr0_lt⟩
              have hl0_a : a l0 = A1 := (hL_c r hr).2 l0 (Or.inl (hl1 ▸ List.Mem.head _)) hl0_ge hl0_lt
              have hr0_a : a r0 = A1 := (hL_c r hr).2 r0 (Or.inr (hr1 ▸ List.Mem.head _)) hr0_ge hr0_lt
              have hli1 : ∀ x ∈ lint, a x = 1 := fun x hx =>
                hint1 x (allGe4MBool_sound M lint hlint_b x hx)
                  (symAppearsInRulesBool_of_mem_lhs N x core r hr (hl1 ▸ List.mem_cons_of_mem l0 hx))
              have hri1 : ∀ x ∈ rint, a x = 1 := fun x hx =>
                hint1 x (allGe4MBool_sound M rint hrint_b x hx)
                  (symAppearsInRulesBool_of_mem_rhs N x core r hr (hr1 ▸ List.mem_cons_of_mem r0 hx))
              have hal : (evalFinAffine1D N a u (l0 :: lint)).2 = u l0 + A1 * evalFinParikh N u lint := by
                dsimp only [evalFinAffine1D]; rw [hl0_a, evalFinAffine1D_all_int_w13 M a u lint hli1]
              have har : (evalFinAffine1D N a u (r0 :: rint)).2 = u r0 + A1 * evalFinParikh N u rint := by
                dsimp only [evalFinAffine1D]; rw [hr0_a, evalFinAffine1D_all_int_w13 M a u rint hri1]
              have hpl : evalFinParikh N wt (l0 :: lint) = A0 * (u l0 + A1 * evalFinParikh N u lint) := by
                simp only [evalFinParikh]
                have hwl0 : wt l0 = A0 * u l0 := by
                  dsimp [wt]; rw [ite_false_of_w10 (by omega), ite_true_of_w10 hl0_lt]
                have hwli : evalFinParikh N wt lint = (A0 * A1) * evalFinParikh N u lint :=
                  parikh_int_scale_w13 M (A0 * A1) u wt lint (fun x hx => by
                    have hx_ge := allGe4MBool_sound M lint hlint_b x hx
                    dsimp [wt]; rw [ite_false_of_w10 (by omega), ite_false_of_w10 (by omega)])
                rw [hwl0, hwli, Nat.mul_add, ← Nat.mul_assoc A0 A1]
              have hpr : evalFinParikh N wt (r0 :: rint) = A0 * (u r0 + A1 * evalFinParikh N u rint) := by
                simp only [evalFinParikh]
                have hwr0 : wt r0 = A0 * u r0 := by
                  dsimp [wt]; rw [ite_false_of_w10 (by omega), ite_true_of_w10 hr0_lt]
                have hwri : evalFinParikh N wt rint = (A0 * A1) * evalFinParikh N u rint :=
                  parikh_int_scale_w13 M (A0 * A1) u wt rint (fun x hx => by
                    have hx_ge := allGe4MBool_sound M rint hrint_b x hx
                    dsimp [wt]; rw [ite_false_of_w10 (by omega), ite_false_of_w10 (by omega)])
                rw [hwr0, hwri, Nat.mul_add, ← Nat.mul_assoc A0 A1]
              rw [hpl, hpr]; rw [hal, har] at hw2 ⊢
              exact ⟨Nat.mul_le_mul_left A0 hw2, fun heq => Nat.eq_of_mul_eq_mul_left (by omega) heq⟩
      · rcases bool_and_split hR_case with ⟨hl_r, hr_r⟩
        have hw2 := (hweak r hr).2
        have hal := evalFinAffine1D_right_or_int_w13 M a u r.1 hl_r
          (fun x hx hx_ge => hint1 x hx_ge (symAppearsInRulesBool_of_mem_lhs N x core r hr hx))
        have har := evalFinAffine1D_right_or_int_w13 M a u r.2 hr_r
          (fun x hx hx_ge => hint1 x hx_ge (symAppearsInRulesBool_of_mem_rhs N x core r hr hx))
        have hge2M_of : ∀ w : List (Fin N), checkWordRightOrIntBool M w = true -> ∀ x ∈ w, x.val ≥ 2 * M := by
          intro w; induction w with
          | nil => intro _ _ hx; cases hx
          | cons s rest ih =>
            cases rest with
            | nil => intro hb x hx; simp only [List.mem_singleton] at hx; subst hx; exact of_decide_eq_true hb
            | cons s2 tl =>
              intro hb x hx; rcases bool_and_split hb with ⟨hs_ge, htl⟩
              cases hx with
              | head => have := of_decide_eq_true hs_ge; omega
              | tail _ hm => exact ih htl x hm
        have hpl : evalFinParikh N wt r.1 = (A0 * A1) * evalFinParikh N u r.1 :=
          parikh_int_scale_w13 M (A0 * A1) u wt r.1 (fun x hx => by
            have := hge2M_of r.1 hl_r x hx
            dsimp [wt]; rw [ite_false_of_w10 (by omega), ite_false_of_w10 (by omega)])
        have hpr : evalFinParikh N wt r.2 = (A0 * A1) * evalFinParikh N u r.2 :=
          parikh_int_scale_w13 M (A0 * A1) u wt r.2 (fun x hx => by
            have := hge2M_of r.2 hr_r x hx
            dsimp [wt]; rw [ite_false_of_w10 (by omega), ite_false_of_w10 (by omega)])
        rw [hpl, hpr]; rw [hal, har] at hw2 ⊢
        have ha01_pos : A0 * A1 ≥ 1 := Nat.mul_le_mul hA0_pos hA1_pos
        exact ⟨Nat.mul_le_mul_left (A0 * A1) hw2, fun heq => Nat.eq_of_mul_eq_mul_left (by omega) heq⟩
    have hpeq := hpar_eq_all wt (fun r hr => (hrel r hr).1)
    refine ⟨fun r hr => (hrel r hr).2 (hpeq r hr), ?_⟩
    intro s hs4 hs_act
    have hwt0 := hpar_int_zero wt hpeq s hs4 hs_act
    dsimp [wt] at hwt0
    rw [ite_false_of_w10 (by omega), ite_false_of_w10 (by omega)] at hwt0
    have ha01_pos : A0 * A1 ≥ 1 := Nat.mul_le_mul hA0_pos hA1_pos
    rcases Nat.mul_eq_zero.mp hwt0 with h0 | hu0 <;> omega
  -- Part 1: Any positive-diagonal upper-triangular `(mat, v)` weakly orienting `core` has `= ` on row 0:
  have hposDiag_no_strict : ∀ (mat : Fin N -> Fin 2 -> Fin 2 -> Nat) (v : Fin N -> Fin 2 -> Nat),
      (∀ s : Fin N, mat s z0 z0 ≥ 1 ∧ mat s z1 z1 ≥ 1) ->
      (∀ s : Fin N, mat s z1 z0 = 0) ->
      (∀ r ∈ core,
        (∀ i j : Fin 2, evalFinWordMat N 2 mat r.1 i j ≥ evalFinWordMat N 2 mat r.2 i j) ∧
        (∀ i : Fin 2, evalFinWordVec N 2 mat v r.1 i ≥ evalFinWordVec N 2 mat v r.2 i)) ->
      ∀ r ∈ core, evalFinWordVec N 2 mat v r.1 z0 = evalFinWordVec N 2 mat v r.2 z0 := by
    intro mat v hpos h10 hweak
    let a : Fin N -> Nat := fun s => mat s z0 z0
    let e : Fin N -> Nat := fun s => mat s z1 z1
    let b : Fin N -> Nat := fun s => mat s z0 z1
    -- `a s = 1` and `e s = 1` on active interior, and `v s z1 = 0` on active interior (from row 1 affine!):
    have hmat00_prod : ∀ w : List (Fin N), evalFinWordMat N 2 mat w z0 z0 = prodFinWordW13 N a w := by
      intro w; induction w with
      | nil => rfl
      | cons s rest ih =>
        simp only [evalFinWordMat, prodFinWordW13]
        rw [natMatMul_two_expand, (upperTri2D_bot_eq_affine1d N mat v h10 rest).1,
            Nat.mul_zero, Nat.add_zero, ih]
    have ha_peq : ∀ r ∈ core, prodFinWordW13 N a r.1 = prodFinWordW13 N a r.2 :=
      hprod_eq_all a (fun s => (hpos s).1) (fun r hr => by
        rw [← hmat00_prod r.1, ← hmat00_prod r.2]; exact (hweak r hr).1 z0 z0)
    have ha_int1 : ∀ s : Fin N, s.val ≥ 4 * M -> symAppearsInRulesBool N s.val core = true -> a s = 1 :=
      hprod_int_one a (fun s => (hpos s).1) ha_peq
    have ha_L := hL_eq_prod a ha_peq ha_int1
    have he_peq : ∀ r ∈ core, prodFinWordW13 N e r.1 = prodFinWordW13 N e r.2 :=
      hprod_eq_all e (fun s => (hpos s).2) (fun r hr => by
        rcases upperTri2D_bot_eq_affine1d N mat v h10 r.1 with ⟨_, hm1, _⟩
        rcases upperTri2D_bot_eq_affine1d N mat v h10 r.2 with ⟨_, hm2, _⟩
        rw [← evalFinAffine1D_fst_w13 N e (fun s => v s z1) r.1,
            ← evalFinAffine1D_fst_w13 N e (fun s => v s z1) r.2, ← hm1, ← hm2]
        exact (hweak r hr).1 z1 z1)
    have he_int1 : ∀ s : Fin N, s.val ≥ 4 * M -> symAppearsInRulesBool N s.val core = true -> e s = 1 :=
      hprod_int_one e (fun s => (hpos s).2) he_peq
    rcases haff_eq_and_int0 e (fun s => v s z1) (fun s => (hpos s).2) (fun r hr => by
      rcases upperTri2D_bot_eq_affine1d N mat v h10 r.1 with ⟨_, hm1, hv1⟩
      rcases upperTri2D_bot_eq_affine1d N mat v h10 r.2 with ⟨_, hm2, hv2⟩
      rw [← hm1, ← hm2, ← hv1, ← hv2]
      exact ⟨(hweak r hr).1 z1 z1, (hweak r hr).2 z1⟩) with ⟨_, hv1_int0⟩
    -- From `hr9_mem : ([r9L, r0Ref], [r9R, r1Ref]) ∈ core`, deduce `e r0Ref = e r1Ref`:
    have he_r01 : e r0Ref = e r1Ref := by
      have hp9 := he_peq _ hr9_mem
      have h9L1 : e r9L = 1 := he_int1 r9L hr_vals.2.2.1
        (symAppearsInRulesBool_of_mem_lhs N r9L core _ hr9_mem (List.Mem.head _))
      have h9R1 : e r9R = 1 := he_int1 r9R hr_vals.2.2.2
        (symAppearsInRulesBool_of_mem_rhs N r9R core _ hr9_mem (List.Mem.head _))
      dsimp only [prodFinWordW13] at hp9
      rw [h9L1, h9R1] at hp9
      omega
    -- Now prove `b s = 0` on all active interior symbols using `subCoreR0`:
    let subR0 := filterRulesByPosMults core syzR0
    rcases syzygy_forces_parikh_and_prod_eq_w13 N subR0 (filterPosMults syzR0) hsyzR0 with ⟨hparR0_eq, _⟩
    rcases signed_annihilation_forces_interior_zero_and_one_w13 M subR0
      (filterRulesByPosMults posR0 syzR0) (filterRulesByPosMults negR0 syzR0) hannR0 with ⟨hparR0_int0, _⟩
    let A0 := a l0Ref
    let A1 := a l1Ref
    let E_R := e r0Ref
    have hA0_pos : A0 ≥ 1 := (hpos l0Ref).1
    have hA1_pos : A1 ≥ 1 := (hpos l1Ref).1
    have hER_pos : E_R ≥ 1 := (hpos r0Ref).2
    let wt_b : Fin N -> Nat := fun s =>
      if s.val < M then (A1 * E_R) * b s
      else if s.val < 2 * M then (A0 * E_R) * b s
      else if s.val < 4 * M then (A0 * A1) * b s
      else (A0 * A1 * E_R) * b s
    have hwt_b_ge : ∀ r ∈ subR0, evalFinParikh N wt_b r.1 ≥ evalFinParikh N wt_b r.2 := by
      intro r hr_sub
      have hr : r ∈ core := mem_of_mem_filterRulesByPosMults core syzR0 r hr_sub
      have hsh := hshape_all r hr
      unfold checkRuleTwoSidedShapeBool at hsh
      have hwm := (hweak r hr).1 z0 z1
      rcases bool_or_split_w13 hsh with hL_c | hR_c
      · cases hl1 : r.1 with
        | nil => rw [hl1] at hL_c; simp at hL_c
        | cons l0 lint =>
          cases hr1 : r.2 with
          | nil => rw [hl1, hr1] at hL_c; simp at hL_c
          | cons r0 rint =>
            rw [hl1, hr1] at hL_c; dsimp only at hL_c
            rw [hl1, hr1] at hwm
            rcases bool_or_split_w13 hL_c with hq0 | hq1
            · rcases bool_and_split hq0 with ⟨hb0, hrint_b⟩
              rcases bool_and_split hb0 with ⟨hlr_b, hlint_b⟩
              rcases of_decide_eq_true hlr_b with ⟨hl0_lt, hr0_lt⟩
              have hl0_a : a l0 = A0 := (ha_L r hr).1 l0 (Or.inl (hl1 ▸ List.Mem.head _)) hl0_lt
              have hr0_a : a r0 = A0 := (ha_L r hr).1 r0 (Or.inr (hr1 ▸ List.Mem.head _)) hr0_lt
              rcases upperTri2D_mat01_all_int N mat h10 lint (fun x hx => by
                have hx4 := allGe4MBool_sound M lint hlint_b x hx
                have hxa := symAppearsInRulesBool_of_mem_lhs N x core r hr (hl1 ▸ List.mem_cons_of_mem l0 hx)
                exact ⟨ha_int1 x hx4 hxa, he_int1 x hx4 hxa⟩) with ⟨_, hli11, hli01⟩
              rcases upperTri2D_mat01_all_int N mat h10 rint (fun x hx => by
                have hx4 := allGe4MBool_sound M rint hrint_b x hx
                have hxa := symAppearsInRulesBool_of_mem_rhs N x core r hr (hr1 ▸ List.mem_cons_of_mem r0 hx)
                exact ⟨ha_int1 x hx4 hxa, he_int1 x hx4 hxa⟩) with ⟨_, hri11, hri01⟩
              have hml : evalFinWordMat N 2 mat (l0 :: lint) z0 z1 = b l0 + A0 * evalFinParikh N b lint := by
                simp only [evalFinWordMat]
                rw [natMatMul_two_expand, hli01, hli11, Nat.mul_one]
                change a l0 * evalFinParikh N b lint + b l0 = _; rw [hl0_a, Nat.add_comm]
              have hmr : evalFinWordMat N 2 mat (r0 :: rint) z0 z1 = b r0 + A0 * evalFinParikh N b rint := by
                simp only [evalFinWordMat]
                rw [natMatMul_two_expand, hri01, hri11, Nat.mul_one]
                change a r0 * evalFinParikh N b rint + b r0 = _; rw [hr0_a, Nat.add_comm]
              rw [hml, hmr] at hwm
              have hpl : evalFinParikh N wt_b (l0 :: lint) = (A1 * E_R) * (b l0 + A0 * evalFinParikh N b lint) := by
                simp only [evalFinParikh]
                have h0 : wt_b l0 = (A1 * E_R) * b l0 := by dsimp [wt_b]; rw [ite_true_of_w10 hl0_lt]
                have hi : evalFinParikh N wt_b lint = (A0 * A1 * E_R) * evalFinParikh N b lint :=
                  parikh_int_scale_w13 M (A0 * A1 * E_R) b wt_b lint (fun x hx => by
                    have hx4 := allGe4MBool_sound M lint hlint_b x hx
                    dsimp [wt_b]
                    rw [ite_false_of_w10 (by omega), ite_false_of_w10 (by omega), ite_false_of_w10 (by omega)])
                rw [h0, hi, Nat.mul_add]; congr 1; ac_rfl
              have hpr : evalFinParikh N wt_b (r0 :: rint) = (A1 * E_R) * (b r0 + A0 * evalFinParikh N b rint) := by
                simp only [evalFinParikh]
                have h0 : wt_b r0 = (A1 * E_R) * b r0 := by dsimp [wt_b]; rw [ite_true_of_w10 hr0_lt]
                have hi : evalFinParikh N wt_b rint = (A0 * A1 * E_R) * evalFinParikh N b rint :=
                  parikh_int_scale_w13 M (A0 * A1 * E_R) b wt_b rint (fun x hx => by
                    have hx4 := allGe4MBool_sound M rint hrint_b x hx
                    dsimp [wt_b]
                    rw [ite_false_of_w10 (by omega), ite_false_of_w10 (by omega), ite_false_of_w10 (by omega)])
                rw [h0, hi, Nat.mul_add]; congr 1; ac_rfl
              rw [hpl, hpr]; exact Nat.mul_le_mul_left (A1 * E_R) hwm
            · rcases bool_and_split hq1 with ⟨hb1, hrint_b⟩
              rcases bool_and_split hb1 with ⟨hlr_b, hlint_b⟩
              rcases of_decide_eq_true hlr_b with ⟨hl0_ge, hl0_lt, hr0_ge, hr0_lt⟩
              have hl0_a : a l0 = A1 := (ha_L r hr).2 l0 (Or.inl (hl1 ▸ List.Mem.head _)) hl0_ge hl0_lt
              have hr0_a : a r0 = A1 := (ha_L r hr).2 r0 (Or.inr (hr1 ▸ List.Mem.head _)) hr0_ge hr0_lt
              rcases upperTri2D_mat01_all_int N mat h10 lint (fun x hx => by
                have hx4 := allGe4MBool_sound M lint hlint_b x hx
                have hxa := symAppearsInRulesBool_of_mem_lhs N x core r hr (hl1 ▸ List.mem_cons_of_mem l0 hx)
                exact ⟨ha_int1 x hx4 hxa, he_int1 x hx4 hxa⟩) with ⟨_, hli11, hli01⟩
              rcases upperTri2D_mat01_all_int N mat h10 rint (fun x hx => by
                have hx4 := allGe4MBool_sound M rint hrint_b x hx
                have hxa := symAppearsInRulesBool_of_mem_rhs N x core r hr (hr1 ▸ List.mem_cons_of_mem r0 hx)
                exact ⟨ha_int1 x hx4 hxa, he_int1 x hx4 hxa⟩) with ⟨_, hri11, hri01⟩
              have hml : evalFinWordMat N 2 mat (l0 :: lint) z0 z1 = b l0 + A1 * evalFinParikh N b lint := by
                simp only [evalFinWordMat]
                rw [natMatMul_two_expand, hli01, hli11, Nat.mul_one]
                change a l0 * evalFinParikh N b lint + b l0 = _; rw [hl0_a, Nat.add_comm]
              have hmr : evalFinWordMat N 2 mat (r0 :: rint) z0 z1 = b r0 + A1 * evalFinParikh N b rint := by
                simp only [evalFinWordMat]
                rw [natMatMul_two_expand, hri01, hri11, Nat.mul_one]
                change a r0 * evalFinParikh N b rint + b r0 = _; rw [hr0_a, Nat.add_comm]
              rw [hml, hmr] at hwm
              have hpl : evalFinParikh N wt_b (l0 :: lint) = (A0 * E_R) * (b l0 + A1 * evalFinParikh N b lint) := by
                simp only [evalFinParikh]
                have h0 : wt_b l0 = (A0 * E_R) * b l0 := by
                  dsimp [wt_b]; rw [ite_false_of_w10 (by omega), ite_true_of_w10 hl0_lt]
                have hi : evalFinParikh N wt_b lint = (A0 * A1 * E_R) * evalFinParikh N b lint :=
                  parikh_int_scale_w13 M (A0 * A1 * E_R) b wt_b lint (fun x hx => by
                    have hx4 := allGe4MBool_sound M lint hlint_b x hx
                    dsimp [wt_b]
                    rw [ite_false_of_w10 (by omega), ite_false_of_w10 (by omega), ite_false_of_w10 (by omega)])
                rw [h0, hi, Nat.mul_add]; congr 1; ac_rfl
              have hpr : evalFinParikh N wt_b (r0 :: rint) = (A0 * E_R) * (b r0 + A1 * evalFinParikh N b rint) := by
                simp only [evalFinParikh]
                have h0 : wt_b r0 = (A0 * E_R) * b r0 := by
                  dsimp [wt_b]; rw [ite_false_of_w10 (by omega), ite_true_of_w10 hr0_lt]
                have hi : evalFinParikh N wt_b rint = (A0 * A1 * E_R) * evalFinParikh N b rint :=
                  parikh_int_scale_w13 M (A0 * A1 * E_R) b wt_b rint (fun x hx => by
                    have hx4 := allGe4MBool_sound M rint hrint_b x hx
                    dsimp [wt_b]
                    rw [ite_false_of_w10 (by omega), ite_false_of_w10 (by omega), ite_false_of_w10 (by omega)])
                rw [h0, hi, Nat.mul_add]; congr 1; ac_rfl
              rw [hpl, hpr]; exact Nat.mul_le_mul_left (A0 * E_R) hwm
      · rcases bool_and_split hR_c with ⟨hl_r, hr_r⟩
        -- Check whether `r.1` has an `.R` symbol (`2*M .. 4*M - 1`) or is purely `≥ 4*M`:
        rcases checkOnlyR0SymsBool_sound M subR0 honlyR0 r hr_sub with ⟨hge4_eq, honly_s⟩
        have he_on_sub : ∀ s : Fin N, (s ∈ r.1 ∨ s ∈ r.2) -> 2 * M ≤ s.val -> s.val < 4 * M -> e s = E_R := by
          intro s hmem h2 h4
          rcases honly_s s hmem h2 h4 with hs0 | hs1
          · rw [show s = r0Ref from Fin.ext (hs0.trans hr_vals.1.symm)]
          · rw [show s = r1Ref from Fin.ext (hs1.trans hr_vals.2.1.symm), ← he_r01]
        have hallGe4_complete : ∀ w : List (Fin N), (∀ x ∈ w, x.val ≥ 4 * M) -> allGe4MBool M w = true := by
          intro w; induction w with
          | nil => intro _; rfl
          | cons x rest ih =>
            intro hall; unfold allGe4MBool
            rw [decide_eq_true (hall x List.mem_cons_self),
                ih (fun y hy => hall y (List.mem_cons_of_mem x hy))]; rfl
        have hlast_R_iff : ∀ w : List (Fin N), checkWordRightOrIntBool M w = true ->
            (∀ x ∈ w, x.val ≥ 4 * M) ∨ (∃ x ∈ w, 2 * M ≤ x.val ∧ x.val < 4 * M) := by
          intro w; induction w with
          | nil => intro _; exact Or.inl (fun _ hx => by cases hx)
          | cons x rest ih =>
            cases rest with
            | nil =>
              intro hbw; have hx2 : x.val ≥ 2 * M := of_decide_eq_true hbw
              by_cases hx4 : x.val ≥ 4 * M
              · exact Or.inl (fun y hy => by simp at hy; subst hy; exact hx4)
              · exact Or.inr ⟨x, List.Mem.head _, hx2, by omega⟩
            | cons x2 tl =>
              intro hbw; rcases bool_and_split hbw with ⟨hx4_b, htl⟩
              rcases ih htl with hall | ⟨y, hy, hy2, hy4⟩
              · exact Or.inl (fun z hz => by
                  cases hz with
                  | head => exact of_decide_eq_true hx4_b
                  | tail _ hm => exact hall z hm)
              · exact Or.inr ⟨y, List.mem_cons_of_mem x hy, hy2, hy4⟩
        rcases upperTri2D_mat01_right_or_int M mat h10 E_R r.1 hl_r
          (fun x hx hx4 => by
            have hxa := symAppearsInRulesBool_of_mem_lhs N x core r hr hx
            exact ⟨ha_int1 x hx4 hxa, he_int1 x hx4 hxa⟩)
          (fun x hx => he_on_sub x (Or.inl hx)) with ⟨_, _, hl_int, hl_R⟩
        rcases upperTri2D_mat01_right_or_int M mat h10 E_R r.2 hr_r
          (fun x hx hx4 => by
            have hxa := symAppearsInRulesBool_of_mem_rhs N x core r hr hx
            exact ⟨ha_int1 x hx4 hxa, he_int1 x hx4 hxa⟩)
          (fun x hx => he_on_sub x (Or.inr hx)) with ⟨_, _, hr_int, hr_R⟩
        by_cases hall_l4 : ∀ x ∈ r.1, x.val ≥ 4 * M
        · have hb_l4 : allGe4MBool M r.1 = true := hallGe4_complete r.1 hall_l4
          have hall_r4 : ∀ x ∈ r.2, x.val ≥ 4 * M :=
            allGe4MBool_sound M r.2 (hge4_eq.symm.trans hb_l4)
          rw [hl_int hall_l4, hr_int hall_r4] at hwm
          have hpl := parikh_int_scale_w13 M (A0 * A1 * E_R) b wt_b r.1 (fun x hx => by
            have := hall_l4 x hx
            dsimp [wt_b]; rw [ite_false_of_w10 (by omega), ite_false_of_w10 (by omega), ite_false_of_w10 (by omega)])
          have hpr := parikh_int_scale_w13 M (A0 * A1 * E_R) b wt_b r.2 (fun x hx => by
            have := hall_r4 x hx
            dsimp [wt_b]; rw [ite_false_of_w10 (by omega), ite_false_of_w10 (by omega), ite_false_of_w10 (by omega)])
          rw [hpl, hpr]; exact Nat.mul_le_mul_left (A0 * A1 * E_R) hwm
        · rcases hlast_R_iff r.1 hl_r with hl4_all | hR1
          · exact False.elim (hall_l4 hl4_all)
          · rcases hlast_R_iff r.2 hr_r with hr4_all | hR2
            · exfalso
              exact hall_l4 (allGe4MBool_sound M r.1 (hge4_eq.trans (hallGe4_complete r.2 hr4_all)))
            · rw [hl_R hR1, hr_R hR2] at hwm
              let bR : Fin N -> Nat := fun s => if s.val < 4 * M then b s else E_R * b s
              have hge2M_w : ∀ w : List (Fin N), checkWordRightOrIntBool M w = true -> ∀ x ∈ w, x.val ≥ 2 * M := by
                intro w; induction w with
                | nil => intro _ _ hx; cases hx
                | cons x rest ih =>
                  cases rest with
                  | nil => intro hbw y hy; simp at hy; subst hy; exact of_decide_eq_true hbw
                  | cons x2 tl =>
                    intro hbw y hy; rcases bool_and_split hbw with ⟨hx4, htl⟩
                    cases hy with
                    | head => have := of_decide_eq_true hx4; omega
                    | tail _ hm => exact ih htl y hm
              have hpl := parikh_int_scale_w13 M (A0 * A1) bR wt_b r.1 (fun x hx => by
                have hx2 := hge2M_w r.1 hl_r x hx
                dsimp [wt_b, bR]
                rw [ite_false_of_w10 (by omega), ite_false_of_w10 (by omega)]
                by_cases hx4 : x.val < 4 * M
                · rw [ite_true_of_w10 hx4, ite_true_of_w10 hx4]
                · rw [ite_false_of_w10 hx4, ite_false_of_w10 hx4, Nat.mul_assoc (A0 * A1) E_R])
              have hpr := parikh_int_scale_w13 M (A0 * A1) bR wt_b r.2 (fun x hx => by
                have hx2 := hge2M_w r.2 hr_r x hx
                dsimp [wt_b, bR]
                rw [ite_false_of_w10 (by omega), ite_false_of_w10 (by omega)]
                by_cases hx4 : x.val < 4 * M
                · rw [ite_true_of_w10 hx4, ite_true_of_w10 hx4]
                · rw [ite_false_of_w10 hx4, ite_false_of_w10 hx4, Nat.mul_assoc (A0 * A1) E_R])
              rw [hpl, hpr]; exact Nat.mul_le_mul_left (A0 * A1) hwm
    have hb_int0 : ∀ s : Fin N, s.val ≥ 4 * M -> symAppearsInRulesBool N s.val core = true -> b s = 0 := by
      intro s hs4 hs_act
      have hs_sub := checkSameActiveIntBool_sound M core subR0 hsameIntR0 s hs4 hs_act
      have hwt0 := hparR0_int0 wt_b (hparR0_eq wt_b hwt_b_ge) s hs4 hs_sub
      dsimp [wt_b] at hwt0
      rw [ite_false_of_w10 (by omega), ite_false_of_w10 (by omega), ite_false_of_w10 (by omega)] at hwt0
      have hprod_pos : A0 * A1 * E_R ≥ 1 :=
        Nat.mul_le_mul (Nat.mul_le_mul hA0_pos hA1_pos) hER_pos
      rcases Nat.mul_eq_zero.mp hwt0 with h0 | hb0 <;> omega
    -- With `a s = 1`, `b s = 0`, `v s z1 = 0` on all active interior symbols, `evalFinWordVec _ z0`
    -- equals `(evalFinAffine1D N a (fun s => v s z0) _).2` on every rule of `core`!
    have hvec0_eq_aff : ∀ r ∈ core,
        evalFinWordVec N 2 mat v r.1 z0 = (evalFinAffine1D N a (fun s => v s z0) r.1).2 ∧
        evalFinWordVec N 2 mat v r.2 z0 = (evalFinAffine1D N a (fun s => v s z0) r.2).2 := by
      have hint_vec : ∀ w : List (Fin N),
          (∀ x ∈ w, a x = 1 ∧ b x = 0 ∧ v x z1 = 0) ->
          evalFinWordVec N 2 mat v w z0 = (evalFinAffine1D N a (fun s => v s z0) w).2 ∧
          evalFinWordVec N 2 mat v w z1 = 0 := by
        intro w; induction w with
        | nil => intro _; exact ⟨rfl, rfl⟩
        | cons x rest ih =>
          intro hall
          rcases hall x List.mem_cons_self with ⟨_, _, hvx1⟩
          rcases ih (fun y hy => hall y (List.mem_cons_of_mem x hy)) with ⟨ih0, ih1⟩
          refine ⟨?_, ?_⟩
          · simp only [evalFinWordVec, evalFinAffine1D]
            rw [natMatVec_two_expand]
            change v x z0 + (a x * evalFinWordVec N 2 mat v rest z0 + b x * evalFinWordVec N 2 mat v rest z1) =
              v x z0 + a x * (evalFinAffine1D N a (fun s => v s z0) rest).2
            rw [ih0, ih1, Nat.mul_zero, Nat.add_zero]
          · simp only [evalFinWordVec]
            rw [natMatVec_two_expand, h10 x, hvx1, ih1, Nat.zero_mul, Nat.mul_zero]
      have hr_vec : ∀ w : List (Fin N), checkWordRightOrIntBool M w = true ->
          (∀ x ∈ w, x.val ≥ 4 * M -> a x = 1 ∧ b x = 0) ->
          evalFinWordVec N 2 mat v w z0 = (evalFinAffine1D N a (fun s => v s z0) w).2 := by
        intro w; induction w with
        | nil => intros; rfl
        | cons x rest ih =>
          cases rest with
          | nil =>
            intros
            simp only [evalFinWordVec, evalFinAffine1D]
            rw [natMatVec_two_expand]; simp
          | cons x2 tl =>
            intro hbw hint_ab
            rcases bool_and_split hbw with ⟨hx4_b, htl⟩
            rcases hint_ab x List.mem_cons_self (of_decide_eq_true hx4_b) with ⟨_, hbx⟩
            have ih0 := ih htl (fun y hy => hint_ab y (List.mem_cons_of_mem x hy))
            change v x z0 + natMatVec 2 (mat x) (evalFinWordVec N 2 mat v (x2 :: tl)) z0 =
              v x z0 + a x * (evalFinAffine1D N a (fun s => v s z0) (x2 :: tl)).2
            rw [natMatVec_two_expand]
            change v x z0 + (a x * evalFinWordVec N 2 mat v (x2 :: tl) z0 +
              b x * evalFinWordVec N 2 mat v (x2 :: tl) z1) = _
            rw [hbx, Nat.zero_mul, Nat.add_zero, ih0]
      intro r hr
      have hsh := hshape_all r hr
      unfold checkRuleTwoSidedShapeBool at hsh
      rcases bool_or_split_w13 hsh with hL_c | hR_c
      · cases hl1 : r.1 with
        | nil => rw [hl1] at hL_c; simp at hL_c
        | cons l0 lint =>
          cases hr1 : r.2 with
          | nil => rw [hl1, hr1] at hL_c; simp at hL_c
          | cons r0 rint =>
            rw [hl1, hr1] at hL_c; dsimp only at hL_c
            have hli_b : allGe4MBool M lint = true := by
              rcases bool_or_split_w13 hL_c with h0 | h1c
              · exact (bool_and_split (bool_and_split h0).1).2
              · exact (bool_and_split (bool_and_split h1c).1).2
            have hri_b : allGe4MBool M rint = true := by
              rcases bool_or_split_w13 hL_c with h0 | h1c
              · exact (bool_and_split h0).2
              · exact (bool_and_split h1c).2
            rcases hint_vec lint (fun x hx => by
              have hx4 := allGe4MBool_sound M lint hli_b x hx
              have hxa := symAppearsInRulesBool_of_mem_lhs N x core r hr (hl1 ▸ List.mem_cons_of_mem l0 hx)
              exact ⟨ha_int1 x hx4 hxa, hb_int0 x hx4 hxa, hv1_int0 x hx4 hxa⟩) with ⟨hl0_e, hl1_e⟩
            rcases hint_vec rint (fun x hx => by
              have hx4 := allGe4MBool_sound M rint hri_b x hx
              have hxa := symAppearsInRulesBool_of_mem_rhs N x core r hr (hr1 ▸ List.mem_cons_of_mem r0 hx)
              exact ⟨ha_int1 x hx4 hxa, hb_int0 x hx4 hxa, hv1_int0 x hx4 hxa⟩) with ⟨hr0_e, hr1_e⟩
            refine ⟨?_, ?_⟩
            · simp only [evalFinWordVec, evalFinAffine1D]
              rw [natMatVec_two_expand, hl0_e, hl1_e, Nat.mul_zero, Nat.add_zero]
            · simp only [evalFinWordVec, evalFinAffine1D]
              rw [natMatVec_two_expand, hr0_e, hr1_e, Nat.mul_zero, Nat.add_zero]
      · rcases bool_and_split hR_c with ⟨hl_r, hr_r⟩
        refine ⟨hr_vec r.1 hl_r (fun x hx hx4 => by
                  have hxa := symAppearsInRulesBool_of_mem_lhs N x core r hr hx
                  exact ⟨ha_int1 x hx4 hxa, hb_int0 x hx4 hxa⟩),
                hr_vec r.2 hr_r (fun x hx hx4 => by
                  have hxa := symAppearsInRulesBool_of_mem_rhs N x core r hr hx
                  exact ⟨ha_int1 x hx4 hxa, hb_int0 x hx4 hxa⟩)⟩
    rcases haff_eq_and_int0 a (fun s => v s z0) (fun s => (hpos s).1) (fun r hr => by
      rcases hvec0_eq_aff r hr with ⟨hlv, hrv⟩
      rw [← hlv, ← hrv, evalFinAffine1D_fst_w13 N a (fun s => v s z0) r.1,
          evalFinAffine1D_fst_w13 N a (fun s => v s z0) r.2, ← hmat00_prod r.1, ← hmat00_prod r.2]
      exact ⟨(hweak r hr).1 z0 z0, (hweak r hr).2 z0⟩) with ⟨heq_aff0, _⟩
    intro r hr
    rcases hvec0_eq_aff r hr with ⟨hlv, hrv⟩
    rw [hlv, hrv]
    exact heq_aff0 r hr
  -- Part 2: Any unit-diagonal `[[1, b_s], [c_s, 1]]` `(mat, v)` weakly orienting `core` has `= ` on row 0:
  have hunitDiag_no_strict : ∀ (mat : Fin N -> Fin 2 -> Fin 2 -> Nat) (v : Fin N -> Fin 2 -> Nat),
      (∀ s : Fin N, mat s z0 z0 = 1 ∧ mat s z1 z1 = 1) ->
      (∀ r ∈ core,
        (∀ i j : Fin 2, evalFinWordMat N 2 mat r.1 i j ≥ evalFinWordMat N 2 mat r.2 i j) ∧
        (∀ i : Fin 2, evalFinWordVec N 2 mat v r.1 i ≥ evalFinWordVec N 2 mat v r.2 i)) ->
      ∀ r ∈ core, evalFinWordVec N 2 mat v r.1 z0 = evalFinWordVec N 2 mat v r.2 z0 := by
    intro mat v hdiag1 hweak
    let b : Fin N -> Nat := fun s => mat s z0 z1
    let c : Fin N -> Nat := fun s => mat s z1 z0
    rcases unitDiag2D_mat_parikh_bounds N mat hdiag1 with ⟨hpar2, hpar123⟩
    have hb_ge : ∀ r ∈ core, evalFinParikh N b r.1 ≥ evalFinParikh N b r.2 := by
      intro r hr
      rcases hlen_all r hr with ⟨hl2, hr1, hr3⟩
      have hm01 := (hweak r hr).1 z0 z1
      rw [(hpar2 r.1 hl2).1] at hm01
      exact Nat.le_trans (hpar123 r.2 hr1 hr3).1 hm01
    have hc_ge : ∀ r ∈ core, evalFinParikh N c r.1 ≥ evalFinParikh N c r.2 := by
      intro r hr
      rcases hlen_all r hr with ⟨hl2, hr1, hr3⟩
      have hm10 := (hweak r hr).1 z1 z0
      rw [(hpar2 r.1 hl2).2] at hm10
      exact Nat.le_trans (hpar123 r.2 hr1 hr3).2 hm10
    have hb_eq_all := hpar_eq_all b hb_ge
    have hc_eq_all := hpar_eq_all c hc_ge
    have hb_int0 := hpar_int_zero b hb_eq_all
    have hc_int0 := hpar_int_zero c hc_eq_all
    have hb_L := hL_eq_par b hb_eq_all hb_int0
    have hint_id : ∀ s : Fin N, s.val ≥ 4 * M -> symAppearsInRulesBool N s.val core = true ->
        ∀ i j : Fin 2, mat s i j = natMatId 2 i j := by
      intro s hs4 hsa i j
      rcases (by have := i.isLt; omega : i.val = 0 ∨ i.val = 1) with hi | hi <;>
      rcases (by have := j.isLt; omega : j.val = 0 ∨ j.val = 1) with hj | hj
      · rw [show i = z0 from Fin.ext hi, show j = z0 from Fin.ext hj]; exact (hdiag1 s).1
      · rw [show i = z0 from Fin.ext hi, show j = z1 from Fin.ext hj]; exact hb_int0 s hs4 hsa
      · rw [show i = z1 from Fin.ext hi, show j = z0 from Fin.ext hj]; exact hc_int0 s hs4 hsa
      · rw [show i = z1 from Fin.ext hi, show j = z1 from Fin.ext hj]; exact (hdiag1 s).2
    rcases idInt2D_vec_eval M mat v with ⟨hvec_int, hvec_r⟩
    -- Prove `evalFinWordVec N 2 mat v r.1 z0 = evalFinWordVec N 2 mat v r.2 z0` on `subL0` and `subL1`!
    let B0 := b l0Ref
    let B1 := b l1Ref
    let wt0 : Fin N -> Nat := fun s => if s.val < 2 * M then v s z0 else v s z0 + B0 * v s z1
    let wt1 : Fin N -> Nat := fun s => if s.val < 2 * M then v s z0 else v s z0 + B1 * v s z1
    have hpar_comb : ∀ (B_val : Nat) (wt_c : Fin N -> Nat),
        (∀ s : Fin N, s.val ≥ 2 * M -> wt_c s = v s z0 + B_val * v s z1) ->
        ∀ w : List (Fin N), (∀ s ∈ w, s.val ≥ 2 * M) ->
          evalFinParikh N wt_c w =
            evalFinParikh N (fun s => v s z0) w + B_val * evalFinParikh N (fun s => v s z1) w := by
      intro B_val wt_c hwt w
      induction w with
      | nil => intro _; simp [evalFinParikh]
      | cons s rest ih =>
        intro hall
        simp only [evalFinParikh, hwt s (hall s List.mem_cons_self),
                   ih (fun x hx => hall x (List.mem_cons_of_mem s hx)), Nat.mul_add]
        omega
    have hge2M_w : ∀ w : List (Fin N), checkWordRightOrIntBool M w = true -> ∀ x ∈ w, x.val ≥ 2 * M := by
      intro w; induction w with
      | nil => intro _ _ hx; cases hx
      | cons x rest ih =>
        cases rest with
        | nil => intro hbw y hy; simp at hy; subst hy; exact of_decide_eq_true hbw
        | cons x2 tl =>
          intro hbw y hy; rcases bool_and_split hbw with ⟨hx4, htl⟩
          cases hy with
          | head => have := of_decide_eq_true hx4; omega
          | tail _ hm => exact ih htl y hm
    -- Sub-core `subL0` (`checkNoL1RulesBool`):
    let subL0 := filterRulesByPosMults core syzL0
    rcases syzygy_forces_parikh_and_prod_eq_w13 N subL0 (filterPosMults syzL0) hsyzL0 with ⟨hparL0_eq, _⟩
    have hnoL1_s := checkNoL1RulesBool_sound M subL0 hnoL1
    have hrelL0 : ∀ r ∈ subL0,
        evalFinParikh N wt0 r.1 ≥ evalFinParikh N wt0 r.2 ∧
        (evalFinParikh N wt0 r.1 = evalFinParikh N wt0 r.2 ->
          evalFinWordVec N 2 mat v r.1 z0 = evalFinWordVec N 2 mat v r.2 z0) := by
      intro r hr_sub
      have hr : r ∈ core := mem_of_mem_filterRulesByPosMults core syzL0 r hr_sub
      have hsh := hshape_all r hr; unfold checkRuleTwoSidedShapeBool at hsh
      rcases bool_or_split_w13 hsh with hL_c | hR_c
      · cases hl1 : r.1 with
        | nil => rw [hl1] at hL_c; simp at hL_c
        | cons l0 lint =>
          cases hr1 : r.2 with
          | nil => rw [hl1, hr1] at hL_c; simp at hL_c
          | cons r0 rint =>
            rw [hl1, hr1] at hL_c; dsimp only at hL_c
            rcases bool_or_split_w13 hL_c with hq0 | hq1
            · rcases bool_and_split hq0 with ⟨hb0, hrint_b⟩
              rcases bool_and_split hb0 with ⟨hlr_b, hlint_b⟩
              rcases of_decide_eq_true hlr_b with ⟨hl0_lt, hr0_lt⟩
              have hbl0 : b l0 = B0 := (hb_L r hr).1 l0 (Or.inl (hl1 ▸ List.Mem.head _)) hl0_lt
              have hbr0 : b r0 = B0 := (hb_L r hr).1 r0 (Or.inr (hr1 ▸ List.Mem.head _)) hr0_lt
              have hli_v := hvec_int lint (fun x hx => hint_id x (allGe4MBool_sound M lint hlint_b x hx)
                (symAppearsInRulesBool_of_mem_lhs N x core r hr (hl1 ▸ List.mem_cons_of_mem l0 hx)))
              have hri_v := hvec_int rint (fun x hx => hint_id x (allGe4MBool_sound M rint hrint_b x hx)
                (symAppearsInRulesBool_of_mem_rhs N x core r hr (hr1 ▸ List.mem_cons_of_mem r0 hx)))
              have hvl : evalFinWordVec N 2 mat v (l0 :: lint) z0 = evalFinParikh N wt0 (l0 :: lint) := by
                simp only [evalFinWordVec, evalFinParikh]
                rw [natMatVec_two_expand, (hdiag1 l0).1, Nat.one_mul, hli_v z0, hli_v z1]
                have hwl0 : wt0 l0 = v l0 z0 := by dsimp [wt0]; rw [ite_true_of_w10 (by omega)]
                have hwli := hpar_comb B0 wt0 (fun s hs => by dsimp [wt0]; rw [ite_false_of_w10 (by omega)])
                  lint (fun x hx => by have := allGe4MBool_sound M lint hlint_b x hx; omega)
                change v l0 z0 + (evalFinParikh N _ lint + b l0 * evalFinParikh N _ lint) = _
                rw [hbl0, hwl0, hwli]
              have hvr : evalFinWordVec N 2 mat v (r0 :: rint) z0 = evalFinParikh N wt0 (r0 :: rint) := by
                simp only [evalFinWordVec, evalFinParikh]
                rw [natMatVec_two_expand, (hdiag1 r0).1, Nat.one_mul, hri_v z0, hri_v z1]
                have hwr0 : wt0 r0 = v r0 z0 := by dsimp [wt0]; rw [ite_true_of_w10 (by omega)]
                have hwri := hpar_comb B0 wt0 (fun s hs => by dsimp [wt0]; rw [ite_false_of_w10 (by omega)])
                  rint (fun x hx => by have := allGe4MBool_sound M rint hrint_b x hx; omega)
                change v r0 z0 + (evalFinParikh N _ rint + b r0 * evalFinParikh N _ rint) = _
                rw [hbr0, hwr0, hwri]
              have hw0 := (hweak r hr).2 z0
              rw [hl1, hr1, hvl, hvr] at hw0
              exact ⟨hw0, fun h => by rw [hvl, hvr, h]⟩
            · rcases bool_and_split hq1 with ⟨hb1, _⟩
              rcases bool_and_split hb1 with ⟨hlr_b, _⟩
              rcases of_decide_eq_true hlr_b with ⟨hl0_ge, hl0_lt, _, _⟩
              exact False.elim (hnoL1_s r hr_sub l0 (Or.inl (hl1 ▸ List.Mem.head _)) ⟨hl0_ge, hl0_lt⟩)
      · rcases bool_and_split hR_c with ⟨hl_r, hr_r⟩
        have hvl := hvec_r r.1 hl_r (fun x hx hx4 => hint_id x hx4 (symAppearsInRulesBool_of_mem_lhs N x core r hr hx))
        have hvr := hvec_r r.2 hr_r (fun x hx hx4 => hint_id x hx4 (symAppearsInRulesBool_of_mem_rhs N x core r hr hx))
        have hpl := hpar_comb B0 wt0 (fun s hs => by dsimp [wt0]; rw [ite_false_of_w10 (by omega)])
          r.1 (hge2M_w r.1 hl_r)
        have hpr := hpar_comb B0 wt0 (fun s hs => by dsimp [wt0]; rw [ite_false_of_w10 (by omega)])
          r.2 (hge2M_w r.2 hr_r)
        rw [← hvl z0, ← hvl z1] at hpl
        rw [← hvr z0, ← hvr z1] at hpr
        have hw0 := (hweak r hr).2 z0
        have hw1 := (hweak r hr).2 z1
        have hm1 : B0 * evalFinWordVec N 2 mat v r.2 z1 ≤ B0 * evalFinWordVec N 2 mat v r.1 z1 :=
          Nat.mul_le_mul_left B0 hw1
        rw [hpl, hpr]
        dsimp only [N] at *
        exact ⟨by omega, fun _ => by omega⟩
    -- Sub-core `subL1` (`checkNoL0RulesBool`):
    let subL1 := filterRulesByPosMults core syzL1
    rcases syzygy_forces_parikh_and_prod_eq_w13 N subL1 (filterPosMults syzL1) hsyzL1 with ⟨hparL1_eq, _⟩
    have hnoL0_s := checkNoL0RulesBool_sound M subL1 hnoL0
    have hrelL1 : ∀ r ∈ subL1,
        evalFinParikh N wt1 r.1 ≥ evalFinParikh N wt1 r.2 ∧
        (evalFinParikh N wt1 r.1 = evalFinParikh N wt1 r.2 ->
          evalFinWordVec N 2 mat v r.1 z0 = evalFinWordVec N 2 mat v r.2 z0) := by
      intro r hr_sub
      have hr : r ∈ core := mem_of_mem_filterRulesByPosMults core syzL1 r hr_sub
      have hsh := hshape_all r hr; unfold checkRuleTwoSidedShapeBool at hsh
      rcases bool_or_split_w13 hsh with hL_c | hR_c
      · cases hl1 : r.1 with
        | nil => rw [hl1] at hL_c; simp at hL_c
        | cons l0 lint =>
          cases hr1 : r.2 with
          | nil => rw [hl1, hr1] at hL_c; simp at hL_c
          | cons r0 rint =>
            rw [hl1, hr1] at hL_c; dsimp only at hL_c
            rcases bool_or_split_w13 hL_c with hq0 | hq1
            · rcases bool_and_split hq0 with ⟨hb0, _⟩
              rcases bool_and_split hb0 with ⟨hlr_b, _⟩
              rcases of_decide_eq_true hlr_b with ⟨hl0_lt, _⟩
              exact False.elim (hnoL0_s r hr_sub l0 (Or.inl (hl1 ▸ List.Mem.head _)) hl0_lt)
            · rcases bool_and_split hq1 with ⟨hb1, hrint_b⟩
              rcases bool_and_split hb1 with ⟨hlr_b, hlint_b⟩
              rcases of_decide_eq_true hlr_b with ⟨hl0_ge, hl0_lt, hr0_ge, hr0_lt⟩
              have hbl0 : b l0 = B1 := (hb_L r hr).2 l0 (Or.inl (hl1 ▸ List.Mem.head _)) hl0_ge hl0_lt
              have hbr0 : b r0 = B1 := (hb_L r hr).2 r0 (Or.inr (hr1 ▸ List.Mem.head _)) hr0_ge hr0_lt
              have hli_v := hvec_int lint (fun x hx => hint_id x (allGe4MBool_sound M lint hlint_b x hx)
                (symAppearsInRulesBool_of_mem_lhs N x core r hr (hl1 ▸ List.mem_cons_of_mem l0 hx)))
              have hri_v := hvec_int rint (fun x hx => hint_id x (allGe4MBool_sound M rint hrint_b x hx)
                (symAppearsInRulesBool_of_mem_rhs N x core r hr (hr1 ▸ List.mem_cons_of_mem r0 hx)))
              have hvl : evalFinWordVec N 2 mat v (l0 :: lint) z0 = evalFinParikh N wt1 (l0 :: lint) := by
                simp only [evalFinWordVec, evalFinParikh]
                rw [natMatVec_two_expand, (hdiag1 l0).1, Nat.one_mul, hli_v z0, hli_v z1]
                have hwl0 : wt1 l0 = v l0 z0 := by dsimp [wt1]; rw [ite_true_of_w10 hl0_lt]
                have hwli := hpar_comb B1 wt1 (fun s hs => by dsimp [wt1]; rw [ite_false_of_w10 (by omega)])
                  lint (fun x hx => by have := allGe4MBool_sound M lint hlint_b x hx; omega)
                change v l0 z0 + (evalFinParikh N _ lint + b l0 * evalFinParikh N _ lint) = _
                rw [hbl0, hwl0, hwli]
              have hvr : evalFinWordVec N 2 mat v (r0 :: rint) z0 = evalFinParikh N wt1 (r0 :: rint) := by
                simp only [evalFinWordVec, evalFinParikh]
                rw [natMatVec_two_expand, (hdiag1 r0).1, Nat.one_mul, hri_v z0, hri_v z1]
                have hwr0 : wt1 r0 = v r0 z0 := by dsimp [wt1]; rw [ite_true_of_w10 hr0_lt]
                have hwri := hpar_comb B1 wt1 (fun s hs => by dsimp [wt1]; rw [ite_false_of_w10 (by omega)])
                  rint (fun x hx => by have := allGe4MBool_sound M rint hrint_b x hx; omega)
                change v r0 z0 + (evalFinParikh N _ rint + b r0 * evalFinParikh N _ rint) = _
                rw [hbr0, hwr0, hwri]
              have hw0 := (hweak r hr).2 z0
              rw [hl1, hr1, hvl, hvr] at hw0
              exact ⟨hw0, fun h => by rw [hvl, hvr, h]⟩
      · rcases bool_and_split hR_c with ⟨hl_r, hr_r⟩
        have hvl := hvec_r r.1 hl_r (fun x hx hx4 => hint_id x hx4 (symAppearsInRulesBool_of_mem_lhs N x core r hr hx))
        have hvr := hvec_r r.2 hr_r (fun x hx hx4 => hint_id x hx4 (symAppearsInRulesBool_of_mem_rhs N x core r hr hx))
        have hpl := hpar_comb B1 wt1 (fun s hs => by dsimp [wt1]; rw [ite_false_of_w10 (by omega)])
          r.1 (hge2M_w r.1 hl_r)
        have hpr := hpar_comb B1 wt1 (fun s hs => by dsimp [wt1]; rw [ite_false_of_w10 (by omega)])
          r.2 (hge2M_w r.2 hr_r)
        rw [← hvl z0, ← hvl z1] at hpl
        rw [← hvr z0, ← hvr z1] at hpr
        have hw0 := (hweak r hr).2 z0
        have hw1 := (hweak r hr).2 z1
        have hm1 : B1 * evalFinWordVec N 2 mat v r.2 z1 ≤ B1 * evalFinWordVec N 2 mat v r.1 z1 :=
          Nat.mul_le_mul_left B1 hw1
        rw [hpl, hpr]
        dsimp only [N] at *
        exact ⟨by omega, fun _ => by omega⟩
    have heqL0 := hparL0_eq wt0 (fun r hr => (hrelL0 r hr).1)
    have heqL1 := hparL1_eq wt1 (fun r hr => (hrelL1 r hr).1)
    intro r hr
    rcases hcoverL01 r hr with hr0 | hr1
    · exact (hrelL0 r hr0).2 (heqL0 r hr0)
    · exact (hrelL1 r hr1).2 (heqL1 r hr1)
  cases hcore_c : core with
  | nil => exact False.elim (hne_core hcore_c)
  | cons r0 rs =>
    rw [← hcore_c]
    have hmem0 : r0 ∈ core := hcore_c ▸ List.Mem.head _
    refine ⟨?_, ?_⟩
    · have himp1 : ∀ (k : Nat) (cur : List (List (Fin N) × List (Fin N))),
          (∀ r ∈ core, r ∈ cur) -> ¬ GenOmegaPosDiagUpperTri2DMatTower N k cur := by
        intro k; induction k with
        | zero =>
          intro cur hsub h0; rw [GenOmegaPosDiagUpperTri2DMatTower] at h0; subst h0
          exact List.not_mem_nil (hsub r0 hmem0)
        | succ k' ih =>
          intro cur hsub hsucc
          rcases hsucc with rfl | ⟨rem, mat, v, hpos, h10, hweak, hkeep, hrem⟩
          · exact List.not_mem_nil (hsub r0 hmem0)
          · have heq := hposDiag_no_strict mat v hpos h10 (fun r hr => hweak r (hsub r hr))
            exact ih rem (fun r hr => hkeep r (hsub r hr) (by rw [heq r hr]; exact Nat.lt_irrefl _)) hrem
      exact fun k => himp1 k core (fun _ hr => hr)
    · have himp2 : ∀ (k : Nat) (cur : List (List (Fin N) × List (Fin N))),
          (∀ r ∈ core, r ∈ cur) -> ¬ GenOmegaUnitDiagFullRank2DMatTower N k cur := by
        intro k; induction k with
        | zero =>
          intro cur hsub h0; rw [GenOmegaUnitDiagFullRank2DMatTower] at h0; subst h0
          exact List.not_mem_nil (hsub r0 hmem0)
        | succ k' ih =>
          intro cur hsub hsucc
          rcases hsucc with rfl | ⟨rem, mat, v, hdiag1, hweak, hkeep, hrem⟩
          · exact List.not_mem_nil (hsub r0 hmem0)
          · have heq := hunitDiag_no_strict mat v hdiag1 (fun r hr => hweak r (hsub r hr))
            exact ih rem (fun r hr => hkeep r (hsub r hr) (by rw [heq r hr]; exact Nat.lt_irrefl _)) hrem
      exact fun k => himp2 k core (fun _ hr => hr)

private theorem coverByPosMults {α : Type} :
    ∀ (rs : List α) (m0 m1 : List Nat),
      rs.length = m0.length -> rs.length = m1.length ->
      (∀ i : Nat, i < m0.length -> natAt m0 i + natAt m1 i ≥ 1) ->
      ∀ r ∈ rs, r ∈ filterRulesByPosMults rs m0 ∨ r ∈ filterRulesByPosMults rs m1
  | [], _, _, _, _, _, _, hr => by cases hr
  | r0 :: rt, [], _, hl0, _, _, _, _ => by simp at hl0
  | r0 :: rt, _ :: _, [], _, hl1, _, _, _ => by simp at hl1
  | r0 :: rt, u0 :: ut0, u1 :: ut1, hl0, hl1, hpos, r, hr => by
    cases hr with
    | head =>
      have h0 := hpos 0 (by simp)
      cases u0 with
      | zero =>
        cases u1 with
        | zero => change 0 + 0 ≥ 1 at h0; omega
        | succ _ => exact Or.inr (List.Mem.head _)
      | succ _ => exact Or.inl (List.Mem.head _)
    | tail _ htl =>
      have ih := coverByPosMults rt ut0 ut1
        (by simp at hl0; omega) (by simp at hl1; omega)
        (fun i hi => by
          have h := hpos (i + 1) (by simp; omega)
          simpa [natAt] using h) r htl
      rcases ih with hA | hB
      · left
        cases u0 with
        | zero => exact hA
        | succ _ => exact List.mem_cons_of_mem r0 hA
      · right
        cases u1 with
        | zero => exact hB
        | succ _ => exact List.mem_cons_of_mem r0 hB

def checkSumPosListsBool : List Nat -> List Nat -> Bool
  | [], [] => true
  | u0 :: us0, u1 :: us1 => decide (u0 + u1 ≥ 1) && checkSumPosListsBool us0 us1
  | _, _ => false

private theorem checkSumPosListsBool_sound :
    ∀ (m0 m1 : List Nat),
      checkSumPosListsBool m0 m1 = true ->
      m0.length = m1.length ∧ ∀ i : Nat, i < m0.length -> natAt m0 i + natAt m1 i ≥ 1
  | [], [], _ => ⟨rfl, fun _ hi => by simp at hi⟩
  | [], _ :: _, hb => by cases hb
  | _ :: _, [], hb => by cases hb
  | u0 :: us0, u1 :: us1, hb => by
    unfold checkSumPosListsBool at hb
    rcases bool_and_split hb with ⟨hu, hrest⟩
    rcases checkSumPosListsBool_sound us0 us1 hrest with ⟨hlen, hall⟩
    refine ⟨by simp [hlen], ?_⟩
    intro i hi
    cases i with
    | zero => exact of_decide_eq_true hu
    | succ j => exact hall j (by simp at hi; omega)

set_option maxRecDepth 65536 in
private theorem c39_base_certs_w13 :
    let c39 := filterFinParikhUnoriented 42 wtTwoSidedMod3OmitR3
      (twoSidedLabelledCollatzRules 3 (by decide) all11OmitR3List)
    checkPositiveParikhSyzygyFastBool 42 c39 syzTwoSidedMod3OmitR3Core39 = true ∧
    checkSignedInteriorAnnihilationBool 3 c39 posMultsC39 negMultsC39 = true ∧
    checkAllRulesShapeBool 3 c39 = true ∧
    c39 ≠ [] ∧
    ([⟨1, by decide⟩, ⟨14, by decide⟩], [⟨2, by decide⟩]) ∈ c39 ∧
    ([⟨4, by decide⟩, ⟨14, by decide⟩], [⟨5, by decide⟩]) ∈ c39 ∧
    symAppearsInRulesBool 42 14 c39 = true ∧
    symAppearsInRulesBool 42 0 c39 = false ∧
    symAppearsInRulesBool 42 3 c39 = false := by decide

set_option maxRecDepth 65536 in
private theorem c78_base_certs_a_w13 :
    let c78 := filterFinParikhUnoriented 84 wtTwoSidedMod6OmitR3
      (twoSidedLabelledCollatzRules 6 (by decide) all11OmitR3List)
    checkPositiveParikhSyzygyFastBool 84 c78 syzTwoSidedMod6OmitR3Core78 = true ∧
    checkSignedInteriorAnnihilationBool 6 c78 posMultsC78 negMultsC78 = true ∧
    checkAllRulesShapeBool 6 c78 = true ∧
    c78 ≠ [] := by decide

set_option maxRecDepth 65536 in
private theorem c78_base_certs_b_w13 :
    let c78 := filterFinParikhUnoriented 84 wtTwoSidedMod6OmitR3
      (twoSidedLabelledCollatzRules 6 (by decide) all11OmitR3List)
    hasTwoToOneRuleBool 84 4 29 5 c78 = true ∧
    hasTwoToOneRuleBool 84 2 28 4 c78 = true ∧
    hasTwoToOneRuleBool 84 2 25 1 c78 = true ∧
    hasTwoToOneRuleBool 84 10 29 11 c78 = true ∧
    hasTwoToOneRuleBool 84 8 28 10 c78 = true ∧
    hasTwoToOneRuleBool 84 8 25 7 c78 = true := by decide

set_option maxRecDepth 65536 in
private theorem c78_base_certs_c_w13 :
    let c78 := filterFinParikhUnoriented 84 wtTwoSidedMod6OmitR3
      (twoSidedLabelledCollatzRules 6 (by decide) all11OmitR3List)
    symAppearsInRulesBool 84 29 c78 = true ∧
    symAppearsInRulesBool 84 28 c78 = true ∧
    symAppearsInRulesBool 84 25 c78 = true ∧
    symAppearsInRulesBool 84 0 c78 = false ∧
    symAppearsInRulesBool 84 3 c78 = false ∧
    symAppearsInRulesBool 84 6 c78 = false ∧
    symAppearsInRulesBool 84 9 c78 = false := by decide

set_option maxRecDepth 65536 in
private theorem c39_w13_certs_ok :
    let c39 := filterFinParikhUnoriented 42 wtTwoSidedMod3OmitR3
      (twoSidedLabelledCollatzRules 3 (by decide) all11OmitR3List)
    checkAllRulesLen2To123Bool c39 = true ∧
    checkPositiveParikhSyzygyFastBool 42
      (filterRulesByPosMults c39 syzC39R0Only) (filterPosMults syzC39R0Only) = true ∧
    checkSignedInteriorAnnihilationBool 3
      (filterRulesByPosMults c39 syzC39R0Only)
      (filterRulesByPosMults posMultsC39R0Only syzC39R0Only)
      (filterRulesByPosMults negMultsC39R0Only syzC39R0Only) = true ∧
    checkOnlyR0SymsBool 3 (filterRulesByPosMults c39 syzC39R0Only) = true ∧
    checkSameActiveIntBool 3 c39 (filterRulesByPosMults c39 syzC39R0Only) = true ∧
    hasTwoToTwoRuleBool 42 28 6 22 9 c39 = true ∧
    checkPositiveParikhSyzygyFastBool 42
      (filterRulesByPosMults c39 syzC39L0Only) (filterPosMults syzC39L0Only) = true ∧
    checkNoL1RulesBool 3 (filterRulesByPosMults c39 syzC39L0Only) = true ∧
    checkPositiveParikhSyzygyFastBool 42
      (filterRulesByPosMults c39 syzC39L1Only) (filterPosMults syzC39L1Only) = true ∧
    checkNoL0RulesBool 3 (filterRulesByPosMults c39 syzC39L1Only) = true ∧
    c39.length = syzC39L0Only.length ∧
    checkSumPosListsBool syzC39L0Only syzC39L1Only = true := by decide

set_option maxRecDepth 65536 in
private theorem c78_w13_certs_ok_a :
    let c78 := filterFinParikhUnoriented 84 wtTwoSidedMod6OmitR3
      (twoSidedLabelledCollatzRules 6 (by decide) all11OmitR3List)
    checkAllRulesLen2To123Bool c78 = true ∧
    checkPositiveParikhSyzygyFastBool 84
      (filterRulesByPosMults c78 syzC78R0Only) (filterPosMults syzC78R0Only) = true ∧
    checkSignedInteriorAnnihilationBool 6
      (filterRulesByPosMults c78 syzC78R0Only)
      (filterRulesByPosMults posMultsC78R0Only syzC78R0Only)
      (filterRulesByPosMults negMultsC78R0Only syzC78R0Only) = true ∧
    checkOnlyR0SymsBool 6 (filterRulesByPosMults c78 syzC78R0Only) = true ∧
    checkSameActiveIntBool 6 c78 (filterRulesByPosMults c78 syzC78R0Only) = true ∧
    hasTwoToTwoRuleBool 84 55 12 43 18 c78 = true := by decide

set_option maxRecDepth 65536 in
private theorem c78_w13_certs_ok_b :
    let c78 := filterFinParikhUnoriented 84 wtTwoSidedMod6OmitR3
      (twoSidedLabelledCollatzRules 6 (by decide) all11OmitR3List)
    checkPositiveParikhSyzygyFastBool 84
      (filterRulesByPosMults c78 syzC78L0Only) (filterPosMults syzC78L0Only) = true ∧
    checkNoL1RulesBool 6 (filterRulesByPosMults c78 syzC78L0Only) = true ∧
    checkPositiveParikhSyzygyFastBool 84
      (filterRulesByPosMults c78 syzC78L1Only) (filterPosMults syzC78L1Only) = true ∧
    checkNoL0RulesBool 6 (filterRulesByPosMults c78 syzC78L1Only) = true ∧
    c78.length = syzC78L0Only.length ∧
    checkSumPosListsBool syzC78L0Only syzC78L1Only = true := by decide

/--
  Theorem W13.1b (`twosided_c39_c78_lowertri_posdiag_and_unitdiag_nontri_impossibility`,
  `zero custom axioms`):
  Complete Collapse of `∀ d ≥ 1` Lower-Triangular (`M_s 0 0 ≥ 1`), `d = 2` Positive-Diagonal
  Upper-Triangular, & `d = 2` Unit-Diagonal Full-Rank Non-Triangular (`[[1, b_s], [c_s, 1]]`) `ω^k`
  Matrix Towers on `TwoSided(2 × 3)` `c39` & `TwoSided(2 × 6)` `c78` (`Branch P4.3`, `W13_H1`):
  1. **Genuine Full-Rank Non-Triangular Witness**:
     `fullRankUnitDiagWitness = [[1, 2], [2, 1]]` lies inside `GenOmegaUnitDiagFullRank2DMatTower`
     with non-zero determinant `intDet 2 [[1, 2], [2, 1]] = -3 ≠ 0`!
  2. **All-Dimension Lower-Triangular Collapse (`∀ d ≥ 1, ∀ k : Nat`)**:
     `¬ GenOmegaLowerTriPosTopMatTower 42 d hd k c39 ∧ ¬ GenOmegaLowerTriPosTopMatTower 84 d hd k c78`!
  3. **Positive-Diagonal Upper-Triangular `d = 2` Collapse (`∀ k : Nat`)**:
     `¬ GenOmegaPosDiagUpperTri2DMatTower 42 k c39 ∧ ¬ GenOmegaPosDiagUpperTri2DMatTower 84 k c78`!
  4. **Unit-Diagonal Full-Rank Non-Triangular `d = 2` Collapse (`∀ k : Nat`)**:
     `¬ GenOmegaUnitDiagFullRank2DMatTower 42 k c39 ∧ ¬ GenOmegaUnitDiagFullRank2DMatTower 84 k c78`!
-/
theorem twosided_c39_c78_lowertri_posdiag_and_unitdiag_nontri_impossibility :
    let c39 := filterFinParikhUnoriented 42 wtTwoSidedMod3OmitR3
      (twoSidedLabelledCollatzRules 3 (by decide) all11OmitR3List)
    let c78 := filterFinParikhUnoriented 84 wtTwoSidedMod6OmitR3
      (twoSidedLabelledCollatzRules 6 (by decide) all11OmitR3List)
    let fullRankW : Fin 2 -> Fin 2 -> Nat := fun i j => if i.val = j.val then 1 else 2
    (fullRankW ⟨0, by decide⟩ ⟨0, by decide⟩ = 1 ∧
     fullRankW ⟨1, by decide⟩ ⟨1, by decide⟩ = 1 ∧
     intDet 2 (fun i j => (fullRankW i j : Int)) = -3) ∧
    (∀ (d : Nat) (hd : d ≥ 1) (k : Nat),
      ¬ GenOmegaLowerTriPosTopMatTower 42 d hd k c39 ∧
      ¬ GenOmegaLowerTriPosTopMatTower 84 d hd k c78) ∧
    (∀ k : Nat,
      ¬ GenOmegaPosDiagUpperTri2DMatTower 42 k c39 ∧
      ¬ GenOmegaPosDiagUpperTri2DMatTower 84 k c78) ∧
    (∀ k : Nat,
      ¬ GenOmegaUnitDiagFullRank2DMatTower 42 k c39 ∧
      ¬ GenOmegaUnitDiagFullRank2DMatTower 84 k c78) := by
  let c39 := filterFinParikhUnoriented 42 wtTwoSidedMod3OmitR3
    (twoSidedLabelledCollatzRules 3 (by decide) all11OmitR3List)
  let c78 := filterFinParikhUnoriented 84 wtTwoSidedMod6OmitR3
    (twoSidedLabelledCollatzRules 6 (by decide) all11OmitR3List)
  -- Part 2 (`GenOmegaLowerTriPosTopMatTower` reduces directly to `GenOmegaAffine1DFinTower`):
  have hlow_to_aff : ∀ (N d : Nat) (hd : d ≥ 1) (k : Nat)
      (rules : List (List (Fin N) × List (Fin N))),
      GenOmegaLowerTriPosTopMatTower N d hd k rules -> GenOmegaAffine1DFinTower N k rules := by
    intro N d hd k; induction k with
    | zero => intro _ h0; exact h0
    | succ k' ih =>
      intro rules hsucc
      rcases hsucc with rfl | ⟨rem, M, v, h00, h0j, hweak, hkeep, hrem⟩
      · exact Or.inl rfl
      · right
        refine ⟨rem, fun s => M s ⟨0, hd⟩ ⟨0, hd⟩, fun s => v s ⟨0, hd⟩, h00, ?_, ?_, ih rem hrem⟩
        · intro r hr
          rcases lowerTriPosTop_eq_affine1d N d hd M v h0j r.1 with ⟨hm1, hv1⟩
          rcases lowerTriPosTop_eq_affine1d N d hd M v h0j r.2 with ⟨hm2, hv2⟩
          rw [← hm1, ← hm2, ← hv1, ← hv2]
          exact ⟨(hweak r hr).1 ⟨0, hd⟩ ⟨0, hd⟩, (hweak r hr).2 ⟨0, hd⟩⟩
        · intro r hr hnot
          apply hkeep r hr
          rcases lowerTriPosTop_eq_affine1d N d hd M v h0j r.1 with ⟨_, hv1⟩
          rcases lowerTriPosTop_eq_affine1d N d hd M v h0j r.2 with ⟨_, hv2⟩
          rwa [hv1, hv2]
  have haff_imp := twosided_c39_c78_affine1d_and_coord_monotone_impossibility.1
  -- Parts 3 & 4 via `twosided_w13_2d_collapse_master`:
  rcases c39_base_certs_w13 with ⟨hsyz3, hann3, hsh3, hne3, hr3_1, hr3_2, ha3_14, hn3_0, hn3_3⟩
  rcases c39_w13_certs_ok with
    ⟨hlen3, hsyzR3, hannR3, honlyR3, hsame3, hr9_3b, hsyzL0_3, hnoL1_3, hsyzL1_3, hnoL0_3, hcl3, hsum3⟩
  have hr9_3 := hasTwoToTwoRuleBool_sound 42 ⟨28, by decide⟩ ⟨6, by decide⟩ ⟨22, by decide⟩ ⟨9, by decide⟩ c39 hr9_3b
  rcases checkSumPosListsBool_sound syzC39L0Only syzC39L1Only hsum3 with ⟨hl01_3, hpos3⟩
  have hcov3 := coverByPosMults c39 syzC39L0Only syzC39L1Only hcl3 (hcl3.trans hl01_3) hpos3
  rcases c78_base_certs_a_w13 with ⟨hsyz6, hann6, hsh6, hne6⟩
  rcases c78_base_certs_b_w13 with ⟨hb6_0, hb6_1, hb6_3, hb6_4, hb6_5, hb6_7⟩
  have hr6_0 := hasTwoToOneRuleBool_sound_w13 84 ⟨4, by decide⟩ ⟨29, by decide⟩ ⟨5, by decide⟩ c78 hb6_0
  have hr6_1 := hasTwoToOneRuleBool_sound_w13 84 ⟨2, by decide⟩ ⟨28, by decide⟩ ⟨4, by decide⟩ c78 hb6_1
  have hr6_3 := hasTwoToOneRuleBool_sound_w13 84 ⟨2, by decide⟩ ⟨25, by decide⟩ ⟨1, by decide⟩ c78 hb6_3
  have hr6_4 := hasTwoToOneRuleBool_sound_w13 84 ⟨10, by decide⟩ ⟨29, by decide⟩ ⟨11, by decide⟩ c78 hb6_4
  have hr6_5 := hasTwoToOneRuleBool_sound_w13 84 ⟨8, by decide⟩ ⟨28, by decide⟩ ⟨10, by decide⟩ c78 hb6_5
  have hr6_7 := hasTwoToOneRuleBool_sound_w13 84 ⟨8, by decide⟩ ⟨25, by decide⟩ ⟨7, by decide⟩ c78 hb6_7
  rcases c78_base_certs_c_w13 with ⟨ha6_29, ha6_28, ha6_25, hn6_0, hn6_3, hn6_6, hn6_9⟩
  rcases c78_w13_certs_ok_a with ⟨hlen6, hsyzR6, hannR6, honlyR6, hsame6, hr9_6b⟩
  rcases c78_w13_certs_ok_b with ⟨hsyzL0_6, hnoL1_6, hsyzL1_6, hnoL0_6, hcl6, hsum6⟩
  have hr9_6 := hasTwoToTwoRuleBool_sound 84 ⟨55, by decide⟩ ⟨12, by decide⟩ ⟨43, by decide⟩ ⟨18, by decide⟩ c78 hr9_6b
  rcases checkSumPosListsBool_sound syzC78L0Only syzC78L1Only hsum6 with ⟨hl01_6, hpos6⟩
  have hcov6 := coverByPosMults c78 syzC78L0Only syzC78L1Only hcl6 (hcl6.trans hl01_6) hpos6
  have hm3 := twosided_w13_2d_collapse_master 3 c39
    syzTwoSidedMod3OmitR3Core39 posMultsC39 negMultsC39
    syzC39R0Only posMultsC39R0Only negMultsC39R0Only syzC39L0Only syzC39L1Only
    ⟨1, by decide⟩ ⟨4, by decide⟩ ⟨6, by decide⟩ ⟨9, by decide⟩ ⟨28, by decide⟩ ⟨22, by decide⟩
    hsyz3 hann3 hsh3 hlen3 hne3 hsyzR3 hannR3 honlyR3 hsame3 hr9_3
    ⟨rfl, rfl, by decide, by decide⟩
    hsyzL0_3 hnoL1_3 hsyzL1_3 hnoL0_3 hcov3 ?_ ?_
  · have hm6 := twosided_w13_2d_collapse_master 6 c78
      syzTwoSidedMod6OmitR3Core78 posMultsC78 negMultsC78
      syzC78R0Only posMultsC78R0Only negMultsC78R0Only syzC78L0Only syzC78L1Only
      ⟨1, by decide⟩ ⟨7, by decide⟩ ⟨12, by decide⟩ ⟨18, by decide⟩ ⟨55, by decide⟩ ⟨43, by decide⟩
      hsyz6 hann6 hsh6 hlen6 hne6 hsyzR6 hannR6 honlyR6 hsame6 hr9_6
      ⟨rfl, rfl, by decide, by decide⟩
      hsyzL0_6 hnoL1_6 hsyzL1_6 hnoL0_6 hcov6 ?_ ?_
    · exact ⟨by decide,
             fun d hd k => ⟨fun h => (haff_imp k).1 (hlow_to_aff 42 d hd k c39 h),
                            fun h => (haff_imp k).2 (hlow_to_aff 84 d hd k c78 h)⟩,
             fun k => ⟨hm3.1 k, hm6.1 k⟩,
             fun k => ⟨hm3.2 k, hm6.2 k⟩⟩
    · -- Multiplicative `L`-equalization on `c78`:
      intro m hpeq hint1 r hr
      have hm29 : m ⟨29, by decide⟩ = 1 := hint1 ⟨29, by decide⟩ (by decide) ha6_29
      have hm28 : m ⟨28, by decide⟩ = 1 := hint1 ⟨28, by decide⟩ (by decide) ha6_28
      have hm25 : m ⟨25, by decide⟩ = 1 := hint1 ⟨25, by decide⟩ (by decide) ha6_25
      have he45 : m ⟨4, by decide⟩ = m ⟨5, by decide⟩ := by
        have h := hpeq _ hr6_0; dsimp only [prodFinWordW13] at h; rw [hm29] at h; omega
      have he24 : m ⟨2, by decide⟩ = m ⟨4, by decide⟩ := by
        have h := hpeq _ hr6_1; dsimp only [prodFinWordW13] at h; rw [hm28] at h; omega
      have he21 : m ⟨2, by decide⟩ = m ⟨1, by decide⟩ := by
        have h := hpeq _ hr6_3; dsimp only [prodFinWordW13] at h; rw [hm25] at h; omega
      have he10_11 : m ⟨10, by decide⟩ = m ⟨11, by decide⟩ := by
        have h := hpeq _ hr6_4; dsimp only [prodFinWordW13] at h; rw [hm29] at h; omega
      have he8_10 : m ⟨8, by decide⟩ = m ⟨10, by decide⟩ := by
        have h := hpeq _ hr6_5; dsimp only [prodFinWordW13] at h; rw [hm28] at h; omega
      have he8_7 : m ⟨8, by decide⟩ = m ⟨7, by decide⟩ := by
        have h := hpeq _ hr6_7; dsimp only [prodFinWordW13] at h; rw [hm25] at h; omega
      refine ⟨?_, ?_⟩
      · intro s hs_mem hs_lt
        have hs_act : symAppearsInRulesBool 84 s.val c78 = true := by
          rcases hs_mem with hl | hr_m
          · exact symAppearsInRulesBool_of_mem_lhs 84 s c78 r hr hl
          · exact symAppearsInRulesBool_of_mem_rhs 84 s c78 r hr hr_m
        rcases (by omega : s.val = 0 ∨ s.val = 1 ∨ s.val = 2 ∨ s.val = 3 ∨ s.val = 4 ∨ s.val = 5) with
          hv | hv | hv | hv | hv | hv
        · rw [hv, hn6_0] at hs_act; cases hs_act
        · rw [show s = ⟨1, by decide⟩ from Fin.ext hv]
        · rw [show s = ⟨2, by decide⟩ from Fin.ext hv, he21]
        · rw [hv, hn6_3] at hs_act; cases hs_act
        · rw [show s = ⟨4, by decide⟩ from Fin.ext hv, ← he24, he21]
        · rw [show s = ⟨5, by decide⟩ from Fin.ext hv, ← he45, ← he24, he21]
      · intro s hs_mem hs_ge hs_lt
        have hs_act : symAppearsInRulesBool 84 s.val c78 = true := by
          rcases hs_mem with hl | hr_m
          · exact symAppearsInRulesBool_of_mem_lhs 84 s c78 r hr hl
          · exact symAppearsInRulesBool_of_mem_rhs 84 s c78 r hr hr_m
        rcases (by omega : s.val = 6 ∨ s.val = 7 ∨ s.val = 8 ∨ s.val = 9 ∨ s.val = 10 ∨ s.val = 11) with
          hv | hv | hv | hv | hv | hv
        · rw [hv, hn6_6] at hs_act; cases hs_act
        · rw [show s = ⟨7, by decide⟩ from Fin.ext hv]
        · rw [show s = ⟨8, by decide⟩ from Fin.ext hv, he8_7]
        · rw [hv, hn6_9] at hs_act; cases hs_act
        · rw [show s = ⟨10, by decide⟩ from Fin.ext hv, ← he8_10, he8_7]
        · rw [show s = ⟨11, by decide⟩ from Fin.ext hv, ← he10_11, ← he8_10, he8_7]
    · -- Additive `L`-equalization on `c78`:
      intro b hpeq hint0 r hr
      have hb29 : b ⟨29, by decide⟩ = 0 := hint0 ⟨29, by decide⟩ (by decide) ha6_29
      have hb28 : b ⟨28, by decide⟩ = 0 := hint0 ⟨28, by decide⟩ (by decide) ha6_28
      have hb25 : b ⟨25, by decide⟩ = 0 := hint0 ⟨25, by decide⟩ (by decide) ha6_25
      have he45 : b ⟨4, by decide⟩ = b ⟨5, by decide⟩ := by
        have h := hpeq _ hr6_0; dsimp only [evalFinParikh] at h; rw [hb29] at h; omega
      have he24 : b ⟨2, by decide⟩ = b ⟨4, by decide⟩ := by
        have h := hpeq _ hr6_1; dsimp only [evalFinParikh] at h; rw [hb28] at h; omega
      have he21 : b ⟨2, by decide⟩ = b ⟨1, by decide⟩ := by
        have h := hpeq _ hr6_3; dsimp only [evalFinParikh] at h; rw [hb25] at h; omega
      have he10_11 : b ⟨10, by decide⟩ = b ⟨11, by decide⟩ := by
        have h := hpeq _ hr6_4; dsimp only [evalFinParikh] at h; rw [hb29] at h; omega
      have he8_10 : b ⟨8, by decide⟩ = b ⟨10, by decide⟩ := by
        have h := hpeq _ hr6_5; dsimp only [evalFinParikh] at h; rw [hb28] at h; omega
      have he8_7 : b ⟨8, by decide⟩ = b ⟨7, by decide⟩ := by
        have h := hpeq _ hr6_7; dsimp only [evalFinParikh] at h; rw [hb25] at h; omega
      refine ⟨?_, ?_⟩
      · intro s hs_mem hs_lt
        have hs_act : symAppearsInRulesBool 84 s.val c78 = true := by
          rcases hs_mem with hl | hr_m
          · exact symAppearsInRulesBool_of_mem_lhs 84 s c78 r hr hl
          · exact symAppearsInRulesBool_of_mem_rhs 84 s c78 r hr hr_m
        rcases (by omega : s.val = 0 ∨ s.val = 1 ∨ s.val = 2 ∨ s.val = 3 ∨ s.val = 4 ∨ s.val = 5) with
          hv | hv | hv | hv | hv | hv
        · rw [hv, hn6_0] at hs_act; cases hs_act
        · rw [show s = ⟨1, by decide⟩ from Fin.ext hv]
        · rw [show s = ⟨2, by decide⟩ from Fin.ext hv, he21]
        · rw [hv, hn6_3] at hs_act; cases hs_act
        · rw [show s = ⟨4, by decide⟩ from Fin.ext hv, ← he24, he21]
        · rw [show s = ⟨5, by decide⟩ from Fin.ext hv, ← he45, ← he24, he21]
      · intro s hs_mem hs_ge hs_lt
        have hs_act : symAppearsInRulesBool 84 s.val c78 = true := by
          rcases hs_mem with hl | hr_m
          · exact symAppearsInRulesBool_of_mem_lhs 84 s c78 r hr hl
          · exact symAppearsInRulesBool_of_mem_rhs 84 s c78 r hr hr_m
        rcases (by omega : s.val = 6 ∨ s.val = 7 ∨ s.val = 8 ∨ s.val = 9 ∨ s.val = 10 ∨ s.val = 11) with
          hv | hv | hv | hv | hv | hv
        · rw [hv, hn6_6] at hs_act; cases hs_act
        · rw [show s = ⟨7, by decide⟩ from Fin.ext hv]
        · rw [show s = ⟨8, by decide⟩ from Fin.ext hv, he8_7]
        · rw [hv, hn6_9] at hs_act; cases hs_act
        · rw [show s = ⟨10, by decide⟩ from Fin.ext hv, ← he8_10, he8_7]
        · rw [show s = ⟨11, by decide⟩ from Fin.ext hv, ← he10_11, ← he8_10, he8_7]
  · -- Multiplicative `L`-equalization on `c39`:
    intro m hpeq hint1 r hr
    have hm14 : m ⟨14, by decide⟩ = 1 := hint1 ⟨14, by decide⟩ (by decide) ha3_14
    have he12 : m ⟨1, by decide⟩ = m ⟨2, by decide⟩ := by
      have h := hpeq _ hr3_1; dsimp only [prodFinWordW13] at h; rw [hm14] at h; omega
    have he45 : m ⟨4, by decide⟩ = m ⟨5, by decide⟩ := by
      have h := hpeq _ hr3_2; dsimp only [prodFinWordW13] at h; rw [hm14] at h; omega
    refine ⟨?_, ?_⟩
    · intro s hs_mem hs_lt
      have hs_act : symAppearsInRulesBool 42 s.val c39 = true := by
        rcases hs_mem with hl | hr_m
        · exact symAppearsInRulesBool_of_mem_lhs 42 s c39 r hr hl
        · exact symAppearsInRulesBool_of_mem_rhs 42 s c39 r hr hr_m
      rcases (by omega : s.val = 0 ∨ s.val = 1 ∨ s.val = 2) with hv | hv | hv
      · rw [hv, hn3_0] at hs_act; cases hs_act
      · rw [show s = ⟨1, by decide⟩ from Fin.ext hv]
      · rw [show s = ⟨2, by decide⟩ from Fin.ext hv, ← he12]
    · intro s hs_mem _ hs_lt
      have hs_act : symAppearsInRulesBool 42 s.val c39 = true := by
        rcases hs_mem with hl | hr_m
        · exact symAppearsInRulesBool_of_mem_lhs 42 s c39 r hr hl
        · exact symAppearsInRulesBool_of_mem_rhs 42 s c39 r hr hr_m
      rcases (by omega : s.val = 3 ∨ s.val = 4 ∨ s.val = 5) with hv | hv | hv
      · rw [hv, hn3_3] at hs_act; cases hs_act
      · rw [show s = ⟨4, by decide⟩ from Fin.ext hv]
      · rw [show s = ⟨5, by decide⟩ from Fin.ext hv, ← he45]
  · -- Additive `L`-equalization on `c39`:
    intro b hpeq hint0 r hr
    have hb14 : b ⟨14, by decide⟩ = 0 := hint0 ⟨14, by decide⟩ (by decide) ha3_14
    have he12 : b ⟨1, by decide⟩ = b ⟨2, by decide⟩ := by
      have h := hpeq _ hr3_1; dsimp only [evalFinParikh] at h; rw [hb14] at h; omega
    have he45 : b ⟨4, by decide⟩ = b ⟨5, by decide⟩ := by
      have h := hpeq _ hr3_2; dsimp only [evalFinParikh] at h; rw [hb14] at h; omega
    refine ⟨?_, ?_⟩
    · intro s hs_mem hs_lt
      have hs_act : symAppearsInRulesBool 42 s.val c39 = true := by
        rcases hs_mem with hl | hr_m
        · exact symAppearsInRulesBool_of_mem_lhs 42 s c39 r hr hl
        · exact symAppearsInRulesBool_of_mem_rhs 42 s c39 r hr hr_m
      rcases (by omega : s.val = 0 ∨ s.val = 1 ∨ s.val = 2) with hv | hv | hv
      · rw [hv, hn3_0] at hs_act; cases hs_act
      · rw [show s = ⟨1, by decide⟩ from Fin.ext hv]
      · rw [show s = ⟨2, by decide⟩ from Fin.ext hv, ← he12]
    · intro s hs_mem _ hs_lt
      have hs_act : symAppearsInRulesBool 42 s.val c39 = true := by
        rcases hs_mem with hl | hr_m
        · exact symAppearsInRulesBool_of_mem_lhs 42 s c39 r hr hl
        · exact symAppearsInRulesBool_of_mem_rhs 42 s c39 r hr hr_m
      rcases (by omega : s.val = 3 ∨ s.val = 4 ∨ s.val = 5) with hv | hv | hv
      · rw [hv, hn3_3] at hs_act; cases hs_act
      · rw [show s = ⟨4, by decide⟩ from Fin.ext hv]
      · rw [show s = ⟨5, by decide⟩ from Fin.ext hv, ← he45]

-- ----------------------------------------------------------------------------
-- Section 1C: End-to-End `.L`-to-`.R` Coupled `DP2` Syracuse Homomorphism,
--             Unconditional `1/2`-Cycle Freedom, & Mersenne Finite-Feature Barrier
-- ----------------------------------------------------------------------------

/-- Global shifted base-`(2, 3)` odd integer decoding of a `DP2` tail word `u` (`≥ 3`, odd;
    when `encodePosBin n ++ [.R] = .B1 :: u`, `dp2GlobalOddVal u = n`). -/
def dp2GlobalOddVal (u : List MixedSRSSym) : Nat :=
  2 * (evalWordAffine1D artsGieslSemanticDP1D u).c + 3

private theorem evalWordAffine1D_append (interp : MixedSRSSym -> NatAffine1D) :
    ∀ u v : List MixedSRSSym,
      evalWordAffine1D interp (u ++ v) =
        { m := (evalWordAffine1D interp u).m * (evalWordAffine1D interp v).m,
          c := (evalWordAffine1D interp u).c +
                 (evalWordAffine1D interp u).m * (evalWordAffine1D interp v).c }
  | [], v => by simp [evalWordAffine1D]
  | s :: rest, v => by
    simp only [List.cons_append, evalWordAffine1D, evalWordAffine1D_append interp rest v,
               NatAffine1D.mk.injEq]
    refine ⟨by ac_rfl, ?_⟩
    rw [Nat.mul_add, ← Nat.mul_assoc]
    omega

private theorem omitR2_rule_classification (r : List MixedSRSSym × List MixedSRSSym)
    (hm : r ∈ all11OmitR2List) :
    (r = ([.L, .B0], [.L]) ∨ (.L ∉ r.1 ∧ .L ∉ r.2 ∧ r ∈ interiorAndRight9RuleList)) ∧
    (.R ∈ r.1 ↔ .R ∈ r.2) := by
  revert r hm; decide

private theorem head_L_unique_split {p l sfx rest : List MixedSRSSym}
    (hnoL : .L ∉ rest) (hl : .L ∈ l)
    (heq : .L :: rest = p ++ l ++ sfx) : p = [] := by
  cases p with
  | nil => rfl
  | cons p0 ptl =>
    simp only [List.cons_append, List.cons.injEq] at heq
    rcases heq with ⟨_, hrest_eq⟩
    exfalso
    apply hnoL
    rw [hrest_eq]
    exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hl)))

private theorem omitR2_reach_anchored_homomorphism :
    ∀ {w1 w2 : List MixedSRSSym},
      srsReachesFromList all11OmitR2List w1 w2 ->
      (∃ t1 : List MixedSRSSym, w1 = .L :: t1 ∧ .L ∉ t1) ->
      (∃ t2 : List MixedSRSSym, w2 = .L :: t2 ∧ .L ∉ t2) ∧
      (.R ∈ w1 ↔ .R ∈ w2) ∧
      (∃ k : Nat,
        2 ^ k * (1 + (evalWordAffine1D artsGieslSemanticDP1D w2).c) =
          1 + (evalWordAffine1D artsGieslSemanticDP1D w1).c) := by
  intro w1 w2 hreach
  induction hreach with
  | refl a =>
    intro h1
    exact ⟨h1, Iff.rfl, 0, by simp⟩
  | @step a b _ hs _ ih =>
    rintro ⟨t1, ha_head, hnoL1⟩
    rcases hs with ⟨p, l, r, sfx, hmem, ha_eq, hb_eq⟩
    rcases omitR2_rule_classification (l, r) hmem with ⟨hcls, hR_iff⟩
    have hR_step : .R ∈ a ↔ .R ∈ b := by
      rw [ha_eq, hb_eq]
      simp only [List.mem_append]
      exact ⟨fun h => by
               rcases h with (hp | hl_m) | hs_m
               · exact Or.inl (Or.inl hp)
               · exact Or.inl (Or.inr (hR_iff.mp hl_m))
               · exact Or.inr hs_m,
             fun h => by
               rcases h with (hp | hr_m) | hs_m
               · exact Or.inl (Or.inl hp)
               · exact Or.inl (Or.inr (hR_iff.mpr hr_m))
               · exact Or.inr hs_m⟩
    rcases hcls with hR1 | ⟨hl_noL, hr_noL, hint9⟩
    · -- Rule `R1 : ([.L, .B0], [.L])`: since `.L ∉ t1`, `p = []`!
      have hl_eq : l = [.L, .B0] := congrArg Prod.fst hR1
      have hr_eq : r = [.L] := congrArg Prod.snd hR1
      subst hl_eq; subst hr_eq
      have hp_nil : p = [] :=
        head_L_unique_split hnoL1 (by simp) (ha_head.symm.trans ha_eq)
      subst hp_nil
      have ht1_eq : t1 = .B0 :: sfx := by
        have h := ha_head.symm.trans ha_eq
        simpa using h
      have hnoL_sfx : .L ∉ sfx := fun hm => hnoL1 (ht1_eq ▸ List.mem_cons_of_mem .B0 hm)
      have hb_head : ∃ tb : List MixedSRSSym, b = .L :: tb ∧ .L ∉ tb :=
        ⟨sfx, by simpa using hb_eq, hnoL_sfx⟩
      rcases ih hb_head with ⟨hc_head, hR_bc, k_tl, hk_tl⟩
      have hhalf : 1 + (evalWordAffine1D artsGieslSemanticDP1D a).c =
          2 * (1 + (evalWordAffine1D artsGieslSemanticDP1D b).c) := by
        rw [ha_eq, hb_eq]
        simp only [List.nil_append, List.cons_append, evalWordAffine1D, artsGieslSemanticDP1D]; omega
      refine ⟨hc_head, hR_step.trans hR_bc, k_tl + 1, ?_⟩
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ k_tl) 2, Nat.mul_assoc 2, hk_tl, hhalf]
    · -- Interior/right rule `r ∈ interiorAndRight9RuleList` (`eval l = eval r`, `.L ∉ l, r`):
      have hp_cons : ∃ p_tl : List MixedSRSSym, p = .L :: p_tl ∧ .L ∉ p_tl := by
        cases p with
        | nil =>
          exfalso
          have h := ha_head.symm.trans ha_eq
          cases l with
          | nil =>
            have hne_l : ∀ x ∈ interiorAndRight9RuleList, x.1 ≠ [] := by decide
            exact hne_l ([], r) hint9 rfl
          | cons l0 ltl =>
            simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
            exact hl_noL (h.1 ▸ List.Mem.head _)
        | cons p0 ptl =>
          have h := ha_head.symm.trans ha_eq
          simp only [List.cons_append, List.cons.injEq] at h
          refine ⟨ptl, congrArg (· :: ptl) h.1.symm, ?_⟩
          intro hm
          exact hnoL1 (h.2 ▸ List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hm))))
      rcases hp_cons with ⟨ptl, hp_eq, hnoL_ptl⟩
      have hnoL_sfx : .L ∉ sfx := by
        intro hm
        have h := ha_head.symm.trans ha_eq
        rw [hp_eq] at h
        simp only [List.cons_append, List.cons.injEq] at h
        exact hnoL1 (h.2 ▸ List.mem_append.mpr (Or.inr hm))
      have hb_head : ∃ tb : List MixedSRSSym, b = .L :: tb ∧ .L ∉ tb := by
        refine ⟨ptl ++ r ++ sfx, ?_, ?_⟩
        · rw [hb_eq, hp_eq]; simp [List.cons_append, List.append_assoc]
        · intro hm
          rcases List.mem_append.mp hm with h1 | h2
          · rcases List.mem_append.mp h1 with hpt | hrm
            · exact hnoL_ptl hpt
            · exact hr_noL hrm
          · exact hnoL_sfx h2
      rcases ih hb_head with ⟨hc_head, hR_bc, k_tl, hk_tl⟩
      have heval_lr := arts_giesl_1d_semantic_dp_removes_dp1_rel_all_interior.2.1 (l, r) hint9
      have heval_ab : evalWordAffine1D artsGieslSemanticDP1D a =
          evalWordAffine1D artsGieslSemanticDP1D b := by
        rw [ha_eq, hb_eq,
            evalWordAffine1D_append _ (p ++ l) sfx,
            evalWordAffine1D_append _ p l,
            evalWordAffine1D_append _ (p ++ r) sfx,
            evalWordAffine1D_append _ p r,
            heval_lr]
      exact ⟨hc_head, hR_step.trans hR_bc, k_tl, by rw [heval_ab]; exact hk_tl⟩

/--
  Theorem W13.1c (`leftAnchoredDP2_r_carrying_syracuse_and_no_1_2_cycles`,
  choice-free `zero custom axioms`):
  End-to-End `.L`-to-`.R` Coupled Syracuse Homomorphism & Unconditional `1`- and `2`-Cycle Freedom
  of `leftAnchoredDP2Step` Across ALL `List MixedSRSSym` (`Branch P4.3`, `W13_H1`):
  1. **`.R`-Marker Preservation & Universal Syracuse Homomorphism (`∀ u1 u2`)**:
     Whenever `leftAnchoredDP2Step u1 u2` holds (across arbitrary interleaved `all11OmitR2List`
     derivations and arbitrary `List MixedSRSSym` words!):
     - `.R ∈ u1 ↔ .R ∈ u2`, AND
     - `∃ a : Nat, a ≥ 1 ∧ 2 ^ a * dp2GlobalOddVal u2 = 3 * dp2GlobalOddVal u1 + 1`!
  2. **Exact Agreement on Encoded Odd Positive Integers (`∀ n ≥ 3` odd)**:
     Whenever `encodePosBin n ++ [.R] = .B1 :: u`, `dp2GlobalOddVal u = n`!
  3. **Unconditional `1`-Cycle and `2`-Cycle Freedom Across ALL `List MixedSRSSym`**:
     - `(∀ u : List MixedSRSSym, ¬ leftAnchoredDP2Step u u)` (zero `1`-cycles!), AND
     - `(∀ u1 u2 : List MixedSRSSym, ¬ (leftAnchoredDP2Step u1 u2 ∧ leftAnchoredDP2Step u2 u1))`
       (zero `2`-cycles!)!
-/
theorem leftAnchoredDP2_r_carrying_syracuse_and_no_1_2_cycles :
    (∀ u1 u2 : List MixedSRSSym,
      leftAnchoredDP2Step u1 u2 ->
      (.R ∈ u1 ↔ .R ∈ u2) ∧
      (∃ a : Nat, a ≥ 1 ∧ 2 ^ a * dp2GlobalOddVal u2 = 3 * dp2GlobalOddVal u1 + 1)) ∧
    (∀ (n : Nat) (u : List MixedSRSSym),
      n ≥ 3 -> n % 2 = 1 -> encodePosBin n ++ [.R] = .B1 :: u ->
      dp2GlobalOddVal u = n) ∧
    (∀ u : List MixedSRSSym, ¬ leftAnchoredDP2Step u u) ∧
    (∀ u1 u2 : List MixedSRSSym, ¬ (leftAnchoredDP2Step u1 u2 ∧ leftAnchoredDP2Step u2 u1)) := by
  have hsyr : ∀ u1 u2 : List MixedSRSSym,
      leftAnchoredDP2Step u1 u2 ->
      (.R ∈ u1 ↔ .R ∈ u2) ∧
      (∃ a : Nat, a ≥ 1 ∧ 2 ^ a * dp2GlobalOddVal u2 = 3 * dp2GlobalOddVal u1 + 1) := by
    intro u1 u2 ⟨hnoL1, _, hreach⟩
    have hnoL_t1 : .L ∉ (.T2 :: u1) := by
      intro hm; simp only [List.mem_cons] at hm; rcases hm with h | h
      · cases h
      · exact hnoL1 h
    rcases omitR2_reach_anchored_homomorphism hreach ⟨.T2 :: u1, rfl, hnoL_t1⟩ with
      ⟨_, hR_iff, k, hk⟩
    have hR_u : .R ∈ u1 ↔ .R ∈ u2 := by
      simp only [List.cons_append, List.nil_append, List.mem_cons] at hR_iff
      exact ⟨fun h1 => by
               rcases hR_iff.mp (Or.inr (Or.inr h1)) with h | h | h
               · cases h
               · cases h
               · exact h,
             fun h2 => by
               rcases hR_iff.mpr (Or.inr (Or.inr h2)) with h | h | h
               · cases h
               · cases h
               · exact h⟩
    refine ⟨hR_u, k + 1, by omega, ?_⟩
    have hc1 : 1 + (evalWordAffine1D artsGieslSemanticDP1D ([.L, .T2] ++ u1)).c =
        3 * (evalWordAffine1D artsGieslSemanticDP1D u1).c + 5 := by
      simp [evalWordAffine1D, artsGieslSemanticDP1D]; omega
    have hc2 : 1 + (evalWordAffine1D artsGieslSemanticDP1D ([.L, .B1] ++ u2)).c =
        dp2GlobalOddVal u2 := by
      simp [evalWordAffine1D, artsGieslSemanticDP1D, dp2GlobalOddVal]; omega
    rw [hc1, hc2] at hk
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, Nat.mul_assoc 2, hk]
    unfold dp2GlobalOddVal
    omega
  -- Part 2: `encodePosBin n ++ [.R] = .B1 :: u -> dp2GlobalOddVal u = n`:
  have henc_eq : ∀ (n : Nat) (u : List MixedSRSSym),
      n ≥ 3 -> n % 2 = 1 -> encodePosBin n ++ [.R] = .B1 :: u ->
      dp2GlobalOddVal u = n := by
    have hbin_eval : ∀ w : List MixedSRSSym,
        (∀ s ∈ w, isBinaryInteriorSym s = true) ->
        (evalWordAffine1D artsGieslSemanticDP1D (w ++ [.R])).c + 1 = srsEvalInterior w := by
      intro w; induction w with
      | nil => intro _; rfl
      | cons s rest ih =>
        intro hbin
        have hs_b := hbin s List.mem_cons_self
        have ih_r := ih (fun x hx => hbin x (List.mem_cons_of_mem s hx))
        cases s <;> simp [isBinaryInteriorSym] at hs_b
        · simp only [List.cons_append, evalWordAffine1D, artsGieslSemanticDP1D, srsEvalInterior]
          omega
        · simp only [List.cons_append, evalWordAffine1D, artsGieslSemanticDP1D, srsEvalInterior]
          omega
    intro n u hn3 _ henc
    rcases encodePosBin_spec n (by omega) with ⟨heval_n, hbin_n⟩
    have hc_full := hbin_eval (encodePosBin n) hbin_n
    rw [heval_n, henc] at hc_full
    simp only [evalWordAffine1D, artsGieslSemanticDP1D] at hc_full
    unfold dp2GlobalOddVal
    omega
  -- Part 3: No 1-cycles and no 2-cycles!
  have hno1 : ∀ u : List MixedSRSSym, ¬ leftAnchoredDP2Step u u := by
    intro u hdp
    rcases hsyr u u hdp with ⟨_, a, ha1, heq⟩
    have hge3 : dp2GlobalOddVal u ≥ 3 := by unfold dp2GlobalOddVal; omega
    rcases (by omega : a = 1 ∨ a = 2 ∨ a ≥ 3) with rfl | rfl | ha3
    · omega
    · omega
    · have hp8 : 2 ^ a ≥ 8 := by
        simpa using nat_pow_mono_exp_pos 2 3 a (by decide) ha3
      have hm := Nat.mul_le_mul_right (dp2GlobalOddVal u) hp8
      omega
  have hno2 : ∀ u1 u2 : List MixedSRSSym,
      ¬ (leftAnchoredDP2Step u1 u2 ∧ leftAnchoredDP2Step u2 u1) := by
    rintro u1 u2 ⟨h12, h21⟩
    rcases hsyr u1 u2 h12 with ⟨_, a1, ha1, heq1⟩
    rcases hsyr u2 u1 h21 with ⟨_, a2, ha2, heq2⟩
    let N1 := dp2GlobalOddVal u1
    have hN1_ge3 : N1 ≥ 3 := by dsimp [N1, dp2GlobalOddVal]; omega
    -- Multiply `heq2` (`2^a2 * N1 = 3 * N2 + 1`) by `2^a1` and substitute `2^a1 * N2 = 3 * N1 + 1`:
    have hcomb : 2 ^ (a1 + a2) * N1 = 9 * N1 + 3 + 2 ^ a1 := by
      calc
        2 ^ (a1 + a2) * N1 = 2 ^ a1 * (2 ^ a2 * N1) := by rw [Nat.pow_add, Nat.mul_assoc]
        _ = 2 ^ a1 * (3 * dp2GlobalOddVal u2 + 1) := by rw [heq2]
        _ = 3 * (2 ^ a1 * dp2GlobalOddVal u2) + 2 ^ a1 := by rw [Nat.mul_add, Nat.mul_one]; ac_rfl
        _ = 3 * (3 * N1 + 1) + 2 ^ a1 := by rw [heq1]
        _ = 9 * N1 + 3 + 2 ^ a1 := by omega
    have hp1_pos : 2 ^ a1 ≥ 1 := pow2_pos_nat a1
    dsimp only [N1] at hN1_ge3 hcomb
    rcases (by omega : a1 + a2 ≤ 3 ∨ a1 + a2 = 4 ∨ a1 + a2 ≥ 5) with hle3 | heq4 | hge5
    · have hp_le8 : 2 ^ (a1 + a2) ≤ 8 := by
        simpa using nat_pow_mono_exp_pos 2 (a1 + a2) 3 (by decide) hle3
      have hm : 2 ^ (a1 + a2) * dp2GlobalOddVal u1 ≤ 8 * dp2GlobalOddVal u1 :=
        Nat.mul_le_mul_right _ hp_le8
      rw [hcomb] at hm
      generalize 2 ^ a1 = P1 at hp1_pos hm
      omega
    · rw [heq4] at hcomb
      rcases (by omega : a1 = 1 ∨ a1 = 2 ∨ a1 = 3) with rfl | rfl | rfl <;> omega
    · have hp_ge32 : 2 ^ (a1 + a2) ≥ 32 := by
        simpa using nat_pow_mono_exp_pos 2 5 (a1 + a2) (by decide) hge5
      have hp_2a1 : 2 ^ (a1 + a2) ≥ 2 * 2 ^ a1 := by
        rw [Nat.pow_add]
        have hp2_ge2 : 2 ^ a2 ≥ 2 := by simpa using pow2_mono_nat ha2
        simpa [Nat.mul_comm] using Nat.mul_le_mul_left (2 ^ a1) hp2_ge2
      have hm_sub : (2 ^ (a1 + a2) - 9) * dp2GlobalOddVal u1 ≥ (2 ^ (a1 + a2) - 9) * 3 :=
        Nat.mul_le_mul_left _ hN1_ge3
      rw [Nat.sub_mul, hcomb, Nat.sub_mul] at hm_sub
      generalize 2 ^ (a1 + a2) = P12, 2 ^ a1 = P1 at hp1_pos hp_ge32 hp_2a1 hm_sub
      omega
  exact ⟨hsyr, henc_eq, hno1, hno2⟩

/-- Deterministic carry-propagation normalizer across `{.B0, .B1}` ending in `[.R]`:
    given carry `c ∈ {.T0, .T1, .T2}` and a binary-plus-`.R` word `w`, returns the exact binary-plus-`.R`
    result of sweeping `c` all the way to `.R` via `{R3..R11}`! -/
def sweepCarryEnd : MixedSRSSym -> List MixedSRSSym
  | .T0 => [.B1, .R]
  | .T1 => [.B0, .B0, .R]
  | .T2 => [.B1, .B0, .R]
  | .B0 => [.B1, .B0, .R]
  | .B1 => [.B1, .B0, .R]
  | .L  => [.B1, .B0, .R]
  | .R  => [.B1, .B0, .R]

def sweepCarryToRAux : List MixedSRSSym -> MixedSRSSym -> List MixedSRSSym
  | [], c => sweepCarryEnd c
  | s :: rest, c =>
    match s with
    | .B0 =>
      match c with
      | .T0 => .B0 :: sweepCarryToRAux rest .T0
      | .T1 => .B1 :: sweepCarryToRAux rest .T0
      | .T2 => .B0 :: sweepCarryToRAux rest .T1
      | .B0 => [.B1, .B0, .R]
      | .B1 => [.B1, .B0, .R]
      | .L  => [.B1, .B0, .R]
      | .R  => [.B1, .B0, .R]
    | .B1 =>
      match c with
      | .T0 => .B1 :: sweepCarryToRAux rest .T1
      | .T1 => .B0 :: sweepCarryToRAux rest .T2
      | .T2 => .B1 :: sweepCarryToRAux rest .T2
      | .B0 => [.B1, .B0, .R]
      | .B1 => [.B1, .B0, .R]
      | .L  => [.B1, .B0, .R]
      | .R  => [.B1, .B0, .R]
    | .T0 => sweepCarryEnd c
    | .T1 => sweepCarryEnd c
    | .T2 => sweepCarryEnd c
    | .L  => sweepCarryEnd c
    | .R  => sweepCarryEnd c

def sweepCarryToR (c : MixedSRSSym) (w : List MixedSRSSym) : List MixedSRSSym :=
  sweepCarryToRAux w c

def isBinRTail : List MixedSRSSym -> Prop
  | [.R] => True
  | .B0 :: rest => isBinRTail rest
  | .B1 :: rest => isBinRTail rest
  | _ => False

private theorem sweepCarryToR_sound :
    ∀ (w : List MixedSRSSym) (c : MixedSRSSym),
      (c = .T0 ∨ c = .T1 ∨ c = .T2) ->
      ∀ (pre : List MixedSRSSym),
        isBinRTail w ->
        isBinRTail (sweepCarryToR c w) ∧
        .L ∉ sweepCarryToR c w ∧
        .R ∈ sweepCarryToR c w ∧
        srsReachesFromList all11OmitR2List (pre ++ [c] ++ w) (pre ++ sweepCarryToR c w)
  | [], _, _, _, hw => by simp [isBinRTail] at hw
  | [s], c, hc, pre, hw => by
    cases s <;> simp [isBinRTail] at hw
    rcases hc with rfl | rfl | rfl
    · refine ⟨trivial, by decide, by decide, ?_⟩
      exact .step ⟨pre, [.T0, .R], [.B1, .R], [], by decide,
        by simp [List.append_assoc], by simp [sweepCarryToR, sweepCarryToRAux, sweepCarryEnd]⟩ (.refl _)
    · refine ⟨trivial, by decide, by decide, ?_⟩
      exact .step ⟨pre, [.T1, .R], [.B0, .B0, .R], [], by decide,
        by simp [List.append_assoc], by simp [sweepCarryToR, sweepCarryToRAux, sweepCarryEnd]⟩ (.refl _)
    · refine ⟨trivial, by decide, by decide, ?_⟩
      exact .step ⟨pre, [.T2, .R], [.B1, .B0, .R], [], by decide,
        by simp [List.append_assoc], by simp [sweepCarryToR, sweepCarryToRAux, sweepCarryEnd]⟩ (.refl _)
  | s :: s2 :: tl, c, hc, pre, hw => by
    cases s <;> try (simp [isBinRTail] at hw)
    · -- `s = .B0`:
      rcases hc with rfl | rfl | rfl
      · rcases sweepCarryToR_sound (s2 :: tl) .T0 (Or.inl rfl) (pre ++ [.B0]) hw with
          ⟨hb_o, hnL, hmR, hr_tl⟩
        refine ⟨hb_o,
                fun hm => (List.mem_cons.mp hm).elim (fun h0 => nomatch h0) hnL,
                show .R ∈ .B0 :: sweepCarryToR .T0 (s2 :: tl) from List.mem_cons_of_mem .B0 hmR,
                ?_⟩
        have hs0 : srsStepFromList all11OmitR2List
            (pre ++ [.T0, .B0] ++ (s2 :: tl)) ((pre ++ [.B0]) ++ [.T0] ++ (s2 :: tl)) :=
          ⟨pre, [.T0, .B0], [.B0, .T0], s2 :: tl, by decide,
           by simp [List.append_assoc], by simp [List.append_assoc]⟩
        simpa [sweepCarryToR, sweepCarryToRAux, List.append_assoc] using
          srsReaches_omitR2_trans (.step hs0 (.refl _)) hr_tl
      · rcases sweepCarryToR_sound (s2 :: tl) .T0 (Or.inl rfl) (pre ++ [.B1]) hw with
          ⟨hb_o, hnL, hmR, hr_tl⟩
        refine ⟨hb_o,
                fun hm => (List.mem_cons.mp hm).elim (fun h0 => nomatch h0) hnL,
                show .R ∈ .B1 :: sweepCarryToR .T0 (s2 :: tl) from List.mem_cons_of_mem .B1 hmR,
                ?_⟩
        have hs0 : srsStepFromList all11OmitR2List
            (pre ++ [.T1, .B0] ++ (s2 :: tl)) ((pre ++ [.B1]) ++ [.T0] ++ (s2 :: tl)) :=
          ⟨pre, [.T1, .B0], [.B1, .T0], s2 :: tl, by decide,
           by simp [List.append_assoc], by simp [List.append_assoc]⟩
        simpa [sweepCarryToR, sweepCarryToRAux, List.append_assoc] using
          srsReaches_omitR2_trans (.step hs0 (.refl _)) hr_tl
      · rcases sweepCarryToR_sound (s2 :: tl) .T1 (Or.inr (Or.inl rfl)) (pre ++ [.B0]) hw with
          ⟨hb_o, hnL, hmR, hr_tl⟩
        refine ⟨hb_o,
                fun hm => (List.mem_cons.mp hm).elim (fun h0 => nomatch h0) hnL,
                show .R ∈ .B0 :: sweepCarryToR .T1 (s2 :: tl) from List.mem_cons_of_mem .B0 hmR,
                ?_⟩
        have hs0 : srsStepFromList all11OmitR2List
            (pre ++ [.T2, .B0] ++ (s2 :: tl)) ((pre ++ [.B0]) ++ [.T1] ++ (s2 :: tl)) :=
          ⟨pre, [.T2, .B0], [.B0, .T1], s2 :: tl, by decide,
           by simp [List.append_assoc], by simp [List.append_assoc]⟩
        simpa [sweepCarryToR, sweepCarryToRAux, List.append_assoc] using
          srsReaches_omitR2_trans (.step hs0 (.refl _)) hr_tl
    · -- `s = .B1`:
      rcases hc with rfl | rfl | rfl
      · rcases sweepCarryToR_sound (s2 :: tl) .T1 (Or.inr (Or.inl rfl)) (pre ++ [.B1]) hw with
          ⟨hb_o, hnL, hmR, hr_tl⟩
        refine ⟨hb_o,
                fun hm => (List.mem_cons.mp hm).elim (fun h0 => nomatch h0) hnL,
                show .R ∈ .B1 :: sweepCarryToR .T1 (s2 :: tl) from List.mem_cons_of_mem .B1 hmR,
                ?_⟩
        have hs0 : srsStepFromList all11OmitR2List
            (pre ++ [.T0, .B1] ++ (s2 :: tl)) ((pre ++ [.B1]) ++ [.T1] ++ (s2 :: tl)) :=
          ⟨pre, [.T0, .B1], [.B1, .T1], s2 :: tl, by decide,
           by simp [List.append_assoc], by simp [List.append_assoc]⟩
        simpa [sweepCarryToR, sweepCarryToRAux, List.append_assoc] using
          srsReaches_omitR2_trans (.step hs0 (.refl _)) hr_tl
      · rcases sweepCarryToR_sound (s2 :: tl) .T2 (Or.inr (Or.inr rfl)) (pre ++ [.B0]) hw with
          ⟨hb_o, hnL, hmR, hr_tl⟩
        refine ⟨hb_o,
                fun hm => (List.mem_cons.mp hm).elim (fun h0 => nomatch h0) hnL,
                show .R ∈ .B0 :: sweepCarryToR .T2 (s2 :: tl) from List.mem_cons_of_mem .B0 hmR,
                ?_⟩
        have hs0 : srsStepFromList all11OmitR2List
            (pre ++ [.T1, .B1] ++ (s2 :: tl)) ((pre ++ [.B0]) ++ [.T2] ++ (s2 :: tl)) :=
          ⟨pre, [.T1, .B1], [.B0, .T2], s2 :: tl, by decide,
           by simp [List.append_assoc], by simp [List.append_assoc]⟩
        simpa [sweepCarryToR, sweepCarryToRAux, List.append_assoc] using
          srsReaches_omitR2_trans (.step hs0 (.refl _)) hr_tl
      · rcases sweepCarryToR_sound (s2 :: tl) .T2 (Or.inr (Or.inr rfl)) (pre ++ [.B1]) hw with
          ⟨hb_o, hnL, hmR, hr_tl⟩
        refine ⟨hb_o,
                fun hm => (List.mem_cons.mp hm).elim (fun h0 => nomatch h0) hnL,
                show .R ∈ .B1 :: sweepCarryToR .T2 (s2 :: tl) from List.mem_cons_of_mem .B1 hmR,
                ?_⟩
        have hs0 : srsStepFromList all11OmitR2List
            (pre ++ [.T2, .B1] ++ (s2 :: tl)) ((pre ++ [.B1]) ++ [.T2] ++ (s2 :: tl)) :=
          ⟨pre, [.T2, .B1], [.B1, .T2], s2 :: tl, by decide,
           by simp [List.append_assoc], by simp [List.append_assoc]⟩
        simpa [sweepCarryToR, sweepCarryToRAux, List.append_assoc] using
          srsReaches_omitR2_trans (.step hs0 (.refl _)) hr_tl

/-- Mersenne `.R`-carrying binary suffix `mersenneAfterOnes t` (`t` sweeps of `.T2` starting from `[.R]`),
    so `mersenneDP2Chain m t := List.replicate (m - t) .B1 ++ mersenneAfterOnes t` executes `m`
    consecutive `.R`-carrying `leftAnchoredDP2Step` transitions! -/
def mersenneAfterOnes : Nat -> List MixedSRSSym
  | 0 => [.R]
  | t + 1 => sweepCarryToR .T2 (mersenneAfterOnes t)

def mersenneDP2Chain (m t : Nat) : List MixedSRSSym :=
  List.replicate (m - t) .B1 ++ mersenneAfterOnes t

private def countValBelow (M_feat : Nat) (V : Fin M_feat -> Nat) (val : Nat) : Nat :=
  natSumPrefix M_feat (fun i => if V i < val then 1 else 0) M_feat

private theorem countValBelow_lt_self (M_feat : Nat) (V : Fin M_feat -> Nat) (x : Fin M_feat) :
    countValBelow M_feat V (V x) < M_feat := by
  unfold countValBelow
  have hst : ∀ n : Nat, n ≤ M_feat ->
      natSumPrefix M_feat (fun i => if V i < V x then 1 else 0) n +
        (if x.val < n then 1 else 0) ≤ n := by
    intro n hn; induction n with
    | zero => simp [natSumPrefix]
    | succ n' ih =>
      have hn'_lt : n' < M_feat := hn
      simp only [natSumPrefix, hn'_lt, dite_true]
      have hp := ih (Nat.le_of_lt hn)
      by_cases hx : x.val = n'
      · have hxf : (⟨n', hn'_lt⟩ : Fin M_feat) = x := Fin.ext hx.symm
        rw [ite_false_of_w10 (by omega : ¬ (x.val < n'))] at hp
        rw [hxf, ite_false_of_w10 (Nat.lt_irrefl _),
            ite_true_of_w10 (by omega : x.val < n' + 1)]
        omega
      · have hle1 : (if V ⟨n', hn'_lt⟩ < V x then 1 else 0) ≤ 1 := by
          by_cases h : V ⟨n', hn'_lt⟩ < V x <;> simp [h]
        by_cases hl : x.val < n'
        · rw [ite_true_of_w10 hl] at hp; rw [ite_true_of_w10 (by omega : x.val < n' + 1)]; omega
        · rw [ite_false_of_w10 hl] at hp; rw [ite_false_of_w10 (by omega : ¬ (x.val < n' + 1))]; omega
  have hf := hst M_feat (Nat.le_refl _)
  rw [ite_true_of_w10 x.isLt] at hf
  omega

private theorem countValBelow_strict_mono (M_feat : Nat) (V : Fin M_feat -> Nat)
    (x y : Fin M_feat) (hxy : V x < V y) :
    countValBelow M_feat V (V x) < countValBelow M_feat V (V y) := by
  unfold countValBelow
  have hst : ∀ n : Nat, n ≤ M_feat ->
      natSumPrefix M_feat (fun i => if V i < V x then 1 else 0) n +
        (if x.val < n then 1 else 0) ≤
        natSumPrefix M_feat (fun i => if V i < V y then 1 else 0) n := by
    intro n hn; induction n with
    | zero => simp [natSumPrefix]
    | succ n' ih =>
      have hn'_lt : n' < M_feat := hn
      simp only [natSumPrefix, hn'_lt, dite_true]
      have hprev := ih (Nat.le_of_lt hn)
      by_cases heq_x : x.val = n'
      · have hxf : (⟨n', hn'_lt⟩ : Fin M_feat) = x := Fin.ext heq_x.symm
        rw [ite_false_of_w10 (by omega : ¬ (x.val < n'))] at hprev
        rw [hxf, ite_false_of_w10 (Nat.lt_irrefl (V x)), ite_true_of_w10 hxy,
            ite_true_of_w10 (by omega : x.val < n' + 1)]
        omega
      · have hterm_le : (if V ⟨n', hn'_lt⟩ < V x then 1 else 0) ≤
            (if V ⟨n', hn'_lt⟩ < V y then 1 else 0) := by
          by_cases hlt_vx : V ⟨n', hn'_lt⟩ < V x
          · rw [ite_true_of_w10 hlt_vx, ite_true_of_w10 (Nat.lt_trans hlt_vx hxy)]
            exact Nat.le_refl 1
          · rw [ite_false_of_w10 hlt_vx]; exact Nat.zero_le _
        by_cases hlx : x.val < n'
        · rw [ite_true_of_w10 hlx] at hprev
          rw [ite_true_of_w10 (by omega : x.val < n' + 1)]; omega
        · rw [ite_false_of_w10 hlx] at hprev
          rw [ite_false_of_w10 (by omega : ¬ (x.val < n' + 1))]; omega
  have hfin := hst M_feat (Nat.le_refl _)
  rw [ite_true_of_w10 x.isLt] at hfin
  omega

/--
  Theorem W13.1d (`leftAnchoredDP2_finite_feature_impossibility`,
  choice-free `zero custom axioms`):
  Universal Mersenne `.R`-Carrying Chain & Finite-Feature `.L`-to-`.R` Ranking Impossibility
  on `leftAnchoredDP2Step` (`Branch P4.3`, `W13_H1`):
  1. **Arbitrarily Long `.R`-Carrying Binary `DP2` Chains (`∀ m : Nat`)**:
     For EVERY `m : Nat` and EVERY `t < m`, `mersenneDP2Chain m t` is a pure `{.B0, .B1}`-plus-`[.R]`
     word (`isBinRTail`, `.R ∈ mersenneDP2Chain m t`) satisfying
     `leftAnchoredDP2Step (mersenneDP2Chain m t) (mersenneDP2Chain m (t + 1))`!
  2. **Universal Finite-Feature `.L`-to-`.R` Ranking Impossibility (`∀ M_feat ≥ 1`)**:
     NO finite-carrier feature abstraction `F : List MixedSRSSym -> Fin M_feat` (simultaneously
     subsuming arbitrary two-boundary `(u.take W_pref, u.reverse.take W_suf)` windows, `Q`-state
     two-way `.L`-to-`.R` automata, AND global `dp2GlobalOddVal u % P` congruence invariants!)
     composed with ANY `V : Fin M_feat -> Nat` can strictly orient `leftAnchoredDP2Step`
     (even when restricted solely to well-formed `.R`-carrying binary tails `isBinRTail u`)!
-/
theorem leftAnchoredDP2_finite_feature_impossibility :
    (∀ (m t : Nat), t ≤ m ->
      isBinRTail (mersenneDP2Chain m t) ∧
      .L ∉ mersenneDP2Chain m t ∧
      .R ∈ mersenneDP2Chain m t ∧
      (t < m -> leftAnchoredDP2Step (mersenneDP2Chain m t) (mersenneDP2Chain m (t + 1)))) ∧
    (∀ (M_feat : Nat) (_hM : M_feat ≥ 1)
       (F : List MixedSRSSym -> Fin M_feat) (V : Fin M_feat -> Nat),
      ¬ (∀ u1 u2 : List MixedSRSSym,
          isBinRTail u1 -> isBinRTail u2 ->
          leftAnchoredDP2Step u1 u2 -> V (F u2) < V (F u1))) := by
  have hafter : ∀ t : Nat,
      isBinRTail (mersenneAfterOnes t) ∧ .L ∉ mersenneAfterOnes t ∧ .R ∈ mersenneAfterOnes t := by
    intro t; induction t with
    | zero => exact ⟨trivial, by decide, by decide⟩
    | succ t' ih =>
      rcases sweepCarryToR_sound (mersenneAfterOnes t') .T2 (Or.inr (Or.inr rfl)) [] ih.1 with
        ⟨hb, hnL, hmR, _⟩
      exact ⟨hb, hnL, hmR⟩
  have hbin_rep : ∀ (k : Nat) (sfx : List MixedSRSSym),
      isBinRTail sfx -> .L ∉ sfx -> .R ∈ sfx ->
      isBinRTail (List.replicate k .B1 ++ sfx) ∧
      .L ∉ (List.replicate k .B1 ++ sfx) ∧
      .R ∈ (List.replicate k .B1 ++ sfx) := by
    intro k; induction k with
    | zero => intro sfx hb hn hr; simpa using ⟨hb, hn, hr⟩
    | succ k' ih =>
      intro sfx hb hn hr
      rcases ih sfx hb hn hr with ⟨hb', hn', hr'⟩
      simp only [List.replicate_succ, List.cons_append]
      exact ⟨hb', fun hm => (List.mem_cons.mp hm).elim (fun h0 => nomatch h0) hn',
             List.mem_cons_of_mem .B1 hr'⟩
  have hsweep_rep_B1 : ∀ (k : Nat) (pre sfx : List MixedSRSSym),
      srsReachesFromList all11OmitR2List
        (pre ++ [.T2] ++ (List.replicate k .B1 ++ sfx))
        (pre ++ List.replicate k .B1 ++ [.T2] ++ sfx) := by
    intro k; induction k with
    | zero => intro pre sfx; simp; exact .refl _
    | succ k' ih =>
      intro pre sfx
      have hs0 : srsStepFromList all11OmitR2List
          (pre ++ [.T2, .B1] ++ (List.replicate k' .B1 ++ sfx))
          ((pre ++ [.B1]) ++ [.T2] ++ (List.replicate k' .B1 ++ sfx)) :=
        ⟨pre, [.T2, .B1], [.B1, .T2], List.replicate k' .B1 ++ sfx, by decide,
         by simp [List.append_assoc], by simp [List.append_assoc]⟩
      have h1 : srsReachesFromList all11OmitR2List
          (pre ++ [.T2] ++ (List.replicate (k' + 1) .B1 ++ sfx))
          ((pre ++ [.B1]) ++ [.T2] ++ (List.replicate k' .B1 ++ sfx)) := by
        simpa [List.replicate_succ, List.append_assoc] using
          (srsReachesFromList.step hs0 (.refl _))
      have h2 := ih (pre ++ [.B1]) sfx
      simpa [List.replicate_succ, List.append_assoc] using srsReaches_omitR2_trans h1 h2
  have hchain : ∀ (m t : Nat), t ≤ m ->
      isBinRTail (mersenneDP2Chain m t) ∧
      .L ∉ mersenneDP2Chain m t ∧
      .R ∈ mersenneDP2Chain m t ∧
      (t < m -> leftAnchoredDP2Step (mersenneDP2Chain m t) (mersenneDP2Chain m (t + 1))) := by
    intro m t _hle
    rcases hafter t with ⟨hb_t, hn_t, hr_t⟩
    rcases hbin_rep (m - t) (mersenneAfterOnes t) hb_t hn_t hr_t with ⟨hb_c, hn_c, hr_c⟩
    refine ⟨hb_c, hn_c, hr_c, ?_⟩
    intro hlt
    rcases hafter (t + 1) with ⟨hb_t1, hn_t1, _⟩
    rcases hbin_rep (m - (t + 1)) (mersenneAfterOnes (t + 1)) hb_t1 hn_t1 (hafter (t + 1)).2.2 with
      ⟨_, hn_c1, _⟩
    refine ⟨hn_c, hn_c1, ?_⟩
    let k := m - (t + 1)
    have hmt : m - t = 1 + k := by dsimp [k]; omega
    have hu1_eq : [.L, .T2] ++ mersenneDP2Chain m t =
        [.L] ++ [.T2] ++ ([.B1] ++ (List.replicate k .B1 ++ mersenneAfterOnes t)) := by
      unfold mersenneDP2Chain
      rw [hmt, Nat.add_comm 1 k, List.replicate_succ]
      simp
    have hs_first : srsStepFromList all11OmitR2List
        ([.L] ++ [.T2, .B1] ++ (List.replicate k .B1 ++ mersenneAfterOnes t))
        ([.L, .B1] ++ [.T2] ++ (List.replicate k .B1 ++ mersenneAfterOnes t)) :=
      ⟨[.L], [.T2, .B1], [.B1, .T2], List.replicate k .B1 ++ mersenneAfterOnes t,
       by decide, by simp, by simp⟩
    have hr1 : srsReachesFromList all11OmitR2List
        ([.L, .T2] ++ mersenneDP2Chain m t)
        ([.L, .B1] ++ [.T2] ++ (List.replicate k .B1 ++ mersenneAfterOnes t)) := by
      rw [hu1_eq]
      simpa [List.append_assoc] using (srsReachesFromList.step hs_first (.refl _))
    have hr2 := hsweep_rep_B1 k [.L, .B1] (mersenneAfterOnes t)
    rcases sweepCarryToR_sound (mersenneAfterOnes t) .T2 (Or.inr (Or.inr rfl))
      ([.L, .B1] ++ List.replicate k .B1) hb_t with ⟨_, _, _, hr3⟩
    have hr_tot := srsReaches_omitR2_trans hr1 (srsReaches_omitR2_trans hr2 hr3)
    simpa [mersenneDP2Chain, mersenneAfterOnes, k, List.append_assoc] using hr_tot
  refine ⟨hchain, ?_⟩
  intro M_feat _hM F V hstrict
  have hwalk : ∀ t : Nat, t ≤ M_feat ->
      countValBelow M_feat V (V (F (mersenneDP2Chain M_feat t))) + t < M_feat := by
    intro t ht; induction t with
    | zero =>
      rw [Nat.add_zero]
      exact countValBelow_lt_self M_feat V (F (mersenneDP2Chain M_feat 0))
    | succ t' ih =>
      have hprev := ih (Nat.le_of_lt ht)
      rcases hchain M_feat t' (Nat.le_of_lt ht) with ⟨hb1, _, _, hdp⟩
      rcases hchain M_feat (t' + 1) ht with ⟨hb2, _, _, _⟩
      have hv_lt := hstrict _ _ hb1 hb2 (hdp ht)
      have hc_lt := countValBelow_strict_mono M_feat V _ _ hv_lt
      omega
  have hbad := hwalk M_feat (Nat.le_refl _)
  omega

/--
  Theorem W13.1e (`m1_dp2_mod_p_and_mersenne_511_cert`, `[]` axioms):
  Explicit `[]`-Axiom `.L`-to-`.R` `dp2GlobalOddVal`, `M1` (`19/5, 29/5, 251/13`) Mod-`p`
  Separation, & Mersenne `511 = 2^9 - 1` `DP2` Chain Certificate (`Branch P4.3`, `W13_H1`):
  1. `dp2GlobalOddVal` decodes `m1Tail0 0 -> 823`, `m1Tail3 0 -> 695`, `m129Tail825 -> 825`,
     `m129Tail697 -> 697`, and `mersenneDP2Chain 7 0 -> 511 -> ... -> mersenneDP2Chain 7 7 -> 8747`
     (with `collatzIter 8 511 = 13121`, `collatzIter 9 511 = 19682`, `collatzIter 10 511 = 9841`);
  2. `M1` rational cycle numerators violate odd-denominator divisibility (`19 % 5 = 4 ≠ 0`,
     `29 % 5 = 4 ≠ 0`, `251 % 13 = 4 ≠ 0`, with `2 ^ 8 - 3 ^ 5 = 13`) whereas every genuine
     encoded integer `n ∈ Z^+` satisfies `(D * n) % D = 0`!
-/
theorem m1_dp2_mod_p_and_mersenne_511_cert :
    dp2GlobalOddVal (m1Tail0 0) = 823 ∧
    dp2GlobalOddVal (m1Tail3 0) = 695 ∧
    dp2GlobalOddVal m129Tail825 = 825 ∧
    dp2GlobalOddVal m129Tail697 = 697 ∧
    dp2GlobalOddVal (mersenneDP2Chain 7 0) = 511 ∧
    dp2GlobalOddVal (mersenneDP2Chain 7 1) = 767 ∧
    dp2GlobalOddVal (mersenneDP2Chain 7 7) = 8747 ∧
    collatzIter 8 511 = 13121 ∧
    collatzIter 9 511 = 19682 ∧
    collatzIter 10 511 = 9841 ∧
    19 % 5 = 4 ∧ 29 % 5 = 4 ∧ 251 % 13 = 4 ∧
    2 ^ 8 - 3 ^ 5 = 13 := by decide

-- ============================================================================
-- SECTION 2: Front B (Branches P3.3 & P3.4) — Second-Order Three-Block `(U = 3)`
--            Mixed-Newton Confluent Divisibility & Confluent-Reduced Majorant Bound,
--            Rectangular `6 × 6` `(T = 2, U = 3)` Row-Side Vandermonde Divisibility
--            vs Square `9 × 9` `(T = 3, U = 3)` `(3, 5, 1)` Non-Divisibility by `7`,
--            Complete `6 × 6` `(T = 3, U = 2)` Zero Classification & Multi-`u`
--            Zero-Multiplicity `≤ 1`, & Universal `m`-Block Brox Carry Telescoping
--            Bound + Cross-Block Companion-Prime Squeeze
-- ============================================================================

-- ----------------------------------------------------------------------------
-- Section 2A: Second-Order Three-Block `(U = 3)` Mixed-Newton Confluent
--             Factorization & Strict Confluent-Reduced Majorant Bound
-- ----------------------------------------------------------------------------

def mixedNode (T P r : Nat) : Nat :=
  if r < T then 1 else if r < 2 * T then P else P * P

def mixedNewtonCoeff (T P : Nat) : Nat -> Nat -> Nat
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | x + 1, 0 => mixedNode T P 0 * mixedNewtonCoeff T P x 0
  | x + 1, r + 1 =>
    mixedNewtonCoeff T P x r + mixedNode T P (r + 1) * mixedNewtonCoeff T P x (r + 1)

def hasseNodePoly (T P : Nat) : Nat -> Nat -> Nat -> Nat
  | 0, _, 0 => 1
  | 0, _, _ + 1 => 0
  | r + 1, zv, 0 => (zv - mixedNode T P r) * hasseNodePoly T P r zv 0
  | r + 1, zv, t + 1 =>
    hasseNodePoly T P r zv t + (zv - mixedNode T P r) * hasseNodePoly T P r zv (t + 1)

def confluentFactorRank3 (T u : Nat) : Nat :=
  2 ^ ((3 * (T * (T - 1) / 2) + T * T) * u) *
    (2 ^ u - 1) ^ (3 * (T * T)) *
    (2 ^ u + 1) ^ (T * T)

private theorem natSumUpTo_congr_w13 (n : Nat) (f g : Nat -> Nat)
    (h : ∀ i : Nat, i < n -> f i = g i) : natSumUpTo n f = natSumUpTo n g := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [natSumUpTo]
    rw [ih (fun i hi => h i (Nat.lt_trans hi (Nat.lt_succ_self k))),
        h k (Nat.lt_succ_self k)]

private theorem natSumUpTo_mul_left_w13 (c n : Nat) (f : Nat -> Nat) :
    c * natSumUpTo n f = natSumUpTo n (fun i => c * f i) := by
  induction n with
  | zero => simp [natSumUpTo]
  | succ k ih => simp only [natSumUpTo, Nat.mul_add, ih]

private theorem two_mul_triNumNat_w13 : ∀ m : Nat, 2 * triNumNat m = m * (m - 1)
  | 0 => rfl
  | m + 1 => by
    simp only [triNumNat, Nat.add_sub_cancel]
    have ih := two_mul_triNumNat_w13 m
    cases m with
    | zero => simp [triNumNat]
    | succ m' =>
      simp only [Nat.add_sub_cancel] at ih
      rw [Nat.mul_add 2 (triNumNat (m' + 1)) (m' + 1), ih,
          Nat.mul_add (m' + 1 + 1) m' 1, Nat.add_mul (m' + 1) 1 m']
      omega

private theorem triNumNat_eq_div2_w13 (m : Nat) : triNumNat m = m * (m - 1) / 2 := by
  rw [← two_mul_triNumNat_w13 m, Nat.mul_div_right _ (by decide : 0 < 2)]

private theorem mixedNewtonCoeff_zero_right (T P : Nat) (hT : T ≥ 1) :
    ∀ x : Nat, mixedNewtonCoeff T P x 0 = 1
  | 0 => rfl
  | x + 1 => by
    have h0T : 0 < T := hT
    simp only [mixedNewtonCoeff, mixedNode, h0T, ite_true, Nat.one_mul,
               mixedNewtonCoeff_zero_right T P hT x]

private theorem mixedNewtonCoeff_mono_x (T P : Nat) (hT : T ≥ 1) (hP : P ≥ 1) :
    ∀ (x r : Nat), mixedNewtonCoeff T P x r ≤ mixedNewtonCoeff T P (x + 1) r
  | x, 0 => by
    rw [mixedNewtonCoeff_zero_right T P hT x, mixedNewtonCoeff_zero_right T P hT (x + 1)]
    exact Nat.le_refl 1
  | x, r + 1 => by
    simp only [mixedNewtonCoeff]
    have hn_pos : mixedNode T P (r + 1) ≥ 1 := by
      unfold mixedNode
      by_cases h1 : r + 1 < T
      · simp [h1]
      · by_cases h2 : r + 1 < 2 * T
        · simp [h1, h2, hP]
        · simp only [h1, h2, ite_false]; exact Nat.mul_le_mul hP hP
    have hm := Nat.mul_le_mul_right (mixedNewtonCoeff T P x (r + 1)) hn_pos
    omega

private theorem mixedNewtonCoeff_le_of_le (T P : Nat) (hT : T ≥ 1) (hP : P ≥ 1) :
    ∀ (x1 x2 r : Nat), x1 ≤ x2 -> mixedNewtonCoeff T P x1 r ≤ mixedNewtonCoeff T P x2 r := by
  intro x1 x2 r hle
  have hst : ∀ d : Nat, mixedNewtonCoeff T P x1 r ≤ mixedNewtonCoeff T P (x1 + d) r := by
    intro d; induction d with
    | zero => exact Nat.le_refl _
    | succ d' ih => exact Nat.le_trans ih (mixedNewtonCoeff_mono_x T P hT hP (x1 + d') r)
  simpa [show x1 + (x2 - x1) = x2 by omega] using hst (x2 - x1)

private theorem mixedNewtonCoeff_pos_of_le (T P : Nat) (hT : T ≥ 1) :
    ∀ (r x : Nat), r ≤ x -> mixedNewtonCoeff T P x r ≥ 1
  | 0, x, _ => by rw [mixedNewtonCoeff_zero_right T P hT x]; exact Nat.le_refl 1
  | r + 1, 0, h => by omega
  | r + 1, x + 1, h => by
    simp only [mixedNewtonCoeff]
    have ih := mixedNewtonCoeff_pos_of_le T P hT r x (by omega)
    omega

private theorem hasseNodePoly_zero_right_block0 (T P zv : Nat) :
    ∀ k : Nat, k ≤ T -> hasseNodePoly T P k zv 0 = (zv - 1) ^ k
  | 0, _ => rfl
  | k + 1, hk => by
    have hk_lt : k < T := hk
    simp only [hasseNodePoly, mixedNode, hk_lt, ite_true]
    rw [hasseNodePoly_zero_right_block0 T P zv k (Nat.le_of_lt hk),
        Nat.pow_succ, Nat.mul_comm]

private theorem hasseNodePoly_zero_right_block1 (T P zv : Nat) :
    ∀ k : Nat, k ≤ T -> hasseNodePoly T P (T + k) zv 0 = (zv - 1) ^ T * (zv - P) ^ k
  | 0, _ => by
    rw [Nat.add_zero, Nat.pow_zero, Nat.mul_one]
    exact hasseNodePoly_zero_right_block0 T P zv T (Nat.le_refl T)
  | k + 1, hk => by
    rw [Nat.add_succ]
    have hnot1 : ¬ (T + k < T) := by omega
    have hlt2 : T + k < 2 * T := by omega
    simp only [hasseNodePoly, mixedNode, hnot1, hlt2, ite_false, ite_true]
    rw [hasseNodePoly_zero_right_block1 T P zv k (Nat.le_of_lt hk), Nat.pow_succ]
    ac_rfl

private theorem hasseNodePoly_in_equal_block (T P b0 zv : Nat)
    (heq_node : ∀ s : Nat, s < T -> mixedNode T P (b0 + s) = zv) :
    ∀ (s t : Nat), s ≤ T ->
      hasseNodePoly T P (b0 + s) zv t =
        if s ≤ t then hasseNodePoly T P b0 zv (t - s) else 0
  | 0, t, _ => by simp
  | s + 1, 0, hsT => by
    rw [Nat.add_succ]
    simp only [hasseNodePoly, heq_node s hsT, Nat.sub_self, Nat.zero_mul]
    simp
  | s + 1, t + 1, hsT => by
    rw [Nat.add_succ]
    simp only [hasseNodePoly, heq_node s hsT, Nat.sub_self, Nat.zero_mul, Nat.add_zero]
    rw [hasseNodePoly_in_equal_block T P b0 zv heq_node s t (Nat.le_of_lt hsT)]
    by_cases hst : s ≤ t
    · have hst1 : s + 1 ≤ t + 1 := by omega
      rw [ite_true_of_w10 hst, ite_true_of_w10 hst1, show t + 1 - (s + 1) = t - s by omega]
    · have hst1 : ¬ (s + 1 ≤ t + 1) := by omega
      rw [ite_false_of_w10 hst, ite_false_of_w10 hst1]

private theorem hasseNodePoly_zero_after_block (T P b0 zv : Nat)
    (hz_base : ∀ t : Nat, t < T -> hasseNodePoly T P (b0 + T) zv t = 0) :
    ∀ (q t : Nat), t < T -> hasseNodePoly T P (b0 + T + q) zv t = 0
  | 0, t, ht => by simpa using hz_base t ht
  | q + 1, 0, ht => by
    rw [Nat.add_succ]
    simp only [hasseNodePoly, hasseNodePoly_zero_after_block T P b0 zv hz_base q 0 ht,
               Nat.mul_zero]
  | q + 1, t + 1, ht => by
    rw [Nat.add_succ]
    simp only [hasseNodePoly,
               hasseNodePoly_zero_after_block T P b0 zv hz_base q t (by omega),
               hasseNodePoly_zero_after_block T P b0 zv hz_base q (t + 1) ht,
               Nat.mul_zero, Nat.add_zero]

private theorem mixedNewton_hasse_col_identity (T P : Nat) (_hT : T ≥ 1) (hP : P ≥ 1) :
    ∀ (m t : Nat), m < 3 -> t < T ->
      let zv := if m = 0 then 1 else if m = 1 then P else P * P
      (∀ r : Nat, m * T + t < r -> hasseNodePoly T P r zv t = 0) ∧
      hasseNodePoly T P (m * T + t) zv t =
        (if m = 0 then 1 else if m = 1 then (P - 1) ^ T else P ^ T * (P - 1) ^ (2 * T) * (P + 1) ^ T) ∧
      (∀ x : Nat,
        zv ^ t * natSumUpTo (m * T + t + 1)
          (fun r => mixedNewtonCoeff T P x r * hasseNodePoly T P r zv t) =
        laurentInterpBinom x t * zv ^ x) := by
  intro m t hm3 htT
  dsimp only
  let zv := if m = 0 then 1 else if m = 1 then P else P * P
  have heq_blk : ∀ s : Nat, s < T -> mixedNode T P (m * T + s) = zv := by
    intro s hsT
    unfold mixedNode
    dsimp [zv]
    rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2) with rfl | rfl | rfl
    · simp [hsT]
    · simp only [Nat.one_mul, (by decide : ¬ ((1 : Nat) = 0)), ite_false, ite_true]
      have h1 : ¬ (T + s < T) := by omega
      have h2 : T + s < 2 * T := by omega
      simp [h1, h2]
    · have h1 : ¬ (2 * T + s < T) := by omega
      have h2 : ¬ (2 * T + s < 2 * T) := by omega
      simp [h1, h2]
  have hle_blk : ∀ r : Nat, r < m * T + T -> mixedNode T P r ≤ zv := by
    intro r hr_le
    unfold mixedNode
    dsimp [zv]
    rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2) with rfl | rfl | rfl
    · have hlt : r < T := by omega
      simp [hlt]
    · by_cases h1 : r < T
      · simp [h1, hP]
      · have h2 : r < 2 * T := by omega
        simp [h1, h2]
    · by_cases h1 : r < T
      · simp only [h1, ite_true]; simpa using Nat.mul_le_mul hP hP
      · by_cases h2 : r < 2 * T
        · simp only [h1, h2, ite_false]
          simpa using Nat.mul_le_mul_left P hP
        · simp [h1, h2]
  have hzero_gt_in_m : ∀ (m' t' r : Nat), m' < 3 -> t' < T -> m' * T + t' < r ->
      let zv' := if m' = 0 then 1 else if m' = 1 then P else P * P
      hasseNodePoly T P r zv' t' = 0 := by
    intro m' t' r hm' ht' hgt
    dsimp only
    let zv' := if m' = 0 then 1 else if m' = 1 then P else P * P
    have heq' : ∀ s : Nat, s < T -> mixedNode T P (m' * T + s) = zv' := by
      intro s hsT
      unfold mixedNode; dsimp [zv']
      rcases (by omega : m' = 0 ∨ m' = 1 ∨ m' = 2) with rfl | rfl | rfl
      · simp [hsT]
      · simp only [Nat.one_mul, (by decide : ¬ ((1 : Nat) = 0)), ite_false, ite_true]
        have h1 : ¬ (T + s < T) := by omega
        have h2 : T + s < 2 * T := by omega
        simp [h1, h2]
      · have h1 : ¬ (2 * T + s < T) := by omega
        have h2 : ¬ (2 * T + s < 2 * T) := by omega
        simp [h1, h2]
    by_cases hr_blk : r ≤ m' * T + T
    · have hrew : r = m' * T + (r - m' * T) := by omega
      rw [hrew, hasseNodePoly_in_equal_block T P (m' * T) zv' heq' (r - m' * T) t' (by omega),
          ite_false_of_w10 (by omega : ¬ (r - m' * T ≤ t'))]
    · have hz_end : ∀ u_t : Nat, u_t < T -> hasseNodePoly T P (m' * T + T) zv' u_t = 0 := by
        intro u_t hut
        rw [hasseNodePoly_in_equal_block T P (m' * T) zv' heq' T u_t (Nat.le_refl T),
            ite_false_of_w10 (by omega : ¬ (T ≤ u_t))]
      have hrew : r = m' * T + T + (r - (m' * T + T)) := by omega
      rw [hrew]
      exact hasseNodePoly_zero_after_block T P (m' * T) zv' hz_end (r - (m' * T + T)) t' ht'
  have hdiag : hasseNodePoly T P (m * T + t) zv t =
      (if m = 0 then 1 else if m = 1 then (P - 1) ^ T else P ^ T * (P - 1) ^ (2 * T) * (P + 1) ^ T) := by
    rw [hasseNodePoly_in_equal_block T P (m * T) zv heq_blk t t (Nat.le_of_lt htT),
        ite_true_of_w10 (Nat.le_refl t), Nat.sub_self]
    dsimp [zv]
    rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2) with rfl | rfl | rfl
    · simp [hasseNodePoly]
    · simp only [Nat.one_mul]
      have h := hasseNodePoly_zero_right_block0 T P P T (Nat.le_refl T)
      simpa using h
    · have hf : ¬ ((2 : Nat) = 0) ∧ ¬ ((2 : Nat) = 1) := by decide
      simp only [hf.1, hf.2, ite_false]
      have h := hasseNodePoly_zero_right_block1 T P (P * P) T (Nat.le_refl T)
      have hb2 : (P - 1) ^ (2 * T) = (P - 1) ^ T * (P - 1) ^ T := by
        rw [Nat.two_mul, Nat.pow_add]
      rw [hb2, show 2 * T = T + T by omega, h]
      have hpp1 : P * P - 1 = (P - 1) * (P + 1) := by
        cases P with
        | zero => rfl
        | succ p' =>
          calc (p' + 1) * (p' + 1) - 1
              = (p' * p' + 2 * p' + 1) - 1 := by
                  congr 1; rw [Nat.mul_add, Nat.add_mul]; omega
            _ = p' * p' + 2 * p' := Nat.add_sub_cancel _ 1
            _ = p' * (p' + 2) := by rw [Nat.mul_add, Nat.mul_comm p' 2]
      have hppp : P * P - P = P * (P - 1) := by
        cases P with
        | zero => omega
        | succ p' =>
          simp only [Nat.add_sub_cancel]
          rw [Nat.mul_add (p' + 1) p' 1, Nat.mul_one]
          omega
      have hmul_pow : ∀ (a b n : Nat), (a * b) ^ n = a ^ n * b ^ n := by
        intro a b n; induction n with
        | zero => simp
        | succ n' ih => rw [Nat.pow_succ, ih, Nat.pow_succ, Nat.pow_succ]; ac_rfl
      rw [hpp1, hppp, hmul_pow (P - 1) (P + 1) T, hmul_pow P (P - 1) T]
      ac_rfl
  refine ⟨fun r hr => hzero_gt_in_m m t r hm3 htT hr, hdiag, ?_⟩
  -- Prove `zv ^ t * ∑_{r=0}^{m*T+t} A(x, r) * hd(r, t) = C(x, t) * zv ^ x` for ALL `t < T` by induction on `x`:
  have hall_t : ∀ (x t0 : Nat), t0 < T ->
      zv ^ t0 * natSumUpTo (m * T + t0 + 1)
        (fun r => mixedNewtonCoeff T P x r * hasseNodePoly T P r zv t0) =
      laurentInterpBinom x t0 * zv ^ x := by
    intro x; induction x with
    | zero =>
      intro t0 _ht0
      -- For `x = 0`, `mixedNewtonCoeff T P 0 0 = 1` and `mixedNewtonCoeff T P 0 (r+1) = 0`:
      have hsum0 : ∀ n : Nat,
          natSumUpTo (n + 1) (fun r => mixedNewtonCoeff T P 0 r * hasseNodePoly T P r zv t0) =
            hasseNodePoly T P 0 zv t0 := by
        intro n; induction n with
        | zero => simp [natSumUpTo, mixedNewtonCoeff]
        | succ n' ihn =>
          conv => lhs; unfold natSumUpTo
          rw [ihn]; simp [mixedNewtonCoeff]
      rw [hsum0 (m * T + t0)]
      cases t0 with
      | zero => simp [hasseNodePoly, laurentInterpBinom]
      | succ t' => simp [hasseNodePoly, laurentInterpBinom]
    | succ x' ihx =>
      intro t0 ht0
      -- Summation-by-parts reindexing lemma for `natSumUpTo (c + 1)`:
      have hsbp : ∀ (c : Nat) (g : Nat -> Nat),
          natSumUpTo (c + 1) (fun r => mixedNewtonCoeff T P (x' + 1) r * g r) =
            natSumUpTo c (fun r =>
              mixedNewtonCoeff T P x' r * (mixedNode T P r * g r + g (r + 1))) +
            mixedNewtonCoeff T P x' c * (mixedNode T P c * g c) := by
        intro c g; induction c with
        | zero =>
          simp only [natSumUpTo, mixedNewtonCoeff, Nat.zero_add]
          ac_rfl
        | succ c' ihc =>
          conv => lhs; unfold natSumUpTo
          rw [ihc]
          simp only [mixedNewtonCoeff, Nat.add_mul]
          conv => rhs; lhs; unfold natSumUpTo
          dsimp only
          simp only [Nat.mul_add]
          ac_rfl
      cases t0 with
      | zero =>
        simp only [Nat.add_zero, Nat.pow_zero, Nat.one_mul, laurentInterpBinom_zero_right]
        rw [hsbp (m * T) (fun r => hasseNodePoly T P r zv 0)]
        have hterm0 : ∀ r : Nat, r < m * T ->
            mixedNode T P r * hasseNodePoly T P r zv 0 + hasseNodePoly T P (r + 1) zv 0 =
              zv * hasseNodePoly T P r zv 0 := by
          intro r hr_lt
          have hle := hle_blk r (by omega)
          simp only [hasseNodePoly, ← Nat.add_mul]
          rw [show mixedNode T P r + (zv - mixedNode T P r) = zv by omega]
        have htop0 : mixedNode T P (m * T) = zv := heq_blk 0 _hT
        have hrew_sum :
            natSumUpTo (m * T) (fun r =>
              mixedNewtonCoeff T P x' r *
                (mixedNode T P r * hasseNodePoly T P r zv 0 + hasseNodePoly T P (r + 1) zv 0)) +
              mixedNewtonCoeff T P x' (m * T) * (mixedNode T P (m * T) * hasseNodePoly T P (m * T) zv 0) =
            zv * natSumUpTo (m * T + 1)
              (fun r => mixedNewtonCoeff T P x' r * hasseNodePoly T P r zv 0) := by
          rw [natSumUpTo_congr_w13 (m * T) _
              (fun r => zv * (mixedNewtonCoeff T P x' r * hasseNodePoly T P r zv 0))
              (fun r hr => by rw [hterm0 r hr]; ac_rfl),
              ← natSumUpTo_mul_left_w13 zv, htop0]
          conv => rhs; rhs; unfold natSumUpTo
          rw [Nat.mul_add]
          congr 1; ac_rfl
        have ih0 := ihx 0 _hT
        simp only [Nat.add_zero, Nat.pow_zero, Nat.one_mul, laurentInterpBinom_zero_right] at ih0
        rw [hrew_sum, ih0, Nat.pow_succ, Nat.mul_comm]
      | succ t' =>
        let c := m * T + (t' + 1)
        change zv ^ (t' + 1) * natSumUpTo (c + 1)
            (fun r => mixedNewtonCoeff T P (x' + 1) r * hasseNodePoly T P r zv (t' + 1)) =
          laurentInterpBinom (x' + 1) (t' + 1) * zv ^ (x' + 1)
        rw [hsbp c (fun r => hasseNodePoly T P r zv (t' + 1))]
        have hterm_s : ∀ r : Nat, r < c ->
            mixedNode T P r * hasseNodePoly T P r zv (t' + 1) +
              hasseNodePoly T P (r + 1) zv (t' + 1) =
            hasseNodePoly T P r zv t' + zv * hasseNodePoly T P r zv (t' + 1) := by
          intro r hr_lt
          have hle := hle_blk r (by dsimp [c] at hr_lt; generalize m * T = MT at hr_lt ⊢; omega)
          simp only [hasseNodePoly]
          have hcomb : mixedNode T P r * hasseNodePoly T P r zv (t' + 1) +
              (zv - mixedNode T P r) * hasseNodePoly T P r zv (t' + 1) =
            zv * hasseNodePoly T P r zv (t' + 1) := by
            rw [← Nat.add_mul, show mixedNode T P r + (zv - mixedNode T P r) = zv by omega]
          calc
            mixedNode T P r * hasseNodePoly T P r zv (t' + 1) +
                (hasseNodePoly T P r zv t' + (zv - mixedNode T P r) * hasseNodePoly T P r zv (t' + 1))
                = hasseNodePoly T P r zv t' +
                    (mixedNode T P r * hasseNodePoly T P r zv (t' + 1) +
                     (zv - mixedNode T P r) * hasseNodePoly T P r zv (t' + 1)) := by ac_rfl
            _ = hasseNodePoly T P r zv t' + zv * hasseNodePoly T P r zv (t' + 1) := by rw [hcomb]
        have htop_c : mixedNode T P c = zv := heq_blk (t' + 1) ht0
        have hz_ct' : hasseNodePoly T P c zv t' = 0 :=
          hzero_gt_in_m m t' c hm3 (by omega) (by dsimp [c]; omega)
        have hsplit_sum : ∀ (n : Nat) (f1 f2 : Nat -> Nat),
            natSumUpTo n (fun r => f1 r + f2 r) = natSumUpTo n f1 + natSumUpTo n f2 := by
          intro n f1 f2; induction n with
          | zero => rfl
          | succ n' ihn => simp only [natSumUpTo, ihn]; omega
        have hrew_sum :
            natSumUpTo c (fun r =>
              mixedNewtonCoeff T P x' r *
                (mixedNode T P r * hasseNodePoly T P r zv (t' + 1) +
                 hasseNodePoly T P (r + 1) zv (t' + 1))) +
              mixedNewtonCoeff T P x' c * (mixedNode T P c * hasseNodePoly T P c zv (t' + 1)) =
            natSumUpTo c (fun r => mixedNewtonCoeff T P x' r * hasseNodePoly T P r zv t') +
              zv * natSumUpTo (c + 1)
                (fun r => mixedNewtonCoeff T P x' r * hasseNodePoly T P r zv (t' + 1)) := by
          rw [natSumUpTo_congr_w13 c _
              (fun r => mixedNewtonCoeff T P x' r * hasseNodePoly T P r zv t' +
                zv * (mixedNewtonCoeff T P x' r * hasseNodePoly T P r zv (t' + 1)))
              (fun r hr => by rw [hterm_s r hr, Nat.mul_add]; ac_rfl),
              hsplit_sum c, ← natSumUpTo_mul_left_w13 zv, htop_c]
          conv => rhs; rhs; rhs; unfold natSumUpTo
          rw [Nat.mul_add]
          have hc_mul : mixedNewtonCoeff T P x' c * (zv * hasseNodePoly T P c zv (t' + 1)) =
              zv * (mixedNewtonCoeff T P x' c * hasseNodePoly T P c zv (t' + 1)) := by ac_rfl
          rw [hc_mul, Nat.add_assoc]
        have hc_eq : c = m * T + t' + 1 := by dsimp [c]; omega
        have ih_t' := ihx t' (by omega)
        have ih_t1 := ihx (t' + 1) ht0
        rw [hrew_sum, Nat.mul_add (zv ^ (t' + 1))]
        have hp_t : zv ^ (t' + 1) * natSumUpTo c
              (fun r => mixedNewtonCoeff T P x' r * hasseNodePoly T P r zv t') =
            zv * (laurentInterpBinom x' t' * zv ^ x') := by
          rw [Nat.pow_succ zv t', Nat.mul_comm (zv ^ t') zv, Nat.mul_assoc zv, hc_eq, ih_t']
        have hp_t1 : zv ^ (t' + 1) * (zv * natSumUpTo (c + 1)
              (fun r => mixedNewtonCoeff T P x' r * hasseNodePoly T P r zv (t' + 1))) =
            zv * (laurentInterpBinom x' (t' + 1) * zv ^ x') := by
          calc
            zv ^ (t' + 1) * (zv * natSumUpTo (c + 1)
                (fun r => mixedNewtonCoeff T P x' r * hasseNodePoly T P r zv (t' + 1)))
                = zv * (zv ^ (t' + 1) * natSumUpTo (m * T + (t' + 1) + 1)
                    (fun r => mixedNewtonCoeff T P x' r * hasseNodePoly T P r zv (t' + 1))) := by
              dsimp [c]; ac_rfl
            _ = zv * (laurentInterpBinom x' (t' + 1) * zv ^ x') := by rw [ih_t1]
        rw [hp_t, hp_t1]
        have hpas : laurentInterpBinom (x' + 1) (t' + 1) =
            laurentInterpBinom x' t' + laurentInterpBinom x' (t' + 1) := by
          simp [laurentInterpBinom]
        rw [hpas, Nat.add_mul, Nat.pow_succ zv x']
        ac_rfl
  exact fun x => hall_t x t htT

private def intDiagProdPrefix (N : Nat) (U : Fin N -> Fin N -> Int) : Nat -> Int
  | 0 => 1
  | k + 1 =>
    if h : k < N then intDiagProdPrefix N U k * U ⟨k, h⟩ ⟨k, h⟩
    else intDiagProdPrefix N U k

private theorem intDet_mul_upper_tri (N : Nat) (A U : Fin N -> Fin N -> Int)
    (hupper : ∀ r c : Fin N, c.val < r.val -> U r c = 0) :
    intDet N (fun i j => intSumPrefix N (fun r => A i r * U r j) N) =
      intDiagProdPrefix N U N * intDet N A := by
  -- Notice `intSumPrefix N (fun r => A i r * U r j) N = intSumPrefix N (fun r => A i r * U r j) (j.val + 1)`:
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
    funext i j
    simp only [M_stage, Nat.not_lt_zero, ite_false]
    exact htrunc i j N (by omega) (Nat.le_refl N)
  have hN_eq : M_stage N = A := by
    funext i j
    dsimp [M_stage]
    rw [ite_true_of_w10 j.isLt]
  have hstep : ∀ k : Nat, k ≤ N ->
      intDet N (M_stage 0) = intDiagProdPrefix N U k * intDet N (M_stage k) := by
    intro k hk; induction k with
    | zero => simp [intDiagProdPrefix]
    | succ k' ih =>
      have hk'_lt : k' < N := hk
      let jk : Fin N := ⟨k', hk'_lt⟩
      rw [ih (Nat.le_of_lt hk)]
      let idxC : Nat -> Fin N := fun r => if h : r < N then ⟨r, h⟩ else jk
      let coefC : Nat -> Int := fun r => if h : r < N then U ⟨r, h⟩ jk else 0
      have hneC : ∀ r : Nat, r < k' -> idxC r ≠ jk := by
        intro r hr
        have hrN : r < N := by omega
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
          rw [Int.mul_comm (A i jk) (U jk jk)]
          omega
        · rw [ite_false_of_w10 hj, ite_false_of_w10 hj]
          have hjv : j.val ≠ k' := fun hv => hj (Fin.ext hv)
          dsimp [M_stage]
          by_cases hlt : j.val < k'
          · rw [ite_true_of_w10 hlt, ite_true_of_w10 (by omega)]
          · rw [ite_false_of_w10 hlt, ite_false_of_w10 (by omega)]
      rw [hcol_rew, intDet_col_scale (U jk jk) N jk (M_stage (k' + 1))]
      simp only [intDiagProdPrefix, hk'_lt, dite_true]
      exact (Int.mul_assoc (intDiagProdPrefix N U k') (U jk jk) _).symm
  rw [h0_eq, hstep N (Nat.le_refl N), hN_eq]

private theorem intDet_lower_tri :
    ∀ (N : Nat) (L_mat : Fin N -> Fin N -> Int),
      (∀ r c : Fin N, r.val < c.val -> L_mat r c = 0) ->
      intDet N L_mat = intDiagProdPrefix N L_mat N
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
      intro r c hlt
      have hskip : (skipFinIdx z0 c).val = c.val + 1 := by
        dsimp [skipFinIdx, z0]
      exact hlow ⟨r.val + 1, Nat.succ_lt_succ r.isLt⟩ (skipFinIdx z0 c) (by dsimp; omega)
    rw [intDet_lower_tri N (intSubMat L_mat z0) hsub_low]
    -- Show `L_mat z0 z0 * intDiagProdPrefix N (intSubMat L_mat z0) m = intDiagProdPrefix (N + 1) L_mat (m + 1)`:
    have hprod_shift : ∀ m : Nat, m ≤ N ->
        L_mat z0 z0 * intDiagProdPrefix N (intSubMat L_mat z0) m =
          intDiagProdPrefix (N + 1) L_mat (m + 1) := by
      intro m hm; induction m with
      | zero =>
        simp only [intDiagProdPrefix, Nat.zero_lt_succ, dite_true, Int.one_mul, Int.mul_one]
        rfl
      | succ m' ih =>
        have hm'_lt : m' < N := hm
        have hm1_lt : m' + 1 < N + 1 := Nat.succ_lt_succ hm'_lt
        simp only [intDiagProdPrefix, hm'_lt, hm1_lt, dite_true]
        rw [← Int.mul_assoc, ih (Nat.le_of_lt hm)]
        congr 1
    exact hprod_shift N (Nat.le_refl N)

private theorem intSumPrefix_eq_natSumUpTo (N : Nat) (f : Nat -> Nat) :
    ∀ m : Nat, m ≤ N ->
      intSumPrefix N (fun r => Int.ofNat (f r.val)) m = Int.ofNat (natSumUpTo m f)
  | 0, _ => rfl
  | m + 1, hm => by
    have hm_lt : m < N := hm
    conv => lhs; unfold intSumPrefix
    simp only [hm_lt, dite_true]
    rw [intSumPrefix_eq_natSumUpTo N f m (Nat.le_of_lt hm)]
    simp [natSumUpTo, Int.natCast_add]

/--
  Theorem W13.2a (`laurent_rank3_second_order_confluent_and_reduced_bound`,
  `zero custom axioms`):
  Universal Second-Order Three-Block `(U = 3)` Mixed-Newton Confluent Factorization
  `2^((3*(T*(T-1)/2) + T^2)*u) * (2^u - 1)^(3*T^2) * (2^u + 1)^(T^2) ∣ intDet (3*T) M0` &
  Strict Confluent-Reduced Majorant Bound Beating `intDet_natAbs_le_fact_mul_colProd`
  (`Branch P3.3`, `W13_H2`):
  1. **Exact `(3T) × (3T)` Mixed-Newton Determinant Factorization (`∀ W, K, T, u ≥ 1`)**:
     Every `(3T) × (3T)` zero-gap evaluation matrix `M0` on `laurentColsRank3OrderT T u`
     factors identically as `intDet (3 * T) M0 = Int.ofNat (confluentFactorRank3 T u) * intDet (3 * T) A_newton`
     where `A_newton i j = Int.ofNat (mixedNewtonCoeff T (2 ^ u) ((rows i).1 * W + (rows i).2 * K) j.val)`,
     upgrading Wave 12's `(2^u - 1)^(2*T^2)` three-block divisibility by an additional factor
     `2^(T^2 * u) * (2^u - 1)^(T^2)` to:
       `((2 ^ ((3 * (T * (T - 1) / 2) + T * T) * u) * (2 ^ u - 1) ^ (3 * (T * T)) *
         (2 ^ u + 1) ^ (T * T) : Nat) : Int) ∣ intDet (3 * T) M0`!
  2. **Canonical `9 × 9` `(T = 3, U = 3)` Second-Order Divisibility (`∀ W, K : Nat, ∀ u ≥ 1`)**:
       `((2 ^ (18 * u) * (2 ^ u - 1) ^ 27 * (2 ^ u + 1) ^ 9 : Nat) : Int) ∣ intDet 9 M0_9`!
  3. **Strict Confluent-Reduced Column-Majorant Upper Bound (`∀ T ≥ 1, u ≥ 1, X_max ≥ 3 * T`)**:
     Whenever `∀ i : Fin (3 * T), (rows i).1 * W + (rows i).2 * K ≤ X_max` (`X_max ≥ 3 * T`):
       `(intDet (3 * T) M0).natAbs ≤
         natFact (3 * T) * (confluentFactorRank3 T u *
           colBoundProdPrefix (3 * T) (fun j => mixedNewtonCoeff T (2 ^ u) X_max j.val) (3 * T))`
     AND this confluent-reduced majorant is **strictly smaller (`<`)** than the unfactored
     Hadamard–Laplace column-majorant bound `intDet_natAbs_le_fact_mul_colProd` across ALL
     `T ≥ 1, u ≥ 1, X_max ≥ 3 * T`!
-/
theorem laurent_rank3_second_order_confluent_and_reduced_bound :
    (∀ (W K T u : Nat) (rows : Fin (3 * T) -> Nat × Nat),
      T ≥ 1 -> u ≥ 1 ->
      let M0 : Fin (3 * T) -> Fin (3 * T) -> Int := fun i j =>
        (laurentZeroGapIntEntry W K (rows i).1 (rows i).2
          (laurentColsRank3OrderT T u j).1 (laurentColsRank3OrderT T u j).2 : Int)
      let A_newton : Fin (3 * T) -> Fin (3 * T) -> Int := fun i j =>
        Int.ofNat (mixedNewtonCoeff T (2 ^ u) ((rows i).1 * W + (rows i).2 * K) j.val)
      intDet (3 * T) M0 = Int.ofNat (confluentFactorRank3 T u) * intDet (3 * T) A_newton ∧
      ((confluentFactorRank3 T u : Nat) : Int) ∣ intDet (3 * T) M0) ∧
    (∀ (W K u : Nat), u ≥ 1 ->
      let M0_9 : Fin 9 -> Fin 9 -> Int := fun i j =>
        (laurentZeroGapIntEntry W K (laurentRowsTwoBase9 i).1 (laurentRowsTwoBase9 i).2
          (laurentColsC33_9 u j).1 (laurentColsC33_9 u j).2 : Int)
      ((2 ^ (18 * u) * (2 ^ u - 1) ^ 27 * (2 ^ u + 1) ^ 9 : Nat) : Int) ∣ intDet 9 M0_9) ∧
    (∀ (W K T u X_max : Nat) (rows : Fin (3 * T) -> Nat × Nat),
      T ≥ 1 -> u ≥ 1 -> X_max ≥ 3 * T ->
      (∀ i : Fin (3 * T), (rows i).1 * W + (rows i).2 * K ≤ X_max) ->
      let M0 : Fin (3 * T) -> Fin (3 * T) -> Int := fun i j =>
        (laurentZeroGapIntEntry W K (rows i).1 (rows i).2
          (laurentColsRank3OrderT T u j).1 (laurentColsRank3OrderT T u j).2 : Int)
      let redProd := confluentFactorRank3 T u *
        colBoundProdPrefix (3 * T) (fun j => mixedNewtonCoeff T (2 ^ u) X_max j.val) (3 * T)
      let rawProd := colBoundProdPrefix (3 * T)
        (fun j => laurentInterpBinom X_max (laurentColsRank3OrderT T u j).1 *
          2 ^ (X_max * (laurentColsRank3OrderT T u j).2)) (3 * T)
      (intDet (3 * T) M0).natAbs ≤ natFact (3 * T) * redProd ∧
      redProd < rawProd) := by
  -- Core decomposition for any `T ≥ 1, u ≥ 1`:
  have hcore : ∀ (T u : Nat), T ≥ 1 -> u ≥ 1 ->
      let P := 2 ^ u
      let U_nat : Fin (3 * T) -> Fin (3 * T) -> Nat := fun r c =>
        let m := c.val / T
        let t := c.val % T
        let zv := if m = 0 then 1 else if m = 1 then P else P * P
        zv ^ t * hasseNodePoly T P r.val zv t
      (∀ r c : Fin (3 * T), c.val < r.val -> U_nat r c = 0) ∧
      colBoundProdPrefix (3 * T) (fun c => U_nat c c) (3 * T) = confluentFactorRank3 T u ∧
      (∀ (x : Nat) (c : Fin (3 * T)),
        natSumUpTo (3 * T) (fun r =>
          if hr : r < 3 * T then mixedNewtonCoeff T P x r * U_nat ⟨r, hr⟩ c else 0) =
        laurentInterpBinom x (laurentColsRank3OrderT T u c).1 *
          2 ^ (x * (laurentColsRank3OrderT T u c).2)) := by
    intro T u hT hu
    dsimp only
    let P := 2 ^ u
    have hP_ge2 : P ≥ 2 := by dsimp [P]; simpa using pow2_mono_nat hu
    have hP_ge1 : P ≥ 1 := by omega
    let U_nat : Fin (3 * T) -> Fin (3 * T) -> Nat := fun r c =>
      let m := c.val / T
      let t := c.val % T
      let zv := if m = 0 then 1 else if m = 1 then P else P * P
      zv ^ t * hasseNodePoly T P r.val zv t
    -- Helper splitting `c.val = (c.val / T) * T + c.val % T`:
    have hc_div : ∀ c : Fin (3 * T),
        c.val / T < 3 ∧ c.val % T < T ∧ (c.val / T) * T + c.val % T = c.val ∧
        laurentColsRank3OrderT T u c = (c.val % T, (c.val / T) * u) := by
      intro c
      have hlt3T := c.isLt
      have hmod_lt : c.val % T < T := Nat.mod_lt c.val hT
      have hdiv_eq : T * (c.val / T) + c.val % T = c.val := Nat.div_add_mod c.val T
      have hdiv_lt3 : c.val / T < 3 := by
        by_cases h : c.val / T < 3
        · exact h
        · have hm : T * 3 ≤ T * (c.val / T) := Nat.mul_le_mul_left T (by omega : 3 ≤ c.val / T)
          rw [Nat.mul_comm T 3] at hm
          omega
      refine ⟨hdiv_lt3, hmod_lt, by rw [Nat.mul_comm]; exact hdiv_eq, ?_⟩
      unfold laurentColsRank3OrderT
      rcases (by generalize c.val / T = q at hdiv_lt3 ⊢; omega :
        c.val / T = 0 ∨ c.val / T = 1 ∨ c.val / T = 2) with hd0 | hd1 | hd2
      · rw [hd0] at hdiv_eq ⊢
        have hc_lt : c.val < T := by omega
        simp [hc_lt]; omega
      · rw [hd1] at hdiv_eq ⊢
        have h1 : ¬ (c.val < T) := by omega
        have h2 : c.val < 2 * T := by omega
        simp [h1, h2]; omega
      · rw [hd2] at hdiv_eq ⊢
        have h1 : ¬ (c.val < T) := by omega
        have h2 : ¬ (c.val < 2 * T) := by omega
        simp [h1, h2]; omega
    have hupper_nat : ∀ r c : Fin (3 * T), c.val < r.val -> U_nat r c = 0 := by
      intro r c hlt
      rcases hc_div c with ⟨hm3, htT, hceq, _⟩
      rcases mixedNewton_hasse_col_identity T P hT hP_ge1 (c.val / T) (c.val % T) hm3 htT with
        ⟨hz_gt, _, _⟩
      dsimp [U_nat]
      rw [hz_gt r.val (by omega), Nat.mul_zero]
    -- Product of diagonal entries `∏_{c < 3T} U_nat c c = confluentFactorRank3 T u`:
    have hdiag_val : ∀ c : Fin (3 * T),
        U_nat c c =
          let m := c.val / T
          let t := c.val % T
          if m = 0 then 1
          else if m = 1 then P ^ t * (P - 1) ^ T
          else P ^ (2 * t + T) * (P - 1) ^ (2 * T) * (P + 1) ^ T := by
      intro c
      rcases hc_div c with ⟨hm3, htT, hceq, _⟩
      rcases mixedNewton_hasse_col_identity T P hT hP_ge1 (c.val / T) (c.val % T) hm3 htT with
        ⟨_, hdiag_c, _⟩
      rw [hceq] at hdiag_c
      dsimp [U_nat]
      rw [hdiag_c]
      rcases (by generalize c.val / T = q at hm3 ⊢; omega :
        c.val / T = 0 ∨ c.val / T = 1 ∨ c.val / T = 2) with hm0 | hm1 | hm2
      · simp [hm0]
      · simp [hm1]
      · have hf0 : ¬ ((2 : Nat) = 0) := by decide
        have hf1 : ¬ ((2 : Nat) = 1) := by decide
        simp only [hm2, hf0, hf1, ite_false]
        have hp2 : (P * P) ^ (c.val % T) = P ^ (2 * (c.val % T)) := by
          rw [← Nat.pow_two P, pow_pow_eq_mul_w5 P 2 (c.val % T)]
        rw [hp2]
        have hp_add : P ^ (2 * (c.val % T)) * P ^ T = P ^ (2 * (c.val % T) + T) :=
          (Nat.pow_add P _ T).symm
        calc
          P ^ (2 * (c.val % T)) * (P ^ T * (P - 1) ^ (2 * T) * (P + 1) ^ T)
              = (P ^ (2 * (c.val % T)) * P ^ T) * (P - 1) ^ (2 * T) * (P + 1) ^ T := by ac_rfl
          _ = P ^ (2 * (c.val % T) + T) * (P - 1) ^ (2 * T) * (P + 1) ^ T := by rw [hp_add]
    have hprod_b0 : ∀ k : Nat, k ≤ T ->
        colBoundProdPrefix (3 * T) (fun c => U_nat c c) k = 1 := by
      intro k hk; induction k with
      | zero => rfl
      | succ k' ih =>
        have hk_lt : k' < 3 * T := by omega
        simp only [colBoundProdPrefix, hk_lt, dite_true, ih (Nat.le_of_lt hk), Nat.one_mul]
        rw [hdiag_val ⟨k', hk_lt⟩]
        have hd0 : k' / T = 0 := Nat.div_eq_of_lt hk
        simp [hd0]
    have hprod_b1 : ∀ k : Nat, k ≤ T ->
        colBoundProdPrefix (3 * T) (fun c => U_nat c c) (T + k) =
          P ^ (triNumNat k) * (P - 1) ^ (k * T) := by
      intro k hk; induction k with
      | zero => simp [triNumNat, hprod_b0 T (Nat.le_refl T)]
      | succ k' ih =>
        rw [Nat.add_succ]
        have hk_lt : T + k' < 3 * T := by omega
        simp only [colBoundProdPrefix, hk_lt, dite_true, ih (Nat.le_of_lt hk)]
        rw [hdiag_val ⟨T + k', hk_lt⟩]
        have hd1 : (T + k') / T = 1 := by
          have := Nat.add_mul_div_right k' 1 hT
          rw [Nat.one_mul, Nat.add_comm k' T, Nat.div_eq_of_lt hk] at this
          exact this
        have hm1 : (T + k') % T = k' := by
          have := Nat.div_add_mod (T + k') T
          rw [hd1, Nat.mul_one] at this; omega
        dsimp only
        rw [hd1, hm1]
        have hf0 : ¬ ((1 : Nat) = 0) := by decide
        simp only [hf0, ite_false, ite_true, triNumNat]
        rw [Nat.pow_add P (triNumNat k') k', show (k' + 1) * T = k' * T + T by rw [Nat.add_mul, Nat.one_mul],
            Nat.pow_add (P - 1) (k' * T) T]
        ac_rfl
    have hprod_b2 : ∀ k : Nat, k ≤ T ->
        colBoundProdPrefix (3 * T) (fun c => U_nat c c) (2 * T + k) =
          P ^ (triNumNat T + 2 * triNumNat k + k * T) *
            (P - 1) ^ (T * T + k * (2 * T)) *
            (P + 1) ^ (k * T) := by
      intro k hk; induction k with
      | zero =>
        simp [triNumNat, show 2 * T = T + T by omega, hprod_b1 T (Nat.le_refl T)]
      | succ k' ih =>
        rw [Nat.add_succ]
        have hk_lt : 2 * T + k' < 3 * T := by omega
        simp only [colBoundProdPrefix, hk_lt, dite_true, ih (Nat.le_of_lt hk)]
        rw [hdiag_val ⟨2 * T + k', hk_lt⟩]
        have hd2 : (2 * T + k') / T = 2 := by
          have := Nat.add_mul_div_right k' 2 hT
          rw [Nat.add_comm k' (2 * T), Nat.div_eq_of_lt hk, Nat.zero_add] at this
          exact this
        have hm2 : (2 * T + k') % T = k' := by
          have := Nat.div_add_mod (2 * T + k') T
          rw [hd2] at this; omega
        dsimp only
        rw [hd2, hm2]
        have hf0 : ¬ ((2 : Nat) = 0) := by decide
        have hf1 : ¬ ((2 : Nat) = 1) := by decide
        simp only [hf0, hf1, ite_false]
        let ep := triNumNat T + 2 * triNumNat k' + k' * T
        let eb := T * T + k' * (2 * T)
        have hp_e : triNumNat T + 2 * triNumNat (k' + 1) + (k' + 1) * T =
            ep + (2 * k' + T) := by
          dsimp [ep]; simp only [triNumNat, Nat.mul_add, Nat.add_mul, Nat.one_mul]; omega
        have hb_e : T * T + (k' + 1) * (2 * T) = eb + 2 * T := by
          dsimp [eb]; rw [Nat.add_mul k' 1 (2 * T), Nat.one_mul]; omega
        have hc_e : (k' + 1) * T = k' * T + T := by rw [Nat.add_mul, Nat.one_mul]
        change P ^ ep * (P - 1) ^ eb * (P + 1) ^ (k' * T) *
            (P ^ (2 * k' + T) * (P - 1) ^ (2 * T) * (P + 1) ^ T) = _
        rw [hp_e, hb_e, hc_e, Nat.pow_add P ep (2 * k' + T),
            Nat.pow_add (P - 1) eb (2 * T), Nat.pow_add (P + 1) (k' * T) T]
        ac_rfl
    have hprod_all : colBoundProdPrefix (3 * T) (fun c => U_nat c c) (3 * T) =
        confluentFactorRank3 T u := by
      have hend := hprod_b2 T (Nat.le_refl T)
      rw [show 2 * T + T = 3 * T by omega] at hend
      rw [hend]
      unfold confluentFactorRank3
      dsimp [P]
      have htri : triNumNat T + 2 * triNumNat T + T * T = 3 * (T * (T - 1) / 2) + T * T := by
        rw [triNumNat_eq_div2_w13 T]; omega
      have hb3 : T * T + T * (2 * T) = 3 * (T * T) := by
        rw [Nat.mul_comm T (2 * T), Nat.mul_assoc 2 T T]; omega
      rw [htri, hb3, pow_pow_eq_mul_w5 2 u, Nat.mul_comm u]
    refine ⟨hupper_nat, hprod_all, ?_⟩
    intro x c
    rcases hc_div c with ⟨hm3, htT, hceq, hcol_eq⟩
    rcases mixedNewton_hasse_col_identity T P hT hP_ge1 (c.val / T) (c.val % T) hm3 htT with
      ⟨hz_gt, _, hsum_id⟩
    -- Truncate `natSumUpTo (3 * T)` down to `natSumUpTo (c.val + 1)`:
    have htrunc_nat : ∀ n : Nat, c.val + 1 ≤ n -> n ≤ 3 * T ->
        natSumUpTo n (fun r =>
          if hr : r < 3 * T then mixedNewtonCoeff T P x r * U_nat ⟨r, hr⟩ c else 0) =
        natSumUpTo (c.val + 1) (fun r =>
          if hr : r < 3 * T then mixedNewtonCoeff T P x r * U_nat ⟨r, hr⟩ c else 0) := by
      intro n hge hle
      have hst : ∀ d : Nat, c.val + 1 + d ≤ 3 * T ->
          natSumUpTo (c.val + 1 + d) (fun r =>
            if hr : r < 3 * T then mixedNewtonCoeff T P x r * U_nat ⟨r, hr⟩ c else 0) =
          natSumUpTo (c.val + 1) (fun r =>
            if hr : r < 3 * T then mixedNewtonCoeff T P x r * U_nat ⟨r, hr⟩ c else 0) := by
        intro d hd; induction d with
        | zero => rfl
        | succ d' ih =>
          rw [Nat.add_succ]
          have hlt : c.val + 1 + d' < 3 * T := hd
          conv => lhs; unfold natSumUpTo
          simp only [hlt, dite_true]
          rw [ih (by omega), hupper_nat ⟨c.val + 1 + d', hlt⟩ c (by dsimp; omega),
              Nat.mul_zero, Nat.add_zero]
      simpa [show c.val + 1 + (n - (c.val + 1)) = n by omega] using hst (n - (c.val + 1)) (by omega)
    rw [htrunc_nat (3 * T) (by omega) (Nat.le_refl _)]
    let zv := if c.val / T = 0 then 1 else if c.val / T = 1 then P else P * P
    have hcongr : natSumUpTo (c.val + 1) (fun r =>
          if hr : r < 3 * T then mixedNewtonCoeff T P x r * U_nat ⟨r, hr⟩ c else 0) =
        zv ^ (c.val % T) * natSumUpTo (c.val + 1)
          (fun r => mixedNewtonCoeff T P x r * hasseNodePoly T P r zv (c.val % T)) := by
      rw [natSumUpTo_mul_left_w13 (zv ^ (c.val % T))]
      apply natSumUpTo_congr_w13; intro r hr_lt
      have hr3T : r < 3 * T := by have := c.isLt; omega
      simp only [hr3T, dite_true]
      dsimp [U_nat, zv]
      ac_rfl
    have hsum_c := hsum_id x
    rw [hceq] at hsum_c
    rw [hcongr, hsum_c, hcol_eq]
    dsimp only [zv, P]
    rcases (by generalize c.val / T = q at hm3 ⊢; omega :
      c.val / T = 0 ∨ c.val / T = 1 ∨ c.val / T = 2) with hd0 | hd1 | hd2
    · simp [hd0]
    · simp only [hd1, (by decide : ¬ ((1 : Nat) = 0)), ite_false, ite_true, Nat.one_mul]
      rw [pow_pow_eq_mul_w5 2 u x, Nat.mul_comm u x]
    · simp only [hd2, (by decide : ¬ ((2 : Nat) = 0)), (by decide : ¬ ((2 : Nat) = 1)), ite_false]
      have hp22 : (2 ^ u * 2 ^ u) ^ x = 2 ^ (x * (2 * u)) := by
        rw [← Nat.pow_two (2 ^ u), pow_pow_eq_mul_w5 2 u 2,
            pow_pow_eq_mul_w5 2 (u * 2) x, show u * 2 * x = x * (2 * u) by ac_rfl]
      rw [hp22]
  refine ⟨?_, ?_, ?_⟩
  · -- Part 1: Exact `(3T) × (3T)` determinant factorization & divisibility:
    intro W K T u rows hT hu
    dsimp only
    rcases hcore T u hT hu with ⟨hup_n, hprod_n, hmat_n⟩
    let P := 2 ^ u
    let A_newton : Fin (3 * T) -> Fin (3 * T) -> Int := fun i j =>
      Int.ofNat (mixedNewtonCoeff T P ((rows i).1 * W + (rows i).2 * K) j.val)
    let U_int : Fin (3 * T) -> Fin (3 * T) -> Int := fun r c =>
      let m := c.val / T
      let t := c.val % T
      let zv := if m = 0 then 1 else if m = 1 then P else P * P
      Int.ofNat (zv ^ t * hasseNodePoly T P r.val zv t)
    have hup_i : ∀ r c : Fin (3 * T), c.val < r.val -> U_int r c = 0 := by
      intro r c hlt
      have h0n := hup_n r c hlt
      dsimp only at h0n
      dsimp only [U_int, P]
      rw [h0n]; rfl
    have hM0_eq : (fun i j : Fin (3 * T) =>
        (laurentZeroGapIntEntry W K (rows i).1 (rows i).2
          (laurentColsRank3OrderT T u j).1 (laurentColsRank3OrderT T u j).2 : Int)) =
        (fun i j : Fin (3 * T) => intSumPrefix (3 * T) (fun r => A_newton i r * U_int r j) (3 * T)) := by
      funext i j
      let x := (rows i).1 * W + (rows i).2 * K
      have h1 : intSumPrefix (3 * T) (fun r => A_newton i r * U_int r j) (3 * T) =
          Int.ofNat (natSumUpTo (3 * T) (fun r =>
            if hr : r < 3 * T then
              mixedNewtonCoeff T P x r *
                ((if j.val / T = 0 then 1 else if j.val / T = 1 then P else P * P) ^ (j.val % T) *
                 hasseNodePoly T P r (if j.val / T = 0 then 1 else if j.val / T = 1 then P else P * P) (j.val % T))
            else 0)) := by
        have hst : ∀ m : Nat, m ≤ 3 * T ->
            intSumPrefix (3 * T) (fun r => A_newton i r * U_int r j) m =
              Int.ofNat (natSumUpTo m (fun r =>
                if hr : r < 3 * T then
                  mixedNewtonCoeff T P x r *
                    ((if j.val / T = 0 then 1 else if j.val / T = 1 then P else P * P) ^ (j.val % T) *
                     hasseNodePoly T P r (if j.val / T = 0 then 1 else if j.val / T = 1 then P else P * P) (j.val % T))
                else 0)) := by
          intro m hm; induction m with
          | zero => rfl
          | succ m' ih =>
            have hm_lt : m' < 3 * T := hm
            conv => lhs; unfold intSumPrefix
            conv => rhs; rhs; unfold natSumUpTo
            simp only [hm_lt, dite_true]
            rw [ih (Nat.le_of_lt hm)]
            rfl
        exact hst (3 * T) (Nat.le_refl _)
      rw [h1, hmat_n x j]
      rfl
    have hdiag_i : ∀ m : Nat, m ≤ 3 * T ->
        intDiagProdPrefix (3 * T) U_int m =
          Int.ofNat (colBoundProdPrefix (3 * T) (fun c =>
            let mb := c.val / T
            let t := c.val % T
            let zv := if mb = 0 then 1 else if mb = 1 then P else P * P
            zv ^ t * hasseNodePoly T P c.val zv t) m) := by
      intro m hm; induction m with
      | zero => rfl
      | succ m' ih =>
        have hm_lt : m' < 3 * T := hm
        conv => lhs; unfold intDiagProdPrefix
        conv => rhs; rhs; unfold colBoundProdPrefix
        simp only [hm_lt, dite_true]
        rw [ih (Nat.le_of_lt hm)]
        rfl
    rw [hM0_eq, intDet_mul_upper_tri (3 * T) A_newton U_int hup_i,
        hdiag_i (3 * T) (Nat.le_refl _), hprod_n]
    exact ⟨rfl, ⟨intDet (3 * T) A_newton, rfl⟩⟩
  · -- Part 2: `9 × 9` specialization (`T = 3`):
    intro W K u hu
    dsimp only
    rcases hcore 3 u (by decide) hu with ⟨hup_n, hprod_n, hmat_n⟩
    -- Note `3 * 3 = 9` and `laurentColsRank3OrderT 3 u = laurentColsC33_9 u`:
    let P := 2 ^ u
    let A9 : Fin 9 -> Fin 9 -> Int := fun i j =>
      Int.ofNat (mixedNewtonCoeff 3 P ((laurentRowsTwoBase9 i).1 * W + (laurentRowsTwoBase9 i).2 * K) j.val)
    let U9 : Fin 9 -> Fin 9 -> Int := fun r c =>
      let m := c.val / 3
      let t := c.val % 3
      let zv := if m = 0 then 1 else if m = 1 then P else P * P
      Int.ofNat (zv ^ t * hasseNodePoly 3 P r.val zv t)
    have hc9_eq : ∀ j : Fin 9, laurentColsC33_9 u j = laurentColsRank3OrderT 3 u j := by
      intro j
      rcases (by have := j.isLt; omega :
        j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 ∨ j.val = 4 ∨
        j.val = 5 ∨ j.val = 6 ∨ j.val = 7 ∨ j.val = 8) with
        h | h | h | h | h | h | h | h | h <;>
      · simp [laurentColsC33_9, laurentColsRank3OrderT, h]
    have hM9_eq : (fun i j : Fin 9 =>
        (laurentZeroGapIntEntry W K (laurentRowsTwoBase9 i).1 (laurentRowsTwoBase9 i).2
          (laurentColsC33_9 u j).1 (laurentColsC33_9 u j).2 : Int)) =
        (fun i j : Fin 9 => intSumPrefix 9 (fun r => A9 i r * U9 r j) 9) := by
      funext i j
      rw [hc9_eq j]
      let x := (laurentRowsTwoBase9 i).1 * W + (laurentRowsTwoBase9 i).2 * K
      have hst : ∀ m : Nat, m ≤ 9 ->
          intSumPrefix 9 (fun r => A9 i r * U9 r j) m =
            Int.ofNat (natSumUpTo m (fun r =>
              if hr : r < 9 then
                mixedNewtonCoeff 3 P x r *
                  ((if j.val / 3 = 0 then 1 else if j.val / 3 = 1 then P else P * P) ^ (j.val % 3) *
                   hasseNodePoly 3 P r (if j.val / 3 = 0 then 1 else if j.val / 3 = 1 then P else P * P) (j.val % 3))
              else 0)) := by
        intro m hm; induction m with
        | zero => rfl
        | succ m' ih =>
          have hm_lt : m' < 9 := hm
          conv => lhs; unfold intSumPrefix
          conv => rhs; rhs; unfold natSumUpTo
          simp only [hm_lt, dite_true]
          rw [ih (Nat.le_of_lt hm)]
          rfl
      rw [hst 9 (Nat.le_refl 9), hmat_n x j]
      rfl
    have hup9 : ∀ r c : Fin 9, c.val < r.val -> U9 r c = 0 := by
      intro r c hlt
      have h0n := hup_n r c hlt
      dsimp only at h0n
      dsimp only [U9, P]; rw [h0n]; rfl
    have hdiag9 : ∀ m : Nat, m ≤ 9 ->
        intDiagProdPrefix 9 U9 m =
          Int.ofNat (colBoundProdPrefix 9 (fun c =>
            let mb := c.val / 3
            let t := c.val % 3
            let zv := if mb = 0 then 1 else if mb = 1 then P else P * P
            zv ^ t * hasseNodePoly 3 P c.val zv t) m) := by
      intro m hm; induction m with
      | zero => rfl
      | succ m' ih =>
        have hm_lt : m' < 9 := hm
        conv => lhs; unfold intDiagProdPrefix
        conv => rhs; rhs; unfold colBoundProdPrefix
        simp only [hm_lt, dite_true]
        rw [ih (Nat.le_of_lt hm)]
        rfl
    rw [hM9_eq, intDet_mul_upper_tri 9 A9 U9 hup9, hdiag9 9 (Nat.le_refl 9), hprod_n]
    have hexp9 : confluentFactorRank3 3 u = 2 ^ (18 * u) * (2 ^ u - 1) ^ 27 * (2 ^ u + 1) ^ 9 := by
      unfold confluentFactorRank3; rfl
    rw [hexp9]
    exact ⟨intDet 9 A9, rfl⟩
  · -- Part 3: Confluent-reduced column-majorant bound `<` Hadamard–Laplace `rawProd`:
    intro W K T u X_max rows hT hu hX hrows_le
    dsimp only
    rcases hcore T u hT hu with ⟨hup_n, hprod_n, hmat_n⟩
    let P := 2 ^ u
    have hP_ge2 : P ≥ 2 := by dsimp [P]; simpa using pow2_mono_nat hu
    have hP_ge1 : P ≥ 1 := by omega
    let A_newton : Fin (3 * T) -> Fin (3 * T) -> Int := fun i j =>
      Int.ofNat (mixedNewtonCoeff T P ((rows i).1 * W + (rows i).2 * K) j.val)
    let U_int : Fin (3 * T) -> Fin (3 * T) -> Int := fun r c =>
      let m := c.val / T
      let t := c.val % T
      let zv := if m = 0 then 1 else if m = 1 then P else P * P
      Int.ofNat (zv ^ t * hasseNodePoly T P r.val zv t)
    -- Re-derive `intDet (3 * T) M0 = Int.ofNat (confluentFactorRank3 T u) * intDet (3 * T) A_newton`:
    have hup_i : ∀ r c : Fin (3 * T), c.val < r.val -> U_int r c = 0 := by
      intro r c hlt
      have h0n := hup_n r c hlt
      dsimp only at h0n
      dsimp only [U_int, P]; rw [h0n]; rfl
    have hM0_eq : (fun i j : Fin (3 * T) =>
        (laurentZeroGapIntEntry W K (rows i).1 (rows i).2
          (laurentColsRank3OrderT T u j).1 (laurentColsRank3OrderT T u j).2 : Int)) =
        (fun i j : Fin (3 * T) => intSumPrefix (3 * T) (fun r => A_newton i r * U_int r j) (3 * T)) := by
      funext i j
      let x := (rows i).1 * W + (rows i).2 * K
      have hst : ∀ m : Nat, m ≤ 3 * T ->
          intSumPrefix (3 * T) (fun r => A_newton i r * U_int r j) m =
            Int.ofNat (natSumUpTo m (fun r =>
              if hr : r < 3 * T then
                mixedNewtonCoeff T P x r *
                  ((if j.val / T = 0 then 1 else if j.val / T = 1 then P else P * P) ^ (j.val % T) *
                   hasseNodePoly T P r (if j.val / T = 0 then 1 else if j.val / T = 1 then P else P * P) (j.val % T))
              else 0)) := by
        intro m hm; induction m with
        | zero => rfl
        | succ m' ih =>
          have hm_lt : m' < 3 * T := hm
          conv => lhs; unfold intSumPrefix
          conv => rhs; rhs; unfold natSumUpTo
          simp only [hm_lt, dite_true]
          rw [ih (Nat.le_of_lt hm)]
          rfl
      rw [hst (3 * T) (Nat.le_refl _), hmat_n x j]; rfl
    have hdiag_i : ∀ m : Nat, m ≤ 3 * T ->
        intDiagProdPrefix (3 * T) U_int m =
          Int.ofNat (colBoundProdPrefix (3 * T) (fun c =>
            let mb := c.val / T
            let t := c.val % T
            let zv := if mb = 0 then 1 else if mb = 1 then P else P * P
            zv ^ t * hasseNodePoly T P c.val zv t) m) := by
      intro m hm; induction m with
      | zero => rfl
      | succ m' ih =>
        have hm_lt : m' < 3 * T := hm
        conv => lhs; unfold intDiagProdPrefix
        conv => rhs; rhs; unfold colBoundProdPrefix
        simp only [hm_lt, dite_true]
        rw [ih (Nat.le_of_lt hm)]
        rfl
    have hdet_eq : intDet (3 * T) (fun i j =>
        (laurentZeroGapIntEntry W K (rows i).1 (rows i).2
          (laurentColsRank3OrderT T u j).1 (laurentColsRank3OrderT T u j).2 : Int)) =
        Int.ofNat (confluentFactorRank3 T u) * intDet (3 * T) A_newton := by
      rw [hM0_eq, intDet_mul_upper_tri (3 * T) A_newton U_int hup_i,
          hdiag_i (3 * T) (Nat.le_refl _), hprod_n]
    have hA_maj : (intDet (3 * T) A_newton).natAbs ≤
        natFact (3 * T) *
          colBoundProdPrefix (3 * T) (fun j => mixedNewtonCoeff T P X_max j.val) (3 * T) :=
      intDet_natAbs_le_fact_mul_colProd (3 * T) A_newton
        (fun j => mixedNewtonCoeff T P X_max j.val)
        (fun i j => by
          dsimp only [A_newton]
          exact mixedNewtonCoeff_le_of_le T P hT hP_ge1 _ X_max j.val (hrows_le i))
    have hbd_red :
        (intDet (3 * T) (fun i j =>
          (laurentZeroGapIntEntry W K (rows i).1 (rows i).2
            (laurentColsRank3OrderT T u j).1 (laurentColsRank3OrderT T u j).2 : Int))).natAbs ≤
        natFact (3 * T) * (confluentFactorRank3 T u *
          colBoundProdPrefix (3 * T) (fun j => mixedNewtonCoeff T P X_max j.val) (3 * T)) := by
      rw [hdet_eq, Int.natAbs_mul]
      simp only [Int.ofNat_eq_natCast, Int.natAbs_natCast]
      have hm := Nat.mul_le_mul_left (confluentFactorRank3 T u) hA_maj
      rwa [show confluentFactorRank3 T u *
              (natFact (3 * T) * colBoundProdPrefix (3 * T) (fun j => mixedNewtonCoeff T P X_max j.val) (3 * T)) =
            natFact (3 * T) * (confluentFactorRank3 T u *
              colBoundProdPrefix (3 * T) (fun j => mixedNewtonCoeff T P X_max j.val) (3 * T)) by ac_rfl] at hm
    refine ⟨hbd_red, ?_⟩
    -- Prove `confluentFactorRank3 T u * ∏_c A(X_max, c) < ∏_c raw(c)`:
    let U_nat : Fin (3 * T) -> Fin (3 * T) -> Nat := fun r c =>
      let m := c.val / T
      let t := c.val % T
      let zv := if m = 0 then 1 else if m = 1 then P else P * P
      zv ^ t * hasseNodePoly T P r.val zv t
    let f_red : Fin (3 * T) -> Nat := fun c => U_nat c c * mixedNewtonCoeff T P X_max c.val
    let f_raw : Fin (3 * T) -> Nat := fun c =>
      laurentInterpBinom X_max (laurentColsRank3OrderT T u c).1 *
        2 ^ (X_max * (laurentColsRank3OrderT T u c).2)
    have hprod_mul : ∀ m : Nat, m ≤ 3 * T ->
        colBoundProdPrefix (3 * T) (fun c => U_nat c c) m *
          colBoundProdPrefix (3 * T) (fun c => mixedNewtonCoeff T P X_max c.val) m =
        colBoundProdPrefix (3 * T) f_red m := by
      intro m hm; induction m with
      | zero => rfl
      | succ m' ih =>
        have hm_lt : m' < 3 * T := hm
        simp only [colBoundProdPrefix, hm_lt, dite_true]
        rw [← ih (Nat.le_of_lt hm)]
        dsimp [f_red]; ac_rfl
    rw [← hprod_n, hprod_mul (3 * T) (Nat.le_refl _)]
    -- Every term `f_red c ≤ f_raw c`, `f_red c ≥ 1`, and at `c_T := ⟨T, ...⟩` `f_red c_T < f_raw c_T`!
    have hcf_pos : confluentFactorRank3 T u ≥ 1 := by
      unfold confluentFactorRank3
      have h1 := nat_pow_pos_of_pos 2 (by decide) ((3 * (T * (T - 1) / 2) + T * T) * u)
      have h2 := nat_pow_pos_of_pos (2 ^ u - 1) (by omega) (3 * (T * T))
      have h3 := nat_pow_pos_of_pos (2 ^ u + 1) (by omega) (T * T)
      exact Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
    have hUcc_pos : ∀ c : Fin (3 * T), U_nat c c ≥ 1 := by
      intro c
      by_cases hz : U_nat c c = 0
      · exfalso
        have hp0 : ∀ m : Nat, c.val < m -> m ≤ 3 * T ->
            colBoundProdPrefix (3 * T) (fun j => U_nat j j) m = 0 := by
          intro m hgt hle
          have hst : ∀ d : Nat, c.val + 1 + d ≤ 3 * T ->
              colBoundProdPrefix (3 * T) (fun j => U_nat j j) (c.val + 1 + d) = 0 := by
            intro d hd; induction d with
            | zero =>
              simp only [colBoundProdPrefix, c.isLt, dite_true, hz, Nat.mul_zero]
            | succ d' ih =>
              rw [Nat.add_succ]
              have hlt : c.val + 1 + d' < 3 * T := hd
              simp only [colBoundProdPrefix, hlt, dite_true, ih (by omega), Nat.zero_mul]
          simpa [show c.val + 1 + (m - (c.val + 1)) = m by omega] using hst (m - (c.val + 1)) (by omega)
        have hbad := hp0 (3 * T) c.isLt (Nat.le_refl _)
        rw [hprod_n] at hbad; omega
      · omega
    have hfred_pos : ∀ c : Fin (3 * T), f_red c ≥ 1 := by
      intro c
      dsimp [f_red]
      exact Nat.mul_le_mul (hUcc_pos c)
        (mixedNewtonCoeff_pos_of_le T P hT c.val X_max (by have := c.isLt; omega))
    -- Bound `natSumUpTo`: single summand `g idx ≤ natSumUpTo n g`, and two distinct summands `g 0 + g idx ≤ natSumUpTo n g`:
    have hsum_ge_one : ∀ (n idx : Nat) (g : Nat -> Nat), idx < n -> g idx ≤ natSumUpTo n g := by
      intro n idx g hlt; induction n with
      | zero => omega
      | succ n' ih =>
        simp only [natSumUpTo]
        by_cases heq : idx = n'
        · subst heq; omega
        · have := ih (by omega); omega
    have hsum_ge_two : ∀ (n idx : Nat) (g : Nat -> Nat), 0 < idx -> idx < n ->
        g 0 + g idx ≤ natSumUpTo n g := by
      intro n idx g hpos hlt; induction n with
      | zero => omega
      | succ m_n ih =>
        simp only [natSumUpTo]
        by_cases heq : idx = m_n
        · rw [heq] at hpos ⊢
          have hg0 := hsum_ge_one m_n 0 g hpos
          omega
        · have := ih (by omega); omega
    have hfred_le : ∀ c : Fin (3 * T), f_red c ≤ f_raw c := by
      intro c
      dsimp [f_raw]
      rw [← hmat_n X_max c]
      have h1 := hsum_ge_one (3 * T) c.val
        (fun r => if hr : r < 3 * T then mixedNewtonCoeff T P X_max r * U_nat ⟨r, hr⟩ c else 0)
        c.isLt
      simp only [c.isLt, dite_true] at h1
      dsimp [f_red]
      rwa [Nat.mul_comm]
    let cT : Fin (3 * T) := ⟨T, by omega⟩
    have hfred_lt_cT : f_red cT < f_raw cT := by
      dsimp [f_raw]
      rw [← hmat_n X_max cT]
      have h2 := hsum_ge_two (3 * T) T
        (fun r => if hr : r < 3 * T then mixedNewtonCoeff T P X_max r * U_nat ⟨r, hr⟩ cT else 0)
        hT (by omega)
      have h0_3T : 0 < 3 * T := by omega
      have hT_3T : T < 3 * T := by omega
      simp only [h0_3T, hT_3T, dite_true] at h2
      have h0_val : mixedNewtonCoeff T P X_max 0 * U_nat ⟨0, h0_3T⟩ cT = 1 := by
        rw [mixedNewtonCoeff_zero_right T P hT X_max, Nat.one_mul]
        dsimp [U_nat, cT]
        have hm0 : T % T = 0 := Nat.mod_self T
        rw [hm0, Nat.pow_zero, Nat.one_mul]
        rfl
      rw [h0_val] at h2
      have hcomm : mixedNewtonCoeff T P X_max T * U_nat ⟨T, hT_3T⟩ cT = f_red cT :=
        Nat.mul_comm _ _
      rw [hcomm] at h2
      dsimp only [U_nat, P] at h2 ⊢
      omega
    -- Prefix product monotonicity with strict inequality at `k = T < 3 * T`:
    have hprod_le : ∀ m : Nat, m ≤ 3 * T ->
        colBoundProdPrefix (3 * T) f_red m ≤ colBoundProdPrefix (3 * T) f_raw m := by
      intro m hm; induction m with
      | zero => exact Nat.le_refl 1
      | succ m' ih =>
        have hm_lt : m' < 3 * T := hm
        simp only [colBoundProdPrefix, hm_lt, dite_true]
        exact Nat.mul_le_mul (ih (Nat.le_of_lt hm)) (hfred_le ⟨m', hm_lt⟩)
    have hprod_pos : ∀ m : Nat, m ≤ 3 * T -> colBoundProdPrefix (3 * T) f_red m ≥ 1 := by
      intro m hm; induction m with
      | zero => exact Nat.le_refl 1
      | succ m' ih =>
        have hm_lt : m' < 3 * T := hm
        simp only [colBoundProdPrefix, hm_lt, dite_true]
        exact Nat.mul_le_mul (ih (Nat.le_of_lt hm)) (hfred_pos ⟨m', hm_lt⟩)
    have hprod_lt : ∀ m : Nat, T + 1 ≤ m -> m ≤ 3 * T ->
        colBoundProdPrefix (3 * T) f_red m < colBoundProdPrefix (3 * T) f_raw m := by
      intro m hge hle
      have hst : ∀ d : Nat, T + 1 + d ≤ 3 * T ->
          colBoundProdPrefix (3 * T) f_red (T + 1 + d) <
            colBoundProdPrefix (3 * T) f_raw (T + 1 + d) := by
        intro d hd; induction d with
        | zero =>
          simp only [colBoundProdPrefix, (by omega : T < 3 * T), dite_true]
          have hle_T := hprod_le T (by omega)
          have hpos_T := hprod_pos T (by omega)
          have h1 := Nat.mul_lt_mul_of_pos_left hfred_lt_cT hpos_T
          have h2 := Nat.mul_le_mul_right (f_raw cT) hle_T
          exact Nat.lt_of_lt_of_le h1 h2
        | succ d' ih =>
          rw [Nat.add_succ]
          have hlt : T + 1 + d' < 3 * T := hd
          simp only [colBoundProdPrefix, hlt, dite_true]
          have hcur_pos : 0 < f_red ⟨T + 1 + d', hlt⟩ := hfred_pos ⟨T + 1 + d', hlt⟩
          have h1 := Nat.mul_lt_mul_of_pos_right (ih (by omega)) hcur_pos
          have h2 := Nat.mul_le_mul_left
            (colBoundProdPrefix (3 * T) f_raw (T + 1 + d')) (hfred_le ⟨T + 1 + d', hlt⟩)
          exact Nat.lt_of_lt_of_le h1 h2
      simpa [show T + 1 + (m - (T + 1)) = m by omega] using hst (m - (T + 1)) (by omega)
    exact hprod_lt (3 * T) (by omega) (Nat.le_refl _)

-- ----------------------------------------------------------------------------
-- Section 2B: Rectangular `6 × 6` `(T = 2, U = 3)` Row-Side Vandermonde
--             Divisibility vs Square `9 × 9` `(T = 3, U = 3)` `(3, 5, 1)` Contrast
-- ----------------------------------------------------------------------------

def laurentRowsRectR3S2_6 (i : Fin 6) : Nat × Nat :=
  ((laurentRowsTwoBase6 i).2, (laurentRowsTwoBase6 i).1)

private def v9CertData : List (List Int) :=
  [[1, 0, 0, 0, 0, 0, 0, 0, 0],
   [0, 1, -1, 37, -121, 3773, -4372804, 1071608759, -928082707063],
   [0, 0, 1, -40, 150, -4936, 5774885, -1442120422, 1264405189826],
   [0, 0, 0, 9, -87, 3489, -4206243, 1111534989, -1008967448289],
   [0, 0, 0, 0, 71, -4025, 5061005, -1441068953, 1366452324149],
   [0, 0, 0, 0, 0, 2846, -4011977, 1366083272, -1425325459364],
   [0, 0, 0, 0, 0, 0, 553398, -544996620, 813410632932],
   [0, 0, 0, 0, 0, 0, 0, 531729768, -1252943408536],
   [0, 0, 0, 0, 0, 0, 0, 0, 1123548905504]]

private def m9CertData : List (List Int) :=
  [[1, 0, 0, 0, 0, 0, 0, 0, 0],
   [1, 3, 0, 0, 0, 0, 0, 0, 0],
   [1, 6, 9, 0, 0, 0, 0, 0, 0],
   [1, 5, 5, -71, 0, 0, 0, 0, 0],
   [1, 8, 20, 1147, 5692, 0, 0, 0, 0],
   [1, 11, 44, 16036, 203772, 4427184, 0, 0, 0],
   [1, 10, 35, 7282, 71560, 1002720, -354486512, 0, 0],
   [1, 13, 65, 70261, 1348736, 51626000, 69095190512, 17976782488064, 0],
   [1, 16, 104, 584383, 17602636, 1145799552, 8966650551808, 6114888762419712, 3178406131882459136]]

private def intListAt2D (tbl : List (List Int)) (i j : Nat) : Int :=
  match tbl.drop i with
  | row :: _ =>
    match row.drop j with
    | x :: _ => x
    | [] => 0
  | [] => 0

private def v9CertMat (i j : Fin 9) : Int := intListAt2D v9CertData i.val j.val
private def m9CertMat (i j : Fin 9) : Int := intListAt2D m9CertData i.val j.val
private def a9ZeroGap35 (i j : Fin 9) : Int :=
  Int.ofNat (mixedNewtonCoeff 3 2 ((laurentRowsTwoBase9 i).1 * 3 + (laurentRowsTwoBase9 i).2 * 5) j.val)

private theorem a9_35_bareiss_cert :
    (∀ r c : Fin 9, c.val < r.val -> v9CertMat r c = 0) ∧
    (∀ r c : Fin 9, r.val < c.val -> m9CertMat r c = 0) ∧
    (∀ i j : Fin 9, intSumPrefix 9 (fun r => a9ZeroGap35 i r * v9CertMat r j) 9 = m9CertMat i j) ∧
    intDiagProdPrefix 9 m9CertMat 9 =
      intDiagProdPrefix 9 v9CertMat 9 * 1627343939523819077632 ∧
    intDiagProdPrefix 9 v9CertMat 9 > 0 := by decide

/--
  Theorem W13.2b (`laurent_rect_6x6_t2u3_row_vandermonde_divisibility`,
  `zero custom axioms`):
  Rectangular `U > T` `6 × 6` `(T = 2, U = 3)` Row-Side `(2^(W*u) - 1)^3` Vandermonde Divisibility
  vs Square `9 × 9` `(T = 3, U = 3)` `(3, 5, 1)` Non-Divisibility by `7` (`Branch P3.3`, `W13_H2`):
  1. **Universal Rectangular `6 × 6` `(T = 2, U = 3)` Row-Side Divisibility (`∀ W ≥ 1, K : Nat, u ≥ 1`)**:
     On `laurentRowsRectR3S2_6` (`R = 3, S = 2`, `(r, s) ∈ {0, 1, 2} × {0, 1}`) and `laurentColsC23_6 u`:
       `((2 ^ ((2 * W + K) * u) * (2 ^ (W * u) - 1) ^ 3 : Nat) : Int) ∣ intDet 6 M0_r3s2`
     (in particular `((2 ^ (W * u) - 1) ^ 2 : Int) ∣ intDet 6 M0_r3s2`), AND symmetrically on
     `laurentRowsTwoBase6` (`R = 2, S = 3`):
       `((2 ^ ((W + 2 * K) * u) * (2 ^ (K * u) - 1) ^ 3 : Nat) : Int) ∣ intDet 6 M0_tb6`!
  2. **Two-Base `W * u`-Dilated Congruence + Row-Side Divisibility (`∀ W ≥ 1, K : Nat, u ≥ 1`, `3^W < 2^K`)**:
     On `M_W := laurentInterpMat W K 6 laurentRowsRectR3S2_6 (laurentColsC23_6 (W * u))` and `M0_r3s2` at `u`:
       `((2 ^ K - 3 ^ W : Nat) : Int) ∣ (intDet 6 M_W - intDet 6 M0_r3s2)` AND
       `((2 ^ ((2 * W + K) * u) * (2 ^ (W * u) - 1) ^ 3 : Nat) : Int) ∣ intDet 6 M0_r3s2`!
  3. **Square `U = T = 3` `9 × 9` Row-Vandermonde Obstruction Certificate (`W13_H2` Witness)**:
     At `(W, K, u) = (3, 5, 1)` on the square `9 × 9` `(T = 3, U = 3)` zero-gap matrix `M0_9(3, 5, 1)`:
       `intDet 9 M0_9(3, 5, 1) = (2 ^ 18 * 3 ^ 9 : Int) * 1627343939523819077632`,
     `intDet 9 M0_9(3, 5, 1) % 7 = 6`, and `¬ (((2 ^ (3 * 1) - 1 : Nat) : Int) ∣ intDet 9 M0_9(3, 5, 1))`!
-/
theorem laurent_rect_6x6_t2u3_row_vandermonde_divisibility :
    (∀ (W K u : Nat), W ≥ 1 -> u ≥ 1 ->
      let M0_r3s2 : Fin 6 -> Fin 6 -> Int := fun i j =>
        (laurentZeroGapIntEntry W K (laurentRowsRectR3S2_6 i).1 (laurentRowsRectR3S2_6 i).2
          (laurentColsC23_6 u j).1 (laurentColsC23_6 u j).2 : Int)
      ((2 ^ ((2 * W + K) * u) * (2 ^ (W * u) - 1) ^ 3 : Nat) : Int) ∣ intDet 6 M0_r3s2 ∧
      (((2 ^ (W * u) - 1) ^ 2 : Nat) : Int) ∣ intDet 6 M0_r3s2) ∧
    (∀ (W K u : Nat), K ≥ 1 -> u ≥ 1 ->
      let M0_tb6 : Fin 6 -> Fin 6 -> Int := fun i j =>
        (laurentZeroGapIntEntry W K (laurentRowsTwoBase6 i).1 (laurentRowsTwoBase6 i).2
          (laurentColsC23_6 u j).1 (laurentColsC23_6 u j).2 : Int)
      ((2 ^ ((W + 2 * K) * u) * (2 ^ (K * u) - 1) ^ 3 : Nat) : Int) ∣ intDet 6 M0_tb6) ∧
    (∀ (W K u : Nat), W ≥ 1 -> u ≥ 1 -> 3 ^ W < 2 ^ K ->
      let M_W := laurentInterpMat W K 6 laurentRowsRectR3S2_6 (laurentColsC23_6 (W * u))
      let M0_r3s2 : Fin 6 -> Fin 6 -> Int := fun i j =>
        (laurentZeroGapIntEntry W K (laurentRowsRectR3S2_6 i).1 (laurentRowsRectR3S2_6 i).2
          (laurentColsC23_6 u j).1 (laurentColsC23_6 u j).2 : Int)
      ((2 ^ K - 3 ^ W : Nat) : Int) ∣ (intDet 6 M_W - intDet 6 M0_r3s2) ∧
      ((2 ^ ((2 * W + K) * u) * (2 ^ (W * u) - 1) ^ 3 : Nat) : Int) ∣ intDet 6 M0_r3s2) ∧
    (let M0_9_35 : Fin 9 -> Fin 9 -> Int := fun i j =>
       (laurentZeroGapIntEntry 3 5 (laurentRowsTwoBase9 i).1 (laurentRowsTwoBase9 i).2
         (laurentColsC33_9 1 j).1 (laurentColsC33_9 1 j).2 : Int)
     intDet 9 M0_9_35 = (2 ^ 18 * 3 ^ 9 : Int) * 1627343939523819077632 ∧
     intDet 9 M0_9_35 % 7 = 6 ∧
     ¬ (((2 ^ (3 * 1) - 1 : Nat) : Int) ∣ intDet 9 M0_9_35)) := by
  -- Core polynomial specialization on `laurentRowsTwoBase6`:
  have htb6_div : ∀ (W K u : Nat), K ≥ 1 -> u ≥ 1 ->
      let M0_tb6 : Fin 6 -> Fin 6 -> Int := fun i j =>
        (laurentZeroGapIntEntry W K (laurentRowsTwoBase6 i).1 (laurentRowsTwoBase6 i).2
          (laurentColsC23_6 u j).1 (laurentColsC23_6 u j).2 : Int)
      ((2 ^ ((W + 2 * K) * u) * (2 ^ (K * u) - 1) ^ 3 : Nat) : Int) ∣ intDet 6 M0_tb6 := by
    intro W K u hK hu
    dsimp only
    let P_n : Nat := 2 ^ (W * u)
    let Q_n : Nat := 2 ^ (K * u)
    have hKu_pos : K * u ≥ 1 := Nat.mul_le_mul hK hu
    have hQ_ge2 : Q_n ≥ 2 := by dsimp [Q_n]; simpa using pow2_mono_nat hKu_pos
    let P_i : Int := (P_n : Int)
    let Q_i : Int := (Q_n : Int)
    -- Show `M0_tb6 i j = evalExpr4 (W : Int) (K : Int) P_i Q_i (twoBaseExprMat6 i j)`:
    have hexpr_pow : ∀ (e : Expr4) (d : Nat) (x0 x1 x2 x3 : Int),
        evalExpr4 x0 x1 x2 x3 (expr4Pow e d) = intPowNat (evalExpr4 x0 x1 x2 x3 e) d := by
      intro e d x0 x1 x2 x3; induction d with
      | zero => rfl
      | succ d' ih => simp [expr4Pow, intPowNat, evalExpr4, ih]
    have hint_pow : ∀ (a d : Nat), intPowNat (a : Int) d = ((a ^ d : Nat) : Int) := by
      intro a d; induction d with
      | zero => rfl
      | succ d' ih => simp [intPowNat, ih, Nat.pow_succ, Int.natCast_mul, Int.mul_comm]
    have hmat_eq : (fun i j : Fin 6 =>
        (laurentZeroGapIntEntry W K (laurentRowsTwoBase6 i).1 (laurentRowsTwoBase6 i).2
          (laurentColsC23_6 u j).1 (laurentColsC23_6 u j).2 : Int)) =
        (fun i j : Fin 6 => evalExpr4 (W : Int) (K : Int) P_i Q_i (twoBaseExprMat6 i j)) := by
      funext i j
      let r := (laurentRowsTwoBase6 i).1
      let s := (laurentRowsTwoBase6 i).2
      let kb := j.val / 2
      let t := j.val % 2
      have hcol_j : laurentColsC23_6 u j = (t, kb * u) := by
        dsimp [t, kb]
        rcases (by have := j.isLt; omega :
          j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 ∨ j.val = 4 ∨ j.val = 5) with
          h | h | h | h | h | h <;>
        · simp [laurentColsC23_6, h]
      have hpow_pq : evalExpr4 (W : Int) (K : Int) P_i Q_i
            (.mul (expr4Pow .v2 (r * kb)) (expr4Pow .v3 (s * kb))) =
          ((2 ^ ((r * W + s * K) * (kb * u)) : Nat) : Int) := by
        simp only [evalExpr4, hexpr_pow, hint_pow, P_i, Q_i, P_n, Q_n]
        rw [← Int.natCast_mul,
            pow_pow_eq_mul_w5 2 (W * u) (r * kb),
            pow_pow_eq_mul_w5 2 (K * u) (s * kb),
            ← Nat.pow_add 2]
        apply congrArg (fun e => ((2 ^ e : Nat) : Int))
        rw [Nat.add_mul (r * W) (s * K) (kb * u)]
        have h1 : W * u * (r * kb) = r * W * (kb * u) := by ac_rfl
        have h2 : K * u * (s * kb) = s * K * (kb * u) := by ac_rfl
        rw [h1, h2]
      rw [hcol_j]
      unfold twoBaseExprMat6 laurentZeroGapIntEntry
      change ((laurentInterpBinom (r * W + s * K) t * 2 ^ ((r * W + s * K) * (kb * u)) : Nat) : Int) =
        evalExpr4 (W : Int) (K : Int) P_i Q_i
          (if t = 0 then .mul (expr4Pow .v2 (r * kb)) (expr4Pow .v3 (s * kb))
           else if r = 0 ∧ s = 0 then .const 0
           else .mul (.add (.mul (.const (r : Int)) .v0) (.mul (.const (s : Int)) .v1))
                     (.mul (expr4Pow .v2 (r * kb)) (expr4Pow .v3 (s * kb))))
      have ht_cases : t = 0 ∨ t = 1 := by dsimp [t]; omega
      rcases ht_cases with ht0 | ht1
      · rw [ht0, ite_true_of_w10 rfl, laurentInterpBinom_zero_right, Nat.one_mul, hpow_pq]
      · rw [ht1, ite_false_of_w10 (by decide : ¬ ((1 : Nat) = 0)), laurentInterpBinom_one_right]
        by_cases hrs0 : r = 0 ∧ s = 0
        · rw [ite_true_of_w10 hrs0, hrs0.1, hrs0.2]; simp [evalExpr4]
        · rw [ite_false_of_w10 hrs0]
          rw [Int.natCast_mul, Int.natCast_add, Int.natCast_mul, Int.natCast_mul, ← hpow_pq]
          simp only [evalExpr4]
    -- Apply `twoBase6_poly_identity`:
    have hid_sub := congrArg (evalPoly4 (W : Int) (K : Int) P_i Q_i) twoBase6_poly_identity
    rw [evalPoly4_addPoly4, evalPoly4_det, evalPoly4_negPoly4, evalPoly4_normExpr4] at hid_sub
    have hdet_poly : intDet 6 (fun i j => evalExpr4 (W : Int) (K : Int) P_i Q_i (twoBaseExprMat6 i j)) =
        evalExpr4 (W : Int) (K : Int) P_i Q_i twoBaseClosedExpr := by
      have hfn : (fun i j : Fin 6 =>
          evalPoly4 (W : Int) (K : Int) P_i Q_i (normExpr4 (twoBaseExprMat6 i j))) =
        (fun i j : Fin 6 => evalExpr4 (W : Int) (K : Int) P_i Q_i (twoBaseExprMat6 i j)) := by
        funext i j; exact evalPoly4_normExpr4 _ _ _ _ _
      rw [hfn] at hid_sub
      change intDet 6 _ + -(evalExpr4 (W : Int) (K : Int) P_i Q_i twoBaseClosedExpr) = 0 at hid_sub
      omega
    rw [hmat_eq, hdet_poly]
    unfold twoBaseClosedExpr
    -- `twoBaseClosedExpr = .mul pref (.mul lin quad)` where `pref = P * Q^2 * (Q - 1)^3`!
    let pref := Expr4.mul .v2 (.mul (expr4Pow .v3 2) (expr4Pow (.sub .v3 (.const 1)) 3))
    change _ ∣ evalExpr4 (W : Int) (K : Int) P_i Q_i pref * _
    have hpref_ev : evalExpr4 (W : Int) (K : Int) P_i Q_i pref =
        ((2 ^ ((W + 2 * K) * u) * (2 ^ (K * u) - 1) ^ 3 : Nat) : Int) := by
      dsimp only [pref]
      simp only [evalExpr4, hexpr_pow]
      have hq_sub : Q_i - 1 = ((Q_n - 1 : Nat) : Int) := by dsimp only [Q_i]; omega
      rw [hq_sub, show Q_i = (Q_n : Int) from rfl, hint_pow Q_n 2, hint_pow (Q_n - 1) 3]
      dsimp only [P_i]
      rw [← Int.natCast_mul, ← Int.natCast_mul]
      apply congrArg (fun n : Nat => (n : Int))
      dsimp only [P_n, Q_n]
      rw [pow_pow_eq_mul_w5 2 (K * u) 2, ← Nat.mul_assoc, ← Nat.pow_add 2]
      congr 1; congr 1
      rw [Nat.add_mul W (2 * K) u]
      ac_rfl
    rw [hpref_ev]
    exact ⟨_, rfl⟩
  -- Swap `(W, K)` to deduce `laurentRowsRectR3S2_6` divisibility:
  have hr3s2_div : ∀ (W K u : Nat), W ≥ 1 -> u ≥ 1 ->
      let M0_r3s2 : Fin 6 -> Fin 6 -> Int := fun i j =>
        (laurentZeroGapIntEntry W K (laurentRowsRectR3S2_6 i).1 (laurentRowsRectR3S2_6 i).2
          (laurentColsC23_6 u j).1 (laurentColsC23_6 u j).2 : Int)
      ((2 ^ ((2 * W + K) * u) * (2 ^ (W * u) - 1) ^ 3 : Nat) : Int) ∣ intDet 6 M0_r3s2 := by
    intro W K u hW hu
    dsimp only
    have hswap_mat : (fun i j : Fin 6 =>
        (laurentZeroGapIntEntry W K (laurentRowsRectR3S2_6 i).1 (laurentRowsRectR3S2_6 i).2
          (laurentColsC23_6 u j).1 (laurentColsC23_6 u j).2 : Int)) =
        (fun i j : Fin 6 =>
          (laurentZeroGapIntEntry K W (laurentRowsTwoBase6 i).1 (laurentRowsTwoBase6 i).2
            (laurentColsC23_6 u j).1 (laurentColsC23_6 u j).2 : Int)) := by
      funext i j
      unfold laurentRowsRectR3S2_6 laurentZeroGapIntEntry
      dsimp only
      rw [Nat.add_comm ((laurentRowsTwoBase6 i).2 * W) ((laurentRowsTwoBase6 i).1 * K)]
    rw [hswap_mat, show 2 * W + K = K + 2 * W by omega]
    exact htb6_div K W u hW hu
  refine ⟨?_, htb6_div, ?_, ?_⟩
  · intro W K u hW hu
    have hd3 := hr3s2_div W K u hW hu
    refine ⟨hd3, ?_⟩
    have hd2_3 : (((2 ^ (W * u) - 1) ^ 2 : Nat) : Int) ∣
        ((2 ^ ((2 * W + K) * u) * (2 ^ (W * u) - 1) ^ 3 : Nat) : Int) := by
      refine ⟨((2 ^ ((2 * W + K) * u) * (2 ^ (W * u) - 1) : Nat) : Int), ?_⟩
      rw [← Int.natCast_mul]
      apply congrArg (fun n : Nat => (n : Int))
      rw [show (3 : Nat) = 2 + 1 from rfl, Nat.pow_add _ 2 1, Nat.pow_one]
      ac_rfl
    exact Int.dvd_trans hd2_3 hd3
  · intro W K u hW hu hgt
    dsimp only
    have hd_m0 := hr3s2_div W K u hW hu
    have hcong := (laurent_wdilated_zero_gap_entry_and_det_congruence.2
      W K 6 laurentRowsRectR3S2_6 (laurentColsC23_6 u) hgt).1
    have hMW_eq : (fun i j : Fin 6 =>
        (laurentInterpEntry W K (laurentRowsRectR3S2_6 i).1 (laurentRowsRectR3S2_6 i).2
          (laurentColsC23_6 u j).1 (W * (laurentColsC23_6 u j).2) : Int)) =
        laurentInterpMat W K 6 laurentRowsRectR3S2_6 (laurentColsC23_6 (W * u)) := by
      funext i j
      unfold laurentInterpMat
      have hc_j : ((laurentColsC23_6 u j).1, W * (laurentColsC23_6 u j).2) =
          laurentColsC23_6 (W * u) j := by
        rcases (by have := j.isLt; omega :
          j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 ∨ j.val = 4 ∨ j.val = 5) with
          h | h | h | h | h | h <;>
        · simp [laurentColsC23_6, h]; try ac_rfl
      rw [← hc_j]
    rw [hMW_eq] at hcong
    have hcong_flip : ((2 ^ K - 3 ^ W : Nat) : Int) ∣
        (intDet 6 (laurentInterpMat W K 6 laurentRowsRectR3S2_6 (laurentColsC23_6 (W * u))) -
         intDet 6 (fun i j =>
           (laurentZeroGapIntEntry W K (laurentRowsRectR3S2_6 i).1 (laurentRowsRectR3S2_6 i).2
             (laurentColsC23_6 u j).1 (laurentColsC23_6 u j).2 : Int))) := by
      rcases hcong with ⟨c, hc⟩
      exact ⟨-c, by rw [Int.mul_neg]; omega⟩
    exact ⟨hcong_flip, hd_m0⟩
  · -- Part 3: Exact `9 × 9` `(T = 3, U = 3)` `(3, 5, 1)` zero-gap evaluation via `a9_35_bareiss_cert`:
    dsimp only
    rcases a9_35_bareiss_cert with ⟨hv_up, hm_low, hmul_eq, hdiag_rel, hv_pos⟩
    rcases (laurent_rank3_second_order_confluent_and_reduced_bound.1 3 5 3 1 laurentRowsTwoBase9
      (by decide) (by decide)) with ⟨hdet_fac, _⟩
    have hc9_eq : ∀ j : Fin 9, laurentColsC33_9 1 j = laurentColsRank3OrderT 3 1 j := by
      intro j
      rcases (by have := j.isLt; omega :
        j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 ∨ j.val = 4 ∨
        j.val = 5 ∨ j.val = 6 ∨ j.val = 7 ∨ j.val = 8) with
        h | h | h | h | h | h | h | h | h <;>
      · simp [laurentColsC33_9, laurentColsRank3OrderT, h]
    have hM9_eq : (fun i j : Fin 9 =>
        (laurentZeroGapIntEntry 3 5 (laurentRowsTwoBase9 i).1 (laurentRowsTwoBase9 i).2
          (laurentColsC33_9 1 j).1 (laurentColsC33_9 1 j).2 : Int)) =
        (fun i j : Fin 9 =>
          (laurentZeroGapIntEntry 3 5 (laurentRowsTwoBase9 i).1 (laurentRowsTwoBase9 i).2
            (laurentColsRank3OrderT 3 1 j).1 (laurentColsRank3OrderT 3 1 j).2 : Int)) := by
      funext i j; rw [hc9_eq j]
    have hdetA : intDet 9 a9ZeroGap35 = 1627343939523819077632 := by
      have hu := intDet_mul_upper_tri 9 a9ZeroGap35 v9CertMat hv_up
      have hfn : (fun i j : Fin 9 => intSumPrefix 9 (fun r => a9ZeroGap35 i r * v9CertMat r j) 9) =
          m9CertMat := by funext i j; exact hmul_eq i j
      rw [hfn, intDet_lower_tri 9 m9CertMat hm_low, hdiag_rel] at hu
      exact Int.eq_of_mul_eq_mul_left (by omega : intDiagProdPrefix 9 v9CertMat 9 ≠ 0) hu.symm
    change intDet 9 _ = _ ∧ _
    rw [hM9_eq]
    have hA_same : (fun i j : Fin (3 * 3) =>
        Int.ofNat (mixedNewtonCoeff 3 (2 ^ 1) ((laurentRowsTwoBase9 i).1 * 3 + (laurentRowsTwoBase9 i).2 * 5) j.val)) =
        a9ZeroGap35 := rfl
    rw [hA_same, hdetA] at hdet_fac
    have hcf_3_1 : Int.ofNat (confluentFactorRank3 3 1) = (2 ^ 18 * 3 ^ 9 : Int) := by decide
    rw [hcf_3_1] at hdet_fac
    rw [hdet_fac]
    refine ⟨rfl, by decide, ?_⟩
    rintro ⟨k, hk⟩
    have hm7 : (((2 ^ 18 * 3 ^ 9 : Int) * 1627343939523819077632)) % 7 = 6 := by decide
    have hk7 : (((2 ^ (3 * 1) - 1 : Nat) : Int) * k) % 7 = 0 := by
      change (7 * k) % 7 = 0
      exact Int.mul_emod_right 7 k
    rw [hk] at hm7
    omega

-- ----------------------------------------------------------------------------
-- Section 2C: Rank-2 `6 × 6` `(T = 3, U = 2)` Exact Diophantine Zero Locus &
--             Universal Multi-`u` Zero-Multiplicity `≤ 1` (`∀ 1 ≤ u1 < u2`)
-- ----------------------------------------------------------------------------

def t3u2FactorMinus (W K p2 q3 : Expr4) : Expr4 :=
  let Q := expr4Pow q3 2
  let q := Expr4.sub Q (.const 1)
  let pm := Expr4.sub p2 (.const 1)
  let pp := Expr4.add p2 (.const 1)
  let a := Expr4.mul (.mul p2 (.mul pm (expr4Pow q 2))) (expr4Pow W 2)
  let b := Expr4.mul (.mul p2 (.mul pp (.mul (.add Q (.const 1)) q))) (.mul W K)
  let c := Expr4.mul (.mul (.const 2) (.mul pm (.mul (expr4Pow pp 2) Q))) (expr4Pow K 2)
  .add (.sub a b) c

def t3u2FactorPlus (W K p2 q3 : Expr4) : Expr4 :=
  let Q := expr4Pow q3 2
  let q := Expr4.sub Q (.const 1)
  let pm := Expr4.sub p2 (.const 1)
  let pp := Expr4.add p2 (.const 1)
  let a := Expr4.mul (.mul p2 (.mul pp (expr4Pow q 2))) (expr4Pow W 2)
  let b := Expr4.mul (.mul p2 (.mul pm (.mul (.add Q (.const 1)) q))) (.mul W K)
  let c := Expr4.mul (.mul (.const 2) (.mul pp (.mul (expr4Pow pm 2) Q))) (expr4Pow K 2)
  .sub (.sub a b) c

def t3u2DiscMinusExpr (p2 q3 : Expr4) : Expr4 :=
  let Q := expr4Pow q3 2
  let pm := Expr4.sub p2 (.const 1)
  .sub
    (.mul (expr4Pow p2 2) (expr4Pow (.add Q (.const 1)) 2))
    (.mul (.const 8) (.mul p2 (.mul (expr4Pow pm 2) Q)))

def t3u2DiscPlusExpr (p2 q3 : Expr4) : Expr4 :=
  let Q := expr4Pow q3 2
  let pm := Expr4.sub p2 (.const 1)
  let pp := Expr4.add p2 (.const 1)
  let _ := pm
  .add
    (.mul (expr4Pow p2 2) (expr4Pow (.add Q (.const 1)) 2))
    (.mul (.const 8) (.mul p2 (.mul (expr4Pow pp 2) Q)))

set_option maxRecDepth 32768 in
private theorem t3u2_even_u_quadratic_identities :
    addPoly4
      (normExpr4 (t3u2BracketExpr .v0 .v1 (expr4Pow .v2 2) (expr4Pow .v3 2)))
      (negPoly4 (normExpr4 (.mul (t3u2FactorMinus .v0 .v1 .v2 .v3)
                                 (t3u2FactorPlus .v0 .v1 .v2 .v3)))) = [] ∧
    addPoly4
      (normExpr4 (.mul (.mul (.const 4) (.mul .v2 (.sub .v2 (.const 1))))
                       (t3u2FactorMinus .v0 .v1 .v2 .v3)))
      (negPoly4 (normExpr4 (.sub
        (expr4Pow (.sub
          (.mul (.mul (.const 2) (.mul .v2 (.mul (.sub .v2 (.const 1)) (.sub (expr4Pow .v3 2) (.const 1))))) .v0)
          (.mul (.mul .v2 (.mul (.add .v2 (.const 1)) (.add (expr4Pow .v3 2) (.const 1)))) .v1)) 2)
        (.mul (t3u2DiscMinusExpr .v2 .v3)
              (expr4Pow (.mul (.add .v2 (.const 1)) .v1) 2))))) = [] ∧
    addPoly4
      (normExpr4 (.mul (.mul (.const 4) (.mul .v2 (.add .v2 (.const 1))))
                       (t3u2FactorPlus .v0 .v1 .v2 .v3)))
      (negPoly4 (normExpr4 (.sub
        (expr4Pow (.sub
          (.mul (.mul (.const 2) (.mul .v2 (.mul (.add .v2 (.const 1)) (.sub (expr4Pow .v3 2) (.const 1))))) .v0)
          (.mul (.mul .v2 (.mul (.sub .v2 (.const 1)) (.add (expr4Pow .v3 2) (.const 1)))) .v1)) 2)
        (.mul (t3u2DiscPlusExpr .v2 .v3)
              (expr4Pow (.mul (.sub .v2 (.const 1)) .v1) 2))))) = [] := by decide

private def t3u2DiscMinusNat (m : Nat) : Nat :=
  let p2 := 2 ^ m
  let Q := 9 ^ m
  (p2 * (Q + 1)) ^ 2 - 8 * p2 * (p2 - 1) ^ 2 * Q

private def t3u2DiscPlusNat (m : Nat) : Nat :=
  let p2 := 2 ^ m
  let Q := 9 ^ m
  (p2 * (Q + 1)) ^ 2 + 8 * p2 * (p2 + 1) ^ 2 * Q

private def discPlusRoots1To36 : List Nat :=
  [41, 415, 6155, 106141, 1893950, 34029183, 612286720, 11020225024,
   198360343553, 3570471430145, 64268426874881, 1156831448571906,
   20822965134180354, 374813368655970306, 6746640620772720642,
   121439531113774710786, 2185911559807417188354, 39346408075571417841667,
   708235345356437192704003, 12748236216400476230385667,
   229468251895146999344791555, 4130428534112399697299636227,
   74347713614022209388370984963, 1338258845052395828339795820547,
   24088659210943109147515213053955, 433595865796975901604874219945987,
   7804725584345565976686147162603523, 140485060518220186571544313068519427,
   2528731089327963354252572330454679555, 45517159607903340360405400806378962947,
   819308872942260126422733610102219079683, 14747559712960682275350950564498772066307,
   265456074833292280955284092492231687012355, 4778209346999261057190981594186422476079107,
   86007768245986699029421140412663086910013443, 1548139828427760582529514414297170441544925187]

private def discMinusRoots1To36 : List Nat :=
  [0, 290, 5640, 104088, 1885752, 33996408, 612155640, 11019700728,
   198358246393, 3570463041529, 64268393320441, 1156831314354170,
   20822964597309434, 374813366508486650, 6746640612182786042,
   121439531079414972410, 2185911559669978234874, 39346408075021662027771,
   708235345354238169448443, 12748236216391680137363451,
   229468251895111814972702715, 4130428534112258959811280891,
   74347713614021646438417563643, 1338258845052393576539982135291,
   24088659210943100140315958312955, 433595865796975865576077200982011,
   7804725584345565832570959086747643, 140485060518220185995083560765095931,
   2528731089327963351946729321240985595, 45517159607903340351182028769524187131,
   819308872942260126385840121954799976443, 14747559712960682275203376611909095653371,
   265456074833292280954693796681872981360635, 4778209346999261057188620410944987653472251,
   86007768245986699029411695679697347619586043, 1548139828427760582529476635365307484383215611]

private def listGetNatD : List Nat -> Nat -> Nat
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, n + 1 => listGetNatD xs n

private def checkStrictRootBetween (E s : Nat) : Bool :=
  decide (s * s < E) && decide (E < (s + 1) * (s + 1))

private def checkT3U2DiscNonSq2To36 : Bool :=
  (List.range 35).all (fun idx =>
    let m := idx + 2
    let sm := listGetNatD discMinusRoots1To36 (m - 1)
    let sp := listGetNatD discPlusRoots1To36 (m - 1)
    checkStrictRootBetween (t3u2DiscMinusNat m) sm &&
    checkStrictRootBetween (t3u2DiscPlusNat m) sp)

private theorem t3u2_disc_finite_certs :
    checkStrictRootBetween (t3u2DiscPlusNat 1) 41 = true ∧
    checkT3U2DiscNonSq2To36 = true ∧
    18 ^ 37 > 77 * 16 ^ 37 := by decide

private theorem sq_eq_mul_sq_imp_is_sq (A E B : Nat) (hB : B ≥ 1)
    (heq : A * A = E * (B * B)) : ∃ s : Nat, s * s = E := by
  let g := Nat.gcd A B
  have hg_pos : 0 < g := Nat.gcd_pos_of_pos_right A hB
  let a := A / g
  let b := B / g
  have hA_eq : A = a * g := (Nat.div_mul_cancel (Nat.gcd_dvd_left A B)).symm
  have hB_eq : B = b * g := (Nat.div_mul_cancel (Nat.gcd_dvd_right A B)).symm
  have hcop : Nat.Coprime a b := Nat.coprime_div_gcd_div_gcd hg_pos
  have hgg_pos : 0 < g * g := Nat.mul_pos hg_pos hg_pos
  have heq_ab : (a * a) * (g * g) = (E * (b * b)) * (g * g) := by
    calc
      (a * a) * (g * g) = (a * g) * (a * g) := by ac_rfl
      _ = A * A := by rw [← hA_eq]
      _ = E * (B * B) := heq
      _ = E * ((b * g) * (b * g)) := by rw [← hB_eq]
      _ = (E * (b * b)) * (g * g) := by ac_rfl
  have hab : a * a = E * (b * b) := Nat.eq_of_mul_eq_mul_right hgg_pos heq_ab
  have hb_dvd : b ∣ a * a := ⟨E * b, by rw [hab]; ac_rfl⟩
  have hb1 : b = 1 := (Nat.Coprime.mul_left hcop hcop).symm.eq_one_of_dvd hb_dvd
  refine ⟨a, ?_⟩
  rw [hb1] at hab
  simpa using hab

private theorem pred_sq_add_two (R : Nat) (hR : R ≥ 1) :
    (R - 1) * (R - 1) + 2 * R = R * R + 1 := by
  cases R with
  | zero => omega
  | succ r' =>
    simp only [Nat.add_sub_cancel]
    rw [Nat.mul_add (r' + 1) r' 1, Nat.add_mul r' 1 r', Nat.mul_one, Nat.one_mul]
    omega

private theorem int_mul_self_eq_natAbs_sq (z : Int) :
    z * z = ((z.natAbs * z.natAbs : Nat) : Int) := by
  rcases Int.natAbs_eq z with h | h
  · conv => lhs; rw [h, ← Int.natCast_mul]
  · conv => lhs; rw [h, Int.neg_mul_neg, ← Int.natCast_mul]

private theorem not_sq_of_between_consecutive (E R : Nat)
    (hlo : (R - 1) * (R - 1) < E) (hhi : E < R * R) :
    ∀ s : Nat, s * s ≠ E := by
  intro s heq
  by_cases hle : s ≤ R - 1
  · have h1 := Nat.mul_le_mul hle hle; omega
  · have hge : R ≤ s := by omega
    have h2 := Nat.mul_le_mul hge hge; omega

private theorem not_sq_of_strictRootBetween (E s : Nat)
    (hb : checkStrictRootBetween E s = true) :
    ∀ r : Nat, r * r ≠ E := by
  unfold checkStrictRootBetween at hb
  rcases bool_and_split hb with ⟨h1, h2⟩
  have hlo : s * s < E := of_decide_eq_true h1
  have hhi : E < (s + 1) * (s + 1) := of_decide_eq_true h2
  exact not_sq_of_between_consecutive E (s + 1) (by simpa using hlo) hhi

private theorem sq_add_four_ident (X Y : Nat) :
    (X + 4 * Y) * (X + 4 * Y) = X * X + 8 * (X * Y) + 16 * (Y * Y) := by
  have h1 : X * (4 * Y) = 4 * (X * Y) := by ac_rfl
  have h2 : 4 * Y * X = 4 * (X * Y) := by ac_rfl
  have h3 : 4 * Y * (4 * Y) = (4 * 4) * (Y * Y) := by ac_rfl
  rw [Nat.mul_add, Nat.add_mul, Nat.add_mul, h1, h2, h3]
  omega

private theorem sq_sub_four_ident (X Y : Nat) (hle : 4 * Y ≤ X) :
    (X - 4 * Y) * (X - 4 * Y) + 8 * (X * Y) = X * X + 16 * (Y * Y) := by
  have hX : X - 4 * Y + 4 * Y = X := Nat.sub_add_cancel hle
  have hid := sq_add_four_ident (X - 4 * Y) Y
  rw [hX] at hid
  have hXY : 8 * (X * Y) = 8 * ((X - 4 * Y) * Y) + 32 * (Y * Y) := by
    have hmul : X * Y = (X - 4 * Y) * Y + 4 * (Y * Y) := by
      calc X * Y = (X - 4 * Y + 4 * Y) * Y := by rw [hX]
        _ = (X - 4 * Y) * Y + 4 * Y * Y := by rw [Nat.add_mul]
        _ = (X - 4 * Y) * Y + 4 * (Y * Y) := by rw [Nat.mul_assoc]
    rw [hmul, Nat.mul_add]
    omega
  omega

/--
  Theorem W13.2c (`laurent_6x6_t3u2_complete_zero_locus_and_multiu_le_one`,
  `zero custom axioms`):
  Complete Diophantine Zero Classification & Universal Multi-`u` Zero-Multiplicity `≤ 1`
  on Rank-2 `6 × 6` `(T = 3, U = 2)` (`Branch P3.3`, `W13_H2`):
  1. **Exact Diophantine Zero Classification Across ALL `W, K, u ≥ 1`**:
     `intDet 6 (laurentTwoBaseT3U2Mat6 W K u) = 0 ↔ (u = 2 ∧ (8 * W = 3 * K ∨ 8 * W = 27 * K))`!
     That is, out of ALL `(W, K, u) ∈ (Z^+)^3`, `det_6^(T=3, U=2)` vanishes **exclusively** at `u = 2`
     along the two rational rays `W / K = 3 / 8` (`3^W < 2^K`) and `W / K = 27 / 8` (`3^W > 2^K`),
     and NEVER vanishes at ANY `u = 1` or `u ≥ 3`!
  2. **Universal Multi-`u` Zero-Multiplicity Ceiling `≤ 1` (`∀ W, K ≥ 1`, `∀ 1 ≤ u1 < u2`)**:
     `¬ (intDet 6 (laurentTwoBaseT3U2Mat6 W K u1) = 0 ∧ intDet 6 (laurentTwoBaseT3U2Mat6 W K u2) = 0)`!
  3. **Coprime Ray Certificates (`(3, 8, 2)` and `(27, 8, 2)`)**:
     `intDet 6 (laurentTwoBaseT3U2Mat6 3 8 2) = 0` and `intDet 6 (laurentTwoBaseT3U2Mat6 27 8 2) = 0`!
-/
theorem laurent_6x6_t3u2_complete_zero_locus_and_multiu_le_one :
    (∀ (W K u : Nat), W ≥ 1 -> K ≥ 1 -> u ≥ 1 ->
      (intDet 6 (laurentTwoBaseT3U2Mat6 W K u) = 0 ↔
        (u = 2 ∧ (8 * W = 3 * K ∨ 8 * W = 27 * K)))) ∧
    (∀ (W K u1 u2 : Nat), W ≥ 1 -> K ≥ 1 -> 1 ≤ u1 -> u1 < u2 ->
      ¬ (intDet 6 (laurentTwoBaseT3U2Mat6 W K u1) = 0 ∧
         intDet 6 (laurentTwoBaseT3U2Mat6 W K u2) = 0)) ∧
    (intDet 6 (laurentTwoBaseT3U2Mat6 3 8 2) = 0 ∧
     intDet 6 (laurentTwoBaseT3U2Mat6 27 8 2) = 0) := by
  rcases laurent_6x6_t3u2_factorization_and_cone_positivity with ⟨hclosed, hodd_nz, _⟩
  rcases t3u2_even_u_quadratic_identities with ⟨hquad_id, hsq_m_id, hsq_p_id⟩
  rcases t3u2_disc_finite_certs with ⟨hp1_nsq, h2_36_nsq, h18_37⟩
  -- Helper: Runge non-squareness of `t3u2DiscMinusNat m` (for all `m ≥ 2`) and `t3u2DiscPlusNat m` (for all `m ≥ 1`):
  have h18_gt_77 : ∀ m : Nat, m ≥ 37 -> 18 ^ m > 77 * 16 ^ m := by
    intro m hm
    have hst : ∀ d : Nat, 18 ^ (37 + d) > 77 * 16 ^ (37 + d) := by
      intro d; induction d with
      | zero => exact h18_37
      | succ d' ih =>
        rw [Nat.add_succ, Nat.pow_succ 18, Nat.pow_succ 16]
        omega
    simpa [show 37 + (m - 37) = m by omega] using hst (m - 37)
  have hdisc_nsq : ∀ m : Nat, m ≥ 1 ->
      (∀ s : Nat, s * s ≠ t3u2DiscPlusNat m) ∧
      (m ≥ 2 -> ∀ s : Nat, s * s ≠ t3u2DiscMinusNat m) := by
    intro m hm1
    by_cases hm36 : m ≤ 36
    · by_cases hm_eq1 : m = 1
      · subst hm_eq1
        exact ⟨not_sq_of_strictRootBetween _ _ hp1_nsq, fun h2 => by omega⟩
      · have hidx_lt : m - 2 < 35 := by omega
        have hall := List.all_eq_true.mp h2_36_nsq (m - 2) (List.mem_range.mpr hidx_lt)
        rw [show m - 2 + 2 = m by omega] at hall
        rcases bool_and_split hall with ⟨hm_b, hp_b⟩
        exact ⟨not_sq_of_strictRootBetween _ _ hp_b, fun _ => not_sq_of_strictRootBetween _ _ hm_b⟩
    · have hm37 : m ≥ 37 := by omega
      let p2 := 2 ^ m
      let Q := 9 ^ m
      have hp2_ge4 : p2 ≥ 4 := by
        dsimp [p2]; simpa using nat_pow_mono_exp_pos 2 2 m (by decide) (by omega)
      have hQ_ge9 : Q ≥ 9 := by
        dsimp [Q]; simpa using nat_pow_mono_exp_pos 9 1 m (by decide) hm1
      -- Exponential dominance `2 * (p2 * Q) > 154 * p2 ^ 4`:
      have hp2Q : p2 * Q = 18 ^ m := by
        dsimp [p2, Q]
        have hmul_p : ∀ k : Nat, 2 ^ k * 9 ^ k = 18 ^ k := by
          intro k; induction k with
          | zero => rfl
          | succ k' ih =>
            calc 2 ^ (k' + 1) * 9 ^ (k' + 1)
                = (2 ^ k' * 9 ^ k') * (2 * 9) := by rw [Nat.pow_succ 2, Nat.pow_succ 9]; ac_rfl
              _ = 18 ^ (k' + 1) := by rw [ih, show (2 : Nat) * 9 = 18 from rfl, Nat.pow_succ 18]
        exact hmul_p m
      have hp2_4 : p2 ^ 4 = 16 ^ m := by
        dsimp [p2]
        rw [pow_pow_eq_mul_w5 2 m 4, Nat.mul_comm m 4, ← pow_pow_eq_mul_w5 2 4 m]
      have h2p2Q_gt : 2 * (p2 * Q) > 154 * p2 ^ 4 := by
        rw [hp2Q, hp2_4]
        have h77 := h18_gt_77 m hm37
        omega
      -- Bound `16 * (p2 + 1) ^ 4 + 8 * (p2 * (p2 + 1) ^ 2) + 1 ≤ 154 * p2 ^ 4` for `p2 ≥ 4`:
      have hpoly_p2 : 16 * (p2 + 1) ^ 4 + 8 * (p2 * (p2 + 1) ^ 2) + 1 ≤ 154 * p2 ^ 4 := by
        have h23 : 2 * (p2 + 1) ≤ 3 * p2 := by omega
        have hpow_le : ∀ (a b k : Nat), a ≤ b -> a ^ k ≤ b ^ k := by
          intro a b k hab; induction k with
          | zero => exact Nat.le_refl 1
          | succ k' ih => rw [Nat.pow_succ, Nat.pow_succ]; exact Nat.mul_le_mul ih hab
        have h4 : (2 * (p2 + 1)) ^ 4 ≤ (3 * p2) ^ 4 := hpow_le _ _ 4 h23
        have hmul4 : ∀ (c x : Nat), (c * x) ^ 4 = c ^ 4 * x ^ 4 := by
          intro c x
          simp only [show (4 : Nat) = 1 + 1 + 1 + 1 from rfl, Nat.pow_add, Nat.pow_one]
          ac_rfl
        rw [hmul4 2 (p2 + 1), hmul4 3 p2] at h4
        change 16 * (p2 + 1) ^ 4 ≤ 81 * p2 ^ 4 at h4
        have h2_le : (p2 + 1) ^ 2 ≤ 4 * p2 ^ 2 := by
          have : p2 + 1 ≤ 2 * p2 := by omega
          have hp := hpow_le _ _ 2 this
          have h22 : (2 * p2) ^ 2 = 4 * p2 ^ 2 := by
            calc (2 * p2) ^ 2 = (2 * 2) * (p2 * p2) := by rw [Nat.pow_two]; ac_rfl
              _ = 4 * p2 ^ 2 := by rw [show (2 : Nat) * 2 = 4 from rfl, ← Nat.pow_two p2]
          rwa [h22] at hp
        have h8 : 8 * (p2 * (p2 + 1) ^ 2) ≤ 32 * p2 ^ 3 := by
          have hm := Nat.mul_le_mul_left (8 * p2) h2_le
          have hl : 8 * p2 * (p2 + 1) ^ 2 = 8 * (p2 * (p2 + 1) ^ 2) := by ac_rfl
          have hr : 8 * p2 * (4 * p2 ^ 2) = 32 * p2 ^ 3 := by
            calc 8 * p2 * (4 * p2 ^ 2) = (8 * 4) * (p2 ^ 2 * p2) := by ac_rfl
              _ = 32 * p2 ^ 3 := by rw [show (8 : Nat) * 4 = 32 from rfl, ← Nat.pow_succ p2 2]
          rwa [hl, hr] at hm
        have hp3_le4 : p2 ^ 3 ≤ p2 ^ 4 := by
          rw [Nat.pow_succ p2 3]
          simpa using Nat.mul_le_mul_left (p2 ^ 3) (by omega : 1 ≤ p2)
        have h1_le4 : 1 ≤ p2 ^ 4 := nat_pow_pos_of_pos p2 (by omega) 4
        omega
      let X := p2 * (Q + 1)
      have hX_split : X = p2 * Q + p2 := by dsimp [X]; rw [Nat.mul_add p2 Q 1, Nat.mul_one]
      -- Squeeze 1: `(Rp - 1)^2 < t3u2DiscPlusNat m < Rp^2` where `Rp := X + 4 * (p2 + 1)^2`:
      have hplus_nsq : ∀ s : Nat, s * s ≠ t3u2DiscPlusNat m := by
        let Yp := (p2 + 1) ^ 2
        let Rp := X + 4 * Yp
        have hYp2 : Yp * Yp = (p2 + 1) ^ 4 := by
          dsimp [Yp]; rw [← Nat.pow_two, pow_pow_eq_mul_w5 (p2 + 1) 2 2]
        have hXYp : 8 * (X * Yp) = 8 * p2 * Yp * Q + 8 * (p2 * Yp) := by
          rw [hX_split, Nat.add_mul, Nat.mul_add]
          have h1 : 8 * (p2 * Q * Yp) = 8 * p2 * Yp * Q := by ac_rfl
          rw [h1]
        have hEp_eq : t3u2DiscPlusNat m = X * X + 8 * p2 * Yp * Q := by
          unfold t3u2DiscPlusNat
          dsimp [X, Yp, p2, Q]
          rw [Nat.pow_two]
        have hRp_id : Rp * Rp = t3u2DiscPlusNat m + 8 * (p2 * Yp) + 16 * (p2 + 1) ^ 4 := by
          have hid := sq_add_four_ident X Yp
          change Rp * Rp = _ at hid
          rw [hXYp, hYp2] at hid
          rw [hEp_eq]
          omega
        have hYp_pos : Yp ≥ 1 := by dsimp [Yp]; exact nat_pow_pos_of_pos _ (by omega) 2
        have hpYp_pos : p2 * Yp ≥ 4 := by
          simpa using Nat.mul_le_mul hp2_ge4 hYp_pos
        have hRp1 : Rp ≥ 1 := by dsimp only [Rp, X]; omega
        have hRp_sub1 := pred_sq_add_two Rp hRp1
        have h2Rp_gt : 2 * Rp > 8 * (p2 * Yp) + 16 * (p2 + 1) ^ 4 + 1 := by
          have hRp_ge : Rp ≥ p2 * Q := by dsimp only [Rp]; omega
          dsimp only [Yp] at *
          omega
        apply not_sq_of_between_consecutive (t3u2DiscPlusNat m) Rp
        · omega
        · omega
      -- Squeeze 2: `(Rm - 1)^2 < t3u2DiscMinusNat m < Rm^2` where `Rm := X - 4 * (p2 - 1)^2`:
      have hminus_nsq : ∀ s : Nat, s * s ≠ t3u2DiscMinusNat m := by
        let Ym := (p2 - 1) ^ 2
        have hpm_le : Ym ≤ p2 ^ 2 := by
          dsimp [Ym]; rw [Nat.pow_two, Nat.pow_two]
          exact Nat.mul_le_mul (by omega : p2 - 1 ≤ p2) (by omega : p2 - 1 ≤ p2)
        have hYm2 : Ym * Ym = (p2 - 1) ^ 4 := by
          dsimp [Ym]; rw [← Nat.pow_two, pow_pow_eq_mul_w5 (p2 - 1) 2 2]
        have hpm4_le : (p2 - 1) ^ 4 ≤ p2 ^ 4 := by
          have h := Nat.mul_le_mul hpm_le hpm_le
          rwa [hYm2, ← Nat.pow_two (p2 ^ 2), pow_pow_eq_mul_w5 p2 2 2] at h
        have h4p2_le : 4 * p2 ^ 2 ≤ p2 ^ 4 := by
          have hp2_16 : 4 ≤ p2 ^ 2 := by
            rw [Nat.pow_two]
            exact Nat.le_trans (by decide : 4 ≤ 4 * 4) (Nat.mul_le_mul hp2_ge4 hp2_ge4)
          have hm_p := Nat.mul_le_mul_right (p2 ^ 2) hp2_16
          rwa [← Nat.pow_two (p2 ^ 2), pow_pow_eq_mul_w5 p2 2 2] at hm_p
        have h4Ym_lt_X : 4 * Ym < X := by
          have : 4 * Ym ≤ 4 * p2 ^ 2 := Nat.mul_le_mul_left 4 hpm_le
          omega
        let Rm := X - 4 * Ym
        have hXYm : 8 * (X * Ym) = 8 * p2 * Ym * Q + 8 * (p2 * Ym) := by
          rw [hX_split, Nat.add_mul, Nat.mul_add]
          have h1 : 8 * (p2 * Q * Ym) = 8 * p2 * Ym * Q := by ac_rfl
          rw [h1]
        have hEm_le : 8 * p2 * Ym * Q ≤ X * X := by
          have hp2Y : 8 * p2 * Ym ≤ 8 * p2 ^ 3 := by
            have hm := Nat.mul_le_mul_left (8 * p2) hpm_le
            have hr : 8 * p2 * p2 ^ 2 = 8 * p2 ^ 3 := by
              calc 8 * p2 * p2 ^ 2 = 8 * (p2 ^ 2 * p2) := by ac_rfl
                _ = 8 * p2 ^ 3 := by rw [← Nat.pow_succ p2 2]
            rwa [hr] at hm
          have h8p3_lt : 8 * p2 ^ 3 < p2 * Q := by
            have hp3_4 : p2 ^ 3 ≤ p2 ^ 4 := by
              rw [Nat.pow_succ p2 3]
              simpa using Nat.mul_le_mul_left (p2 ^ 3) (by omega : 1 ≤ p2)
            omega
          have hmQ := Nat.mul_le_mul_right Q (Nat.le_trans hp2Y (Nat.le_of_lt h8p3_lt))
          have hXQ_le : p2 * Q * Q ≤ X * X := by
            have h1 : p2 * Q ≤ X := by omega
            have h2 : Q ≤ X := by
              have hQ_le : Q ≤ 1 * Q := by omega
              have h1p : 1 * Q ≤ p2 * Q := Nat.mul_le_mul_right Q (by omega : 1 ≤ p2)
              omega
            exact Nat.mul_le_mul h1 h2
          exact Nat.le_trans hmQ hXQ_le
        have hEm_add : t3u2DiscMinusNat m + 8 * p2 * Ym * Q = X * X := by
          unfold t3u2DiscMinusNat
          dsimp only [X, Ym, p2, Q] at *
          rw [Nat.pow_two]
          exact Nat.sub_add_cancel hEm_le
        have hRm_id : Rm * Rm + 8 * (p2 * Ym) = t3u2DiscMinusNat m + 16 * (p2 - 1) ^ 4 := by
          have hid := sq_sub_four_ident X Ym (Nat.le_of_lt h4Ym_lt_X)
          change Rm * Rm + 8 * (X * Ym) = X * X + 16 * (Ym * Ym) at hid
          rw [hXYm, hYm2, ← hEm_add] at hid
          omega
        have h8lt16 : 8 * (p2 * Ym) < 16 * (p2 - 1) ^ 4 := by
          rw [← hYm2]
          have hYm_ge9 : Ym ≥ 9 := by
            dsimp [Ym]; rw [Nat.pow_two]
            exact Nat.mul_le_mul (by omega : 3 ≤ p2 - 1) (by omega : 3 ≤ p2 - 1)
          have h2Y : 8 * p2 < 16 * Ym := by
            have h3pm : 3 * (p2 - 1) ≤ Ym := by
              dsimp [Ym]; rw [Nat.pow_two]
              exact Nat.mul_le_mul_right (p2 - 1) (by omega : 3 ≤ p2 - 1)
            omega
          have hm := Nat.mul_lt_mul_of_pos_right h2Y (by omega : 0 < Ym)
          rwa [Nat.mul_assoc 8 p2 Ym, Nat.mul_assoc 16 Ym Ym] at hm
        have hRm1 : Rm ≥ 1 := by dsimp only [Rm]; omega
        have hRm_sub1 := pred_sq_add_two Rm hRm1
        have h2Rm_gt : 2 * Rm > 16 * (p2 - 1) ^ 4 + 1 := by
          have hRm_add : Rm + 4 * Ym = X := Nat.sub_add_cancel (Nat.le_of_lt h4Ym_lt_X)
          have h4Ym_le : 4 * Ym ≤ p2 ^ 4 := Nat.le_trans (Nat.mul_le_mul_left 4 hpm_le) h4p2_le
          omega
        apply not_sq_of_between_consecutive (t3u2DiscMinusNat m) Rm
        · omega
        · omega
      exact ⟨hplus_nsq, fun _ => hminus_nsq⟩
  -- Helper at `u = 2`: `t3u2FactorMinus W K 2 3 = 2 * (8 * W - 3 * K) * (8 * W - 27 * K)`:
  have hlin_u2 : ∀ (W K : Nat),
      evalExpr4 (W : Int) (K : Int) 2 3 (t3u2FactorMinus .v0 .v1 .v2 .v3) =
        2 * (8 * (W : Int) - 3 * (K : Int)) * (8 * (W : Int) - 27 * (K : Int)) := by
    have hid1 : addPoly4 (normExpr4 (t3u2FactorMinus .v0 .v1 (.const 2) (.const 3)))
        (negPoly4 (normExpr4 (.mul (.const 2)
          (.mul (.sub (.mul (.const 8) .v0) (.mul (.const 3) .v1))
                (.sub (.mul (.const 8) .v0) (.mul (.const 27) .v1)))))) = [] := by decide
    intro W K
    have hev1 := expr4_eq_of_norm_sub_nil _ _ hid1 (W : Int) (K : Int) 2 3
    have hsame : evalExpr4 (W : Int) (K : Int) 2 3 (t3u2FactorMinus .v0 .v1 (.const 2) (.const 3)) =
        evalExpr4 (W : Int) (K : Int) 2 3 (t3u2FactorMinus .v0 .v1 .v2 .v3) := rfl
    rw [← hsame, hev1]
    simp [evalExpr4, Int.mul_assoc]
  -- Main equivalence `intDet 6 (laurentTwoBaseT3U2Mat6 W K u) = 0 ↔ u = 2 ∧ (8 * W = 3 * K ∨ 8 * W = 27 * K)`:
  have hiff : ∀ (W K u : Nat), W ≥ 1 -> K ≥ 1 -> u ≥ 1 ->
      (intDet 6 (laurentTwoBaseT3U2Mat6 W K u) = 0 ↔
        (u = 2 ∧ (8 * W = 3 * K ∨ 8 * W = 27 * K))) := by
    intro W K u hW hK hu
    have hexprPow_c : ∀ (e : Expr4) (d : Nat) (x0 x1 x2 x3 : Int),
        evalExpr4 x0 x1 x2 x3 (expr4Pow e d) = intPowNat (evalExpr4 x0 x1 x2 x3 e) d := by
      intro e d x0 x1 x2 x3; induction d with
      | zero => rfl
      | succ d' ih => simp [expr4Pow, intPowNat, evalExpr4, ih]
    have hintPow_c : ∀ (a d : Nat), intPowNat (a : Int) d = ((a ^ d : Nat) : Int) := by
      intro a d; induction d with
      | zero => rfl
      | succ d' ih => simp [intPowNat, ih, Nat.pow_succ, Int.natCast_mul, Int.mul_comm]
    constructor
    · intro hdet0
      by_cases hu_odd : u % 2 = 1
      · exact False.elim (hodd_nz W K u hW hK hu_odd hdet0)
      · let m := u / 2
        have hm1 : m ≥ 1 := by dsimp [m]; omega
        have hu_ev : u = 2 * m := by dsimp [m]; omega
        have hc := hclosed W K u hW hK hu
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
        -- Apply `hquad_id` at `(W, K, p2 := 2^m, q3 := 3^m)`:
        let p2 := 2 ^ m
        let q3 := 3 ^ m
        have hp2_ge2 : p2 ≥ 2 := by dsimp [p2]; simpa using pow2_mono_nat hm1
        have hp2_sq : intPowNat (p2 : Int) 2 = ((2 ^ u : Nat) : Int) := by
          rw [hintPow_c, hu_ev, Nat.mul_comm 2 m, ← pow_pow_eq_mul_w5 2 m 2]
        have hq3_sq : intPowNat (q3 : Int) 2 = ((3 ^ u : Nat) : Int) := by
          rw [hintPow_c, hu_ev, Nat.mul_comm 2 m, ← pow_pow_eq_mul_w5 3 m 2]
        have hev_quad := expr4_eq_of_norm_sub_nil _ _ hquad_id (W : Int) (K : Int) (p2 : Int) (q3 : Int)
        have hbr_subst : evalExpr4 (W : Int) (K : Int) (p2 : Int) (q3 : Int)
            (t3u2BracketExpr .v0 .v1 (expr4Pow .v2 2) (expr4Pow .v3 2)) =
            evalExpr4 (W : Int) (K : Int) ((2 ^ u : Nat) : Int) ((3 ^ u : Nat) : Int)
              (t3u2BracketExpr .v0 .v1 .v2 .v3) := by
          unfold t3u2BracketExpr
          simp only [evalExpr4, hexprPow_c, hp2_sq, hq3_sq]
        rw [hbr_subst, hbr0] at hev_quad
        simp only [evalExpr4] at hev_quad
        rcases Int.mul_eq_zero.mp hev_quad.symm with hfm0 | hfp0
        · -- `t3u2FactorMinus = 0`:
          have hsq_m := expr4_eq_of_norm_sub_nil _ _ hsq_m_id (W : Int) (K : Int) (p2 : Int) (q3 : Int)
          simp only [evalExpr4] at hsq_m
          rw [hfm0, Int.mul_zero] at hsq_m
          have hd_m_ev : evalExpr4 (W : Int) (K : Int) (p2 : Int) (q3 : Int)
              (t3u2DiscMinusExpr .v2 .v3) = (t3u2DiscMinusNat m : Int) := by
            unfold t3u2DiscMinusExpr t3u2DiscMinusNat
            simp only [evalExpr4, hexprPow_c, hintPow_c]
            have hq9 : q3 ^ 2 = 9 ^ m := by
              dsimp [q3]; rw [pow_pow_eq_mul_w5 3 m 2, Nat.mul_comm m 2, ← pow_pow_eq_mul_w5 3 2 m]
            have hpm : (p2 : Int) - 1 = ((p2 - 1 : Nat) : Int) := by omega
            have hq1 : ((q3 ^ 2 : Nat) : Int) + 1 = ((9 ^ m + 1 : Nat) : Int) := by rw [hq9]; omega
            rw [hpm, hq1, hintPow_c, hintPow_c, hq9]
            have hp2Q1 : ((p2 ^ 2 : Nat) : Int) * (((9 ^ m + 1) ^ 2 : Nat) : Int) =
                (((p2 * (9 ^ m + 1)) ^ 2 : Nat) : Int) := by
              rw [← Int.natCast_mul]
              apply congrArg (fun n : Nat => (n : Int))
              rw [Nat.pow_two p2, Nat.pow_two (9 ^ m + 1), Nat.pow_two (p2 * (9 ^ m + 1))]
              ac_rfl
            rw [hp2Q1]
            have hsub_le : 8 * p2 * (p2 - 1) ^ 2 * 9 ^ m ≤ (p2 * (9 ^ m + 1)) ^ 2 := by
              by_cases hm_one : m = 1
              · dsimp only [p2]; rw [hm_one]; decide
              · have hm2 : m ≥ 2 := by omega
                have h8_9 : ∀ k : Nat, k ≥ 2 -> 8 * 2 ^ k ≤ 9 ^ k := by
                  intro k hk
                  have hst : ∀ d : Nat, 8 * 2 ^ (2 + d) ≤ 9 ^ (2 + d) := by
                    intro d; induction d with
                    | zero => decide
                    | succ d' ih => rw [Nat.add_succ, Nat.pow_succ 2, Nat.pow_succ 9]; omega
                  simpa [show 2 + (k - 2) = k by omega] using hst (k - 2)
                have hpm2 : (p2 - 1) ^ 2 ≤ p2 ^ 2 := by
                  rw [Nat.pow_two, Nat.pow_two]
                  exact Nat.mul_le_mul (by omega : p2 - 1 ≤ p2) (by omega : p2 - 1 ≤ p2)
                have h1 : 8 * p2 * (p2 - 1) ^ 2 ≤ 9 ^ m * p2 ^ 2 :=
                  Nat.mul_le_mul (h8_9 m hm2) hpm2
                have h2 : 9 ^ m * p2 ^ 2 * 9 ^ m ≤ (p2 * (9 ^ m + 1)) ^ 2 := by
                  rw [Nat.pow_two p2, Nat.pow_two (p2 * (9 ^ m + 1))]
                  have hl : 9 ^ m * (p2 * p2) * 9 ^ m = (p2 * 9 ^ m) * (p2 * 9 ^ m) := by ac_rfl
                  rw [hl]
                  have hle := Nat.mul_le_mul_left p2 (by omega : 9 ^ m ≤ 9 ^ m + 1)
                  exact Nat.mul_le_mul hle hle
                exact Nat.le_trans (Nat.mul_le_mul_right (9 ^ m) h1) h2
            have hrhs_cast : (8 : Int) * ((p2 : Int) * ((((p2 - 1) ^ 2 : Nat) : Int) * ((9 ^ m : Nat) : Int))) =
                ((8 * p2 * (p2 - 1) ^ 2 * 9 ^ m : Nat) : Int) := by
              rw [show (8 : Int) = ((8 : Nat) : Int) from rfl]
              simp only [← Int.natCast_mul]
              apply congrArg (fun n : Nat => (n : Int))
              ac_rfl
            rw [hrhs_cast]
            have hadd_sub : (((p2 * (9 ^ m + 1)) ^ 2 - 8 * p2 * (p2 - 1) ^ 2 * 9 ^ m : Nat) : Int) +
                ((8 * p2 * (p2 - 1) ^ 2 * 9 ^ m : Nat) : Int) =
                (((p2 * (9 ^ m + 1)) ^ 2 : Nat) : Int) := by
              rw [← Int.natCast_add, Nat.sub_add_cancel hsub_le]
            dsimp only [p2] at hadd_sub ⊢
            omega
          rw [hd_m_ev] at hsq_m
          by_cases hm_eq1 : m = 1
          · have hu2 : u = 2 := by omega
            refine ⟨hu2, ?_⟩
            have hm1_p2 : (p2 : Int) = 2 := by dsimp [p2]; rw [hm_eq1]; rfl
            have hm1_q3 : (q3 : Int) = 3 := by dsimp [q3]; rw [hm_eq1]; rfl
            rw [hm1_p2, hm1_q3, hlin_u2 W K] at hfm0
            rcases Int.mul_eq_zero.mp hfm0 with h2a | hb27
            · rcases Int.mul_eq_zero.mp h2a with h2 | ha3
              · omega
              · exact Or.inl (by omega)
            · exact Or.inr (by omega)
          · exfalso
            let X_int := evalExpr4 (W : Int) (K : Int) (p2 : Int) (q3 : Int)
              (.sub (.mul (.mul (.const 2) (.mul .v2 (.mul (.sub .v2 (.const 1)) (.sub (expr4Pow .v3 2) (.const 1))))) .v0)
                    (.mul (.mul .v2 (.mul (.add .v2 (.const 1)) (.add (expr4Pow .v3 2) (.const 1)))) .v1))
            let B_nat := (p2 + 1) * K
            have hB_pos : B_nat ≥ 1 := by
              dsimp [B_nat]; simpa using Nat.mul_le_mul (by omega : 1 ≤ p2 + 1) hK
            have hsq_nat : X_int.natAbs * X_int.natAbs = t3u2DiscMinusNat m * (B_nat * B_nat) := by
              have hX2 : intPowNat X_int 2 = ((X_int.natAbs * X_int.natAbs : Nat) : Int) := by
                simp only [intPowNat, Int.mul_one]
                exact int_mul_self_eq_natAbs_sq X_int
              have hB2 : evalExpr4 (W : Int) (K : Int) (p2 : Int) (q3 : Int)
                  (expr4Pow (.mul (.add .v2 (.const 1)) .v1) 2) = ((B_nat * B_nat : Nat) : Int) := by
                rw [hexprPow_c]; simp only [intPowNat, evalExpr4, Int.mul_one, B_nat]
                have hpp : (p2 : Int) + 1 = ((p2 + 1 : Nat) : Int) := by omega
                rw [hpp]; simp only [Int.natCast_mul]
              change 0 = intPowNat X_int 2 - (t3u2DiscMinusNat m : Int) *
                evalExpr4 (W : Int) (K : Int) (p2 : Int) (q3 : Int)
                  (expr4Pow (.mul (.add .v2 (.const 1)) .v1) 2) at hsq_m
              rw [hX2, hB2, ← Int.natCast_mul] at hsq_m
              omega
            rcases sq_eq_mul_sq_imp_is_sq X_int.natAbs (t3u2DiscMinusNat m) B_nat hB_pos hsq_nat with ⟨s, hs⟩
            exact (hdisc_nsq m hm1).2 (by omega) s hs
        · exfalso
          have hsq_p := expr4_eq_of_norm_sub_nil _ _ hsq_p_id (W : Int) (K : Int) (p2 : Int) (q3 : Int)
          simp only [evalExpr4] at hsq_p
          rw [hfp0, Int.mul_zero] at hsq_p
          have hd_p_ev : evalExpr4 (W : Int) (K : Int) (p2 : Int) (q3 : Int)
              (t3u2DiscPlusExpr .v2 .v3) = (t3u2DiscPlusNat m : Int) := by
            unfold t3u2DiscPlusExpr t3u2DiscPlusNat
            simp only [evalExpr4, hexprPow_c, hintPow_c]
            have hq9 : q3 ^ 2 = 9 ^ m := by
              dsimp [q3]; rw [pow_pow_eq_mul_w5 3 m 2, Nat.mul_comm m 2, ← pow_pow_eq_mul_w5 3 2 m]
            have hpp : (p2 : Int) + 1 = ((p2 + 1 : Nat) : Int) := by omega
            have hq1 : ((q3 ^ 2 : Nat) : Int) + 1 = ((9 ^ m + 1 : Nat) : Int) := by rw [hq9]; omega
            rw [hpp, hq1, hintPow_c, hintPow_c, hq9, show (8 : Int) = ((8 : Nat) : Int) from rfl]
            simp only [← Int.natCast_mul, ← Int.natCast_add]
            apply congrArg (fun n : Nat => (n : Int))
            dsimp only [p2]
            rw [Nat.pow_two (2 ^ m), Nat.pow_two (9 ^ m + 1), Nat.pow_two (2 ^ m * (9 ^ m + 1))]
            have h1 : 2 ^ m * 2 ^ m * ((9 ^ m + 1) * (9 ^ m + 1)) =
                2 ^ m * (9 ^ m + 1) * (2 ^ m * (9 ^ m + 1)) := by ac_rfl
            have h2 : 8 * (2 ^ m * ((2 ^ m + 1) ^ 2 * 9 ^ m)) =
                8 * 2 ^ m * (2 ^ m + 1) ^ 2 * 9 ^ m := by ac_rfl
            rw [h1, h2]
          rw [hd_p_ev] at hsq_p
          let X_int := evalExpr4 (W : Int) (K : Int) (p2 : Int) (q3 : Int)
            (.sub (.mul (.mul (.const 2) (.mul .v2 (.mul (.add .v2 (.const 1)) (.sub (expr4Pow .v3 2) (.const 1))))) .v0)
                  (.mul (.mul .v2 (.mul (.sub .v2 (.const 1)) (.add (expr4Pow .v3 2) (.const 1)))) .v1))
          let B_nat := (p2 - 1) * K
          have hB_pos : B_nat ≥ 1 := by
            dsimp [B_nat]; simpa using Nat.mul_le_mul (by omega : 1 ≤ p2 - 1) hK
          have hsq_nat : X_int.natAbs * X_int.natAbs = t3u2DiscPlusNat m * (B_nat * B_nat) := by
            have hX2 : intPowNat X_int 2 = ((X_int.natAbs * X_int.natAbs : Nat) : Int) := by
              simp only [intPowNat, Int.mul_one]
              exact int_mul_self_eq_natAbs_sq X_int
            have hB2 : evalExpr4 (W : Int) (K : Int) (p2 : Int) (q3 : Int)
                (expr4Pow (.mul (.sub .v2 (.const 1)) .v1) 2) = ((B_nat * B_nat : Nat) : Int) := by
              rw [hexprPow_c]; simp only [intPowNat, evalExpr4, Int.mul_one, B_nat]
              have hpm : (p2 : Int) - 1 = ((p2 - 1 : Nat) : Int) := by omega
              rw [hpm]; simp only [Int.natCast_mul]
            change 0 = intPowNat X_int 2 - (t3u2DiscPlusNat m : Int) *
              evalExpr4 (W : Int) (K : Int) (p2 : Int) (q3 : Int)
                (expr4Pow (.mul (.sub .v2 (.const 1)) .v1) 2) at hsq_p
            rw [hX2, hB2, ← Int.natCast_mul] at hsq_p
            omega
          rcases sq_eq_mul_sq_imp_is_sq X_int.natAbs (t3u2DiscPlusNat m) B_nat hB_pos hsq_nat with ⟨s, hs⟩
          exact (hdisc_nsq m hm1).1 s hs
    · -- Reverse direction: `u = 2 ∧ (8 * W = 3 * K ∨ 8 * W = 27 * K) -> det = 0`:
      rintro ⟨rfl, hray⟩
      have hc := hclosed W K 2 hW hK (by decide)
      have hev_quad := expr4_eq_of_norm_sub_nil _ _ hquad_id (W : Int) (K : Int) 2 3
      have hbr_subst : evalExpr4 (W : Int) (K : Int) 2 3
          (t3u2BracketExpr .v0 .v1 (expr4Pow .v2 2) (expr4Pow .v3 2)) =
          evalExpr4 (W : Int) (K : Int) 4 9
            (t3u2BracketExpr .v0 .v1 .v2 .v3) := by
        unfold t3u2BracketExpr
        simp only [evalExpr4, expr4Pow]
        rfl
      have hfm0 : evalExpr4 (W : Int) (K : Int) 2 3 (t3u2FactorMinus .v0 .v1 .v2 .v3) = 0 := by
        rw [hlin_u2 W K]
        rcases hray with h38 | h278
        · rw [show 8 * (W : Int) - 3 * (K : Int) = 0 by omega]; simp
        · rw [show 8 * (W : Int) - 27 * (K : Int) = 0 by omega]; simp
      have hbr0 : evalExpr4 (W : Int) (K : Int) 4 9 (t3u2BracketExpr .v0 .v1 .v2 .v3) = 0 := by
        rw [← hbr_subst, hev_quad]
        simp only [evalExpr4, hfm0, Int.zero_mul]
      unfold twoBaseT3U2ScaledClosedExpr at hc
      change 4 * intDet 6 (laurentTwoBaseT3U2Mat6 W K 2) =
        evalExpr4 (W : Int) (K : Int) 4 9 (expr4Pow .v1 2) *
          (9 * evalExpr4 (W : Int) (K : Int) 4 9 (t3u2BracketExpr .v0 .v1 .v2 .v3)) at hc
      rw [hbr0, Int.mul_zero, Int.mul_zero] at hc
      omega
  refine ⟨hiff, ?_, ?_⟩
  · intro W K u1 u2 hW hK hu1 hu_lt ⟨hz1, hz2⟩
    have h1 := (hiff W K u1 hW hK hu1).mp hz1
    have h2 := (hiff W K u2 hW hK (by omega)).mp hz2
    omega
  · exact ⟨(hiff 3 8 2 (by decide) (by decide) (by decide)).mpr ⟨rfl, Or.inl rfl⟩,
           (hiff 27 8 2 (by decide) (by decide) (by decide)).mpr ⟨rfl, Or.inr rfl⟩⟩

-- ----------------------------------------------------------------------------
-- Section 2D: Universal `m`-Block Brox Carry Telescoping Bound & Cross-Block
--             Companion-Prime Archimedean Squeeze (Choice-Free)
-- ----------------------------------------------------------------------------

private theorem blockWeightSum_le_stepSum :
    ∀ bs : List (Nat × Nat), blockWeightSum bs ≤ blockStepSum bs
  | [] => Nat.le_refl 0
  | b :: rest => by
    simp only [blockWeightSum, blockStepSum]
    have ih := blockWeightSum_le_stepSum rest
    omega

private theorem broxSpiralCarry_pos_and_telescoping_bound :
    ∀ (b0 : Nat × Nat) (rest : List (Nat × Nat)),
      (∀ b ∈ (b0 :: rest), b.1 ≥ 1 ∧ b.2 ≥ 1) ->
      broxSpiralCarry (b0 :: rest) ≥ 1 ∧
      broxSpiralCarry (b0 :: rest) + 3 ^ blockWeightSum rest ≤
        3 ^ blockWeightSum rest * 2 ^ (blockStepSum (b0 :: rest) - blockWeightSum (b0 :: rest))
  | b0, [], hpos => by
    have hb0 := hpos b0 List.mem_cons_self
    have hp2_ge2 : 2 ^ b0.2 ≥ 2 := by simpa using pow2_mono_nat hb0.2
    simp only [broxSpiralCarry, blockWeightSum, blockStepSum, Nat.add_zero, Nat.pow_zero, Nat.one_mul]
    rw [show b0.1 + b0.2 - b0.1 = b0.2 by omega]
    exact ⟨by omega, by omega⟩
  | b0, b1 :: tail, hpos => by
    have hb0 := hpos b0 List.mem_cons_self
    have hp2_ge2 : 2 ^ b0.2 ≥ 2 := by simpa using pow2_mono_nat hb0.2
    rcases broxSpiralCarry_pos_and_telescoping_bound b1 tail
      (fun b hb => hpos b (List.mem_cons_of_mem b0 hb)) with ⟨hpos_tl, hbd_tl⟩
    simp only [broxSpiralCarry]
    have h3_pos : 3 ^ blockWeightSum (b1 :: tail) ≥ 1 := pow3_pos_nat _
    refine ⟨by have := Nat.mul_le_mul h3_pos (by omega : 1 ≤ 2 ^ b0.2 - 1); omega, ?_⟩
    -- Key inequality: `2 ^ (b0.2 + b1.1) ≤ 2 ^ b0.2 * 3 ^ b1.1` since `2 ^ b1.1 ≤ 3 ^ b1.1`:
    have h2_le_3 : ∀ k : Nat, 2 ^ k ≤ 3 ^ k := by
      intro k; induction k with
      | zero => exact Nat.le_refl 1
      | succ k' ih => rw [Nat.pow_succ, Nat.pow_succ]; omega
    have hp_23 : 2 ^ (b0.2 + b1.1) ≤ 2 ^ b0.2 * 3 ^ b1.1 := by
      rw [Nat.pow_add]; exact Nat.mul_le_mul_left (2 ^ b0.2) (h2_le_3 b1.1)
    let Wt := blockWeightSum tail
    let Et := blockStepSum (b1 :: tail) - blockWeightSum (b1 :: tail)
    have hEt_split : blockStepSum (b0 :: b1 :: tail) - blockWeightSum (b0 :: b1 :: tail) =
        b0.2 + Et := by
      have hle_tl := blockWeightSum_le_stepSum (b1 :: tail)
      dsimp only [Et]
      simp only [blockStepSum, blockWeightSum] at hle_tl ⊢
      omega
    rw [hEt_split]
    have hW1 : blockWeightSum (b1 :: tail) = b1.1 + Wt := rfl
    have h3W1 : 3 ^ (b1.1 + Wt) = 3 ^ b1.1 * 3 ^ Wt := Nat.pow_add 3 b1.1 Wt
    -- Multiply `hbd_tl : broxSpiralCarry (b1 :: tail) + 3 ^ Wt ≤ 3 ^ Wt * 2 ^ Et` by `2 ^ b0.2 * 3 ^ b1.1`:
    have hm_tl := Nat.mul_le_mul_left (2 ^ b0.2 * 3 ^ b1.1) hbd_tl
    rw [Nat.mul_add] at hm_tl
    have hcarry_le : 2 ^ (b0.2 + b1.1) * broxSpiralCarry (b1 :: tail) ≤
        2 ^ b0.2 * 3 ^ b1.1 * broxSpiralCarry (b1 :: tail) :=
      Nat.mul_le_mul_right _ hp_23
    have hrhs_rew : 2 ^ b0.2 * 3 ^ b1.1 * (3 ^ Wt * 2 ^ Et) =
        3 ^ blockWeightSum (b1 :: tail) * 2 ^ (b0.2 + Et) := by
      rw [hW1, h3W1, Nat.pow_add 2 b0.2 Et]; ac_rfl
    have hmid_rew : 2 ^ b0.2 * 3 ^ b1.1 * 3 ^ Wt = 3 ^ blockWeightSum (b1 :: tail) * 2 ^ b0.2 := by
      rw [hW1, h3W1]; ac_rfl
    have hlhs_expand : 3 ^ blockWeightSum (b1 :: tail) * (2 ^ b0.2 - 1) + 3 ^ blockWeightSum (b1 :: tail) =
        3 ^ blockWeightSum (b1 :: tail) * 2 ^ b0.2 := by
      have : 2 ^ b0.2 - 1 + 1 = 2 ^ b0.2 := by omega
      calc
        3 ^ blockWeightSum (b1 :: tail) * (2 ^ b0.2 - 1) + 3 ^ blockWeightSum (b1 :: tail)
            = 3 ^ blockWeightSum (b1 :: tail) * (2 ^ b0.2 - 1 + 1) := by rw [Nat.mul_add, Nat.mul_one]
        _ = 3 ^ blockWeightSum (b1 :: tail) * 2 ^ b0.2 := by rw [this]
    dsimp only [Wt, Et] at hm_tl hcarry_le hrhs_rew hmid_rew hlhs_expand ⊢
    omega

def maxWeightIdx : Nat × Nat -> List (Nat × Nat) -> Nat
  | _, [] => 0
  | b0, b1 :: tail =>
    let j_tl := maxWeightIdx b1 tail
    let b_best := blockAt (b1 :: tail) j_tl
    if b0.1 ≥ b_best.1 then 0 else j_tl + 1

private theorem maxWeightIdx_spec :
    ∀ (b0 : Nat × Nat) (rest : List (Nat × Nat)),
      let blocks := b0 :: rest
      let j := maxWeightIdx b0 rest
      j < blocks.length ∧
      (∀ b ∈ blocks, b.1 ≤ (blockAt blocks j).1) ∧
      blocks.length * (blockAt blocks j).1 ≥ blockWeightSum blocks
  | b0, [] => by
    simp [maxWeightIdx, blockAt, blockWeightSum]
  | b0, b1 :: tail => by
    rcases maxWeightIdx_spec b1 tail with ⟨hj_lt, hall_tl, _⟩
    let j_tl := maxWeightIdx b1 tail
    change (if b0.1 ≥ (blockAt (b1 :: tail) j_tl).1 then 0 else j_tl + 1) < (b0 :: b1 :: tail).length ∧
      (∀ b ∈ b0 :: b1 :: tail,
        b.1 ≤ (blockAt (b0 :: b1 :: tail) (if b0.1 ≥ (blockAt (b1 :: tail) j_tl).1 then 0 else j_tl + 1)).1) ∧
      (b0 :: b1 :: tail).length *
        (blockAt (b0 :: b1 :: tail) (if b0.1 ≥ (blockAt (b1 :: tail) j_tl).1 then 0 else j_tl + 1)).1 ≥
        blockWeightSum (b0 :: b1 :: tail)
    have hsum_le : ∀ (M : Nat) (bs : List (Nat × Nat)),
        (∀ b ∈ bs, b.1 ≤ M) -> blockWeightSum bs ≤ bs.length * M := by
      intro M bs; induction bs with
      | nil => intro _; simp [blockWeightSum]
      | cons x xs ih =>
        intro hall
        simp only [blockWeightSum, List.length_cons, Nat.add_mul, Nat.one_mul]
        have hx := hall x List.mem_cons_self
        have hxs := ih (fun y hy => hall y (List.mem_cons_of_mem x hy))
        omega
    split
    · next hge =>
      have hb0_at : blockAt (b0 :: b1 :: tail) 0 = b0 := rfl
      have hall_all : ∀ b ∈ (b0 :: b1 :: tail), b.1 ≤ (blockAt (b0 :: b1 :: tail) 0).1 := by
        rw [hb0_at]
        intro b hb
        rcases List.mem_cons.mp hb with rfl | htl
        · exact Nat.le_refl _
        · exact Nat.le_trans (hall_tl b htl) hge
      exact ⟨by simp, hall_all, hsum_le _ _ hall_all⟩
    · next hge =>
      have hsucc_at : blockAt (b0 :: b1 :: tail) (j_tl + 1) = blockAt (b1 :: tail) j_tl := rfl
      have hall_all : ∀ b ∈ (b0 :: b1 :: tail), b.1 ≤ (blockAt (b0 :: b1 :: tail) (j_tl + 1)).1 := by
        rw [hsucc_at]
        intro b hb
        rcases List.mem_cons.mp hb with rfl | htl
        · omega
        · exact hall_tl b htl
      exact ⟨by simp at hj_lt ⊢; omega, hall_all, hsum_le _ _ hall_all⟩

private theorem rotBlocks_cons_of_lt :
    ∀ (blocks : List (Nat × Nat)) (j : Nat),
      j < blocks.length ->
      ∃ rest_j : List (Nat × Nat), rotBlocks j blocks = blockAt blocks j :: rest_j := by
  intro blocks j hj
  unfold rotBlocks blockAt
  have hdrop_ne : blocks.drop j ≠ [] := by
    intro hemp
    have hlen := List.length_drop (i := j) (l := blocks)
    rw [hemp] at hlen; simp at hlen; omega
  cases hd : blocks.drop j with
  | nil => exact False.elim (hdrop_ne hd)
  | cons b tl => exact ⟨tl ++ blocks.take j, by simp⟩

private theorem mem_of_mem_rotBlocks_w13 {α : Type} (j : Nat) :
    ∀ (xs : List α) (x : α), x ∈ (xs.drop j ++ xs.take j) -> x ∈ xs := by
  have hm_drop : ∀ (k : Nat) (l : List α) (x : α), x ∈ l.drop k -> x ∈ l := by
    intro k; induction k with
    | zero => intro l x hx; simpa using hx
    | succ k' ih =>
      intro l x hx; cases l with
      | nil => simp at hx
      | cons _ tl => exact List.mem_cons_of_mem _ (ih tl x hx)
  have hm_take : ∀ (k : Nat) (l : List α) (x : α), x ∈ l.take k -> x ∈ l := by
    intro k; induction k with
    | zero => intro _ _ hx; simp at hx
    | succ k' ih =>
      intro l x hx; cases l with
      | nil => simp at hx
      | cons y tl =>
        simp only [List.take_succ_cons, List.mem_cons] at hx
        rcases hx with rfl | htl
        · exact List.Mem.head _
        · exact List.mem_cons_of_mem y (ih tl x htl)
  intro xs x hx
  rcases List.mem_append.mp hx with hd | ht
  · exact hm_drop j xs x hd
  · exact hm_take j xs x ht

/--
  Theorem W13.2d (`m_block_brox_carry_bound_and_cross_block_squeeze`,
  choice-free `zero custom axioms`):
  Universal `m`-Block Brox Carry Telescoping Bound & Cross-Block Companion-Prime Archimedean Squeeze
  (`Branch P3.4`, `W13_H2`):
  1. **Universal `∀ m ≥ 1` Rotated Brox Carry Telescoping Bound (`blocks = b0 :: rest`)**:
     For EVERY rotation `j < blocks.length` (with `W := blockWeightSum blocks`, `K := blockStepSum blocks`,
     `∀ b ∈ blocks, b.1 ≥ 1 ∧ b.2 ≥ 1`):
       `broxSpiralCarry (rotBlocks j blocks) ≥ 1` AND
       `broxSpiralCarry (rotBlocks j blocks) + 3 ^ (W - (blockAt blocks j).1) ≤
         3 ^ (W - (blockAt blocks j).1) * 2 ^ (K - W)`!
  2. **Universal Cross-Block Companion-Prime + Archimedean Squeeze (`d_mult ∣ natListGcd qs`)**:
     Whenever `3 ^ W < 2 ^ K`, `qs.length = blocks.length`, `∀ j < blocks.length, D * natAt qs j =
     broxSpiralCarry (rotBlocks j blocks)`, and `d_mult ∣ natListGcd qs` (such as `d_mult ∈ {3, 15, 255,
     51, 7, 31, 511, 73}` from `m_block_companion_prime_quotient_cascades`!), EVERY rotation `j < blocks.length`
     satisfies `natAt qs j ≥ 1` and:
       `d_mult * (2 ^ K - 3 ^ W) + 3 ^ (W - (blockAt blocks j).1) ≤
         3 ^ (W - (blockAt blocks j).1) * 2 ^ (K - W)`
     — and in particular at `j_star := maxWeightIdx b0 rest` (`blocks.length * w_{j_star} ≥ W`),
     unconditionally eliminating EVERY structured `m`-block family violating this inequality!
  3. **Asymmetric `m = 2` Rotation Sharpness Certificate (`blocks = [(1, 2), (5, 2)]`, `W13_H2` Witness)**:
     At `blocks_asym := [(1, 2), (5, 2)]` (`W = 6, K = 10, D = 2^10 - 3^6 = 295`, `2 ∣ b.2` so `d_mult = 3`),
     unrotated `j = 0` (`w_0 = 1`) has `broxSpiralCarry blocks_asym = 1113 > 885 = 3 * 295`
     (`M1` cycle has `q_0 = 1113 / 295 > 3`!), whereas rotating to `j_star = 1` (`w_1 = 5`) gives
     `broxSpiralCarry (rotBlocks 1 blocks_asym) = 33 ≤ 45 = 3 ^ 1 * (2 ^ 4 - 1) < 885 = 3 * 295`,
     unconditionally refuting `[(1, 2), (5, 2)]` over `Z^+`!
-/
theorem m_block_brox_carry_bound_and_cross_block_squeeze :
    (∀ (b0 : Nat × Nat) (rest : List (Nat × Nat)),
      let blocks := b0 :: rest
      let W := blockWeightSum blocks
      let K := blockStepSum blocks
      (∀ b ∈ blocks, b.1 ≥ 1 ∧ b.2 ≥ 1) ->
      (∀ j : Nat, j < blocks.length ->
        broxSpiralCarry (rotBlocks j blocks) ≥ 1 ∧
        broxSpiralCarry (rotBlocks j blocks) + 3 ^ (W - (blockAt blocks j).1) ≤
          3 ^ (W - (blockAt blocks j).1) * 2 ^ (K - W)) ∧
      (maxWeightIdx b0 rest < blocks.length ∧
       blocks.length * (blockAt blocks (maxWeightIdx b0 rest)).1 ≥ W)) ∧
    (∀ (b0 : Nat × Nat) (rest : List (Nat × Nat)) (qs : List Nat) (d_mult : Nat),
      let blocks := b0 :: rest
      let W := blockWeightSum blocks
      let K := blockStepSum blocks
      let D := 2 ^ K - 3 ^ W
      (∀ b ∈ blocks, b.1 ≥ 1 ∧ b.2 ≥ 1) ->
      3 ^ W < 2 ^ K ->
      qs.length = blocks.length ->
      (∀ j : Nat, j < blocks.length -> D * natAt qs j = broxSpiralCarry (rotBlocks j blocks)) ->
      d_mult ∣ natListGcd qs ->
      (∀ j : Nat, j < blocks.length ->
        natAt qs j ≥ 1 ∧
        d_mult * D + 3 ^ (W - (blockAt blocks j).1) ≤
          3 ^ (W - (blockAt blocks j).1) * 2 ^ (K - W)) ∧
      ((∀ b ∈ blocks, 2 ∣ b.2) ->
        3 * D + 3 ^ (W - (blockAt blocks (maxWeightIdx b0 rest)).1) ≤
          3 ^ (W - (blockAt blocks (maxWeightIdx b0 rest)).1) * 2 ^ (K - W))) ∧
    (let blocks_asym : List (Nat × Nat) := [(1, 2), (5, 2)]
     2 ^ blockStepSum blocks_asym - 3 ^ blockWeightSum blocks_asym = 295 ∧
     broxSpiralCarry blocks_asym = 1113 ∧
     1113 > 3 * 295 ∧
     maxWeightIdx (1, 2) [(5, 2)] = 1 ∧
     broxSpiralCarry (rotBlocks 1 blocks_asym) = 33 ∧
     33 < 3 * 295) := by
  have hrot_bound : ∀ (b0 : Nat × Nat) (rest : List (Nat × Nat)),
      let blocks := b0 :: rest
      let W := blockWeightSum blocks
      let K := blockStepSum blocks
      (∀ b ∈ blocks, b.1 ≥ 1 ∧ b.2 ≥ 1) ->
      ∀ j : Nat, j < blocks.length ->
        broxSpiralCarry (rotBlocks j blocks) ≥ 1 ∧
        broxSpiralCarry (rotBlocks j blocks) + 3 ^ (W - (blockAt blocks j).1) ≤
          3 ^ (W - (blockAt blocks j).1) * 2 ^ (K - W) := by
    intro b0 rest; dsimp only; intro hpos j hj_lt
    let blocks := b0 :: rest
    rcases rotBlocks_cons_of_lt blocks j hj_lt with ⟨rest_j, hrot_eq⟩
    rcases blockSums_rotBlocks j blocks with ⟨hw_rot, hk_rot⟩
    have hpos_rot : ∀ b ∈ (blockAt blocks j :: rest_j), b.1 ≥ 1 ∧ b.2 ≥ 1 := by
      intro b hb
      rw [← hrot_eq] at hb
      exact hpos b (mem_of_mem_rotBlocks_w13 j blocks b hb)
    rcases broxSpiralCarry_pos_and_telescoping_bound (blockAt blocks j) rest_j hpos_rot with
      ⟨hc_pos, hc_bd⟩
    rw [← hrot_eq] at hc_pos hc_bd
    have hrest_w : blockWeightSum rest_j = blockWeightSum blocks - (blockAt blocks j).1 := by
      rw [hrot_eq, blockWeightSum] at hw_rot
      omega
    rw [hrest_w, hw_rot, hk_rot] at hc_bd
    exact ⟨hc_pos, hc_bd⟩
  refine ⟨?_, ?_, ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩⟩
  · intro b0 rest; dsimp only; intro hpos
    rcases maxWeightIdx_spec b0 rest with ⟨hj_lt, _, hj_avg⟩
    exact ⟨hrot_bound b0 rest hpos, hj_lt, hj_avg⟩
  · intro b0 rest qs d_mult; dsimp only; intro hpos hgt hq_len hqs_eq hd_gcd
    have hall_j : ∀ (d_m : Nat), d_m ∣ natListGcd qs -> ∀ j : Nat, j < (b0 :: rest).length ->
        natAt qs j ≥ 1 ∧
        d_m * (2 ^ blockStepSum (b0 :: rest) - 3 ^ blockWeightSum (b0 :: rest)) +
            3 ^ (blockWeightSum (b0 :: rest) - (blockAt (b0 :: rest) j).1) ≤
          3 ^ (blockWeightSum (b0 :: rest) - (blockAt (b0 :: rest) j).1) *
            2 ^ (blockStepSum (b0 :: rest) - blockWeightSum (b0 :: rest)) := by
      intro d_m hd_m j hj_lt
      rcases hrot_bound b0 rest hpos j hj_lt with ⟨hc_pos, hc_bd⟩
      have hqj_eq := hqs_eq j hj_lt
      have hqj_pos : natAt qs j ≥ 1 := by
        if hz : natAt qs j = 0 then
          rw [hz, Nat.mul_zero] at hqj_eq; omega
        else
          omega
      have hj_qs : j < qs.length := by rw [hq_len]; exact hj_lt
      have hd_qj : d_m ∣ natAt qs j := Nat.dvd_trans hd_m (natListGcd_dvd_natAt qs j hj_qs)
      rcases hd_qj with ⟨k_q, hkq⟩
      have hdm_le : d_m ≤ natAt qs j := by
        cases k_q with
        | zero => rw [Nat.mul_zero] at hkq; omega
        | succ k' => rw [hkq, Nat.mul_succ]; omega
      have hmD : d_m * (2 ^ blockStepSum (b0 :: rest) - 3 ^ blockWeightSum (b0 :: rest)) ≤
          (2 ^ blockStepSum (b0 :: rest) - 3 ^ blockWeightSum (b0 :: rest)) * natAt qs j := by
        rw [Nat.mul_comm (2 ^ blockStepSum (b0 :: rest) - 3 ^ blockWeightSum (b0 :: rest))]
        exact Nat.mul_le_mul_right _ hdm_le
      rw [hqj_eq] at hmD
      exact ⟨hqj_pos, by omega⟩
    refine ⟨hall_j d_mult hd_gcd, ?_⟩
    intro h2_all
    have h3_gcd : 3 ∣ natListGcd qs :=
      (m_block_companion_prime_quotient_cascades.1 b0 rest qs hpos hgt hq_len hqs_eq).2.1 h2_all
    rcases maxWeightIdx_spec b0 rest with ⟨hj_lt, _, _⟩
    exact (hall_j 3 h3_gcd (maxWeightIdx b0 rest) hj_lt).2

end CollatzFormal

