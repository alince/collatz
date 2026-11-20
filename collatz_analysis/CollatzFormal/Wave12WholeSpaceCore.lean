/-
  CollatzFormal/Wave12WholeSpaceCore.lean
  Wave 12 Whole-Space Mathematical & CS Proof Loop (Core — Fronts A & B):
  1. Front A — Non-Parikh `d ≥ 2` Commutator Trace-Diagonal Lock (`A * B ≥ B * A ->
     (A * B) i i = (B * A) i i` + `d = 2` Off-Diagonal Sharpness Certificate), Complete
     `1D`-Affine (`m_s ≥ 1`) / `d ≥ 1` Diagonal Coordinatewise-Monotone / `d ≥ 1` Upper-Unitriangular
     (`Pol_d`) Collapse on `TwoSided(2 × 3)` `c39` & `TwoSided(2 × 6)` `c78` (`omit R3`),
     Unconditional `.R`-Free Termination of `leftAnchoredDP2Step` (`leftAnchoredDP2_r_free_terminates`, choice-free `zero custom axioms`), & Universal
     `M1 = 19/5` `R3`-Free Bounded-Prefix Simulation Obstruction (`∀ W_pref ≥ 1`, Branch P4.3)
  2. Front B — Universal Arbitrary-`T` Confluent `2^(T*(T-1)/2 * u) * (2^u - 1)^(T^2)` Zero-Gap
     Determinant Divisibility (`∀ L, T ≥ 1` + `(2T) × (2T)` Rank-2 Two-Base Grids), Universal
     `4 × 4` Multi-`u` Zero-Multiplicity `≤ 1` (`∀ 1 ≤ u1 < u2`), Rank-3 Two-Base `9 × 9`
     `(T = 3, U = 3)` Closed Form / `P^1(F_61)` Universal Non-Vanishing / `2^569 < 3^359`
     Convergent-Cone Positivity / Outer `(1, 3, 1)` Sign-Flip, Exact Prime-Power `ℓ^r` Sylow
     Order-Lock Biconditional on `q ≡ 1 (mod 24)` (`q = 457`, `q = 601`, `p_3 = 45,661,129`), &
     Universal `∀ m ≥ 1` `m`-Block Companion-Prime Quotient Cascades (`15, 255, 7, 31, 511`, Branches P3.3 & P3.4)

  Zero `sorry`, zero `native_decide`, zero custom axioms.
-/

import CollatzFormal.Wave11WholeSpace

namespace CollatzFormal

-- ============================================================================
-- SECTION 1: Front A (Branch P4.3) — Non-Parikh Commutator Diagonal Lock,
--            `c39` / `c78` `1D`-Affine & `d ≥ 1` Monotone / `Pol_d` Collapse,
--            `.R`-Free `DP2` Termination, & `M1 = 19/5` Bounded-Prefix Barrier
-- ============================================================================

-- ----------------------------------------------------------------------------
-- Section 1A: Trace Symmetry & Commutator Diagonal Lock (`∀ d : Nat`)
-- ----------------------------------------------------------------------------

private theorem natSumPrefix_swap_fin2 :
    ∀ (d m n : Nat) (_hm : m ≤ d) (_hn : n ≤ d) (F : Fin d -> Fin d -> Nat),
      natSumPrefix d (fun i => natSumPrefix d (fun j => F i j) n) m =
        natSumPrefix d (fun j => natSumPrefix d (fun i => F i j) m) n
  | _, 0, 0, _, _, _ => rfl
  | d, 0, n + 1, hm, hn, F => by
    have hn_lt : n < d := hn
    simp only [natSumPrefix, hn_lt, dite_true, Nat.add_zero]
    exact natSumPrefix_swap_fin2 d 0 n hm (Nat.le_of_lt hn) F
  | d, m + 1, n, hm, hn, F => by
    have hm_lt : m < d := hm
    simp only [natSumPrefix, hm_lt, dite_true]
    rw [natSumPrefix_swap_fin2 d m n (Nat.le_of_lt hm) hn F]
    clear hm
    induction n with
    | zero => rfl
    | succ n' ih =>
      have hn'_lt : n' < d := hn
      have hih := ih (Nat.le_of_lt hn)
      dsimp only [natSumPrefix] at hih ⊢
      simp only [hn'_lt, dite_true]
      omega

private theorem natSumPrefix_eq_of_le_and_sum_eq (d : Nat) (f g : Fin d -> Nat)
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
    · exact natSumPrefix_eq_of_le_and_sum_eq d f g hle k (Nat.le_of_lt hk) hpre_le i (by omega)

def commSharpMatT2 (i j : Fin 2) : Nat :=
  match i.val, j.val with
  | 0, 0 => 1 | 0, _ => 1
  | _, 0 => 0 | _, _ => 1

def commSharpMatB1 (i j : Fin 2) : Nat :=
  match i.val, j.val with
  | 0, 0 => 1 | 0, _ => 0
  | _, 0 => 0 | _, _ => 2

/--
  Theorem W12.1a (`natMatMul_commutator_diag_eq`, choice-free `zero custom axioms`):
  Universal `∀ d : Nat` Non-Commutative Matrix Commutator Diagonal Lock & `2D` Off-Diagonal Sharpness:
  1. **Exact Trace Symmetry (`tr(A * B) = tr(B * A)`)**:
       `natSumFin d (fun i => natMatMul d A B i i) = natSumFin d (fun i => natMatMul d B A i i)`.
  2. **Universal Diagonal Equality Under Entrywise Commutator Orientation (`A * B ≥ B * A`)**:
     Whenever entrywise `∀ i j : Fin d, natMatMul d A B i j ≥ natMatMul d B A i j` holds (as required
     on every `R8 : [T2, B1] -> [B1, T2]` or `R3 : [T0, B0] -> [B0, T0]` swap rule in a Hofbauer–Waldmann
     matrix interpretation), EVERY diagonal entry satisfies `natMatMul d A B i i = natMatMul d B A i i`!
  3. **Sharp `2D` Off-Diagonal Commutator Certificate**:
     `commSharpMatT2 = [[1, 1], [0, 1]]` and `commSharpMatB1 = [[1, 0], [0, 2]]` satisfy entrywise
     `T2 * B1 ≥ B1 * T2` with strict off-diagonal drop `(T2 * B1) 0 1 = 2 > 1 = (B1 * T2) 0 1`!
-/
theorem natMatMul_commutator_diag_eq :
    (∀ (d : Nat) (A B : Fin d -> Fin d -> Nat),
      natSumFin d (fun i => natMatMul d A B i i) =
        natSumFin d (fun i => natMatMul d B A i i)) ∧
    (∀ (d : Nat) (A B : Fin d -> Fin d -> Nat),
      (∀ i j : Fin d, natMatMul d A B i j ≥ natMatMul d B A i j) ->
      ∀ i : Fin d, natMatMul d A B i i = natMatMul d B A i i) ∧
    ((∀ i j : Fin 2,
        natMatMul 2 commSharpMatT2 commSharpMatB1 i j ≥
          natMatMul 2 commSharpMatB1 commSharpMatT2 i j) ∧
     natMatMul 2 commSharpMatT2 commSharpMatB1 ⟨0, by decide⟩ ⟨1, by decide⟩ >
       natMatMul 2 commSharpMatB1 commSharpMatT2 ⟨0, by decide⟩ ⟨1, by decide⟩) := by
  have htr : ∀ (d : Nat) (A B : Fin d -> Fin d -> Nat),
      natSumFin d (fun i => natMatMul d A B i i) =
        natSumFin d (fun i => natMatMul d B A i i) := by
    intro d A B
    dsimp only [natSumFin, natMatMul]
    have hsw := natSumPrefix_swap_fin2 d d d (Nat.le_refl d) (Nat.le_refl d) (fun i k => A i k * B k i)
    rw [hsw]
    have hcong : ∀ m : Nat, m ≤ d ->
        natSumPrefix d (fun k => natSumPrefix d (fun i => A i k * B k i) d) m =
          natSumPrefix d (fun k => natSumPrefix d (fun i => B k i * A i k) d) m := by
      intro m hm; induction m with
      | zero => rfl
      | succ m' ih =>
        have hm'_lt : m' < d := hm
        simp only [natSumPrefix, hm'_lt, dite_true, ih (Nat.le_of_lt hm)]
        apply congrArg (natSumPrefix d _ m' + ·)
        have hinner : ∀ n : Nat, n ≤ d ->
            natSumPrefix d (fun i => A i ⟨m', hm'_lt⟩ * B ⟨m', hm'_lt⟩ i) n =
              natSumPrefix d (fun i => B ⟨m', hm'_lt⟩ i * A i ⟨m', hm'_lt⟩) n := by
          intro n hn; induction n with
          | zero => rfl
          | succ n' ihn =>
            have hn'_lt : n' < d := hn
            simp only [natSumPrefix, hn'_lt, dite_true, ihn (Nat.le_of_lt hn), Nat.mul_comm]
        exact hinner d (Nat.le_refl d)
    exact hcong d (Nat.le_refl d)
  refine ⟨htr, ?_, ⟨by decide, by decide⟩⟩
  intro d A B hge i
  have hle_diag : ∀ k : Fin d, natMatMul d B A k k ≤ natMatMul d A B k k := fun k => hge k k
  have hsum_eq := htr d A B
  unfold natSumFin at hsum_eq
  exact natSumPrefix_eq_of_le_and_sum_eq d
    (fun k => natMatMul d A B k k) (fun k => natMatMul d B A k k)
    hle_diag d (Nat.le_refl d) (by omega) i i.isLt

-- ----------------------------------------------------------------------------
-- Section 1B: `1D`-Affine, Diagonal Monotone, & Upper-Unitriangular (`Pol_d`)
--             Collapse on `TwoSided(2 × 3)` `c39` & `TwoSided(2 × 6)` `c78`
-- ----------------------------------------------------------------------------

def evalFinAffine1D (N : Nat) (m v : Fin N -> Nat) : List (Fin N) -> Nat × Nat
  | [] => (1, 0)
  | s :: rest =>
    let r := evalFinAffine1D N m v rest
    (m s * r.1, v s + m s * r.2)

def GenOmegaAffine1DFinTower (N : Nat) : Nat -> List (List (Fin N) × List (Fin N)) -> Prop
  | 0, rules => rules = []
  | k + 1, rules =>
    rules = [] ∨
    ∃ (rem : List (List (Fin N) × List (Fin N))) (m v : Fin N -> Nat),
      (∀ s : Fin N, m s ≥ 1) ∧
      (∀ r ∈ rules,
        (evalFinAffine1D N m v r.1).1 ≥ (evalFinAffine1D N m v r.2).1 ∧
        (evalFinAffine1D N m v r.1).2 ≥ (evalFinAffine1D N m v r.2).2) ∧
      (∀ r ∈ rules,
        ¬ ((evalFinAffine1D N m v r.1).2 > (evalFinAffine1D N m v r.2).2) -> r ∈ rem) ∧
      GenOmegaAffine1DFinTower N k rem

def evalFinWordMat (N d : Nat) (M : Fin N -> Fin d -> Fin d -> Nat) :
    List (Fin N) -> Fin d -> Fin d -> Nat
  | [] => natMatId d
  | s :: rest => natMatMul d (M s) (evalFinWordMat N d M rest)

def evalFinWordVec (N d : Nat) (M : Fin N -> Fin d -> Fin d -> Nat) (v : Fin N -> Fin d -> Nat) :
    List (Fin N) -> Fin d -> Nat
  | [] => fun _ => 0
  | s :: rest =>
    let r := evalFinWordVec N d M v rest
    fun i => v s i + natMatVec d (M s) r i

def GenOmegaDiagCoordMonoMatTower (N d : Nat) (hd : d ≥ 1) :
    Nat -> List (List (Fin N) × List (Fin N)) -> Prop
  | 0, rules => rules = []
  | k + 1, rules =>
    rules = [] ∨
    ∃ (rem : List (List (Fin N) × List (Fin N)))
      (M : Fin N -> Fin d -> Fin d -> Nat) (v : Fin N -> Fin d -> Nat),
      (∀ (s : Fin N) (i : Fin d), M s i i ≥ 1) ∧
      (∀ (s : Fin N) (i j : Fin d), i ≠ j -> M s i j = 0) ∧
      (∀ r ∈ rules,
        (∀ i j : Fin d, evalFinWordMat N d M r.1 i j ≥ evalFinWordMat N d M r.2 i j) ∧
        (∀ i : Fin d, evalFinWordVec N d M v r.1 i ≥ evalFinWordVec N d M v r.2 i)) ∧
      (∀ r ∈ rules,
        ¬ (evalFinWordVec N d M v r.1 ⟨0, hd⟩ > evalFinWordVec N d M v r.2 ⟨0, hd⟩) -> r ∈ rem) ∧
      GenOmegaDiagCoordMonoMatTower N d hd k rem

def GenOmegaUnitriangularMatTower (N d : Nat) (hd : d ≥ 1) :
    Nat -> List (List (Fin N) × List (Fin N)) -> Prop
  | 0, rules => rules = []
  | k + 1, rules =>
    rules = [] ∨
    ∃ (rem : List (List (Fin N) × List (Fin N)))
      (M : Fin N -> Fin d -> Fin d -> Nat) (v : Fin N -> Fin d -> Nat),
      (∀ (s : Fin N) (i : Fin d), M s i i = 1) ∧
      (∀ (s : Fin N) (i j : Fin d), j.val < i.val -> M s i j = 0) ∧
      (∀ r ∈ rules,
        (∀ i j : Fin d, evalFinWordMat N d M r.1 i j ≥ evalFinWordMat N d M r.2 i j) ∧
        (∀ i : Fin d, evalFinWordVec N d M v r.1 i ≥ evalFinWordVec N d M v r.2 i)) ∧
      (∀ r ∈ rules,
        ¬ (evalFinWordVec N d M v r.1 ⟨0, hd⟩ > evalFinWordVec N d M v r.2 ⟨0, hd⟩) -> r ∈ rem) ∧
      GenOmegaUnitriangularMatTower N d hd k rem

private theorem bool_or_split {a b : Bool} (h : (a || b) = true) : a = true ∨ b = true := by
  cases a <;> cases b <;> simp at h ⊢

private theorem mul_pow_w12 (a b : Nat) : ∀ n : Nat, (a * b) ^ n = a ^ n * b ^ n
  | 0 => rfl
  | n + 1 => by
    rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, mul_pow_w12 a b n]
    ac_rfl

private theorem pow_mono_base_w12 (a b : Nat) (hle : a ≤ b) : ∀ n : Nat, a ^ n ≤ b ^ n
  | 0 => Nat.le_refl 1
  | n + 1 => Nat.mul_le_mul (pow_mono_base_w12 a b hle n) hle

private def prodFinWord (N : Nat) (m : Fin N -> Nat) : List (Fin N) -> Nat
  | [] => 1
  | s :: rest => m s * prodFinWord N m rest

private theorem evalFinAffine1D_fst (N : Nat) (m v : Fin N -> Nat) :
    ∀ w : List (Fin N), (evalFinAffine1D N m v w).1 = prodFinWord N m w
  | [] => rfl
  | _ :: rest => by simp [evalFinAffine1D, prodFinWord, evalFinAffine1D_fst N m v rest]

private theorem prodFinWord_pos (N : Nat) (m : Fin N -> Nat) (hm : ∀ s : Fin N, m s ≥ 1) :
    ∀ w : List (Fin N), prodFinWord N m w ≥ 1
  | [] => Nat.le_refl 1
  | s :: rest => Nat.mul_le_mul (hm s) (prodFinWord_pos N m hm rest)

private def weightedProdLhs (N : Nat) (m : Fin N -> Nat) :
    List (List (Fin N) × List (Fin N)) -> List Nat -> Nat
  | [], _ => 1
  | _, [] => 1
  | r :: rs, u :: us => (prodFinWord N m r.1) ^ u * weightedProdLhs N m rs us

private def weightedProdRhs (N : Nat) (m : Fin N -> Nat) :
    List (List (Fin N) × List (Fin N)) -> List Nat -> Nat
  | [], _ => 1
  | _, [] => 1
  | r :: rs, u :: us => (prodFinWord N m r.2) ^ u * weightedProdRhs N m rs us

private theorem prodFinWord_eq_sym_pow_prefix (N : Nat) (m : Fin N -> Nat) :
    ∀ w : List (Fin N),
      prodFinWord N m w = colBoundProdPrefix N (fun s => (m s) ^ countFinOcc N s w) N
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
    simp only [prodFinWord, prodFinWord_eq_sym_pow_prefix N m rest]
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

private theorem colBoundProdPrefix_pow_mul (N : Nat) (m : Fin N -> Nat)
    (f g : Fin N -> Nat) (u : Nat) :
    ∀ k : Nat, k ≤ N ->
      (colBoundProdPrefix N (fun s => (m s) ^ f s) k) ^ u *
        colBoundProdPrefix N (fun s => (m s) ^ g s) k =
      colBoundProdPrefix N (fun s => (m s) ^ (u * f s + g s)) k
  | 0, _ => by simp [colBoundProdPrefix]
  | k + 1, hk => by
    have hk_lt : k < N := hk
    simp only [colBoundProdPrefix, hk_lt, dite_true]
    rw [mul_pow_w12 _ _ u,
        pow_pow_eq_mul_w5 (m ⟨k, hk_lt⟩) (f ⟨k, hk_lt⟩) u,
        Nat.mul_comm (f ⟨k, hk_lt⟩) u]
    have ih := colBoundProdPrefix_pow_mul N m f g u k (Nat.le_of_lt hk)
    calc
      ((colBoundProdPrefix N (fun s => (m s) ^ f s) k) ^ u * (m ⟨k, hk_lt⟩) ^ (u * f ⟨k, hk_lt⟩)) *
          (colBoundProdPrefix N (fun s => (m s) ^ g s) k * (m ⟨k, hk_lt⟩) ^ g ⟨k, hk_lt⟩)
          = ((colBoundProdPrefix N (fun s => (m s) ^ f s) k) ^ u *
              colBoundProdPrefix N (fun s => (m s) ^ g s) k) *
            ((m ⟨k, hk_lt⟩) ^ (u * f ⟨k, hk_lt⟩) * (m ⟨k, hk_lt⟩) ^ g ⟨k, hk_lt⟩) := by ac_rfl
      _ = colBoundProdPrefix N (fun s => (m s) ^ (u * f s + g s)) k *
            (m ⟨k, hk_lt⟩) ^ (u * f ⟨k, hk_lt⟩ + g ⟨k, hk_lt⟩) := by
            rw [ih, ← Nat.pow_add]

private theorem weightedProd_eq_sym_pow (N : Nat) (m : Fin N -> Nat) :
    ∀ (rules : List (List (Fin N) × List (Fin N))) (mults : List Nat),
      weightedProdLhs N m rules mults =
        colBoundProdPrefix N (fun s => (m s) ^ weightedSymLhsSum N s rules mults) N ∧
      weightedProdRhs N m rules mults =
        colBoundProdPrefix N (fun s => (m s) ^ weightedSymRhsSum N s rules mults) N
  | [], _ => by
    have hz : ∀ k : Nat, k ≤ N -> colBoundProdPrefix N (fun _ => 1) k = 1 := by
      intro k hk; induction k with
      | zero => rfl
      | succ k' ih =>
        have hk'_lt : k' < N := hk
        simp only [colBoundProdPrefix, hk'_lt, dite_true]
        rw [ih (Nat.le_of_lt hk), Nat.mul_one]
    refine ⟨?_, ?_⟩ <;> simpa [weightedProdLhs, weightedProdRhs, weightedSymLhsSum, weightedSymRhsSum]
      using (hz N (Nat.le_refl N)).symm
  | _ :: _, [] => by
    have hz : ∀ k : Nat, k ≤ N -> colBoundProdPrefix N (fun _ => 1) k = 1 := by
      intro k hk; induction k with
      | zero => rfl
      | succ k' ih =>
        have hk'_lt : k' < N := hk
        simp only [colBoundProdPrefix, hk'_lt, dite_true]
        rw [ih (Nat.le_of_lt hk), Nat.mul_one]
    refine ⟨?_, ?_⟩ <;> simpa [weightedProdLhs, weightedProdRhs, weightedSymLhsSum, weightedSymRhsSum]
      using (hz N (Nat.le_refl N)).symm
  | r0 :: rs, u0 :: us => by
    rcases weightedProd_eq_sym_pow N m rs us with ⟨hl, hr⟩
    refine ⟨?_, ?_⟩
    · simp only [weightedProdLhs, hl, prodFinWord_eq_sym_pow_prefix N m r0.1]
      exact colBoundProdPrefix_pow_mul N m _ _ u0 N (Nat.le_refl N)
    · simp only [weightedProdRhs, hr, prodFinWord_eq_sym_pow_prefix N m r0.2]
      exact colBoundProdPrefix_pow_mul N m _ _ u0 N (Nat.le_refl N)

private theorem colBoundProdPrefix_mono_pos (N : Nat) (f g : Fin N -> Nat)
    (hpos : ∀ s : Fin N, f s ≥ 1) (hle : ∀ s : Fin N, f s ≤ g s) :
    ∀ k : Nat, k ≤ N ->
      colBoundProdPrefix N f k ≥ 1 ∧
      colBoundProdPrefix N f k ≤ colBoundProdPrefix N g k ∧
      (colBoundProdPrefix N f k = colBoundProdPrefix N g k ->
        ∀ (s : Fin N), s.val < k -> f s = g s)
  | 0, _ => ⟨Nat.le_refl 1, Nat.le_refl 1, fun _ _ hs => by omega⟩
  | k + 1, hk => by
    have hk_lt : k < N := hk
    rcases colBoundProdPrefix_mono_pos N f g hpos hle k (Nat.le_of_lt hk) with ⟨hp, hm, heq_imp⟩
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

private theorem syzygy_forces_parikh_and_prod_eq
    (N : Nat) (rules : List (List (Fin N) × List (Fin N))) (mults : List Nat)
    (hsyz : checkPositiveParikhSyzygyFastBool N rules mults = true) :
    (∀ wt : Fin N -> Nat,
      (∀ r ∈ rules, evalFinParikh N wt r.1 ≥ evalFinParikh N wt r.2) ->
      ∀ r ∈ rules, evalFinParikh N wt r.1 = evalFinParikh N wt r.2) ∧
    (∀ m : Fin N -> Nat,
      (∀ s : Fin N, m s ≥ 1) ->
      (∀ r ∈ rules, prodFinWord N m r.1 ≥ prodFinWord N m r.2) ->
      ∀ r ∈ rules, prodFinWord N m r.1 = prodFinWord N m r.2) := by
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
        (∀ r ∈ rs, prodFinWord N m r.1 ≥ prodFinWord N m r.2) ->
        weightedProdRhs N m rs us ≥ 1 ∧
        weightedProdLhs N m rs us ≥ weightedProdRhs N m rs us ∧
        (weightedProdLhs N m rs us = weightedProdRhs N m rs us ->
          ∀ r ∈ rs, prodFinWord N m r.1 = prodFinWord N m r.2) := by
      intro rs; induction rs with
      | nil =>
        intro _ _ _ _
        exact ⟨by simp [weightedProdRhs], by simp [weightedProdLhs, weightedProdRhs],
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
          simp only [weightedProdLhs, weightedProdRhs]
          have hp_r2 := prodFinWord_pos N m hm1 r0.2
          have hpu_pos := nat_pow_pos_of_pos (prodFinWord N m r0.2) hp_r2 u0
          have hw0 := hw r0 List.mem_cons_self
          have hpu_ge := pow_mono_base_w12 (prodFinWord N m r0.2) (prodFinWord N m r0.1) hw0 u0
          refine ⟨Nat.mul_le_mul hpu_pos hr_pos, Nat.mul_le_mul hpu_ge hge_tl, ?_⟩
          intro heq_mul r hr_mem
          have h1_eq : (prodFinWord N m r0.1) ^ u0 = (prodFinWord N m r0.2) ^ u0 := by
            by_cases hne : (prodFinWord N m r0.1) ^ u0 = (prodFinWord N m r0.2) ^ u0
            · exact hne
            · exfalso
              have hlt : (prodFinWord N m r0.2) ^ u0 < (prodFinWord N m r0.1) ^ u0 := by omega
              have hm1_lt := Nat.mul_lt_mul_of_pos_right hlt
                (Nat.lt_of_lt_of_le Nat.zero_lt_one hr_pos)
              have hm2_le := Nat.mul_le_mul_left ((prodFinWord N m r0.1) ^ u0) hge_tl
              exact Nat.ne_of_lt (Nat.lt_of_lt_of_le hm1_lt hm2_le) heq_mul.symm
          have h2_eq : weightedProdLhs N m rt ut = weightedProdRhs N m rt ut := by
            rw [h1_eq] at heq_mul
            exact Nat.eq_of_mul_eq_mul_left (by omega) heq_mul
          cases hr_mem with
          | head =>
            by_cases hbase : prodFinWord N m r0.1 = prodFinWord N m r0.2
            · exact hbase
            · exfalso
              have hgt : prodFinWord N m r0.2 < prodFinWord N m r0.1 := by omega
              have hpow_lt : (prodFinWord N m r0.2) ^ u0 < (prodFinWord N m r0.1) ^ u0 := by
                rw [show u0 = (u0 - 1) + 1 by omega, Nat.pow_succ, Nat.pow_succ]
                have hm_b := pow_mono_base_w12 _ _ hw0 (u0 - 1)
                have hm_p := nat_pow_pos_of_pos _ hp_r2 (u0 - 1)
                have h1 := Nat.mul_le_mul_right (prodFinWord N m r0.2) hm_b
                have h2 := Nat.mul_lt_mul_of_pos_left hgt
                  (Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_trans hm_p hm_b))
                exact Nat.lt_of_le_of_lt h1 h2
              omega
          | tail _ htl => exact heq_tl h2_eq r htl
    rcases hprod_ge rules mults hlen hpos_m hweak with ⟨_, htot_ge, htot_imp⟩
    rcases weightedProd_eq_sym_pow N m rules mults with ⟨hl_sym, hr_sym⟩
    have hsym_pow_le : ∀ s : Fin N,
        (m s) ^ weightedSymLhsSum N s rules mults ≤ (m s) ^ weightedSymRhsSum N s rules mults :=
      fun s => nat_pow_mono_exp_pos (m s) _ _ (hm1 s) (hsym_le s)
    have hsym_pow_pos : ∀ s : Fin N, (m s) ^ weightedSymLhsSum N s rules mults ≥ 1 :=
      fun s => nat_pow_pos_of_pos (m s) (hm1 s) _
    rcases colBoundProdPrefix_mono_pos N _ _ hsym_pow_pos hsym_pow_le N (Nat.le_refl N) with
      ⟨_, htot_le_sym, _⟩
    rw [← hl_sym, ← hr_sym] at htot_le_sym
    exact htot_imp (by omega)

-- Signed syzygy interior-annihilation certificate `(posMults, negMults)`:
private theorem weightedParikh_eq_of_all_eq (N : Nat) (wt : Fin N -> Nat) :
    ∀ (rs : List (List (Fin N) × List (Fin N))) (us : List Nat),
      (∀ r ∈ rs, evalFinParikh N wt r.1 = evalFinParikh N wt r.2) ->
      weightedParikhLhs N wt rs us = weightedParikhRhs N wt rs us
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | r0 :: rt, u0 :: ut, heq => by
    simp only [weightedParikhLhs, weightedParikhRhs, heq r0 List.mem_cons_self,
      weightedParikh_eq_of_all_eq N wt rt ut (fun r hr => heq r (List.mem_cons_of_mem r0 hr))]

private theorem weightedProd_eq_of_all_eq (N : Nat) (m : Fin N -> Nat) :
    ∀ (rs : List (List (Fin N) × List (Fin N))) (us : List Nat),
      (∀ r ∈ rs, prodFinWord N m r.1 = prodFinWord N m r.2) ->
      weightedProdLhs N m rs us = weightedProdRhs N m rs us
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | r0 :: rt, u0 :: ut, heq => by
    simp only [weightedProdLhs, weightedProdRhs, heq r0 List.mem_cons_self,
      weightedProd_eq_of_all_eq N m rt ut (fun r hr => heq r (List.mem_cons_of_mem r0 hr))]

def symAppearsInRulesBool (N : Nat) (idx : Nat) : List (List (Fin N) × List (Fin N)) -> Bool
  | [] => false
  | (l, r) :: rs =>
    decide (countNatOccW11 idx (l.map Fin.val) + countNatOccW11 idx (r.map Fin.val) ≥ 1) ||
      symAppearsInRulesBool N idx rs

private theorem countFinOcc_pos_of_mem (N : Nat) (s : Fin N) :
    ∀ w : List (Fin N), s ∈ w -> countFinOcc N s w ≥ 1
  | [], hs => by cases hs
  | x :: xs, hs => by
    simp only [countFinOcc]
    cases hs with
    | head => simp
    | tail _ htl => have := countFinOcc_pos_of_mem N s xs htl; omega

theorem symAppearsInRulesBool_of_mem_lhs (N : Nat) (s : Fin N) :
    ∀ (rules : List (List (Fin N) × List (Fin N))) (r : List (Fin N) × List (Fin N)),
      r ∈ rules -> s ∈ r.1 -> symAppearsInRulesBool N s.val rules = true
  | [], _, hr, _ => by cases hr
  | (l0, r0) :: rs, r, hr, hs => by
    unfold symAppearsInRulesBool
    cases hr with
    | head =>
      have hc := countFinOcc_pos_of_mem N s l0 hs
      rw [decide_eq_true (by rw [countNatOccW11_map_val N s l0]; omega)]
      rfl
    | tail _ htl =>
      rw [symAppearsInRulesBool_of_mem_lhs N s rs r htl hs, Bool.or_true]

theorem symAppearsInRulesBool_of_mem_rhs (N : Nat) (s : Fin N) :
    ∀ (rules : List (List (Fin N) × List (Fin N))) (r : List (Fin N) × List (Fin N)),
      r ∈ rules -> s ∈ r.2 -> symAppearsInRulesBool N s.val rules = true
  | [], _, hr, _ => by cases hr
  | (l0, r0) :: rs, r, hr, hs => by
    unfold symAppearsInRulesBool
    cases hr with
    | head =>
      have hc := countFinOcc_pos_of_mem N s r0 hs
      rw [decide_eq_true (by rw [countNatOccW11_map_val N s r0]; omega)]
      rfl
    | tail _ htl =>
      rw [symAppearsInRulesBool_of_mem_rhs N s rs r htl hs, Bool.or_true]

def checkInteriorAnnihilationPairsAux (M N : Nat) (rules : List (List (Fin N) × List (Fin N))) :
    Nat -> List (Nat × Nat) -> List (Nat × Nat) -> Bool
  | _, [], _ => true
  | _, _, [] => true
  | idx, p :: ps, n :: ns =>
    let a := p.1 + n.2
    let b := p.2 + n.1
    decide (a ≤ b) &&
    (if idx ≥ 4 * M && symAppearsInRulesBool N idx rules then decide (a < b) else true) &&
    checkInteriorAnnihilationPairsAux M N rules (idx + 1) ps ns

def checkSignedInteriorAnnihilationBool (M : Nat)
    (rules : List (List (Fin (14 * M)) × List (Fin (14 * M))))
    (posMults negMults : List Nat) : Bool :=
  checkInteriorAnnihilationPairsAux M (14 * M) rules 0
    (accumSymCountsW11 (14 * M) rules posMults)
    (accumSymCountsW11 (14 * M) rules negMults)

private theorem checkInteriorAnnihilationPairsAux_sound (M N : Nat)
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
  | p0 :: ps, n0 :: ns, idx, hlen, hb, 0, _ => by
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
    have ih := checkInteriorAnnihilationPairsAux_sound M N rules ps ns (idx + 1)
      (by simp at hlen; omega) hrest k (by simp at hk; omega)
    simpa [getPairAtW11, show idx + 1 + k = idx + (k + 1) by omega] using ih

private theorem signed_annihilation_forces_interior_zero_and_one (M : Nat)
    (rules : List (List (Fin (14 * M)) × List (Fin (14 * M))))
    (posMults negMults : List Nat)
    (hann : checkSignedInteriorAnnihilationBool M rules posMults negMults = true) :
    (∀ wt : Fin (14 * M) -> Nat,
      (∀ r ∈ rules, evalFinParikh (14 * M) wt r.1 = evalFinParikh (14 * M) wt r.2) ->
      ∀ s : Fin (14 * M), s.val ≥ 4 * M -> symAppearsInRulesBool (14 * M) s.val rules = true ->
        wt s = 0) ∧
    (∀ m : Fin (14 * M) -> Nat,
      (∀ s : Fin (14 * M), m s ≥ 1) ->
      (∀ r ∈ rules, prodFinWord (14 * M) m r.1 = prodFinWord (14 * M) m r.2) ->
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
    have hsnd := checkInteriorAnnihilationPairsAux_sound M (14 * M) rules
      (accumSymCountsW11 (14 * M) rules posMults) (accumSymCountsW11 (14 * M) rules negMults) 0
      (hlen_p.trans hlen_n.symm) hann s.val (by rw [hlen_p]; exact s.isLt)
    simp only [Nat.zero_add, hget_p s, hget_n s] at hsnd
    exact hsnd
  refine ⟨?_, ?_⟩
  · intro wt heq s hs_ge hs_act
    have hp_eq := weightedParikh_eq_of_all_eq (14 * M) wt rules posMults heq
    have hn_eq := weightedParikh_eq_of_all_eq (14 * M) wt rules negMults heq
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
      natSumPrefix_eq_of_le_and_sum_eq (14 * M)
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
    have hp_eq := weightedProd_eq_of_all_eq (14 * M) m rules posMults heq
    have hn_eq := weightedProd_eq_of_all_eq (14 * M) m rules negMults heq
    rcases weightedProd_eq_sym_pow (14 * M) m rules posMults with ⟨hl_p, hr_p⟩
    rcases weightedProd_eq_sym_pow (14 * M) m rules negMults with ⟨hl_n, hr_n⟩
    have hprod_mul : ∀ (f g : Fin (14 * M) -> Nat) (k : Nat), k ≤ 14 * M ->
        colBoundProdPrefix (14 * M) (fun x => (m x) ^ f x) k *
          colBoundProdPrefix (14 * M) (fun x => (m x) ^ g x) k =
        colBoundProdPrefix (14 * M) (fun x => (m x) ^ (f x + g x)) k := by
      intro f g k hk
      have h1 := colBoundProdPrefix_pow_mul (14 * M) m f g 1 k hk
      simpa using h1
    have htot_eq : colBoundProdPrefix (14 * M) (fun x => (m x) ^ A_cnt x) (14 * M) =
        colBoundProdPrefix (14 * M) (fun x => (m x) ^ B_cnt x) (14 * M) := by
      rw [← hprod_mul _ _ (14 * M) (Nat.le_refl _), ← hprod_mul _ _ (14 * M) (Nat.le_refl _),
          ← hl_p, ← hr_p, ← hl_n, ← hr_n, hp_eq, hn_eq]
    rcases colBoundProdPrefix_mono_pos (14 * M)
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

-- Rule-shape & L-equalization helpers for `c39` (`M = 3`) and `c78` (`M = 6`):
def allGe4MBool (M : Nat) : List (Fin (14 * M)) -> Bool
  | [] => true
  | s :: rest => decide (s.val ≥ 4 * M) && allGe4MBool M rest

theorem allGe4MBool_sound (M : Nat) :
    ∀ (w : List (Fin (14 * M))), allGe4MBool M w = true -> ∀ s ∈ w, s.val ≥ 4 * M
  | [], _, _, hs => by cases hs
  | s0 :: rest, hb, s, hs => by
    rcases bool_and_split hb with ⟨h0, hrest⟩
    cases hs with
    | head => exact of_decide_eq_true h0
    | tail _ htl => exact allGe4MBool_sound M rest hrest s htl

def checkWordRightOrIntBool (M : Nat) : List (Fin (14 * M)) -> Bool
  | [] => true
  | [s] => decide (s.val ≥ 2 * M)
  | s :: rest => decide (s.val ≥ 4 * M) && checkWordRightOrIntBool M rest

def checkRuleTwoSidedShapeBool (M : Nat) (r : List (Fin (14 * M)) × List (Fin (14 * M))) : Bool :=
  (match r.1, r.2 with
   | l0 :: lint, r0 :: rint =>
     (decide (l0.val < M ∧ r0.val < M) && allGe4MBool M lint && allGe4MBool M rint) ||
     (decide (M ≤ l0.val ∧ l0.val < 2 * M ∧ M ≤ r0.val ∧ r0.val < 2 * M) &&
       allGe4MBool M lint && allGe4MBool M rint)
   | _, _ => false) ||
  (checkWordRightOrIntBool M r.1 && checkWordRightOrIntBool M r.2)

def checkAllRulesShapeBool (M : Nat) : List (List (Fin (14 * M)) × List (Fin (14 * M))) -> Bool
  | [] => true
  | r :: rs => checkRuleTwoSidedShapeBool M r && checkAllRulesShapeBool M rs

theorem checkAllRulesShapeBool_sound (M : Nat) :
    ∀ (rules : List (List (Fin (14 * M)) × List (Fin (14 * M)))),
      checkAllRulesShapeBool M rules = true ->
      ∀ r ∈ rules, checkRuleTwoSidedShapeBool M r = true
  | [], _, _, hr => by cases hr
  | r0 :: rs, hb, r, hr => by
    rcases bool_and_split hb with ⟨h0, hrs⟩
    cases hr with
    | head => exact h0
    | tail _ htl => exact checkAllRulesShapeBool_sound M rs hrs r htl

private theorem evalFinAffine1D_all_int (M : Nat) (m v : Fin (14 * M) -> Nat) :
    ∀ w : List (Fin (14 * M)),
      (∀ s ∈ w, m s = 1) ->
      evalFinAffine1D (14 * M) m v w = (1, evalFinParikh (14 * M) v w)
  | [], _ => rfl
  | s :: rest, hall => by
    have hs1 : m s = 1 := hall s List.mem_cons_self
    have ih := evalFinAffine1D_all_int M m v rest (fun x hx => hall x (List.mem_cons_of_mem s hx))
    simp [evalFinAffine1D, evalFinParikh, hs1, ih]

private theorem evalFinAffine1D_right_or_int (M : Nat) (m v : Fin (14 * M) -> Nat) :
    ∀ w : List (Fin (14 * M)),
      checkWordRightOrIntBool M w = true ->
      (∀ s ∈ w, s.val ≥ 4 * M -> m s = 1) ->
      (evalFinAffine1D (14 * M) m v w).2 = evalFinParikh (14 * M) v w
  | [], _, _ => rfl
  | [s], _, _ => by simp [evalFinAffine1D, evalFinParikh]
  | s :: s2 :: rest, hb, hint => by
    rcases bool_and_split hb with ⟨hs_ge, hrest⟩
    have hs1 : m s = 1 := hint s List.mem_cons_self (of_decide_eq_true hs_ge)
    have ih := evalFinAffine1D_right_or_int M m v (s2 :: rest) hrest
      (fun x hx => hint x (List.mem_cons_of_mem s hx))
    change v s + m s * (evalFinAffine1D (14 * M) m v (s2 :: rest)).2 =
      v s + evalFinParikh (14 * M) v (s2 :: rest)
    rw [hs1, Nat.one_mul, ih]

private theorem parikh_int_scale (M c : Nat) (v wt : Fin (14 * M) -> Nat) :
    ∀ w : List (Fin (14 * M)),
      (∀ s ∈ w, wt s = c * v s) ->
      evalFinParikh (14 * M) wt w = c * evalFinParikh (14 * M) v w
  | [], _ => by simp [evalFinParikh]
  | s :: rest, hall => by
    simp only [evalFinParikh, hall s List.mem_cons_self,
      parikh_int_scale M c v wt rest (fun x hx => hall x (List.mem_cons_of_mem s hx)),
      Nat.mul_add]

-- General `1D`-affine & diagonal-monotone & upper-unitriangular core impossibility theorem:
private theorem natSumPrefix_single_fin (d : Nat) (f : Fin d -> Nat) (k0 : Fin d)
    (hz : ∀ k : Fin d, k ≠ k0 -> f k = 0) :
    natSumFin d f = f k0 := by
  unfold natSumFin
  have hst : ∀ m : Nat, m ≤ d ->
      natSumPrefix d f m = (if k0.val < m then f k0 else 0) := by
    intro m hm; induction m with
    | zero => simp [natSumPrefix]
    | succ m' ih =>
      have hm'_lt : m' < d := hm
      simp only [natSumPrefix, hm'_lt, dite_true, ih (Nat.le_of_lt hm)]
      by_cases hlt : k0.val < m'
      · have hlt1 : k0.val < m' + 1 := by omega
        have hne : (⟨m', hm'_lt⟩ : Fin d) ≠ k0 := fun he => by
          have hv := congrArg Fin.val he; dsimp at hv; omega
        rw [ite_true_of_w10 hlt, ite_true_of_w10 hlt1, hz ⟨m', hm'_lt⟩ hne, Nat.add_zero]
      · by_cases heq : k0.val = m'
        · have hlt1 : k0.val < m' + 1 := by omega
          have hkf : (⟨m', hm'_lt⟩ : Fin d) = k0 := Fin.ext heq.symm
          rw [ite_false_of_w10 hlt, ite_true_of_w10 hlt1, hkf, Nat.zero_add]
        · have hgt1 : ¬ (k0.val < m' + 1) := by omega
          have hne : (⟨m', hm'_lt⟩ : Fin d) ≠ k0 := fun he => heq (congrArg Fin.val he).symm
          rw [ite_false_of_w10 hlt, ite_false_of_w10 hgt1, hz ⟨m', hm'_lt⟩ hne]
  rw [hst d (Nat.le_refl d), ite_true_of_w10 k0.isLt]

private theorem diag_mat_vec_eq_affine1d (N d : Nat)
    (M : Fin N -> Fin d -> Fin d -> Nat) (v : Fin N -> Fin d -> Nat)
    (hdiag : ∀ (s : Fin N) (i j : Fin d), i ≠ j -> M s i j = 0) (i0 : Fin d) :
    ∀ w : List (Fin N),
      evalFinWordMat N d M w i0 i0 = (evalFinAffine1D N (fun s => M s i0 i0) (fun s => v s i0) w).1 ∧
      evalFinWordVec N d M v w i0 = (evalFinAffine1D N (fun s => M s i0 i0) (fun s => v s i0) w).2
  | [] => by simp [evalFinWordMat, evalFinWordVec, evalFinAffine1D, natMatId]
  | s :: rest => by
    rcases diag_mat_vec_eq_affine1d N d M v hdiag i0 rest with ⟨hm_ih, hv_ih⟩
    refine ⟨?_, ?_⟩
    · simp only [evalFinWordMat, evalFinAffine1D, natMatMul]
      rw [natSumPrefix_single_fin d (fun k => M s i0 k * evalFinWordMat N d M rest k i0) i0
        (fun k hk => by rw [hdiag s i0 k hk.symm, Nat.zero_mul]), hm_ih]
    · simp only [evalFinWordVec, evalFinAffine1D, natMatVec]
      rw [natSumPrefix_single_fin d (fun k => M s i0 k * evalFinWordVec N d M v rest k) i0
        (fun k hk => by rw [hdiag s i0 k hk.symm, Nat.zero_mul]), hv_ih]

private theorem unitriangular_wordMat_tri_and_diag (N d : Nat)
    (M : Fin N -> Fin d -> Fin d -> Nat)
    (h1 : ∀ (s : Fin N) (i : Fin d), M s i i = 1)
    (htri : ∀ (s : Fin N) (i j : Fin d), j.val < i.val -> M s i j = 0) :
    ∀ (w : List (Fin N)) (i j : Fin d),
      (j.val < i.val -> evalFinWordMat N d M w i j = 0) ∧
      (i = j -> evalFinWordMat N d M w i j = 1)
  | [], i, j => by
    refine ⟨?_, ?_⟩
    · intro hlt
      have hnev : i.val ≠ j.val := by omega
      simp [evalFinWordMat, natMatId, hnev]
    · intro heq; subst heq; simp [evalFinWordMat, natMatId]
  | s :: rest, i, j => by
    refine ⟨?_, ?_⟩
    · intro hlt
      simp only [evalFinWordMat, natMatMul]
      unfold natSumFin
      have hz : ∀ m : Nat, m ≤ d ->
          natSumPrefix d (fun k => M s i k * evalFinWordMat N d M rest k j) m = 0 := by
        intro m hm; induction m with
        | zero => rfl
        | succ m' ih =>
          have hm'_lt : m' < d := hm
          simp only [natSumPrefix, hm'_lt, dite_true, ih (Nat.le_of_lt hm), Nat.zero_add]
          by_cases hki : m' < i.val
          · rw [htri s i ⟨m', hm'_lt⟩ hki, Nat.zero_mul]
          · have hjk : j.val < m' := by omega
            rw [(unitriangular_wordMat_tri_and_diag N d M h1 htri rest ⟨m', hm'_lt⟩ j).1 hjk, Nat.mul_zero]
      exact hz d (Nat.le_refl d)
    · intro heq
      subst heq
      simp only [evalFinWordMat, natMatMul]
      rw [natSumPrefix_single_fin d (fun k => M s i k * evalFinWordMat N d M rest k i) i]
      · rw [h1 s i, (unitriangular_wordMat_tri_and_diag N d M h1 htri rest i i).2 rfl, Nat.mul_one]
      · intro k hk
        by_cases hki : k.val < i.val
        · rw [htri s i k hki, Nat.zero_mul]
        · have hik : i.val < k.val := by
            have hnev : k.val ≠ i.val := fun hv => hk (Fin.ext hv)
            omega
          rw [(unitriangular_wordMat_tri_and_diag N d M h1 htri rest k i).1 hik, Nat.mul_zero]

private theorem natSumFin_two_terms (d : Nat) (f : Fin d -> Nat) (k1 k2 : Fin d) (hne : k1 ≠ k2)
    (hz : ∀ k : Fin d, k ≠ k1 -> k ≠ k2 -> f k = 0) :
    natSumFin d f = f k1 + f k2 := by
  unfold natSumFin
  have hst : ∀ m : Nat, m ≤ d ->
      natSumPrefix d f m = (if k1.val < m then f k1 else 0) + (if k2.val < m then f k2 else 0) := by
    intro m hm; induction m with
    | zero => simp [natSumPrefix]
    | succ m' ih =>
      have hm'_lt : m' < d := hm
      simp only [natSumPrefix, hm'_lt, dite_true, ih (Nat.le_of_lt hm)]
      by_cases he1 : k1.val = m'
      · have he2 : k2.val ≠ m' := fun h2 => hne (Fin.ext (he1.trans h2.symm))
        have hlt1 : k1.val < m' + 1 := by omega
        have hnl1 : ¬ (k1.val < m') := by omega
        have hk1f : (⟨m', hm'_lt⟩ : Fin d) = k1 := Fin.ext he1.symm
        rw [ite_false_of_w10 hnl1, ite_true_of_w10 hlt1, hk1f]
        by_cases hl2 : k2.val < m'
        · rw [ite_true_of_w10 hl2, ite_true_of_w10 (by omega : k2.val < m' + 1)]; omega
        · rw [ite_false_of_w10 hl2, ite_false_of_w10 (by omega : ¬ (k2.val < m' + 1))]; omega
      · by_cases he2 : k2.val = m'
        · have hlt2 : k2.val < m' + 1 := by omega
          have hnl2 : ¬ (k2.val < m') := by omega
          have hk2f : (⟨m', hm'_lt⟩ : Fin d) = k2 := Fin.ext he2.symm
          rw [ite_false_of_w10 hnl2, ite_true_of_w10 hlt2, hk2f]
          by_cases hl1 : k1.val < m'
          · rw [ite_true_of_w10 hl1, ite_true_of_w10 (by omega : k1.val < m' + 1)]; omega
          · rw [ite_false_of_w10 hl1, ite_false_of_w10 (by omega : ¬ (k1.val < m' + 1))]
        · have hne1 : (⟨m', hm'_lt⟩ : Fin d) ≠ k1 := fun h => he1 (congrArg Fin.val h).symm
          have hne2 : (⟨m', hm'_lt⟩ : Fin d) ≠ k2 := fun h => he2 (congrArg Fin.val h).symm
          rw [hz ⟨m', hm'_lt⟩ hne1 hne2, Nat.add_zero]
          by_cases hl1 : k1.val < m'
          · rw [ite_true_of_w10 hl1, ite_true_of_w10 (by omega : k1.val < m' + 1)]
            by_cases hl2 : k2.val < m'
            · rw [ite_true_of_w10 hl2, ite_true_of_w10 (by omega : k2.val < m' + 1)]
            · rw [ite_false_of_w10 hl2, ite_false_of_w10 (by omega : ¬ (k2.val < m' + 1))]
          · rw [ite_false_of_w10 hl1, ite_false_of_w10 (by omega : ¬ (k1.val < m' + 1))]
            by_cases hl2 : k2.val < m'
            · rw [ite_true_of_w10 hl2, ite_true_of_w10 (by omega : k2.val < m' + 1)]
            · rw [ite_false_of_w10 hl2, ite_false_of_w10 (by omega : ¬ (k2.val < m' + 1))]
  rw [hst d (Nat.le_refl d), ite_true_of_w10 k1.isLt, ite_true_of_w10 k2.isLt]

private theorem unitriangular_superdiag_parikh (M d : Nat)
    (mat : Fin (14 * M) -> Fin d -> Fin d -> Nat)
    (h1 : ∀ (s : Fin (14 * M)) (i : Fin d), mat s i i = 1)
    (htri : ∀ (s : Fin (14 * M)) (i j : Fin d), j.val < i.val -> mat s i j = 0)
    (gap : Nat) (_hgap : gap ≥ 1) :
    -- First on purely interior words (`∀ s ∈ w, < gap` super-diagonals are 0):
    (∀ (w : List (Fin (14 * M))),
      (∀ s ∈ w, ∀ a b : Fin d, a.val < b.val -> b.val - a.val < gap -> mat s a b = 0) ->
      ∀ (i j : Fin d), i.val < j.val ->
        (j.val - i.val < gap -> evalFinWordMat (14 * M) d mat w i j = 0) ∧
        (j.val - i.val = gap ->
          evalFinWordMat (14 * M) d mat w i j = evalFinParikh (14 * M) (fun s => mat s i j) w)) ∧
    -- Second on `checkWordRightOrIntBool` words:
    (∀ (w : List (Fin (14 * M))),
      checkWordRightOrIntBool M w = true ->
      (∀ s ∈ w, s.val ≥ 4 * M ->
        ∀ a b : Fin d, a.val < b.val -> b.val - a.val < gap -> mat s a b = 0) ->
      ∀ (i j : Fin d), i.val < j.val -> j.val - i.val = gap ->
        evalFinWordMat (14 * M) d mat w i j = evalFinParikh (14 * M) (fun s => mat s i j) w) := by
  have hint_lem : ∀ (w : List (Fin (14 * M))),
      (∀ s ∈ w, ∀ a b : Fin d, a.val < b.val -> b.val - a.val < gap -> mat s a b = 0) ->
      ∀ (i j : Fin d), i.val < j.val ->
        (j.val - i.val < gap -> evalFinWordMat (14 * M) d mat w i j = 0) ∧
        (j.val - i.val = gap ->
          evalFinWordMat (14 * M) d mat w i j = evalFinParikh (14 * M) (fun s => mat s i j) w) := by
    intro w; induction w with
    | nil =>
      intro _ i j hij
      have hnev : i.val ≠ j.val := by omega
      exact ⟨fun _ => by simp [evalFinWordMat, natMatId, hnev],
             fun _ => by simp [evalFinWordMat, evalFinParikh, natMatId, hnev]⟩
    | cons s rest ih =>
      intro hall i j hij
      have hs_z := hall s List.mem_cons_self
      have hrest_ih := ih (fun x hx => hall x (List.mem_cons_of_mem s hx))
      have hne_ij : i ≠ j := fun he => by subst he; omega
      refine ⟨?_, ?_⟩
      · intro hlt_g
        simp only [evalFinWordMat, natMatMul]
        rw [natSumFin_two_terms d (fun k => mat s i k * evalFinWordMat (14 * M) d mat rest k j) i j hne_ij]
        · rw [h1 s i, (hrest_ih i j hij).1 hlt_g, hs_z i j hij hlt_g, Nat.mul_zero, Nat.zero_mul]
        · intro k hki hkj
          by_cases hlt_k : k.val < i.val
          · rw [htri s i k hlt_k, Nat.zero_mul]
          · by_cases hgt_k : j.val < k.val
            · rw [(unitriangular_wordMat_tri_and_diag (14 * M) d mat h1 htri rest k j).1 hgt_k, Nat.mul_zero]
            · have hik : i.val < k.val := by
                have : k.val ≠ i.val := fun hv => hki (Fin.ext hv); omega
              rw [hs_z i k hik (by omega), Nat.zero_mul]
      · intro heq_g
        simp only [evalFinWordMat, evalFinParikh, natMatMul]
        rw [natSumFin_two_terms d (fun k => mat s i k * evalFinWordMat (14 * M) d mat rest k j) i j hne_ij]
        · rw [h1 s i, Nat.one_mul, (hrest_ih i j hij).2 heq_g,
              (unitriangular_wordMat_tri_and_diag (14 * M) d mat h1 htri rest j j).2 rfl,
              Nat.mul_one, Nat.add_comm]
        · intro k hki hkj
          by_cases hlt_k : k.val < i.val
          · rw [htri s i k hlt_k, Nat.zero_mul]
          · by_cases hgt_k : j.val < k.val
            · rw [(unitriangular_wordMat_tri_and_diag (14 * M) d mat h1 htri rest k j).1 hgt_k, Nat.mul_zero]
            · have hik : i.val < k.val := by
                have : k.val ≠ i.val := fun hv => hki (Fin.ext hv); omega
              rw [hs_z i k hik (by omega), Nat.zero_mul]
  refine ⟨hint_lem, ?_⟩
  intro w
  induction w with
  | nil =>
    intro _ _ i j hij _
    have hnev : i.val ≠ j.val := by omega
    simp [evalFinWordMat, evalFinParikh, natMatId, hnev]
  | cons s rest ih =>
    cases rest with
    | nil =>
      intro _ _ i j hij _
      simp only [evalFinWordMat, evalFinParikh, natMatMul, Nat.add_zero]
      rw [natSumPrefix_single_fin d (fun k => mat s i k * natMatId d k j) j]
      · simp [natMatId]
      · intro k hkj
        have hkv : k.val ≠ j.val := fun hv => hkj (Fin.ext hv)
        simp [natMatId, hkv]
    | cons s2 tl =>
      intro hb hint i j hij heq_g
      rcases bool_and_split hb with ⟨hs_ge, hrest⟩
      have hs_z := hint s List.mem_cons_self (of_decide_eq_true hs_ge)
      have hne_ij : i ≠ j := fun he => by subst he; omega
      change natSumFin d (fun k => mat s i k * evalFinWordMat (14 * M) d mat (s2 :: tl) k j) =
        mat s i j + evalFinParikh (14 * M) (fun x => mat x i j) (s2 :: tl)
      rw [natSumFin_two_terms d (fun k => mat s i k * evalFinWordMat (14 * M) d mat (s2 :: tl) k j) i j hne_ij]
      · rw [h1 s i, Nat.one_mul,
            ih hrest (fun x hx => hint x (List.mem_cons_of_mem s hx)) i j hij heq_g,
            (unitriangular_wordMat_tri_and_diag (14 * M) d mat h1 htri (s2 :: tl) j j).2 rfl,
            Nat.mul_one, Nat.add_comm]
      · intro k hki hkj
        by_cases hlt_k : k.val < i.val
        · rw [htri s i k hlt_k, Nat.zero_mul]
        · by_cases hgt_k : j.val < k.val
          · rw [(unitriangular_wordMat_tri_and_diag (14 * M) d mat h1 htri (s2 :: tl) k j).1 hgt_k, Nat.mul_zero]
          · have hik : i.val < k.val := by
              have : k.val ≠ i.val := fun hv => hki (Fin.ext hv); omega
            rw [hs_z i k hik (by omega), Nat.zero_mul]

private theorem unitriangular_vec_parikh (M d : Nat)
    (mat : Fin (14 * M) -> Fin d -> Fin d -> Nat) (v : Fin (14 * M) -> Fin d -> Nat)
    (h1 : ∀ (s : Fin (14 * M)) (i : Fin d), mat s i i = 1)
    (_htri : ∀ (s : Fin (14 * M)) (i j : Fin d), j.val < i.val -> mat s i j = 0) (i0 : Fin d) :
    -- Purely interior words (`mat s = natMatId d` and `v s k = 0` for `k > i0`):
    (∀ w : List (Fin (14 * M)),
      (∀ s ∈ w, ∀ a b : Fin d, a ≠ b -> mat s a b = 0) ->
      (∀ s ∈ w, ∀ k : Fin d, i0.val < k.val -> v s k = 0) ->
      (∀ k : Fin d, i0.val < k.val -> evalFinWordVec (14 * M) d mat v w k = 0) ∧
      evalFinWordVec (14 * M) d mat v w i0 = evalFinParikh (14 * M) (fun s => v s i0) w) ∧
    -- `checkWordRightOrIntBool` words:
    (∀ w : List (Fin (14 * M)),
      checkWordRightOrIntBool M w = true ->
      (∀ s ∈ w, s.val ≥ 4 * M -> ∀ a b : Fin d, a ≠ b -> mat s a b = 0) ->
      evalFinWordVec (14 * M) d mat v w i0 = evalFinParikh (14 * M) (fun s => v s i0) w) := by
  have hint_v : ∀ w : List (Fin (14 * M)),
      (∀ s ∈ w, ∀ a b : Fin d, a ≠ b -> mat s a b = 0) ->
      (∀ s ∈ w, ∀ k : Fin d, i0.val < k.val -> v s k = 0) ->
      (∀ k : Fin d, i0.val < k.val -> evalFinWordVec (14 * M) d mat v w k = 0) ∧
      evalFinWordVec (14 * M) d mat v w i0 = evalFinParikh (14 * M) (fun s => v s i0) w := by
    intro w; induction w with
    | nil => intro _ _; exact ⟨fun _ _ => rfl, rfl⟩
    | cons s rest ih =>
      intro hm_id hv_z
      rcases ih (fun x hx => hm_id x (List.mem_cons_of_mem s hx))
                (fun x hx => hv_z x (List.mem_cons_of_mem s hx)) with ⟨hk_z, hi0_eq⟩
      refine ⟨?_, ?_⟩
      · intro k hk
        simp only [evalFinWordVec, natMatVec]
        rw [natSumPrefix_single_fin d (fun c => mat s k c * evalFinWordVec (14 * M) d mat v rest c) k
          (fun c hc => by rw [hm_id s List.mem_cons_self k c hc.symm, Nat.zero_mul])]
        rw [h1 s k, Nat.one_mul, hv_z s List.mem_cons_self k hk, hk_z k hk]
      · simp only [evalFinWordVec, evalFinParikh, natMatVec]
        rw [natSumPrefix_single_fin d (fun c => mat s i0 c * evalFinWordVec (14 * M) d mat v rest c) i0
          (fun c hc => by rw [hm_id s List.mem_cons_self i0 c hc.symm, Nat.zero_mul])]
        rw [h1 s i0, Nat.one_mul, hi0_eq]
  refine ⟨hint_v, ?_⟩
  intro w; induction w with
  | nil => intros; rfl
  | cons s rest ih =>
    cases rest with
    | nil =>
      intros
      simp only [evalFinWordVec, evalFinParikh, natMatVec, Nat.add_zero]
      have hz0 : natSumFin d (fun k => mat s i0 k * 0) = 0 := by
        unfold natSumFin
        have hz : ∀ m : Nat, m ≤ d -> natSumPrefix d (fun k => mat s i0 k * 0) m = 0 := by
          intro m hm; induction m with
          | zero => rfl
          | succ m' ihm =>
            have hm'_lt : m' < d := hm
            unfold natSumPrefix
            simp only [hm'_lt, dite_true, Nat.mul_zero, Nat.add_zero]
            exact ihm (Nat.le_of_lt hm)
        exact hz d (Nat.le_refl d)
      rw [hz0, Nat.add_zero]
    | cons s2 tl =>
      intro hb hm_id
      rcases bool_and_split hb with ⟨hs_ge, hrest⟩
      have hs_id := hm_id s List.mem_cons_self (of_decide_eq_true hs_ge)
      change v s i0 + natSumFin d (fun c => mat s i0 c * evalFinWordVec (14 * M) d mat v (s2 :: tl) c) =
        v s i0 + evalFinParikh (14 * M) (fun x => v x i0) (s2 :: tl)
      rw [natSumPrefix_single_fin d (fun c => mat s i0 c * evalFinWordVec (14 * M) d mat v (s2 :: tl) c) i0
        (fun c hc => by rw [hs_id i0 c hc.symm, Nat.zero_mul])]
      rw [h1 s i0, Nat.one_mul, ih hrest (fun x hx => hm_id x (List.mem_cons_of_mem s hx))]

def posMultsC39 : List Nat :=
  [2, 4, 0, 4, 24, 2, 0, 41, 27, 13, 29, 13, 14, 4, 0, 11, 12, 2, 15, 19,
   7, 9, 27, 3, 2, 9, 7, 4, 4, 4, 2, 2, 2, 2, 2, 2, 2, 2, 2]

def negMultsC39 : List Nat :=
  [0, 0, 37, 0, 0, 0, 11, 0, 0, 0, 0, 0, 0, 0, 15, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

def posMultsC78 : List Nat :=
  [2, 4, 2, 4, 0, 0, 2, 73, 126, 2, 4, 2, 59, 21, 0, 52, 25, 0, 73, 3,
   101, 4, 7, 0, 3, 67, 0, 66, 53, 0, 0, 0, 21, 21, 0, 39, 2, 0, 60, 74,
   0, 57, 91, 16, 8, 46, 72, 0, 2, 28, 58, 88, 32, 2, 4, 4, 4, 4, 4, 32,
   2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 30]

def negMultsC78 : List Nat :=
  [0, 0, 0, 0, 78, 76, 0, 0, 0, 0, 0, 0, 0, 0, 57, 0, 0, 18, 0, 0,
   0, 0, 0, 27, 0, 0, 40, 0, 0, 47, 4, 40, 0, 0, 44, 0, 0, 23, 0, 0,
   24, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

-- Check active L0 / L1 symbols and L-equalizing rules by `decide`:
def checkActiveLSymsAndEqRulesBool (M : Nat)
    (rules : List (List (Fin (14 * M)) × List (Fin (14 * M))))
    (l0Ref l1Ref : Fin (14 * M))
    (allowedL0 allowedL1 : List Nat) : Bool :=
  (let checkSym : Nat -> Bool := fun idx =>
    if idx < M then
      if symAppearsInRulesBool (14 * M) idx rules then decide (idx ∈ allowedL0) else true
    else if idx < 2 * M then
      if symAppearsInRulesBool (14 * M) idx rules then decide (idx ∈ allowedL1) else true
    else true
   let rec loop : Nat -> Bool
     | 0 => true
     | k + 1 => checkSym k && loop k
   loop (2 * M)) &&
  decide (l0Ref.val < M ∧ M ≤ l1Ref.val ∧ l1Ref.val < 2 * M)

private theorem twosided_core_collapse_master (M : Nat)
    (core : List (List (Fin (14 * M)) × List (Fin (14 * M))))
    (syz posMults negMults : List Nat)
    (l0Ref l1Ref : Fin (14 * M))
    (hsyz : checkPositiveParikhSyzygyFastBool (14 * M) core syz = true)
    (hann : checkSignedInteriorAnnihilationBool M core posMults negMults = true)
    (hshape : checkAllRulesShapeBool M core = true)
    (hne_core : core ≠ [])
    (hL_eq : ∀ m : Fin (14 * M) -> Nat,
      (∀ r ∈ core, prodFinWord (14 * M) m r.1 = prodFinWord (14 * M) m r.2) ->
      (∀ s : Fin (14 * M), s.val ≥ 4 * M -> symAppearsInRulesBool (14 * M) s.val core = true -> m s = 1) ->
      ∀ (r : List (Fin (14 * M)) × List (Fin (14 * M))), r ∈ core ->
        (∀ s : Fin (14 * M), (s ∈ r.1 ∨ s ∈ r.2) -> s.val < M -> m s = m l0Ref) ∧
        (∀ s : Fin (14 * M), (s ∈ r.1 ∨ s ∈ r.2) -> M ≤ s.val -> s.val < 2 * M -> m s = m l1Ref)) :
    (∀ k : Nat, ¬ GenOmegaAffine1DFinTower (14 * M) k core) ∧
    (∀ (d : Nat) (hd : d ≥ 1) (k : Nat), ¬ GenOmegaDiagCoordMonoMatTower (14 * M) d hd k core) ∧
    (∀ (d : Nat) (hd : d ≥ 1) (k : Nat), ¬ GenOmegaUnitriangularMatTower (14 * M) d hd k core) := by
  let N := 14 * M
  rcases syzygy_forces_parikh_and_prod_eq N core syz hsyz with ⟨hpar_eq_all, hprod_eq_all⟩
  rcases signed_annihilation_forces_interior_zero_and_one M core posMults negMults hann with
    ⟨hpar_int_zero, hprod_int_one⟩
  have hshape_all := checkAllRulesShapeBool_sound M core hshape
  -- Core lemma 1: Any `1D`-affine `(m, v)` (`m s ≥ 1`) weakly orienting `core` has `= ` on ALL rules of `core`:
  have haff_no_strict : ∀ (m v : Fin N -> Nat),
      (∀ s : Fin N, m s ≥ 1) ->
      (∀ r ∈ core,
        (evalFinAffine1D N m v r.1).1 ≥ (evalFinAffine1D N m v r.2).1 ∧
        (evalFinAffine1D N m v r.1).2 ≥ (evalFinAffine1D N m v r.2).2) ->
      ∀ r ∈ core, (evalFinAffine1D N m v r.1).2 = (evalFinAffine1D N m v r.2).2 := by
    intro m v hm1 hweak
    have hprod_eq : ∀ r ∈ core, prodFinWord N m r.1 = prodFinWord N m r.2 :=
      hprod_eq_all m hm1 (fun r hr => by
        rw [← evalFinAffine1D_fst N m v r.1, ← evalFinAffine1D_fst N m v r.2]
        exact (hweak r hr).1)
    have hint1 : ∀ s : Fin N, s.val ≥ 4 * M -> symAppearsInRulesBool N s.val core = true -> m s = 1 :=
      hprod_int_one m hm1 hprod_eq
    have hL_const := hL_eq m hprod_eq hint1
    let M0 := m l0Ref
    let M1 := m l1Ref
    have hM0_pos : M0 ≥ 1 := hm1 l0Ref
    have hM1_pos : M1 ≥ 1 := hm1 l1Ref
    let wt : Fin N -> Nat := fun s =>
      if s.val < M then M1 * v s
      else if s.val < 2 * M then M0 * v s
      else (M0 * M1) * v s
    have hrule_rel : ∀ r ∈ core,
        evalFinParikh N wt r.1 ≥ evalFinParikh N wt r.2 ∧
        (evalFinParikh N wt r.1 = evalFinParikh N wt r.2 ->
          (evalFinAffine1D N m v r.1).2 = (evalFinAffine1D N m v r.2).2) := by
      intro r hr
      have hsh := hshape_all r hr
      unfold checkRuleTwoSidedShapeBool at hsh
      rcases bool_or_split hsh with hL_case | hR_case
      · cases hl1 : r.1 with
        | nil => rw [hl1] at hL_case; simp at hL_case
        | cons l0 lint =>
          cases hr1 : r.2 with
          | nil => rw [hl1, hr1] at hL_case; simp at hL_case
          | cons r0 rint =>
            rw [hl1, hr1] at hL_case
            dsimp only at hL_case
            have hw2 := (hweak r hr).2
            rw [hl1, hr1] at hw2
            rcases bool_or_split hL_case with hq0 | hq1
            · rcases bool_and_split hq0 with ⟨hb0, hrint_b⟩
              rcases bool_and_split hb0 with ⟨hlr_b, hlint_b⟩
              rcases of_decide_eq_true hlr_b with ⟨hl0_lt, hr0_lt⟩
              have hl0_m : m l0 = M0 := (hL_const r hr).1 l0
                (Or.inl (hl1 ▸ List.Mem.head _)) hl0_lt
              have hr0_m : m r0 = M0 := (hL_const r hr).1 r0
                (Or.inr (hr1 ▸ List.Mem.head _)) hr0_lt
              have hlint_1 : ∀ x ∈ lint, m x = 1 := fun x hx =>
                hint1 x (allGe4MBool_sound M lint hlint_b x hx)
                  (symAppearsInRulesBool_of_mem_lhs N x core r hr (hl1 ▸ List.mem_cons_of_mem l0 hx))
              have hrint_1 : ∀ x ∈ rint, m x = 1 := fun x hx =>
                hint1 x (allGe4MBool_sound M rint hrint_b x hx)
                  (symAppearsInRulesBool_of_mem_rhs N x core r hr (hr1 ▸ List.mem_cons_of_mem r0 hx))
              have hal : (evalFinAffine1D N m v (l0 :: lint)).2 =
                  v l0 + M0 * evalFinParikh N v lint := by
                dsimp only [evalFinAffine1D]
                rw [hl0_m, evalFinAffine1D_all_int M m v lint hlint_1]
              have har : (evalFinAffine1D N m v (r0 :: rint)).2 =
                  v r0 + M0 * evalFinParikh N v rint := by
                dsimp only [evalFinAffine1D]
                rw [hr0_m, evalFinAffine1D_all_int M m v rint hrint_1]
              have hpl : evalFinParikh N wt (l0 :: lint) =
                  M1 * (v l0 + M0 * evalFinParikh N v lint) := by
                simp only [evalFinParikh]
                have hwt_l0 : wt l0 = M1 * v l0 := by dsimp [wt]; rw [ite_true_of_w10 hl0_lt]
                have hwt_li : evalFinParikh N wt lint = (M0 * M1) * evalFinParikh N v lint :=
                  parikh_int_scale M (M0 * M1) v wt lint (fun x hx => by
                    have hx_ge := allGe4MBool_sound M lint hlint_b x hx
                    dsimp [wt]
                    rw [ite_false_of_w10 (by omega), ite_false_of_w10 (by omega)])
                rw [hwt_l0, hwt_li, Nat.mul_add, ← Nat.mul_assoc M1 M0, Nat.mul_comm M1 M0]
              have hpr : evalFinParikh N wt (r0 :: rint) =
                  M1 * (v r0 + M0 * evalFinParikh N v rint) := by
                simp only [evalFinParikh]
                have hwt_r0 : wt r0 = M1 * v r0 := by dsimp [wt]; rw [ite_true_of_w10 hr0_lt]
                have hwt_ri : evalFinParikh N wt rint = (M0 * M1) * evalFinParikh N v rint :=
                  parikh_int_scale M (M0 * M1) v wt rint (fun x hx => by
                    have hx_ge := allGe4MBool_sound M rint hrint_b x hx
                    dsimp [wt]
                    rw [ite_false_of_w10 (by omega), ite_false_of_w10 (by omega)])
                rw [hwt_r0, hwt_ri, Nat.mul_add, ← Nat.mul_assoc M1 M0, Nat.mul_comm M1 M0]
              rw [hpl, hpr]
              rw [hal, har] at hw2 ⊢
              exact ⟨Nat.mul_le_mul_left M1 hw2, fun heq => Nat.eq_of_mul_eq_mul_left (by omega) heq⟩
            · rcases bool_and_split hq1 with ⟨hb1, hrint_b⟩
              rcases bool_and_split hb1 with ⟨hlr_b, hlint_b⟩
              rcases of_decide_eq_true hlr_b with ⟨hl0_ge, hl0_lt, hr0_ge, hr0_lt⟩
              have hl0_m : m l0 = M1 := (hL_const r hr).2 l0
                (Or.inl (hl1 ▸ List.Mem.head _)) hl0_ge hl0_lt
              have hr0_m : m r0 = M1 := (hL_const r hr).2 r0
                (Or.inr (hr1 ▸ List.Mem.head _)) hr0_ge hr0_lt
              have hlint_1 : ∀ x ∈ lint, m x = 1 := fun x hx =>
                hint1 x (allGe4MBool_sound M lint hlint_b x hx)
                  (symAppearsInRulesBool_of_mem_lhs N x core r hr (hl1 ▸ List.mem_cons_of_mem l0 hx))
              have hrint_1 : ∀ x ∈ rint, m x = 1 := fun x hx =>
                hint1 x (allGe4MBool_sound M rint hrint_b x hx)
                  (symAppearsInRulesBool_of_mem_rhs N x core r hr (hr1 ▸ List.mem_cons_of_mem r0 hx))
              have hal : (evalFinAffine1D N m v (l0 :: lint)).2 =
                  v l0 + M1 * evalFinParikh N v lint := by
                dsimp only [evalFinAffine1D]
                rw [hl0_m, evalFinAffine1D_all_int M m v lint hlint_1]
              have har : (evalFinAffine1D N m v (r0 :: rint)).2 =
                  v r0 + M1 * evalFinParikh N v rint := by
                dsimp only [evalFinAffine1D]
                rw [hr0_m, evalFinAffine1D_all_int M m v rint hrint_1]
              have hpl : evalFinParikh N wt (l0 :: lint) =
                  M0 * (v l0 + M1 * evalFinParikh N v lint) := by
                simp only [evalFinParikh]
                have hwt_l0 : wt l0 = M0 * v l0 := by
                  dsimp [wt]; rw [ite_false_of_w10 (by omega), ite_true_of_w10 hl0_lt]
                have hwt_li : evalFinParikh N wt lint = (M0 * M1) * evalFinParikh N v lint :=
                  parikh_int_scale M (M0 * M1) v wt lint (fun x hx => by
                    have hx_ge := allGe4MBool_sound M lint hlint_b x hx
                    dsimp [wt]
                    rw [ite_false_of_w10 (by omega), ite_false_of_w10 (by omega)])
                rw [hwt_l0, hwt_li, Nat.mul_add, ← Nat.mul_assoc M0 M1]
              have hpr : evalFinParikh N wt (r0 :: rint) =
                  M0 * (v r0 + M1 * evalFinParikh N v rint) := by
                simp only [evalFinParikh]
                have hwt_r0 : wt r0 = M0 * v r0 := by
                  dsimp [wt]; rw [ite_false_of_w10 (by omega), ite_true_of_w10 hr0_lt]
                have hwt_ri : evalFinParikh N wt rint = (M0 * M1) * evalFinParikh N v rint :=
                  parikh_int_scale M (M0 * M1) v wt rint (fun x hx => by
                    have hx_ge := allGe4MBool_sound M rint hrint_b x hx
                    dsimp [wt]
                    rw [ite_false_of_w10 (by omega), ite_false_of_w10 (by omega)])
                rw [hwt_r0, hwt_ri, Nat.mul_add, ← Nat.mul_assoc M0 M1]
              rw [hpl, hpr]
              rw [hal, har] at hw2 ⊢
              exact ⟨Nat.mul_le_mul_left M0 hw2, fun heq => Nat.eq_of_mul_eq_mul_left (by omega) heq⟩
      · rcases bool_and_split hR_case with ⟨hl_r, hr_r⟩
        have hw2 := (hweak r hr).2
        have hal := evalFinAffine1D_right_or_int M m v r.1 hl_r
          (fun x hx hx_ge => hint1 x hx_ge (symAppearsInRulesBool_of_mem_lhs N x core r hr hx))
        have har := evalFinAffine1D_right_or_int M m v r.2 hr_r
          (fun x hx hx_ge => hint1 x hx_ge (symAppearsInRulesBool_of_mem_rhs N x core r hr hx))
        have hge2M_of : ∀ w : List (Fin N), checkWordRightOrIntBool M w = true -> ∀ x ∈ w, x.val ≥ 2 * M := by
          intro w; induction w with
          | nil => intro _ _ hx; cases hx
          | cons s rest ih =>
            cases rest with
            | nil =>
              intro hb x hx
              simp only [List.mem_singleton] at hx; subst hx
              exact of_decide_eq_true hb
            | cons s2 tl =>
              intro hb x hx
              rcases bool_and_split hb with ⟨hs_ge, htl⟩
              cases hx with
              | head => have := of_decide_eq_true hs_ge; omega
              | tail _ hmem => exact ih htl x hmem
        have hpl : evalFinParikh N wt r.1 = (M0 * M1) * evalFinParikh N v r.1 :=
          parikh_int_scale M (M0 * M1) v wt r.1 (fun x hx => by
            have hx_ge := hge2M_of r.1 hl_r x hx
            dsimp [wt]; rw [ite_false_of_w10 (by omega), ite_false_of_w10 (by omega)])
        have hpr : evalFinParikh N wt r.2 = (M0 * M1) * evalFinParikh N v r.2 :=
          parikh_int_scale M (M0 * M1) v wt r.2 (fun x hx => by
            have hx_ge := hge2M_of r.2 hr_r x hx
            dsimp [wt]; rw [ite_false_of_w10 (by omega), ite_false_of_w10 (by omega)])
        rw [hpl, hpr]
        rw [hal, har] at hw2 ⊢
        have hm01_pos : M0 * M1 ≥ 1 := Nat.mul_le_mul hM0_pos hM1_pos
        exact ⟨Nat.mul_le_mul_left (M0 * M1) hw2, fun heq => Nat.eq_of_mul_eq_mul_left (by omega) heq⟩
    have hpeq := hpar_eq_all wt (fun r hr => (hrule_rel r hr).1)
    exact fun r hr => (hrule_rel r hr).2 (hpeq r hr)
  -- Core lemma 2: Any upper-unitriangular `(mat, v)` weakly orienting `core` has `= ` in ALL rows of `v`:
  have hunitri_no_strict : ∀ (d : Nat) (hd : d ≥ 1)
      (mat : Fin N -> Fin d -> Fin d -> Nat) (v : Fin N -> Fin d -> Nat),
      (∀ (s : Fin N) (i : Fin d), mat s i i = 1) ->
      (∀ (s : Fin N) (i j : Fin d), j.val < i.val -> mat s i j = 0) ->
      (∀ r ∈ core,
        (∀ i j : Fin d, evalFinWordMat N d mat r.1 i j ≥ evalFinWordMat N d mat r.2 i j) ∧
        (∀ i : Fin d, evalFinWordVec N d mat v r.1 i ≥ evalFinWordVec N d mat v r.2 i)) ->
      ∀ r ∈ core, evalFinWordVec N d mat v r.1 ⟨0, hd⟩ = evalFinWordVec N d mat v r.2 ⟨0, hd⟩ := by
    intro d hd mat v h1 htri hweak
    -- Step A: Prove by induction on `G : Nat` that for all `1 ≤ gap ≤ G`, active interior symbols have `mat s i j = 0`:
    have hband_zero : ∀ G : Nat,
        ∀ (s : Fin N), s.val ≥ 4 * M -> symAppearsInRulesBool N s.val core = true ->
          ∀ (i j : Fin d), i.val < j.val -> j.val - i.val ≤ G -> mat s i j = 0 := by
      intro G; induction G with
      | zero => intros; omega
      | succ G' ihG =>
        intro s hs_ge hs_act i j hij hle_G
        by_cases hlt_G : j.val - i.val ≤ G'
        · exact ihG s hs_ge hs_act i j hij hlt_G
        · have heq_gap : j.val - i.val = G' + 1 := by omega
          -- On `gap = G' + 1`, `evalFinWordMat r.1 i j = evalFinParikh (fun x => mat x i j) r.1` for ALL `r ∈ core`!
          rcases unitriangular_superdiag_parikh M d mat h1 htri (G' + 1) (by omega) with ⟨hsup_int, hsup_r⟩
          have hmat_par : ∀ r ∈ core,
              evalFinParikh N (fun x => mat x i j) r.1 ≥ evalFinParikh N (fun x => mat x i j) r.2 := by
            intro r hr
            have hsh := hshape_all r hr
            unfold checkRuleTwoSidedShapeBool at hsh
            have hwm := (hweak r hr).1 i j
            rcases bool_or_split hsh with hL_c | hR_c
            · cases hl1 : r.1 with
              | nil => rw [hl1] at hL_c; simp at hL_c
              | cons l0 lint =>
                cases hr1 : r.2 with
                | nil => rw [hl1, hr1] at hL_c; simp at hL_c
                | cons r0 rint =>
                  rw [hl1, hr1] at hL_c
                  dsimp only at hL_c
                  have hlint_b : allGe4MBool M lint = true := by
                    rcases bool_or_split hL_c with h0 | h1c
                    · exact (bool_and_split (bool_and_split h0).1).2
                    · exact (bool_and_split (bool_and_split h1c).1).2
                  have hrint_b : allGe4MBool M rint = true := by
                    rcases bool_or_split hL_c with h0 | h1c
                    · exact (bool_and_split h0).2
                    · exact (bool_and_split h1c).2
                  have hl_ih : ∀ x ∈ lint, ∀ a b : Fin d, a.val < b.val -> b.val - a.val < G' + 1 -> mat x a b = 0 :=
                    fun x hx a b hab hbg =>
                      ihG x (allGe4MBool_sound M lint hlint_b x hx)
                        (symAppearsInRulesBool_of_mem_lhs N x core r hr (hl1 ▸ List.mem_cons_of_mem l0 hx))
                        a b hab (by omega)
                  have hr_ih : ∀ x ∈ rint, ∀ a b : Fin d, a.val < b.val -> b.val - a.val < G' + 1 -> mat x a b = 0 :=
                    fun x hx a b hab hbg =>
                      ihG x (allGe4MBool_sound M rint hrint_b x hx)
                        (symAppearsInRulesBool_of_mem_rhs N x core r hr (hr1 ▸ List.mem_cons_of_mem r0 hx))
                        a b hab (by omega)
                  have hne_ij : i ≠ j := fun he => by subst he; omega
                  have hl_ev : evalFinWordMat N d mat (l0 :: lint) i j =
                      evalFinParikh N (fun x => mat x i j) (l0 :: lint) := by
                    simp only [evalFinWordMat, evalFinParikh, natMatMul]
                    rw [natSumFin_two_terms d (fun k => mat l0 i k * evalFinWordMat N d mat lint k j) i j hne_ij]
                    · rw [h1 l0 i, Nat.one_mul, (hsup_int lint hl_ih i j hij).2 heq_gap,
                          (unitriangular_wordMat_tri_and_diag N d mat h1 htri lint j j).2 rfl,
                          Nat.mul_one, Nat.add_comm]
                    · intro k hki hkj
                      by_cases hlk : k.val < i.val
                      · rw [htri l0 i k hlk, Nat.zero_mul]
                      · by_cases hgk : j.val < k.val
                        · rw [(unitriangular_wordMat_tri_and_diag N d mat h1 htri lint k j).1 hgk, Nat.mul_zero]
                        · have hkj_lt : k.val < j.val := by
                            have : k.val ≠ j.val := fun hv => hkj (Fin.ext hv); omega
                          rw [(hsup_int lint hl_ih k j hkj_lt).1 (by omega), Nat.mul_zero]
                  have hr_ev : evalFinWordMat N d mat (r0 :: rint) i j =
                      evalFinParikh N (fun x => mat x i j) (r0 :: rint) := by
                    simp only [evalFinWordMat, evalFinParikh, natMatMul]
                    rw [natSumFin_two_terms d (fun k => mat r0 i k * evalFinWordMat N d mat rint k j) i j hne_ij]
                    · rw [h1 r0 i, Nat.one_mul, (hsup_int rint hr_ih i j hij).2 heq_gap,
                          (unitriangular_wordMat_tri_and_diag N d mat h1 htri rint j j).2 rfl,
                          Nat.mul_one, Nat.add_comm]
                    · intro k hki hkj
                      by_cases hlk : k.val < i.val
                      · rw [htri r0 i k hlk, Nat.zero_mul]
                      · by_cases hgk : j.val < k.val
                        · rw [(unitriangular_wordMat_tri_and_diag N d mat h1 htri rint k j).1 hgk, Nat.mul_zero]
                        · have hkj_lt : k.val < j.val := by
                            have : k.val ≠ j.val := fun hv => hkj (Fin.ext hv); omega
                          rw [(hsup_int rint hr_ih k j hkj_lt).1 (by omega), Nat.mul_zero]
                  rw [hl1, hr1] at hwm
                  rwa [hl_ev, hr_ev] at hwm
            · rcases bool_and_split hR_c with ⟨hl_r, hr_r⟩
              have hl_ev := hsup_r r.1 hl_r
                (fun x hx hxg a b hab hbg =>
                  ihG x hxg (symAppearsInRulesBool_of_mem_lhs N x core r hr hx) a b hab (by omega))
                i j hij heq_gap
              have hr_ev := hsup_r r.2 hr_r
                (fun x hx hxg a b hab hbg =>
                  ihG x hxg (symAppearsInRulesBool_of_mem_rhs N x core r hr hx) a b hab (by omega))
                i j hij heq_gap
              rwa [hl_ev, hr_ev] at hwm
          exact hpar_int_zero (fun x => mat x i j) (hpar_eq_all _ hmat_par) s hs_ge hs_act
    have hint_id : ∀ (s : Fin N), s.val ≥ 4 * M -> symAppearsInRulesBool N s.val core = true ->
        ∀ a b : Fin d, a ≠ b -> mat s a b = 0 := by
      intro s hs_ge hs_act a b hab
      by_cases hlt : b.val < a.val
      · exact htri s a b hlt
      · have hab_lt : a.val < b.val := by
          have : a.val ≠ b.val := fun hv => hab (Fin.ext hv); omega
        exact hband_zero d s hs_ge hs_act a b hab_lt (by have := b.isLt; omega)
    -- Step B: Downward induction on `rem = d - 1 - i.val` proves `v s i = 0` on active interior AND `v_l = v_r`:
    have hvec_down : ∀ (rem : Nat) (i0 : Fin d),
        d - 1 - i0.val ≤ rem ->
        (∀ r ∈ core, evalFinWordVec N d mat v r.1 i0 = evalFinWordVec N d mat v r.2 i0) ∧
        (∀ s : Fin N, s.val ≥ 4 * M -> symAppearsInRulesBool N s.val core = true -> v s i0 = 0) := by
      intro rem; induction rem with
      | zero =>
        intro i0 hrem0
        rcases unitriangular_vec_parikh M d mat v h1 htri i0 with ⟨hv_int, hv_r⟩
        have hv_eq_par : ∀ r ∈ core,
            evalFinWordVec N d mat v r.1 i0 = evalFinParikh N (fun x => v x i0) r.1 ∧
            evalFinWordVec N d mat v r.2 i0 = evalFinParikh N (fun x => v x i0) r.2 := by
          intro r hr
          have hsh := hshape_all r hr
          unfold checkRuleTwoSidedShapeBool at hsh
          rcases bool_or_split hsh with hL_c | hR_c
          · cases hl1 : r.1 with
            | nil => rw [hl1] at hL_c; simp at hL_c
            | cons l0 lint =>
              cases hr1 : r.2 with
              | nil => rw [hl1, hr1] at hL_c; simp at hL_c
              | cons r0 rint =>
                rw [hl1, hr1] at hL_c; dsimp only at hL_c
                have hlint_b : allGe4MBool M lint = true := by
                  rcases bool_or_split hL_c with h0 | h1c
                  · exact (bool_and_split (bool_and_split h0).1).2
                  · exact (bool_and_split (bool_and_split h1c).1).2
                have hrint_b : allGe4MBool M rint = true := by
                  rcases bool_or_split hL_c with h0 | h1c
                  · exact (bool_and_split h0).2
                  · exact (bool_and_split h1c).2
                have hn_gt : ∀ k : Fin d, ¬ (i0.val < k.val) := by
                  intro k; have := k.isLt; omega
                rcases hv_int lint
                  (fun x hx => hint_id x (allGe4MBool_sound M lint hlint_b x hx)
                    (symAppearsInRulesBool_of_mem_lhs N x core r hr (hl1 ▸ List.mem_cons_of_mem l0 hx)))
                  (fun _ _ k hk => False.elim (hn_gt k hk)) with ⟨hlk0, hli0⟩
                rcases hv_int rint
                  (fun x hx => hint_id x (allGe4MBool_sound M rint hrint_b x hx)
                    (symAppearsInRulesBool_of_mem_rhs N x core r hr (hr1 ▸ List.mem_cons_of_mem r0 hx)))
                  (fun _ _ k hk => False.elim (hn_gt k hk)) with ⟨hrk0, hri0⟩
                refine ⟨?_, ?_⟩
                · simp only [evalFinWordVec, evalFinParikh, natMatVec]
                  rw [natSumPrefix_single_fin d (fun k => mat l0 i0 k * evalFinWordVec N d mat v lint k) i0]
                  · rw [h1 l0 i0, Nat.one_mul, hli0]
                  · intro k hk
                    by_cases hlt : k.val < i0.val
                    · rw [htri l0 i0 k hlt, Nat.zero_mul]
                    · exact False.elim (hn_gt k (by
                        have : k.val ≠ i0.val := fun hv => hk (Fin.ext hv); omega))
                · simp only [evalFinWordVec, evalFinParikh, natMatVec]
                  rw [natSumPrefix_single_fin d (fun k => mat r0 i0 k * evalFinWordVec N d mat v rint k) i0]
                  · rw [h1 r0 i0, Nat.one_mul, hri0]
                  · intro k hk
                    by_cases hlt : k.val < i0.val
                    · rw [htri r0 i0 k hlt, Nat.zero_mul]
                    · exact False.elim (hn_gt k (by
                        have : k.val ≠ i0.val := fun hv => hk (Fin.ext hv); omega))
          · rcases bool_and_split hR_c with ⟨hl_r, hr_r⟩
            exact ⟨hv_r r.1 hl_r (fun x hx hxg => hint_id x hxg (symAppearsInRulesBool_of_mem_lhs N x core r hr hx)),
                   hv_r r.2 hr_r (fun x hx hxg => hint_id x hxg (symAppearsInRulesBool_of_mem_rhs N x core r hr hx))⟩
        have hpar_ge : ∀ r ∈ core,
            evalFinParikh N (fun x => v x i0) r.1 ≥ evalFinParikh N (fun x => v x i0) r.2 := by
          intro r hr
          rcases hv_eq_par r hr with ⟨hl_e, hr_e⟩
          rw [← hl_e, ← hr_e]
          exact (hweak r hr).2 i0
        have hpeq := hpar_eq_all (fun x => v x i0) hpar_ge
        refine ⟨fun r hr => by rcases hv_eq_par r hr with ⟨hl_e, hr_e⟩; rw [hl_e, hr_e]; exact hpeq r hr,
                hpar_int_zero (fun x => v x i0) hpeq⟩
      | succ rem' ihR =>
        intro i0 hrem
        by_cases hle' : d - 1 - i0.val ≤ rem'
        · exact ihR i0 hle'
        · rcases unitriangular_vec_parikh M d mat v h1 htri i0 with ⟨hv_int, hv_r⟩
          have hv_gt_zero : ∀ (k : Fin d), i0.val < k.val ->
              ∀ s : Fin N, s.val ≥ 4 * M -> symAppearsInRulesBool N s.val core = true -> v s k = 0 :=
            fun k hk => (ihR k (by omega)).2
          have hv_eq_par : ∀ r ∈ core,
              evalFinWordVec N d mat v r.1 i0 = evalFinParikh N (fun x => v x i0) r.1 ∧
              evalFinWordVec N d mat v r.2 i0 = evalFinParikh N (fun x => v x i0) r.2 := by
            intro r hr
            have hsh := hshape_all r hr
            unfold checkRuleTwoSidedShapeBool at hsh
            rcases bool_or_split hsh with hL_c | hR_c
            · cases hl1 : r.1 with
              | nil => rw [hl1] at hL_c; simp at hL_c
              | cons l0 lint =>
                cases hr1 : r.2 with
                | nil => rw [hl1, hr1] at hL_c; simp at hL_c
                | cons r0 rint =>
                  rw [hl1, hr1] at hL_c; dsimp only at hL_c
                  have hlint_b : allGe4MBool M lint = true := by
                    rcases bool_or_split hL_c with h0 | h1c
                    · exact (bool_and_split (bool_and_split h0).1).2
                    · exact (bool_and_split (bool_and_split h1c).1).2
                  have hrint_b : allGe4MBool M rint = true := by
                    rcases bool_or_split hL_c with h0 | h1c
                    · exact (bool_and_split h0).2
                    · exact (bool_and_split h1c).2
                  rcases hv_int lint
                    (fun x hx => hint_id x (allGe4MBool_sound M lint hlint_b x hx)
                      (symAppearsInRulesBool_of_mem_lhs N x core r hr (hl1 ▸ List.mem_cons_of_mem l0 hx)))
                    (fun x hx k hk => hv_gt_zero k hk x (allGe4MBool_sound M lint hlint_b x hx)
                      (symAppearsInRulesBool_of_mem_lhs N x core r hr (hl1 ▸ List.mem_cons_of_mem l0 hx)))
                    with ⟨hlk0, hli0⟩
                  rcases hv_int rint
                    (fun x hx => hint_id x (allGe4MBool_sound M rint hrint_b x hx)
                      (symAppearsInRulesBool_of_mem_rhs N x core r hr (hr1 ▸ List.mem_cons_of_mem r0 hx)))
                    (fun x hx k hk => hv_gt_zero k hk x (allGe4MBool_sound M rint hrint_b x hx)
                      (symAppearsInRulesBool_of_mem_rhs N x core r hr (hr1 ▸ List.mem_cons_of_mem r0 hx)))
                    with ⟨hrk0, hri0⟩
                  refine ⟨?_, ?_⟩
                  · simp only [evalFinWordVec, evalFinParikh, natMatVec]
                    rw [natSumPrefix_single_fin d (fun k => mat l0 i0 k * evalFinWordVec N d mat v lint k) i0]
                    · rw [h1 l0 i0, Nat.one_mul, hli0]
                    · intro k hk
                      by_cases hlt : k.val < i0.val
                      · rw [htri l0 i0 k hlt, Nat.zero_mul]
                      · rw [hlk0 k (by have : k.val ≠ i0.val := fun hv => hk (Fin.ext hv); omega), Nat.mul_zero]
                  · simp only [evalFinWordVec, evalFinParikh, natMatVec]
                    rw [natSumPrefix_single_fin d (fun k => mat r0 i0 k * evalFinWordVec N d mat v rint k) i0]
                    · rw [h1 r0 i0, Nat.one_mul, hri0]
                    · intro k hk
                      by_cases hlt : k.val < i0.val
                      · rw [htri r0 i0 k hlt, Nat.zero_mul]
                      · rw [hrk0 k (by have : k.val ≠ i0.val := fun hv => hk (Fin.ext hv); omega), Nat.mul_zero]
            · rcases bool_and_split hR_c with ⟨hl_r, hr_r⟩
              exact ⟨hv_r r.1 hl_r (fun x hx hxg => hint_id x hxg (symAppearsInRulesBool_of_mem_lhs N x core r hr hx)),
                     hv_r r.2 hr_r (fun x hx hxg => hint_id x hxg (symAppearsInRulesBool_of_mem_rhs N x core r hr hx))⟩
          have hpar_ge : ∀ r ∈ core,
              evalFinParikh N (fun x => v x i0) r.1 ≥ evalFinParikh N (fun x => v x i0) r.2 := by
            intro r hr
            rcases hv_eq_par r hr with ⟨hl_e, hr_e⟩
            rw [← hl_e, ← hr_e]
            exact (hweak r hr).2 i0
          have hpeq := hpar_eq_all (fun x => v x i0) hpar_ge
          refine ⟨fun r hr => by rcases hv_eq_par r hr with ⟨hl_e, hr_e⟩; rw [hl_e, hr_e]; exact hpeq r hr,
                  hpar_int_zero (fun x => v x i0) hpeq⟩
    exact (hvec_down d ⟨0, hd⟩ (by omega)).1
  cases hcore_c : core with
  | nil => exact False.elim (hne_core hcore_c)
  | cons r0 rs =>
    rw [← hcore_c]
    have hmem0 : r0 ∈ core := hcore_c ▸ List.Mem.head _
    refine ⟨?_, ?_, ?_⟩
    · have himp1 : ∀ (k : Nat) (cur : List (List (Fin N) × List (Fin N))),
          (∀ r ∈ core, r ∈ cur) -> ¬ GenOmegaAffine1DFinTower N k cur := by
        intro k; induction k with
        | zero =>
          intro cur hsub h0; rw [GenOmegaAffine1DFinTower] at h0; subst h0
          exact List.not_mem_nil (hsub r0 hmem0)
        | succ k' ih =>
          intro cur hsub hsucc
          rcases hsucc with rfl | ⟨rem, m, v, hm1, hweak, hkeep, hrem⟩
          · exact List.not_mem_nil (hsub r0 hmem0)
          · have heq := haff_no_strict m v hm1 (fun r hr => hweak r (hsub r hr))
            exact ih rem (fun r hr => hkeep r (hsub r hr) (by rw [heq r hr]; exact Nat.lt_irrefl _)) hrem
      exact fun k => himp1 k core (fun _ hr => hr)
    · intro d hd
      have himp2 : ∀ (k : Nat) (cur : List (List (Fin N) × List (Fin N))),
          (∀ r ∈ core, r ∈ cur) -> ¬ GenOmegaDiagCoordMonoMatTower N d hd k cur := by
        intro k; induction k with
        | zero =>
          intro cur hsub h0; rw [GenOmegaDiagCoordMonoMatTower] at h0; subst h0
          exact List.not_mem_nil (hsub r0 hmem0)
        | succ k' ih =>
          intro cur hsub hsucc
          rcases hsucc with rfl | ⟨rem, mat, v, hpos, hdiag, hweak, hkeep, hrem⟩
          · exact List.not_mem_nil (hsub r0 hmem0)
          · let i0 : Fin d := ⟨0, hd⟩
            have heq := haff_no_strict (fun s => mat s i0 i0) (fun s => v s i0) (fun s => hpos s i0)
              (fun r hr => by
                rcases diag_mat_vec_eq_affine1d N d mat v hdiag i0 r.1 with ⟨hm1_e, hv1_e⟩
                rcases diag_mat_vec_eq_affine1d N d mat v hdiag i0 r.2 with ⟨hm2_e, hv2_e⟩
                rw [← hm1_e, ← hm2_e, ← hv1_e, ← hv2_e]
                exact ⟨(hweak r (hsub r hr)).1 i0 i0, (hweak r (hsub r hr)).2 i0⟩)
            exact ih rem (fun r hr => hkeep r (hsub r hr) (by
              rcases diag_mat_vec_eq_affine1d N d mat v hdiag i0 r.1 with ⟨_, hv1_e⟩
              rcases diag_mat_vec_eq_affine1d N d mat v hdiag i0 r.2 with ⟨_, hv2_e⟩
              rw [hv1_e, hv2_e, heq r hr]
              exact Nat.lt_irrefl _)) hrem
      exact fun k => himp2 k core (fun _ hr => hr)
    · intro d hd
      have himp3 : ∀ (k : Nat) (cur : List (List (Fin N) × List (Fin N))),
          (∀ r ∈ core, r ∈ cur) -> ¬ GenOmegaUnitriangularMatTower N d hd k cur := by
        intro k; induction k with
        | zero =>
          intro cur hsub h0; rw [GenOmegaUnitriangularMatTower] at h0; subst h0
          exact List.not_mem_nil (hsub r0 hmem0)
        | succ k' ih =>
          intro cur hsub hsucc
          rcases hsucc with rfl | ⟨rem, mat, v, h1, htri, hweak, hkeep, hrem⟩
          · exact List.not_mem_nil (hsub r0 hmem0)
          · have heq := hunitri_no_strict d hd mat v h1 htri (fun r hr => hweak r (hsub r hr))
            exact ih rem (fun r hr => hkeep r (hsub r hr) (by rw [heq r hr]; exact Nat.lt_irrefl _)) hrem
      exact fun k => himp3 k core (fun _ hr => hr)

set_option maxRecDepth 65536 in
private theorem c39_certs_ok :
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
private theorem c78_certs_ok_a :
    let c78 := filterFinParikhUnoriented 84 wtTwoSidedMod6OmitR3
      (twoSidedLabelledCollatzRules 6 (by decide) all11OmitR3List)
    checkPositiveParikhSyzygyFastBool 84 c78 syzTwoSidedMod6OmitR3Core78 = true ∧
    checkSignedInteriorAnnihilationBool 6 c78 posMultsC78 negMultsC78 = true ∧
    checkAllRulesShapeBool 6 c78 = true ∧
    c78 ≠ [] := by decide

def hasTwoToOneRuleBool (N : Nat) (a b c : Nat) : List (List (Fin N) × List (Fin N)) -> Bool
  | [] => false
  | (l, r) :: rs =>
    decide (l.map Fin.val = [a, b] ∧ r.map Fin.val = [c]) || hasTwoToOneRuleBool N a b c rs

private theorem hasTwoToOneRuleBool_sound (N : Nat) (a b c : Fin N) :
    ∀ rs : List (List (Fin N) × List (Fin N)),
      hasTwoToOneRuleBool N a.val b.val c.val rs = true -> ([a, b], [c]) ∈ rs
  | [], h => by cases h
  | (l, r) :: rs, h => by
    unfold hasTwoToOneRuleBool at h
    rcases bool_or_split h with h0 | htl
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
    · exact List.mem_cons_of_mem _ (hasTwoToOneRuleBool_sound N a b c rs htl)

set_option maxRecDepth 65536 in
private theorem c78_certs_ok_b :
    let c78 := filterFinParikhUnoriented 84 wtTwoSidedMod6OmitR3
      (twoSidedLabelledCollatzRules 6 (by decide) all11OmitR3List)
    hasTwoToOneRuleBool 84 4 29 5 c78 = true ∧
    hasTwoToOneRuleBool 84 2 28 4 c78 = true ∧
    hasTwoToOneRuleBool 84 2 25 1 c78 = true ∧
    hasTwoToOneRuleBool 84 10 29 11 c78 = true ∧
    hasTwoToOneRuleBool 84 8 28 10 c78 = true ∧
    hasTwoToOneRuleBool 84 8 25 7 c78 = true := by decide

set_option maxRecDepth 65536 in
private theorem c78_certs_ok_c :
    let c78 := filterFinParikhUnoriented 84 wtTwoSidedMod6OmitR3
      (twoSidedLabelledCollatzRules 6 (by decide) all11OmitR3List)
    symAppearsInRulesBool 84 29 c78 = true ∧
    symAppearsInRulesBool 84 28 c78 = true ∧
    symAppearsInRulesBool 84 25 c78 = true ∧
    symAppearsInRulesBool 84 0 c78 = false ∧
    symAppearsInRulesBool 84 3 c78 = false ∧
    symAppearsInRulesBool 84 6 c78 = false ∧
    symAppearsInRulesBool 84 9 c78 = false := by decide

/--
  Theorem W12.1b (`twosided_c39_c78_affine1d_and_coord_monotone_impossibility`,
  `zero custom axioms`):
  Complete Collapse of `1D`-Affine (`m_s ≥ 1`), `∀ d ≥ 1` Diagonal Coordinatewise-Monotone, &
  `∀ d ≥ 1` Upper-Unitriangular (`Pol_d`) `ω^k` Matrix Towers on `TwoSided(2 × 3)` `c39` &
  `TwoSided(2 × 6)` `c78` (`all11 \ {R3}`, `Branch P4.3`, `W12_H2`):
  For ALL tower heights `k : Nat` and ALL dimensions `d ≥ 1`:
  1. `¬ GenOmegaAffine1DFinTower 42 k c39 ∧ ¬ GenOmegaAffine1DFinTower 84 k c78`,
  2. `¬ GenOmegaDiagCoordMonoMatTower 42 d hd k c39 ∧ ¬ GenOmegaDiagCoordMonoMatTower 84 d hd k c78`, AND
  3. `¬ GenOmegaUnitriangularMatTower 42 d hd k c39 ∧ ¬ GenOmegaUnitriangularMatTower 84 d hd k c78`!
-/
theorem twosided_c39_c78_affine1d_and_coord_monotone_impossibility :
    let c39 := filterFinParikhUnoriented 42 wtTwoSidedMod3OmitR3
      (twoSidedLabelledCollatzRules 3 (by decide) all11OmitR3List)
    let c78 := filterFinParikhUnoriented 84 wtTwoSidedMod6OmitR3
      (twoSidedLabelledCollatzRules 6 (by decide) all11OmitR3List)
    (∀ k : Nat, ¬ GenOmegaAffine1DFinTower 42 k c39 ∧ ¬ GenOmegaAffine1DFinTower 84 k c78) ∧
    (∀ (d : Nat) (hd : d ≥ 1) (k : Nat),
      ¬ GenOmegaDiagCoordMonoMatTower 42 d hd k c39 ∧
      ¬ GenOmegaDiagCoordMonoMatTower 84 d hd k c78) ∧
    (∀ (d : Nat) (hd : d ≥ 1) (k : Nat),
      ¬ GenOmegaUnitriangularMatTower 42 d hd k c39 ∧
      ¬ GenOmegaUnitriangularMatTower 84 d hd k c78) := by
  let c39 := filterFinParikhUnoriented 42 wtTwoSidedMod3OmitR3
    (twoSidedLabelledCollatzRules 3 (by decide) all11OmitR3List)
  let c78 := filterFinParikhUnoriented 84 wtTwoSidedMod6OmitR3
    (twoSidedLabelledCollatzRules 6 (by decide) all11OmitR3List)
  rcases c39_certs_ok with
    ⟨hsyz3, hann3, hsh3, hne3, hr3_1, hr3_2, ha3_14, hn3_0, hn3_3⟩
  rcases c78_certs_ok_a with ⟨hsyz6, hann6, hsh6, hne6⟩
  rcases c78_certs_ok_b with ⟨hb6_0, hb6_1, hb6_3, hb6_4, hb6_5, hb6_7⟩
  have hr6_0 := hasTwoToOneRuleBool_sound 84 ⟨4, by decide⟩ ⟨29, by decide⟩ ⟨5, by decide⟩ c78 hb6_0
  have hr6_1 := hasTwoToOneRuleBool_sound 84 ⟨2, by decide⟩ ⟨28, by decide⟩ ⟨4, by decide⟩ c78 hb6_1
  have hr6_3 := hasTwoToOneRuleBool_sound 84 ⟨2, by decide⟩ ⟨25, by decide⟩ ⟨1, by decide⟩ c78 hb6_3
  have hr6_4 := hasTwoToOneRuleBool_sound 84 ⟨10, by decide⟩ ⟨29, by decide⟩ ⟨11, by decide⟩ c78 hb6_4
  have hr6_5 := hasTwoToOneRuleBool_sound 84 ⟨8, by decide⟩ ⟨28, by decide⟩ ⟨10, by decide⟩ c78 hb6_5
  have hr6_7 := hasTwoToOneRuleBool_sound 84 ⟨8, by decide⟩ ⟨25, by decide⟩ ⟨7, by decide⟩ c78 hb6_7
  rcases c78_certs_ok_c with ⟨ha6_29, ha6_28, ha6_25, hn6_0, hn6_3, hn6_6, hn6_9⟩
  have hm3 := twosided_core_collapse_master 3 c39 syzTwoSidedMod3OmitR3Core39
    posMultsC39 negMultsC39 ⟨1, by decide⟩ ⟨4, by decide⟩ hsyz3 hann3 hsh3 hne3 ?_
  · have hm6 := twosided_core_collapse_master 6 c78 syzTwoSidedMod6OmitR3Core78
      posMultsC78 negMultsC78 ⟨1, by decide⟩ ⟨7, by decide⟩ hsyz6 hann6 hsh6 hne6 ?_
    · exact ⟨fun k => ⟨hm3.1 k, hm6.1 k⟩,
             fun d hd k => ⟨hm3.2.1 d hd k, hm6.2.1 d hd k⟩,
             fun d hd k => ⟨hm3.2.2 d hd k, hm6.2.2 d hd k⟩⟩
    · -- `L`-equalization on `c78`:
      intro m hpeq hint1 r hr
      have hm29 : m ⟨29, by decide⟩ = 1 := hint1 ⟨29, by decide⟩ (by decide) ha6_29
      have hm28 : m ⟨28, by decide⟩ = 1 := hint1 ⟨28, by decide⟩ (by decide) ha6_28
      have hm25 : m ⟨25, by decide⟩ = 1 := hint1 ⟨25, by decide⟩ (by decide) ha6_25
      have he45 : m ⟨4, by decide⟩ = m ⟨5, by decide⟩ := by
        have h := hpeq _ hr6_0; dsimp only [prodFinWord] at h; rw [hm29] at h; omega
      have he24 : m ⟨2, by decide⟩ = m ⟨4, by decide⟩ := by
        have h := hpeq _ hr6_1; dsimp only [prodFinWord] at h; rw [hm28] at h; omega
      have he21 : m ⟨2, by decide⟩ = m ⟨1, by decide⟩ := by
        have h := hpeq _ hr6_3; dsimp only [prodFinWord] at h; rw [hm25] at h; omega
      have he10_11 : m ⟨10, by decide⟩ = m ⟨11, by decide⟩ := by
        have h := hpeq _ hr6_4; dsimp only [prodFinWord] at h; rw [hm29] at h; omega
      have he8_10 : m ⟨8, by decide⟩ = m ⟨10, by decide⟩ := by
        have h := hpeq _ hr6_5; dsimp only [prodFinWord] at h; rw [hm28] at h; omega
      have he8_7 : m ⟨8, by decide⟩ = m ⟨7, by decide⟩ := by
        have h := hpeq _ hr6_7; dsimp only [prodFinWord] at h; rw [hm25] at h; omega
      refine ⟨?_, ?_⟩
      · intro s hs_mem hs_lt
        have hs_act : symAppearsInRulesBool 84 s.val c78 = true := by
          rcases hs_mem with hl | hr_m
          · exact symAppearsInRulesBool_of_mem_lhs 84 s c78 r hr hl
          · exact symAppearsInRulesBool_of_mem_rhs 84 s c78 r hr hr_m
        rcases (by omega : s.val = 0 ∨ s.val = 1 ∨ s.val = 2 ∨ s.val = 3 ∨ s.val = 4 ∨ s.val = 5) with
          hv | hv | hv | hv | hv | hv
        · rw [hv, hn6_0] at hs_act; cases hs_act
        · have hs_eq : s = ⟨1, by decide⟩ := Fin.ext hv; rw [hs_eq]
        · have hs_eq : s = ⟨2, by decide⟩ := Fin.ext hv; rw [hs_eq, he21]
        · rw [hv, hn6_3] at hs_act; cases hs_act
        · have hs_eq : s = ⟨4, by decide⟩ := Fin.ext hv; rw [hs_eq, ← he24, he21]
        · have hs_eq : s = ⟨5, by decide⟩ := Fin.ext hv; rw [hs_eq, ← he45, ← he24, he21]
      · intro s hs_mem hs_ge hs_lt
        have hs_act : symAppearsInRulesBool 84 s.val c78 = true := by
          rcases hs_mem with hl | hr_m
          · exact symAppearsInRulesBool_of_mem_lhs 84 s c78 r hr hl
          · exact symAppearsInRulesBool_of_mem_rhs 84 s c78 r hr hr_m
        rcases (by omega : s.val = 6 ∨ s.val = 7 ∨ s.val = 8 ∨ s.val = 9 ∨ s.val = 10 ∨ s.val = 11) with
          hv | hv | hv | hv | hv | hv
        · rw [hv, hn6_6] at hs_act; cases hs_act
        · have hs_eq : s = ⟨7, by decide⟩ := Fin.ext hv; rw [hs_eq]
        · have hs_eq : s = ⟨8, by decide⟩ := Fin.ext hv; rw [hs_eq, he8_7]
        · rw [hv, hn6_9] at hs_act; cases hs_act
        · have hs_eq : s = ⟨10, by decide⟩ := Fin.ext hv; rw [hs_eq, ← he8_10, he8_7]
        · have hs_eq : s = ⟨11, by decide⟩ := Fin.ext hv; rw [hs_eq, ← he10_11, ← he8_10, he8_7]
  · -- `L`-equalization on `c39`:
    intro m hpeq hint1 r hr
    have hm14 : m ⟨14, by decide⟩ = 1 := hint1 ⟨14, by decide⟩ (by decide) ha3_14
    have he12 : m ⟨1, by decide⟩ = m ⟨2, by decide⟩ := by
      have h := hpeq _ hr3_1; dsimp only [prodFinWord] at h; rw [hm14] at h; omega
    have he45 : m ⟨4, by decide⟩ = m ⟨5, by decide⟩ := by
      have h := hpeq _ hr3_2; dsimp only [prodFinWord] at h; rw [hm14] at h; omega
    refine ⟨?_, ?_⟩
    · intro s hs_mem hs_lt
      have hs_act : symAppearsInRulesBool 42 s.val c39 = true := by
        rcases hs_mem with hl | hr_m
        · exact symAppearsInRulesBool_of_mem_lhs 42 s c39 r hr hl
        · exact symAppearsInRulesBool_of_mem_rhs 42 s c39 r hr hr_m
      rcases (by omega : s.val = 0 ∨ s.val = 1 ∨ s.val = 2) with hv | hv | hv
      · rw [hv, hn3_0] at hs_act; cases hs_act
      · have hs_eq : s = ⟨1, by decide⟩ := Fin.ext hv; rw [hs_eq]
      · have hs_eq : s = ⟨2, by decide⟩ := Fin.ext hv; rw [hs_eq, ← he12]
    · intro s hs_mem hs_ge hs_lt
      have hs_act : symAppearsInRulesBool 42 s.val c39 = true := by
        rcases hs_mem with hl | hr_m
        · exact symAppearsInRulesBool_of_mem_lhs 42 s c39 r hr hl
        · exact symAppearsInRulesBool_of_mem_rhs 42 s c39 r hr hr_m
      rcases (by omega : s.val = 3 ∨ s.val = 4 ∨ s.val = 5) with hv | hv | hv
      · rw [hv, hn3_3] at hs_act; cases hs_act
      · have hs_eq : s = ⟨4, by decide⟩ := Fin.ext hv; rw [hs_eq]
      · have hs_eq : s = ⟨5, by decide⟩ := Fin.ext hv; rw [hs_eq, ← he45]

-- ----------------------------------------------------------------------------
-- Section 1B': Universal `∀ d ≥ 1` Non-Unitriangular Zero-Diagonal (`2`-Gram &
--              Column-Memory) `ω^k` Matrix Tower Collapse on `c39` & `c78`
-- ----------------------------------------------------------------------------

def GenOmegaLowerZeroDiagMatTower (N d : Nat) (hd : d ≥ 1) :
    Nat -> List (List (Fin N) × List (Fin N)) -> Prop
  | 0, rules => rules = []
  | k + 1, rules =>
    rules = [] ∨
    ∃ (rem : List (List (Fin N) × List (Fin N)))
      (M : Fin N -> Fin d -> Fin d -> Nat) (v : Fin N -> Fin d -> Nat),
      (∀ s : Fin N, M s ⟨0, hd⟩ ⟨0, hd⟩ = 1) ∧
      (∀ (s : Fin N) (j : Fin d), j.val > 0 -> M s ⟨0, hd⟩ j = 0) ∧
      (∀ (s : Fin N) (i j : Fin d), i.val > 0 -> j.val > 0 -> M s i j = 0) ∧
      (∀ r ∈ rules,
        (∀ i j : Fin d, evalFinWordMat N d M r.1 i j ≥ evalFinWordMat N d M r.2 i j) ∧
        (∀ i : Fin d, evalFinWordVec N d M v r.1 i ≥ evalFinWordVec N d M v r.2 i)) ∧
      (∀ r ∈ rules,
        ¬ (evalFinWordVec N d M v r.1 ⟨0, hd⟩ > evalFinWordVec N d M v r.2 ⟨0, hd⟩) -> r ∈ rem) ∧
      GenOmegaLowerZeroDiagMatTower N d hd k rem

def GenOmegaUpperZeroDiagMatTower (N d : Nat) (hd : d ≥ 1) :
    Nat -> List (List (Fin N) × List (Fin N)) -> Prop
  | 0, rules => rules = []
  | k + 1, rules =>
    rules = [] ∨
    ∃ (rem : List (List (Fin N) × List (Fin N)))
      (M : Fin N -> Fin d -> Fin d -> Nat) (v : Fin N -> Fin d -> Nat),
      (∀ s : Fin N, M s ⟨0, hd⟩ ⟨0, hd⟩ = 1) ∧
      (∀ (s : Fin N) (i j : Fin d), i.val > 0 -> M s i j = 0) ∧
      (∀ r ∈ rules,
        (∀ i j : Fin d, evalFinWordMat N d M r.1 i j ≥ evalFinWordMat N d M r.2 i j) ∧
        (∀ i : Fin d, evalFinWordVec N d M v r.1 i ≥ evalFinWordVec N d M v r.2 i)) ∧
      (∀ r ∈ rules,
        ¬ (evalFinWordVec N d M v r.1 ⟨0, hd⟩ > evalFinWordVec N d M v r.2 ⟨0, hd⟩) -> r ∈ rem) ∧
      GenOmegaUpperZeroDiagMatTower N d hd k rem

private theorem natSumFin_zero_w12 (d : Nat) (f : Fin d -> Nat)
    (hz : ∀ k : Fin d, f k = 0) : natSumFin d f = 0 := by
  unfold natSumFin
  have hst : ∀ m : Nat, m ≤ d -> natSumPrefix d f m = 0 := by
    intro m hm; induction m with
    | zero => rfl
    | succ m' ih =>
      have hm'_lt : m' < d := hm
      simp only [natSumPrefix, hm'_lt, dite_true, ih (Nat.le_of_lt hm), hz ⟨m', hm'_lt⟩]
  exact hst d (Nat.le_refl d)

private theorem natSumFin_split_zero (d : Nat) (hd : d ≥ 1) (f : Fin d -> Nat) :
    natSumFin d f = f ⟨0, hd⟩ + natSumFin d (fun j => if j.val = 0 then 0 else f j) := by
  unfold natSumFin
  have hst : ∀ m : Nat, 1 ≤ m -> m ≤ d ->
      natSumPrefix d f m =
        f ⟨0, hd⟩ + natSumPrefix d (fun j => if j.val = 0 then 0 else f j) m := by
    intro m hm1 hmd; induction m with
    | zero => omega
    | succ m' ih =>
      cases m' with
      | zero =>
        have h0d : 0 < d := hd
        simp [natSumPrefix, h0d]
      | succ k =>
        have hk1_lt : k + 1 < d := hmd
        have hne0 : k + 1 ≠ 0 := by omega
        unfold natSumPrefix
        simp only [hk1_lt, dite_true, ite_false_of_w10 hne0]
        rw [ih (by omega) (Nat.le_of_lt hmd), Nat.add_assoc]
  exact hst d hd (Nat.le_refl d)

private theorem lowerZeroDiag_wordVec_top (N d : Nat) (hd : d ≥ 1)
    (M : Fin N -> Fin d -> Fin d -> Nat) (v : Fin N -> Fin d -> Nat)
    (h00 : ∀ s : Fin N, M s ⟨0, hd⟩ ⟨0, hd⟩ = 1)
    (h0j : ∀ (s : Fin N) (j : Fin d), j.val > 0 -> M s ⟨0, hd⟩ j = 0) :
    ∀ w : List (Fin N),
      evalFinWordVec N d M v w ⟨0, hd⟩ = evalFinParikh N (fun s => v s ⟨0, hd⟩) w
  | [] => rfl
  | s :: rest => by
    simp only [evalFinWordVec, evalFinParikh, natMatVec]
    rw [natSumPrefix_single_fin d
      (fun j => M s ⟨0, hd⟩ j * evalFinWordVec N d M v rest j) ⟨0, hd⟩]
    · rw [h00 s, Nat.one_mul, lowerZeroDiag_wordVec_top N d hd M v h00 h0j rest]
    · intro j hj
      have hj_pos : j.val > 0 := by
        have : j.val ≠ 0 := fun hv => hj (Fin.ext hv); omega
      rw [h0j s j hj_pos, Nat.zero_mul]

def lastFinSym {N : Nat} (dflt : Fin N) : List (Fin N) -> Fin N
  | [] => dflt
  | [s] => s
  | _ :: s2 :: tl => lastFinSym dflt (s2 :: tl)

def lastNatVal (dflt : Nat) : List Nat -> Nat
  | [] => dflt
  | [x] => x
  | _ :: y :: tl => lastNatVal dflt (y :: tl)

private theorem lastFinSym_val_eq {N : Nat} (dflt : Fin N) :
    ∀ w : List (Fin N), (lastFinSym dflt w).val = lastNatVal dflt.val (w.map Fin.val)
  | [] => rfl
  | [_] => rfl
  | _ :: s2 :: tl => lastFinSym_val_eq dflt (s2 :: tl)

private theorem upperZeroDiag_wordMat_lower_zero (N d : Nat)
    (M : Fin N -> Fin d -> Fin d -> Nat)
    (hlow : ∀ (s : Fin N) (i j : Fin d), i.val > 0 -> M s i j = 0) :
    ∀ (s0 : Fin N) (rest : List (Fin N)) (i j : Fin d),
      i.val > 0 -> evalFinWordMat N d M (s0 :: rest) i j = 0 := by
  intro s0 rest i j hi
  simp only [evalFinWordMat, natMatMul]
  exact natSumFin_zero_w12 d _ (fun k => by rw [hlow s0 i k hi, Nat.zero_mul])

private theorem lastFinSym_irrel {N : Nat} (d1 d2 : Fin N) :
    ∀ (a : Fin N) (tl : List (Fin N)),
      lastFinSym d1 (a :: tl) = lastFinSym d2 (a :: tl)
  | _, [] => rfl
  | _, b :: tl => lastFinSym_irrel d1 d2 b tl

private theorem upperZeroDiag_wordMat_top (N d : Nat) (hd : d ≥ 1)
    (M : Fin N -> Fin d -> Fin d -> Nat)
    (h00 : ∀ s : Fin N, M s ⟨0, hd⟩ ⟨0, hd⟩ = 1)
    (hlow : ∀ (s : Fin N) (i j : Fin d), i.val > 0 -> M s i j = 0) :
    ∀ (s0 : Fin N) (rest : List (Fin N)) (j : Fin d),
      evalFinWordMat N d M (s0 :: rest) ⟨0, hd⟩ j =
        M (lastFinSym s0 (s0 :: rest)) ⟨0, hd⟩ j
  | s0, [], j => by
    simp only [evalFinWordMat, natMatMul, lastFinSym]
    rw [natSumPrefix_single_fin d (fun k => M s0 ⟨0, hd⟩ k * natMatId d k j) j]
    · simp [natMatId]
    · intro k hkj
      have hkv : k.val ≠ j.val := fun hv => hkj (Fin.ext hv)
      simp [natMatId, hkv]
  | s0, s1 :: tl, j => by
    change natSumFin d (fun k => M s0 ⟨0, hd⟩ k * evalFinWordMat N d M (s1 :: tl) k j) =
      M (lastFinSym s0 (s1 :: tl)) ⟨0, hd⟩ j
    rw [natSumPrefix_single_fin d
      (fun k => M s0 ⟨0, hd⟩ k * evalFinWordMat N d M (s1 :: tl) k j) ⟨0, hd⟩]
    · rw [h00 s0, Nat.one_mul]
      have ih := upperZeroDiag_wordMat_top N d hd M h00 hlow s1 tl j
      rwa [lastFinSym_irrel s1 s0 s1 tl] at ih
    · intro k hk0
      have hk_pos : k.val > 0 := by
        have : k.val ≠ 0 := fun hv => hk0 (Fin.ext hv); omega
      rw [upperZeroDiag_wordMat_lower_zero N d M hlow s1 tl k j hk_pos, Nat.mul_zero]

private theorem upperZeroDiag_wordVec_lower (N d : Nat)
    (M : Fin N -> Fin d -> Fin d -> Nat) (v : Fin N -> Fin d -> Nat)
    (hlow : ∀ (s : Fin N) (i j : Fin d), i.val > 0 -> M s i j = 0) :
    ∀ (s0 : Fin N) (rest : List (Fin N)) (i : Fin d),
      i.val > 0 -> evalFinWordVec N d M v (s0 :: rest) i = v s0 i := by
  intro s0 rest i hi
  simp only [evalFinWordVec, natMatVec]
  rw [natSumFin_zero_w12 d _ (fun k => by rw [hlow s0 i k hi, Nat.zero_mul]), Nat.add_zero]

def pairWeightFin (N d : Nat) (hd : d ≥ 1)
    (M : Fin N -> Fin d -> Fin d -> Nat) (v : Fin N -> Fin d -> Nat) (x y : Fin N) : Nat :=
  natSumFin d (fun j => if j.val = 0 then 0 else M x ⟨0, hd⟩ j * v y j)

def eval2GramFin (N : Nat) (pw : Fin N -> Fin N -> Nat) : List (Fin N) -> Nat
  | [] => 0
  | [_] => 0
  | a :: b :: tl => pw a b + eval2GramFin N pw (b :: tl)

private theorem upperZeroDiag_wordVec_top (N d : Nat) (hd : d ≥ 1)
    (M : Fin N -> Fin d -> Fin d -> Nat) (v : Fin N -> Fin d -> Nat)
    (h00 : ∀ s : Fin N, M s ⟨0, hd⟩ ⟨0, hd⟩ = 1)
    (hlow : ∀ (s : Fin N) (i j : Fin d), i.val > 0 -> M s i j = 0) :
    ∀ w : List (Fin N),
      evalFinWordVec N d M v w ⟨0, hd⟩ =
        evalFinParikh N (fun s => v s ⟨0, hd⟩) w + eval2GramFin N (pairWeightFin N d hd M v) w
  | [] => rfl
  | [s] => by
    simp only [evalFinWordVec, evalFinParikh, eval2GramFin, natMatVec, Nat.add_zero]
    rw [natSumFin_zero_w12 d _ (fun _ => Nat.mul_zero _), Nat.add_zero]
  | a :: b :: tl => by
    change v a ⟨0, hd⟩ + natSumFin d (fun j => M a ⟨0, hd⟩ j * evalFinWordVec N d M v (b :: tl) j) =
      (v a ⟨0, hd⟩ + evalFinParikh N (fun s => v s ⟨0, hd⟩) (b :: tl)) +
        (pairWeightFin N d hd M v a b + eval2GramFin N (pairWeightFin N d hd M v) (b :: tl))
    rw [natSumFin_split_zero d hd, h00 a, Nat.one_mul,
        upperZeroDiag_wordVec_top N d hd M v h00 hlow (b :: tl)]
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
        | succ m' ih =>
          have hm'_lt : m' < d := hm
          simp only [natSumPrefix, hm'_lt, dite_true, ih (Nat.le_of_lt hm)]
          by_cases hm0 : m' = 0
          · simp [hm0]
          · simp only [hm0, ite_false]
            have hm'_pos : (⟨m', hm'_lt⟩ : Fin d).val > 0 := Nat.pos_of_ne_zero hm0
            rw [upperZeroDiag_wordVec_lower N d M v hlow b tl ⟨m', hm'_lt⟩ hm'_pos]
      exact hcon d (Nat.le_refl d)
    rw [hpw]
    omega

def evalWeightedPairs (N : Nat) (pw : Fin N -> Fin N -> Nat) :
    List (Nat × Nat × Nat) -> Nat
  | [] => 0
  | (x, y, w) :: rest =>
    (if hx : x < N then if hy : y < N then w * pw ⟨x, hx⟩ ⟨y, hy⟩ else 0 else 0) +
      evalWeightedPairs N pw rest

private theorem evalWeightedPairs_append (N : Nat) (pw : Fin N -> Fin N -> Nat) :
    ∀ xs ys : List (Nat × Nat × Nat),
      evalWeightedPairs N pw (xs ++ ys) = evalWeightedPairs N pw xs + evalWeightedPairs N pw ys
  | [], _ => by simp [evalWeightedPairs]
  | _ :: xs, ys => by
    simp only [List.cons_append, evalWeightedPairs, evalWeightedPairs_append N pw xs ys,
               Nat.add_assoc]

def subFromWeightedPairs (x y : Nat) :
    Nat -> List (Nat × Nat × Nat) -> Option (List (Nat × Nat × Nat))
  | 0, ys => some ys
  | _ + 1, [] => none
  | rem + 1, (rx, ry, rw) :: rest =>
    if x = rx ∧ y = ry then
      if rem + 1 ≤ rw then some ((rx, ry, rw - (rem + 1)) :: rest)
      else subFromWeightedPairs x y (rem + 1 - rw) rest
    else
      match subFromWeightedPairs x y (rem + 1) rest with
      | some rest' => some ((rx, ry, rw) :: rest')
      | none => none

private theorem subFromWeightedPairs_sound (N : Nat) (pw : Fin N -> Fin N -> Nat)
    (x y : Nat) :
    ∀ (rem : Nat) (ys ys' : List (Nat × Nat × Nat)),
      subFromWeightedPairs x y rem ys = some ys' ->
      (if hx : x < N then if hy : y < N then rem * pw ⟨x, hx⟩ ⟨y, hy⟩ else 0 else 0) +
        evalWeightedPairs N pw ys' = evalWeightedPairs N pw ys
  | 0, ys, ys', h => by
    simp [subFromWeightedPairs] at h; subst h; simp
  | rem + 1, [], _, h => by cases h
  | rem + 1, (rx, ry, rw) :: rest, ys', h => by
    unfold subFromWeightedPairs at h
    by_cases heq : x = rx ∧ y = ry
    · rcases heq with ⟨rfl, rfl⟩
      simp only [and_self, ite_true] at h
      by_cases hle : rem + 1 ≤ rw
      · simp only [hle, ite_true, Option.some.injEq] at h
        subst h
        simp only [evalWeightedPairs]
        by_cases hx : x < N
        · by_cases hy : y < N
          · simp only [hx, hy, dite_true, ← Nat.add_assoc, ← Nat.add_mul]
            rw [show rem + 1 + (rw - (rem + 1)) = rw by omega]
          · simp [hx, hy]
        · simp [hx]
      · simp only [hle, ite_false] at h
        have ih := subFromWeightedPairs_sound N pw x y (rem + 1 - rw) rest ys' h
        simp only [evalWeightedPairs]
        rw [← ih]
        by_cases hx : x < N
        · by_cases hy : y < N
          · simp only [hx, hy, dite_true, ← Nat.add_assoc, ← Nat.add_mul]
            rw [show rw + (rem + 1 - rw) = rem + 1 by omega]
          · simp [hx, hy]
        · simp [hx]
    · simp only [heq, ite_false] at h
      cases hsub : subFromWeightedPairs x y (rem + 1) rest with
      | none => rw [hsub] at h; cases h
      | some rest' =>
        rw [hsub] at h
        simp only [Option.some.injEq] at h
        subst h
        have ih := subFromWeightedPairs_sound N pw x y (rem + 1) rest rest' hsub
        simp only [evalWeightedPairs]
        rw [← ih]
        omega

def cancelAllWeightedPairs : List (Nat × Nat × Nat) -> List (Nat × Nat × Nat) -> Bool
  | [], _ => true
  | (x, y, w) :: xs, ys =>
    match subFromWeightedPairs x y w ys with
    | some ys' => cancelAllWeightedPairs xs ys'
    | none => false

private theorem cancelAllWeightedPairs_sound (N : Nat) (pw : Fin N -> Fin N -> Nat) :
    ∀ (xs ys : List (Nat × Nat × Nat)),
      cancelAllWeightedPairs xs ys = true ->
      evalWeightedPairs N pw xs ≤ evalWeightedPairs N pw ys
  | [], _, _ => Nat.zero_le _
  | (x, y, w) :: xs, ys, hb => by
    unfold cancelAllWeightedPairs at hb
    cases hsub : subFromWeightedPairs x y w ys with
    | none => rw [hsub] at hb; cases hb
    | some ys' =>
      rw [hsub] at hb
      have heq := subFromWeightedPairs_sound N pw x y w ys ys' hsub
      have hle := cancelAllWeightedPairs_sound N pw xs ys' hb
      simp only [evalWeightedPairs]
      rw [← heq]
      exact Nat.add_le_add_left hle _

def word2GramItems (m : Nat) : List Nat -> List (Nat × Nat × Nat)
  | [] => []
  | [_] => []
  | x :: y :: tl => (x, y, m) :: word2GramItems m (y :: tl)

private theorem evalWeightedPairs_word2GramItems (N : Nat) (pw : Fin N -> Fin N -> Nat)
    (m : Nat) :
    ∀ u : List (Fin N),
      evalWeightedPairs N pw (word2GramItems m (u.map Fin.val)) = m * eval2GramFin N pw u
  | [] => by simp [word2GramItems, evalWeightedPairs, eval2GramFin]
  | [_] => by simp [word2GramItems, evalWeightedPairs, eval2GramFin]
  | a :: b :: tl => by
    have ih := evalWeightedPairs_word2GramItems N pw m (b :: tl)
    simp only [List.map_cons] at ih ⊢
    simp only [word2GramItems, evalWeightedPairs, eval2GramFin,
               a.isLt, b.isLt, dite_true, ih, Nat.mul_add]

def weighted2GramLhs (N : Nat) (pw : Fin N -> Fin N -> Nat) :
    List (List (Fin N) × List (Fin N)) -> List Nat -> Nat
  | [], _ => 0
  | _, [] => 0
  | r :: rs, m :: ms => m * eval2GramFin N pw r.1 + weighted2GramLhs N pw rs ms

def weighted2GramRhs (N : Nat) (pw : Fin N -> Fin N -> Nat) :
    List (List (Fin N) × List (Fin N)) -> List Nat -> Nat
  | [], _ => 0
  | _, [] => 0
  | r :: rs, m :: ms => m * eval2GramFin N pw r.2 + weighted2GramRhs N pw rs ms

def rulesLhs2GramItems {N : Nat} :
    List (List (Fin N) × List (Fin N)) -> List Nat -> List (Nat × Nat × Nat)
  | [], _ => []
  | _, [] => []
  | r :: rs, m :: ms => word2GramItems m (r.1.map Fin.val) ++ rulesLhs2GramItems rs ms

def rulesRhs2GramItems {N : Nat} :
    List (List (Fin N) × List (Fin N)) -> List Nat -> List (Nat × Nat × Nat)
  | [], _ => []
  | _, [] => []
  | r :: rs, m :: ms => word2GramItems m (r.2.map Fin.val) ++ rulesRhs2GramItems rs ms

private theorem evalWeightedPairs_rules2Gram (N : Nat) (pw : Fin N -> Fin N -> Nat) :
    ∀ (rules : List (List (Fin N) × List (Fin N))) (syz : List Nat),
      evalWeightedPairs N pw (rulesLhs2GramItems rules syz) = weighted2GramLhs N pw rules syz ∧
      evalWeightedPairs N pw (rulesRhs2GramItems rules syz) = weighted2GramRhs N pw rules syz
  | [], _ => ⟨rfl, rfl⟩
  | _ :: _, [] => ⟨rfl, rfl⟩
  | r :: rs, m :: ms => by
    rcases evalWeightedPairs_rules2Gram N pw rs ms with ⟨hl, hr⟩
    refine ⟨?_, ?_⟩
    · simp only [rulesLhs2GramItems, weighted2GramLhs, evalWeightedPairs_append,
                 evalWeightedPairs_word2GramItems, hl]
    · simp only [rulesRhs2GramItems, weighted2GramRhs, evalWeightedPairs_append,
                 evalWeightedPairs_word2GramItems, hr]

def flowSrcItems : List (Nat × Nat × Nat × Nat × Nat) -> List (Nat × Nat × Nat)
  | [] => []
  | (x1, y1, _, _, fw) :: rest => (x1, y1, fw) :: flowSrcItems rest

def flowDstItems : List (Nat × Nat × Nat × Nat × Nat) -> List (Nat × Nat × Nat)
  | [] => []
  | (_, _, x2, y2, fw) :: rest => (x2, y2, fw) :: flowDstItems rest

def hasLastRulePairBool {N : Nat} (a b : Nat) :
    List (List (Fin N) × List (Fin N)) -> Bool
  | [] => false
  | r :: rs =>
    (match r.1, r.2 with
     | l0 :: ltl, r0 :: rtl =>
       decide (lastNatVal l0.val ((l0 :: ltl).map Fin.val) = a ∧
               lastNatVal r0.val ((r0 :: rtl).map Fin.val) = b)
     | _, _ => false) || hasLastRulePairBool a b rs

def hasFirstRulePairBool {N : Nat} (a b : Nat) :
    List (List (Fin N) × List (Fin N)) -> Bool
  | [] => false
  | r :: rs =>
    (match r.1, r.2 with
     | l0 :: _, r0 :: _ => decide (l0.val = a ∧ r0.val = b)
     | _, _ => false) || hasFirstRulePairBool a b rs

private theorem hasLastRulePairBool_dom (N d : Nat) (hd : d ≥ 1)
    (M : Fin N -> Fin d -> Fin d -> Nat)
    (h00 : ∀ s : Fin N, M s ⟨0, hd⟩ ⟨0, hd⟩ = 1)
    (hlow : ∀ (s : Fin N) (i j : Fin d), i.val > 0 -> M s i j = 0)
    (x2 x1 : Fin N) :
    ∀ (rules : List (List (Fin N) × List (Fin N))),
      (∀ r ∈ rules, ∀ i j : Fin d, evalFinWordMat N d M r.1 i j ≥ evalFinWordMat N d M r.2 i j) ->
      hasLastRulePairBool x2.val x1.val rules = true ->
      ∀ j : Fin d, M x2 ⟨0, hd⟩ j ≥ M x1 ⟨0, hd⟩ j
  | [], _, hb => by cases hb
  | r :: rs, hweak, hb => by
    unfold hasLastRulePairBool at hb
    rcases bool_or_split hb with h0 | htl
    · cases hl : r.1 with
      | nil => rw [hl] at h0; cases h0
      | cons l0 ltl =>
        cases hr : r.2 with
        | nil => rw [hl, hr] at h0; cases h0
        | cons r0 rtl =>
          rw [hl, hr] at h0
          rcases of_decide_eq_true h0 with ⟨ha, hb_e⟩
          have hx2 : lastFinSym l0 (l0 :: ltl) = x2 :=
            Fin.ext ((lastFinSym_val_eq l0 (l0 :: ltl)).trans ha)
          have hx1 : lastFinSym r0 (r0 :: rtl) = x1 :=
            Fin.ext ((lastFinSym_val_eq r0 (r0 :: rtl)).trans hb_e)
          intro j
          have hm := hweak r List.mem_cons_self ⟨0, hd⟩ j
          rw [hl, hr,
              upperZeroDiag_wordMat_top N d hd M h00 hlow l0 ltl j,
              upperZeroDiag_wordMat_top N d hd M h00 hlow r0 rtl j,
              hx2, hx1] at hm
          exact hm
    · exact hasLastRulePairBool_dom N d hd M h00 hlow x2 x1 rs
        (fun q hq => hweak q (List.mem_cons_of_mem r hq)) htl

private theorem hasFirstRulePairBool_dom (N d : Nat)
    (M : Fin N -> Fin d -> Fin d -> Nat) (v : Fin N -> Fin d -> Nat)
    (hlow : ∀ (s : Fin N) (i j : Fin d), i.val > 0 -> M s i j = 0)
    (y2 y1 : Fin N) :
    ∀ (rules : List (List (Fin N) × List (Fin N))),
      (∀ r ∈ rules, ∀ i : Fin d, evalFinWordVec N d M v r.1 i ≥ evalFinWordVec N d M v r.2 i) ->
      hasFirstRulePairBool y2.val y1.val rules = true ->
      ∀ j : Fin d, j.val > 0 -> v y2 j ≥ v y1 j
  | [], _, hb => by cases hb
  | r :: rs, hweak, hb => by
    unfold hasFirstRulePairBool at hb
    rcases bool_or_split hb with h0 | htl
    · cases hl : r.1 with
      | nil => rw [hl] at h0; cases h0
      | cons l0 ltl =>
        cases hr : r.2 with
        | nil => rw [hl, hr] at h0; cases h0
        | cons r0 rtl =>
          rw [hl, hr] at h0
          rcases of_decide_eq_true h0 with ⟨ha, hb_e⟩
          have hy2 : l0 = y2 := Fin.ext ha
          have hy1 : r0 = y1 := Fin.ext hb_e
          intro j hj
          have hv := hweak r List.mem_cons_self j
          rw [hl, hr,
              upperZeroDiag_wordVec_lower N d M v hlow l0 ltl j hj,
              upperZeroDiag_wordVec_lower N d M v hlow r0 rtl j hj,
              hy2, hy1] at hv
          exact hv
    · exact hasFirstRulePairBool_dom N d M v hlow y2 y1 rs
        (fun q hq => hweak q (List.mem_cons_of_mem r hq)) htl

def checkFlowEdgesDomBool (N : Nat) (rules : List (List (Fin N) × List (Fin N))) :
    List (Nat × Nat × Nat × Nat × Nat) -> Bool
  | [] => true
  | (x1, y1, x2, y2, _) :: rest =>
    decide (x1 < N ∧ y1 < N ∧ x2 < N ∧ y2 < N) &&
    (decide (x1 = x2) || hasLastRulePairBool x2 x1 rules) &&
    (decide (y1 = y2) || hasFirstRulePairBool y2 y1 rules) &&
    checkFlowEdgesDomBool N rules rest

private theorem checkFlowEdgesDomBool_sound (N d : Nat) (hd : d ≥ 1)
    (M : Fin N -> Fin d -> Fin d -> Nat) (v : Fin N -> Fin d -> Nat)
    (h00 : ∀ s : Fin N, M s ⟨0, hd⟩ ⟨0, hd⟩ = 1)
    (hlow : ∀ (s : Fin N) (i j : Fin d), i.val > 0 -> M s i j = 0)
    (rules : List (List (Fin N) × List (Fin N)))
    (hweak : ∀ r ∈ rules,
      (∀ i j : Fin d, evalFinWordMat N d M r.1 i j ≥ evalFinWordMat N d M r.2 i j) ∧
      (∀ i : Fin d, evalFinWordVec N d M v r.1 i ≥ evalFinWordVec N d M v r.2 i)) :
    ∀ flow : List (Nat × Nat × Nat × Nat × Nat),
      checkFlowEdgesDomBool N rules flow = true ->
      evalWeightedPairs N (pairWeightFin N d hd M v) (flowSrcItems flow) ≤
        evalWeightedPairs N (pairWeightFin N d hd M v) (flowDstItems flow)
  | [], _ => Nat.le_refl 0
  | (x1, y1, x2, y2, fw) :: rest, hb => by
    unfold checkFlowEdgesDomBool at hb
    rcases bool_and_split hb with ⟨hb1, hrest⟩
    rcases bool_and_split hb1 with ⟨hb2, hy_dom⟩
    rcases bool_and_split hb2 with ⟨hbnd, hx_dom⟩
    rcases of_decide_eq_true hbnd with ⟨hx1, hy1, hx2, hy2⟩
    have hx_le : ∀ j : Fin d, M ⟨x1, hx1⟩ ⟨0, hd⟩ j ≤ M ⟨x2, hx2⟩ ⟨0, hd⟩ j := by
      rcases bool_or_split hx_dom with heq | hrl
      · have hf : (⟨x1, hx1⟩ : Fin N) = ⟨x2, hx2⟩ := Fin.ext (of_decide_eq_true heq)
        intro j; rw [hf]; exact Nat.le_refl _
      · exact hasLastRulePairBool_dom N d hd M h00 hlow ⟨x2, hx2⟩ ⟨x1, hx1⟩ rules
          (fun r hr => (hweak r hr).1) hrl
    have hy_le : ∀ j : Fin d, j.val > 0 -> v ⟨y1, hy1⟩ j ≤ v ⟨y2, hy2⟩ j := by
      rcases bool_or_split hy_dom with heq | hrf
      · have hf : (⟨y1, hy1⟩ : Fin N) = ⟨y2, hy2⟩ := Fin.ext (of_decide_eq_true heq)
        intro j _; rw [hf]; exact Nat.le_refl _
      · exact hasFirstRulePairBool_dom N d M v hlow ⟨y2, hy2⟩ ⟨y1, hy1⟩ rules
          (fun r hr => (hweak r hr).2) hrf
    have hpw_le : pairWeightFin N d hd M v ⟨x1, hx1⟩ ⟨y1, hy1⟩ ≤
        pairWeightFin N d hd M v ⟨x2, hx2⟩ ⟨y2, hy2⟩ := by
      unfold pairWeightFin natSumFin
      exact natSumPrefix_mono_w5 d _ _ (fun j => by
        by_cases hj0 : j.val = 0
        · simp [hj0]
        · simp only [hj0, ite_false]
          exact Nat.mul_le_mul (hx_le j) (hy_le j (by omega))) d
    have ih := checkFlowEdgesDomBool_sound N d hd M v h00 hlow rules hweak rest hrest
    simp only [flowSrcItems, flowDstItems, evalWeightedPairs, hx1, hy1, hx2, hy2, dite_true]
    exact Nat.add_le_add (Nat.mul_le_mul_left fw hpw_le) ih

def checkZeroDiag2GramCertBool (N : Nat)
    (rules : List (List (Fin N) × List (Fin N)))
    (syz : List Nat)
    (flow : List (Nat × Nat × Nat × Nat × Nat)) : Bool :=
  checkPositiveParikhSyzygyFastBool N rules syz &&
  checkFlowEdgesDomBool N rules flow &&
  cancelAllWeightedPairs
    (rulesLhs2GramItems rules syz ++ flowDstItems flow)
    (rulesRhs2GramItems rules syz ++ flowSrcItems flow)

private def weightedRuleFnLhs {N : Nat} (f : List (Fin N) -> Nat) :
    List (List (Fin N) × List (Fin N)) -> List Nat -> Nat
  | [], _ => 0
  | _, [] => 0
  | r :: rs, m :: ms => m * f r.1 + weightedRuleFnLhs f rs ms

private def weightedRuleFnRhs {N : Nat} (f : List (Fin N) -> Nat) :
    List (List (Fin N) × List (Fin N)) -> List Nat -> Nat
  | [], _ => 0
  | _, [] => 0
  | r :: rs, m :: ms => m * f r.2 + weightedRuleFnRhs f rs ms

private theorem weightedRuleFn_parikh_add_2gram (N : Nat)
    (wt : Fin N -> Nat) (pw : Fin N -> Fin N -> Nat) :
    ∀ (rules : List (List (Fin N) × List (Fin N))) (syz : List Nat),
      weightedRuleFnLhs (fun w => evalFinParikh N wt w + eval2GramFin N pw w) rules syz =
        weightedParikhLhs N wt rules syz + weighted2GramLhs N pw rules syz ∧
      weightedRuleFnRhs (fun w => evalFinParikh N wt w + eval2GramFin N pw w) rules syz =
        weightedParikhRhs N wt rules syz + weighted2GramRhs N pw rules syz
  | [], _ => ⟨rfl, rfl⟩
  | _ :: _, [] => ⟨rfl, rfl⟩
  | r :: rs, m :: ms => by
    rcases weightedRuleFn_parikh_add_2gram N wt pw rs ms with ⟨hl, hr⟩
    refine ⟨?_, ?_⟩
    · simp only [weightedRuleFnLhs, weightedParikhLhs, weighted2GramLhs, Nat.mul_add, hl]
      omega
    · simp only [weightedRuleFnRhs, weightedParikhRhs, weighted2GramRhs, Nat.mul_add, hr]
      omega

private theorem weightedRuleFn_forces_all_eq {N : Nat} (f : List (Fin N) -> Nat) :
    ∀ (rules : List (List (Fin N) × List (Fin N))) (syz : List Nat),
      rules.length = syz.length ->
      checkAllPosNatList syz = true ->
      (∀ r ∈ rules, f r.1 ≥ f r.2) ->
      weightedRuleFnLhs f rules syz ≤ weightedRuleFnRhs f rules syz ->
      ∀ r ∈ rules, f r.1 = f r.2
  | [], _, _, _, _, _, _, hr => by cases hr
  | _ :: _, [], hl, _, _, _, _, _ => by simp at hl
  | r0 :: rs, m0 :: ms, hl, hpos, hweak, htot_le, r, hmem => by
    rcases bool_and_split hpos with ⟨hm0_b, hms_pos⟩
    have hm0 : m0 ≥ 1 := of_decide_eq_true hm0_b
    have hge_rs : weightedRuleFnLhs f rs ms ≥ weightedRuleFnRhs f rs ms := by
      have hrec : ∀ (qs : List (List (Fin N) × List (Fin N))) (us : List Nat),
          (∀ q ∈ qs, f q.1 ≥ f q.2) ->
          weightedRuleFnLhs f qs us ≥ weightedRuleFnRhs f qs us := by
        intro qs; induction qs with
        | nil => intro _ _; simp [weightedRuleFnLhs, weightedRuleFnRhs]
        | cons q0 qt ih =>
          intro us hw; cases us with
          | nil => simp [weightedRuleFnLhs, weightedRuleFnRhs]
          | cons u0 ut =>
            simp only [weightedRuleFnLhs, weightedRuleFnRhs]
            exact Nat.add_le_add
              (Nat.mul_le_mul_left u0 (hw q0 List.mem_cons_self))
              (ih ut (fun q hq => hw q (List.mem_cons_of_mem q0 hq)))
      exact hrec rs ms (fun q hq => hweak q (List.mem_cons_of_mem r0 hq))
    have hw0 := hweak r0 List.mem_cons_self
    simp only [weightedRuleFnLhs, weightedRuleFnRhs] at htot_le
    cases hmem with
    | head =>
      by_cases heq0 : f r0.1 = f r0.2
      · exact heq0
      · exfalso
        have hlt : m0 * f r0.2 < m0 * f r0.1 :=
          Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
        omega
    | tail _ htl =>
      have hm0_ge : m0 * f r0.1 ≥ m0 * f r0.2 := Nat.mul_le_mul_left m0 hw0
      exact weightedRuleFn_forces_all_eq f rs ms (by simp at hl; omega) hms_pos
        (fun q hq => hweak q (List.mem_cons_of_mem r0 hq)) (by omega) r htl

private theorem checkZeroDiag2GramCertBool_sound (N d : Nat) (hd : d ≥ 1)
    (rules : List (List (Fin N) × List (Fin N)))
    (syz : List Nat)
    (flow : List (Nat × Nat × Nat × Nat × Nat))
    (hcert : checkZeroDiag2GramCertBool N rules syz flow = true)
    (M : Fin N -> Fin d -> Fin d -> Nat) (v : Fin N -> Fin d -> Nat)
    (h00 : ∀ s : Fin N, M s ⟨0, hd⟩ ⟨0, hd⟩ = 1)
    (hlow : ∀ (s : Fin N) (i j : Fin d), i.val > 0 -> M s i j = 0)
    (hweak : ∀ r ∈ rules,
      (∀ i j : Fin d, evalFinWordMat N d M r.1 i j ≥ evalFinWordMat N d M r.2 i j) ∧
      (∀ i : Fin d, evalFinWordVec N d M v r.1 i ≥ evalFinWordVec N d M v r.2 i)) :
    ∀ r ∈ rules, evalFinWordVec N d M v r.1 ⟨0, hd⟩ = evalFinWordVec N d M v r.2 ⟨0, hd⟩ := by
  unfold checkZeroDiag2GramCertBool at hcert
  rcases bool_and_split hcert with ⟨hc1, hcan⟩
  rcases bool_and_split hc1 with ⟨hsyz, hflow⟩
  have hsyz_raw := hsyz
  unfold checkPositiveParikhSyzygyFastBool at hsyz_raw
  rcases bool_and_split hsyz_raw with ⟨hb1, hpairs⟩
  rcases bool_and_split hb1 with ⟨hb2, hpos_m⟩
  rcases bool_and_split hb2 with ⟨_, hlen_eq⟩
  have hlen : rules.length = syz.length := of_decide_eq_true hlen_eq
  rcases accumSymCountsW11_spec N rules syz with ⟨hacc_len, hacc_get⟩
  let wt : Fin N -> Nat := fun s => v s ⟨0, hd⟩
  let pw : Fin N -> Fin N -> Nat := pairWeightFin N d hd M v
  rcases weightedParikh_eq_sum_sym N wt rules syz with ⟨hl_sum, hr_sum⟩
  have hpar_le : weightedParikhLhs N wt rules syz ≤ weightedParikhRhs N wt rules syz := by
    rw [hl_sum, hr_sum]
    exact natSumPrefix_mono_w5 N _ _ (fun s => Nat.mul_le_mul_left (wt s) (by
      have hle := checkPairsLeBoolW11_sound _ hpairs s.val (by rw [hacc_len]; exact s.isLt)
      rwa [hacc_get s] at hle)) N
  have hflow_le := checkFlowEdgesDomBool_sound N d hd M v h00 hlow rules hweak flow hflow
  change evalWeightedPairs N pw (flowSrcItems flow) ≤
    evalWeightedPairs N pw (flowDstItems flow) at hflow_le
  have hcan_le := cancelAllWeightedPairs_sound N pw _ _ hcan
  rw [evalWeightedPairs_append, evalWeightedPairs_append] at hcan_le
  rcases evalWeightedPairs_rules2Gram N pw rules syz with ⟨hl2, hr2⟩
  rw [hl2, hr2] at hcan_le
  have h2g_le : weighted2GramLhs N pw rules syz ≤ weighted2GramRhs N pw rules syz := by omega
  let fTop : List (Fin N) -> Nat := fun w => evalFinParikh N wt w + eval2GramFin N pw w
  rcases weightedRuleFn_parikh_add_2gram N wt pw rules syz with ⟨hfl, hfr⟩
  have htot_le : weightedRuleFnLhs fTop rules syz ≤ weightedRuleFnRhs fTop rules syz := by
    rw [hfl, hfr]; exact Nat.add_le_add hpar_le h2g_le
  have hf_eq := weightedRuleFn_forces_all_eq fTop rules syz hlen hpos_m
    (fun r hr => by
      dsimp only [fTop, wt, pw]
      rw [← upperZeroDiag_wordVec_top N d hd M v h00 hlow r.1,
          ← upperZeroDiag_wordVec_top N d hd M v h00 hlow r.2]
      exact (hweak r hr).2 ⟨0, hd⟩)
    htot_le
  intro r hr
  rw [upperZeroDiag_wordVec_top N d hd M v h00 hlow r.1,
      upperZeroDiag_wordVec_top N d hd M v h00 hlow r.2]
  exact hf_eq r hr

def syzC39ZeroDiag2Gram : List Nat :=
  [1, 2, 1, 2, 26, 1, 1, 1, 17, 25, 17, 22, 15, 5, 12, 2, 25, 2, 22, 25,
   12, 12, 14, 14, 1, 15, 1, 2, 2, 8, 2, 2, 1, 1, 1, 7, 1, 1, 1]

def flowC39ZeroDiag2Gram : List (Nat × Nat × Nat × Nat × Nat) :=
  [ (1, 14, 13, 31, 1), (1, 18, 13, 31, 1), (2, 13, 2, 38, 1), (2, 13, 14, 13, 1),
    (2, 20, 2, 36, 1), (2, 20, 2, 38, 25), (4, 14, 13, 31, 1), (4, 18, 13, 31, 1),
    (5, 13, 5, 38, 1), (5, 13, 14, 13, 1), (5, 20, 5, 36, 1), (28, 6, 13, 6, 1),
    (28, 6, 16, 6, 7), (28, 7, 13, 7, 2), (28, 8, 13, 8, 2), (28, 18, 13, 31, 18),
    (28, 18, 13, 32, 2), (28, 18, 16, 31, 5), (29, 20, 14, 36, 12), (29, 20, 14, 38, 5),
    (31, 6, 16, 6, 1), (31, 7, 16, 7, 2), (31, 8, 16, 8, 2), (31, 14, 16, 31, 7),
    (31, 14, 16, 32, 10), (31, 18, 16, 32, 12), (32, 13, 17, 37, 22), (32, 20, 17, 37, 3),
    (32, 20, 17, 38, 2), (33, 22, 18, 28, 22), (33, 22, 18, 29, 3), (35, 16, 20, 16, 9),
    (35, 16, 20, 40, 6), (35, 23, 20, 39, 2), (36, 22, 18, 29, 14), (37, 9, 22, 9, 7),
    (37, 10, 22, 10, 1), (37, 11, 22, 11, 1), (37, 17, 22, 33, 2), (37, 21, 22, 35, 14),
    (38, 16, 20, 40, 8), (38, 16, 20, 41, 12), (38, 16, 23, 16, 2), (38, 23, 20, 39, 12),
    (39, 22, 21, 28, 15), (40, 9, 22, 9, 1), (40, 10, 22, 10, 1), (40, 11, 22, 11, 1),
    (40, 17, 22, 33, 23), (40, 17, 22, 35, 2), (40, 21, 22, 35, 1), (41, 16, 23, 16, 1),
    (41, 16, 23, 40, 11), (41, 23, 23, 39, 1) ]

def syzC78ZeroDiag2Gram : List Nat :=
  [1, 2, 1, 2, 1, 2, 1, 2, 63, 1, 2, 1, 1, 1, 2, 1, 7, 10, 32, 1,
   39, 1, 3, 7, 2, 30, 8, 33, 1, 1, 1, 2, 6, 8, 1, 5, 1, 4, 8, 37,
   7, 36, 44, 1, 1, 29, 34, 1, 41, 14, 29, 44, 16, 1, 2, 2, 2, 2, 2, 16,
   1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 15]

def flowC78ZeroDiag2Gram : List (Nat × Nat × Nat × Nat × Nat) :=
  [ (1, 36, 25, 62, 1), (1, 39, 25, 64, 1), (2, 25, 2, 74, 1), (2, 25, 26, 25, 1),
    (2, 28, 2, 74, 1), (2, 28, 26, 74, 1), (4, 26, 28, 61, 1), (4, 29, 28, 61, 1),
    (5, 38, 5, 75, 1), (5, 38, 5, 77, 1), (5, 41, 5, 77, 62), (5, 41, 29, 75, 1),
    (7, 36, 25, 64, 1), (7, 39, 25, 64, 1), (8, 25, 26, 25, 2), (8, 28, 8, 74, 2),
    (10, 26, 28, 61, 1), (10, 29, 28, 61, 1), (11, 38, 11, 75, 1), (11, 38, 11, 77, 1),
    (11, 41, 29, 75, 1), (55, 12, 25, 12, 1), (55, 12, 31, 12, 15), (55, 13, 25, 13, 1),
    (55, 13, 31, 13, 1), (55, 14, 25, 14, 1), (55, 14, 31, 14, 1), (55, 15, 25, 15, 1),
    (55, 15, 31, 15, 1), (55, 16, 25, 16, 1), (55, 16, 31, 16, 1), (55, 17, 25, 17, 1),
    (55, 17, 31, 17, 1), (55, 36, 25, 64, 1), (55, 39, 25, 64, 1), (55, 39, 31, 62, 7),
    (55, 39, 31, 64, 2), (59, 38, 29, 75, 31), (59, 38, 29, 77, 1), (59, 41, 29, 77, 7),
    (61, 12, 31, 12, 1), (61, 13, 31, 13, 1), (61, 14, 31, 14, 1), (61, 15, 31, 15, 1),
    (61, 16, 31, 16, 1), (61, 17, 31, 17, 1), (61, 36, 31, 64, 1), (61, 39, 31, 64, 33),
    (62, 25, 32, 74, 6), (62, 25, 32, 76, 1), (62, 28, 32, 76, 1), (64, 26, 34, 61, 3),
    (64, 29, 34, 61, 33), (64, 29, 34, 65, 6), (65, 38, 35, 73, 1), (65, 41, 35, 73, 7),
    (65, 41, 35, 77, 1), (68, 31, 38, 31, 6), (68, 31, 38, 80, 24), (68, 34, 38, 80, 2),
    (69, 43, 39, 55, 7), (69, 43, 39, 59, 1), (69, 46, 39, 59, 2), (71, 44, 41, 79, 6),
    (71, 47, 41, 79, 1), (73, 18, 43, 18, 1), (73, 19, 43, 19, 1), (73, 20, 43, 20, 1),
    (73, 21, 43, 21, 1), (73, 22, 43, 22, 1), (73, 23, 43, 23, 1), (73, 42, 43, 68, 1),
    (73, 45, 43, 68, 1), (74, 31, 38, 80, 3), (74, 31, 38, 82, 1), (74, 34, 44, 80, 5),
    (75, 43, 39, 59, 34), (75, 46, 39, 59, 1), (76, 32, 46, 69, 1), (76, 35, 46, 69, 1),
    (77, 44, 41, 79, 27), (77, 44, 41, 81, 1), (77, 44, 41, 83, 1), (77, 47, 41, 83, 43),
    (77, 47, 47, 79, 1), (79, 18, 43, 18, 15), (79, 19, 43, 19, 1), (79, 20, 43, 20, 1),
    (79, 21, 43, 21, 1), (79, 22, 43, 22, 1), (79, 23, 43, 23, 1), (79, 42, 43, 68, 1),
    (79, 45, 43, 68, 29), (80, 31, 44, 31, 20), (80, 31, 44, 80, 16), (80, 34, 44, 80, 23),
    (80, 34, 44, 82, 14), (81, 43, 45, 55, 16), (81, 46, 45, 55, 14), (82, 32, 46, 69, 7),
    (82, 35, 46, 69, 1), (82, 35, 46, 71, 7), (83, 44, 47, 79, 15), (83, 44, 47, 81, 29),
    (83, 47, 47, 83, 41) ]

set_option maxRecDepth 65536 in
private theorem zero_diag_2gram_certs_ok :
    let c39 := filterFinParikhUnoriented 42 wtTwoSidedMod3OmitR3
      (twoSidedLabelledCollatzRules 3 (by decide) all11OmitR3List)
    let c78 := filterFinParikhUnoriented 84 wtTwoSidedMod6OmitR3
      (twoSidedLabelledCollatzRules 6 (by decide) all11OmitR3List)
    checkZeroDiag2GramCertBool 42 c39 syzC39ZeroDiag2Gram flowC39ZeroDiag2Gram = true ∧
    checkZeroDiag2GramCertBool 84 c78 syzC78ZeroDiag2Gram flowC78ZeroDiag2Gram = true := by decide

/--
  Theorem W12.1b' (`twosided_c39_c78_zero_diag_non_unitriangular_impossibility`,
  `zero custom axioms`):
  Universal `∀ d ≥ 1` Collapse of Non-Unitriangular Zero-Diagonal (`2`-Gram Row-Memory &
  Column-Memory) `ω^k` Hofbauer–Waldmann Matrix Towers on `c39` & `c78` (`Branch P4.3`, `W12_H2`):
  1. **Genuine `d = 2` Non-Commutativity (`M_A * M_B ≠ M_B * M_A`)**:
     Zero-diagonal matrices `A = [[1, 1], [0, 0]]` and `B = [[1, 0], [0, 0]]` satisfy
     `(A * B) 0 1 = 0 ≠ 1 = (B * A) 0 1`!
  2. **All-Dimension `ω^k` Collapse on `c39` and `c78` (`∀ d ≥ 1, ∀ k : Nat`)**:
     - `¬ GenOmegaLowerZeroDiagMatTower 42 d hd k c39 ∧ ¬ GenOmegaLowerZeroDiagMatTower 84 d hd k c78`
       (non-triangular column-memory `M_s = [[1, 0], [c_s, 0]]`), AND
     - `¬ GenOmegaUpperZeroDiagMatTower 42 d hd k c39 ∧ ¬ GenOmegaUpperZeroDiagMatTower 84 d hd k c78`
       (non-unitriangular `d`-dimensional `2`-gram KBO `M_s = [[1, b_s^T], [0, 0]]`, refuted via
       exact bilinear dominance flow certificates of `54` edges on `c39` and `105` edges on `c78`)!
-/
theorem twosided_c39_c78_zero_diag_non_unitriangular_impossibility :
    let c39 := filterFinParikhUnoriented 42 wtTwoSidedMod3OmitR3
      (twoSidedLabelledCollatzRules 3 (by decide) all11OmitR3List)
    let c78 := filterFinParikhUnoriented 84 wtTwoSidedMod6OmitR3
      (twoSidedLabelledCollatzRules 6 (by decide) all11OmitR3List)
    let zA : Fin 2 -> Fin 2 -> Nat := fun i _ => if i.val = 0 then 1 else 0
    let zB : Fin 2 -> Fin 2 -> Nat := fun i j => if i.val = 0 ∧ j.val = 0 then 1 else 0
    (natMatMul 2 zA zB ⟨0, by decide⟩ ⟨1, by decide⟩ = 0 ∧
     natMatMul 2 zB zA ⟨0, by decide⟩ ⟨1, by decide⟩ = 1) ∧
    (∀ (d : Nat) (hd : d ≥ 1) (k : Nat),
      ¬ GenOmegaLowerZeroDiagMatTower 42 d hd k c39 ∧
      ¬ GenOmegaLowerZeroDiagMatTower 84 d hd k c78) ∧
    (∀ (d : Nat) (hd : d ≥ 1) (k : Nat),
      ¬ GenOmegaUpperZeroDiagMatTower 42 d hd k c39 ∧
      ¬ GenOmegaUpperZeroDiagMatTower 84 d hd k c78) := by
  let c39 := filterFinParikhUnoriented 42 wtTwoSidedMod3OmitR3
    (twoSidedLabelledCollatzRules 3 (by decide) all11OmitR3List)
  let c78 := filterFinParikhUnoriented 84 wtTwoSidedMod6OmitR3
    (twoSidedLabelledCollatzRules 6 (by decide) all11OmitR3List)
  rcases c39_certs_ok with ⟨hsyz3, _, _, hne3, _, _, _, _, _⟩
  rcases c78_certs_ok_a with ⟨hsyz6, _, _, hne6⟩
  rcases zero_diag_2gram_certs_ok with ⟨hz3, hz6⟩
  have hlow_imp : ∀ (N : Nat) (core : List (List (Fin N) × List (Fin N))) (syz : List Nat),
      checkPositiveParikhSyzygyFastBool N core syz = true ->
      core ≠ [] ->
      ∀ (d : Nat) (hd : d ≥ 1) (k : Nat), ¬ GenOmegaLowerZeroDiagMatTower N d hd k core := by
    intro N core syz hsyz hne d hd
    rcases syzygy_forces_parikh_and_prod_eq N core syz hsyz with ⟨hpar_eq, _⟩
    cases hcore : core with
    | nil => exact False.elim (hne hcore)
    | cons r0 rs =>
      rw [← hcore]
      have hmem0 : r0 ∈ core := hcore ▸ List.Mem.head _
      have himp : ∀ (k : Nat) (cur : List (List (Fin N) × List (Fin N))),
          (∀ r ∈ core, r ∈ cur) -> ¬ GenOmegaLowerZeroDiagMatTower N d hd k cur := by
        intro k; induction k with
        | zero =>
          intro cur hsub h0; rw [GenOmegaLowerZeroDiagMatTower] at h0; subst h0
          exact List.not_mem_nil (hsub r0 hmem0)
        | succ k' ih =>
          intro cur hsub hsucc
          rcases hsucc with rfl | ⟨rem, M, v, h00, h0j, _, hweak, hkeep, hrem⟩
          · exact List.not_mem_nil (hsub r0 hmem0)
          · have heq := hpar_eq (fun s => v s ⟨0, hd⟩) (fun r hr => by
              rw [← lowerZeroDiag_wordVec_top N d hd M v h00 h0j r.1,
                  ← lowerZeroDiag_wordVec_top N d hd M v h00 h0j r.2]
              exact (hweak r (hsub r hr)).2 ⟨0, hd⟩)
            exact ih rem (fun r hr => hkeep r (hsub r hr) (by
              rw [lowerZeroDiag_wordVec_top N d hd M v h00 h0j r.1,
                  lowerZeroDiag_wordVec_top N d hd M v h00 h0j r.2,
                  heq r hr]
              exact Nat.lt_irrefl _)) hrem
      exact fun k => himp k core (fun _ hr => hr)
  have hup_imp : ∀ (N : Nat) (core : List (List (Fin N) × List (Fin N)))
      (syz : List Nat) (flow : List (Nat × Nat × Nat × Nat × Nat)),
      checkZeroDiag2GramCertBool N core syz flow = true ->
      core ≠ [] ->
      ∀ (d : Nat) (hd : d ≥ 1) (k : Nat), ¬ GenOmegaUpperZeroDiagMatTower N d hd k core := by
    intro N core syz flow hcert hne d hd
    cases hcore : core with
    | nil => exact False.elim (hne hcore)
    | cons r0 rs =>
      rw [← hcore]
      have hmem0 : r0 ∈ core := hcore ▸ List.Mem.head _
      have himp : ∀ (k : Nat) (cur : List (List (Fin N) × List (Fin N))),
          (∀ r ∈ core, r ∈ cur) -> ¬ GenOmegaUpperZeroDiagMatTower N d hd k cur := by
        intro k; induction k with
        | zero =>
          intro cur hsub h0; rw [GenOmegaUpperZeroDiagMatTower] at h0; subst h0
          exact List.not_mem_nil (hsub r0 hmem0)
        | succ k' ih =>
          intro cur hsub hsucc
          rcases hsucc with rfl | ⟨rem, M, v, h00, hlow, hweak, hkeep, hrem⟩
          · exact List.not_mem_nil (hsub r0 hmem0)
          · have heq := checkZeroDiag2GramCertBool_sound N d hd core syz flow hcert M v h00 hlow
              (fun r hr => hweak r (hsub r hr))
            exact ih rem (fun r hr => hkeep r (hsub r hr) (by
              rw [heq r hr]; exact Nat.lt_irrefl _)) hrem
      exact fun k => himp k core (fun _ hr => hr)
  exact ⟨by decide,
         fun d hd k => ⟨hlow_imp 42 c39 syzTwoSidedMod3OmitR3Core39 hsyz3 hne3 d hd k,
                        hlow_imp 84 c78 syzTwoSidedMod6OmitR3Core78 hsyz6 hne6 d hd k⟩,
         fun d hd k => ⟨hup_imp 42 c39 syzC39ZeroDiag2Gram flowC39ZeroDiag2Gram hz3 hne3 d hd k,
                        hup_imp 84 c78 syzC78ZeroDiag2Gram flowC78ZeroDiag2Gram hz6 hne6 d hd k⟩⟩

-- ----------------------------------------------------------------------------
-- Section 1C: Unconditional `.R`-Free Termination of `leftAnchoredDP2Step` (`leftAnchoredDP2_r_free_terminates`, choice-free `zero custom axioms`)
-- ----------------------------------------------------------------------------

def countBinSyms : List MixedSRSSym -> Nat
  | [] => 0
  | .B0 :: rest => 1 + countBinSyms rest
  | .B1 :: rest => 1 + countBinSyms rest
  | _ :: rest => countBinSyms rest

private theorem countBinSyms_append :
    ∀ u v : List MixedSRSSym, countBinSyms (u ++ v) = countBinSyms u + countBinSyms v
  | [], _ => by simp [countBinSyms]
  | s :: rest, v => by
    cases s <;> simp only [List.cons_append, countBinSyms, countBinSyms_append rest v]
    · rw [Nat.add_assoc]
    · rw [Nat.add_assoc]

private theorem omitR2_no_R_preserves_and_bin_noninc
    (r : List MixedSRSSym × List MixedSRSSym)
    (hm : r ∈ all11OmitR2List) (hnoR : .R ∉ r.1) :
    .R ∉ r.2 ∧ countBinSyms r.2 ≤ countBinSyms r.1 := by
  revert r hm hnoR; decide

private theorem srsReaches_omitR2_noR_inv {w1 w2 : List MixedSRSSym}
    (hreach : srsReachesFromList all11OmitR2List w1 w2) :
    .R ∉ w1 -> .R ∉ w2 ∧ countBinSyms w2 ≤ countBinSyms w1 := by
  induction hreach with
  | refl _ => intro hno; exact ⟨hno, Nat.le_refl _⟩
  | @step a b _ hs _ ih =>
    intro hno_a
    rcases hs with ⟨p, l, r, sfx, hmem, ha_eq, hb_eq⟩
    have hl_noR : .R ∉ l := fun hm =>
      hno_a (ha_eq ▸ List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hm))))
    rcases omitR2_no_R_preserves_and_bin_noninc (l, r) hmem hl_noR with ⟨hr_noR, hbin_le⟩
    have hno_b : .R ∉ b := by
      rw [hb_eq]
      intro hm
      rcases List.mem_append.mp hm with h1 | h2
      · rcases List.mem_append.mp h1 with hp | hr
        · exact hno_a (ha_eq ▸ List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hp))))
        · exact hr_noR hr
      · exact hno_a (ha_eq ▸ List.mem_append.mpr (Or.inr h2))
    rcases ih hno_b with ⟨hno_c, hle_cb⟩
    have hle_ba : countBinSyms b ≤ countBinSyms a := by
      rw [ha_eq, hb_eq, countBinSyms_append, countBinSyms_append,
          countBinSyms_append, countBinSyms_append]
      exact Nat.add_le_add_right (Nat.add_le_add_left hbin_le _) _
    exact ⟨hno_c, Nat.le_trans hle_cb hle_ba⟩

/--
  Theorem W12.1c (`leftAnchoredDP2_r_free_terminates`, choice-free `zero custom axioms`):
  Unconditional Termination of `leftAnchoredDP2Step` Across All `.R`-Free Words:
  1. Every `.R`-free `leftAnchoredDP2Step u1 u2` preserves `.R ∉ u2` AND strictly decreases
     `countBinSyms u2 < countBinSyms u1`!
  2. Every `.R`-free word `u0` (`∀ u0, .R ∉ u0`) is unconditionally accessible (`Acc`) under
     `leftAnchoredDP2Step` (localizing any hypothetical infinite `DP2` chain exclusively to `.R`-carrying words)!
-/
theorem leftAnchoredDP2_r_free_terminates :
    (∀ u1 u2 : List MixedSRSSym,
      .R ∉ u1 ->
      leftAnchoredDP2Step u1 u2 ->
      .R ∉ u2 ∧ countBinSyms u2 < countBinSyms u1) ∧
    (∀ u0 : List MixedSRSSym,
      .R ∉ u0 ->
      Acc (fun u2 u1 => leftAnchoredDP2Step u1 u2) u0) := by
  have hstep : ∀ u1 u2 : List MixedSRSSym,
      .R ∉ u1 -> leftAnchoredDP2Step u1 u2 -> .R ∉ u2 ∧ countBinSyms u2 < countBinSyms u1 := by
    intro u1 u2 hno1 ⟨_, _, hreach⟩
    have hno_in : .R ∉ ([.L, .T2] ++ u1) := by
      intro hm
      rcases List.mem_append.mp hm with hlt | hu
      · simp at hlt
      · exact hno1 hu
    rcases srsReaches_omitR2_noR_inv hreach hno_in with ⟨hno_out, hbin_le⟩
    have hno2 : .R ∉ u2 := fun hm => hno_out (List.mem_append.mpr (Or.inr hm))
    simp only [List.cons_append, List.nil_append, countBinSyms] at hbin_le
    exact ⟨hno2, Nat.lt_of_succ_le (by rwa [Nat.one_add] at hbin_le)⟩
  refine ⟨hstep, ?_⟩
  have hacc : ∀ (fuel : Nat) (u : List MixedSRSSym),
      .R ∉ u -> countBinSyms u ≤ fuel -> Acc (fun u2 u1 => leftAnchoredDP2Step u1 u2) u := by
    intro fuel; induction fuel with
    | zero =>
      intro u hno hle0
      refine Acc.intro u (fun u2 hdp => ?_)
      rcases hstep u u2 hno hdp with ⟨_, hlt⟩
      exact False.elim (Nat.not_lt_zero _ (Nat.lt_of_lt_of_le hlt hle0))
    | succ fuel' ih =>
      intro u hno hle
      refine Acc.intro u (fun u2 hdp => ?_)
      rcases hstep u u2 hno hdp with ⟨hno2, hlt⟩
      exact ih u2 hno2 (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hlt hle))
  exact fun u0 hno0 => hacc (countBinSyms u0) u0 hno0 (Nat.le_refl _)

-- ----------------------------------------------------------------------------
-- Section 1D: `M1 = 19/5` `R3`-Free `DP2` Prefix Family & Bounded-Prefix Barrier
-- ----------------------------------------------------------------------------

def repWord4 (k : Nat) (blk : List MixedSRSSym) : List MixedSRSSym :=
  match k with
  | 0 => []
  | k' + 1 => blk ++ repWord4 k' blk

def m1Tail0 (k : Nat) : List MixedSRSSym :=
  [.B1, .B1, .B0, .B1, .B1] ++ repWord4 k [.B0, .B0, .B1, .B1] ++ [.B0, .B0, .B1, .R]

def m1Tail1 (k : Nat) : List MixedSRSSym :=
  [.B1, .B0, .B0, .B1] ++ repWord4 k [.B0, .B1, .B1, .B0] ++ [.B0, .B1, .B1, .B0, .B0, .R]

def m1Tail2 (k : Nat) : List MixedSRSSym :=
  [.B0, .B1, .B1, .B1, .B1] ++ repWord4 k [.B0, .B0, .B1, .B1] ++ [.B0, .B0, .B1, .B1, .R]

def m1Tail3 (k : Nat) : List MixedSRSSym :=
  [.B1, .B1, .B0, .B1, .B1] ++ repWord4 k [.B0, .B0, .B1, .B1] ++ [.B0, .B1, .B0, .R]

private theorem no_L_repWord4 (blk : List MixedSRSSym) (hno : .L ∉ blk) :
    ∀ k : Nat, .L ∉ repWord4 k blk
  | 0 => List.not_mem_nil
  | k + 1 => fun hm => by
    rcases List.mem_append.mp hm with h1 | h2
    · exact hno h1
    · exact no_L_repWord4 blk hno k h2

private theorem srsStep_both_omitR2_and_omitR3
    (p l r sfx : List MixedSRSSym)
    (hr2 : (l, r) ∈ all11OmitR2List) (hr3 : (l, r) ∈ all11OmitR3List) :
    srsStepFromList all11OmitR2List (p ++ l ++ sfx) (p ++ r ++ sfx) ∧
    srsStepFromList all11OmitR3List (p ++ l ++ sfx) (p ++ r ++ sfx) :=
  ⟨⟨p, l, r, sfx, hr2, rfl, rfl⟩, ⟨p, l, r, sfx, hr3, rfl, rfl⟩⟩

private theorem srsReaches_both_trans {a b c : List MixedSRSSym}
    (h1 : srsReachesFromList all11OmitR2List a b ∧ srsReachesFromList all11OmitR3List a b)
    (h2 : srsReachesFromList all11OmitR2List b c ∧ srsReachesFromList all11OmitR3List b c) :
    srsReachesFromList all11OmitR2List a c ∧ srsReachesFromList all11OmitR3List a c := by
  have htr3 : ∀ {x y z : List MixedSRSSym},
      srsReachesFromList all11OmitR3List x y ->
      srsReachesFromList all11OmitR3List y z ->
      srsReachesFromList all11OmitR3List x z := by
    intro x y z hxy hyz
    induction hxy with
    | refl _ => exact hyz
    | step hs _ ih => exact .step hs (ih hyz)
  exact ⟨srsReaches_omitR2_trans h1.1 h2.1, htr3 h1.2 h2.2⟩

private theorem srsStep_to_reaches_both {a b : List MixedSRSSym}
    (p l r sfx : List MixedSRSSym)
    (hr2 : (l, r) ∈ all11OmitR2List) (hr3 : (l, r) ∈ all11OmitR3List)
    (ha : a = p ++ l ++ sfx) (hb : b = p ++ r ++ sfx) :
    srsReachesFromList all11OmitR2List a b ∧ srsReachesFromList all11OmitR3List a b := by
  subst ha; subst hb
  rcases srsStep_both_omitR2_and_omitR3 p l r sfx hr2 hr3 with ⟨s2, s3⟩
  exact ⟨.step s2 (.refl _), .step s3 (.refl _)⟩

private theorem sweep_T2_0011_both :
    ∀ (k : Nat) (pre sfx : List MixedSRSSym),
      srsReachesFromList all11OmitR2List
        (pre ++ [.T2] ++ repWord4 k [.B0, .B0, .B1, .B1] ++ sfx)
        (pre ++ repWord4 k [.B0, .B1, .B1, .B0] ++ [.T2] ++ sfx) ∧
      srsReachesFromList all11OmitR3List
        (pre ++ [.T2] ++ repWord4 k [.B0, .B0, .B1, .B1] ++ sfx)
        (pre ++ repWord4 k [.B0, .B1, .B1, .B0] ++ [.T2] ++ sfx)
  | 0, pre, sfx => by
    simp only [repWord4, List.append_nil]
    exact ⟨.refl _, .refl _⟩
  | k + 1, pre, sfx => by
    let rest := repWord4 k [.B0, .B0, .B1, .B1] ++ sfx
    -- `.T2 :: [.B0, .B0, .B1, .B1]` ->* `[.B0, .B1, .B1, .B0] ++ [.T2]` via `R7, R5, R4, R6`:
    have hs1 := srsStep_to_reaches_both pre [.T2, .B0] [.B0, .T1] ([.B0, .B1, .B1] ++ rest)
      (by decide) (by decide) rfl rfl
    have hs2 := srsStep_to_reaches_both (pre ++ [.B0]) [.T1, .B0] [.B1, .T0] ([.B1, .B1] ++ rest)
      (by decide) (by decide) rfl rfl
    have hs3 := srsStep_to_reaches_both (pre ++ [.B0, .B1]) [.T0, .B1] [.B1, .T1] ([.B1] ++ rest)
      (by decide) (by decide) rfl rfl
    have hs4 := srsStep_to_reaches_both (pre ++ [.B0, .B1, .B1]) [.T1, .B1] [.B0, .T2] rest
      (by decide) (by decide) rfl rfl
    have hblk := srsReaches_both_trans
      (by simpa [List.append_assoc] using hs1)
      (srsReaches_both_trans
        (by simpa [List.append_assoc] using hs2)
        (srsReaches_both_trans
          (by simpa [List.append_assoc] using hs3)
          (by simpa [List.append_assoc] using hs4)))
    have hih := sweep_T2_0011_both k (pre ++ [.B0, .B1, .B1, .B0]) sfx
    simpa [repWord4, rest, List.append_assoc] using
      srsReaches_both_trans
        (by simpa [rest, List.append_assoc] using hblk)
        (by simpa [List.append_assoc] using hih)

private theorem sweep_T1_0110_both :
    ∀ (k : Nat) (pre sfx : List MixedSRSSym),
      srsReachesFromList all11OmitR2List
        (pre ++ [.T1] ++ repWord4 k [.B0, .B1, .B1, .B0] ++ sfx)
        (pre ++ repWord4 k [.B1, .B1, .B0, .B0] ++ [.T1] ++ sfx) ∧
      srsReachesFromList all11OmitR3List
        (pre ++ [.T1] ++ repWord4 k [.B0, .B1, .B1, .B0] ++ sfx)
        (pre ++ repWord4 k [.B1, .B1, .B0, .B0] ++ [.T1] ++ sfx)
  | 0, pre, sfx => by
    simp only [repWord4, List.append_nil]
    exact ⟨.refl _, .refl _⟩
  | k + 1, pre, sfx => by
    let rest := repWord4 k [.B0, .B1, .B1, .B0] ++ sfx
    -- `.T1 :: [.B0, .B1, .B1, .B0]` ->* `[.B1, .B1, .B0, .B0] ++ [.T1]` via `R5, R4, R6, R7`:
    have hs1 := srsStep_to_reaches_both pre [.T1, .B0] [.B1, .T0] ([.B1, .B1, .B0] ++ rest)
      (by decide) (by decide) rfl rfl
    have hs2 := srsStep_to_reaches_both (pre ++ [.B1]) [.T0, .B1] [.B1, .T1] ([.B1, .B0] ++ rest)
      (by decide) (by decide) rfl rfl
    have hs3 := srsStep_to_reaches_both (pre ++ [.B1, .B1]) [.T1, .B1] [.B0, .T2] ([.B0] ++ rest)
      (by decide) (by decide) rfl rfl
    have hs4 := srsStep_to_reaches_both (pre ++ [.B1, .B1, .B0]) [.T2, .B0] [.B0, .T1] rest
      (by decide) (by decide) rfl rfl
    have hblk := srsReaches_both_trans
      (by simpa [List.append_assoc] using hs1)
      (srsReaches_both_trans
        (by simpa [List.append_assoc] using hs2)
        (srsReaches_both_trans
          (by simpa [List.append_assoc] using hs3)
          (by simpa [List.append_assoc] using hs4)))
    have hih := sweep_T1_0110_both k (pre ++ [.B1, .B1, .B0, .B0]) sfx
    simpa [repWord4, rest, List.append_assoc] using
      srsReaches_both_trans
        (by simpa [rest, List.append_assoc] using hblk)
        (by simpa [List.append_assoc] using hih)

private theorem repWord4_shift_1100_to_0011 :
    ∀ k : Nat,
      [.B1, .B1] ++ repWord4 k [.B0, .B0, .B1, .B1] ++ [.B0, .B0] =
        repWord4 k [.B1, .B1, .B0, .B0] ++ [.B1, .B1, .B0, .B0]
  | 0 => rfl
  | k + 1 => by
    have ih := repWord4_shift_1100_to_0011 k
    simp only [repWord4, List.cons_append, List.nil_append] at ih ⊢
    exact congrArg (fun l => .B1 :: .B1 :: .B0 :: .B0 :: l) ih

private theorem m1Tail0_take_eq_m1Tail3 :
    ∀ k : Nat, (m1Tail0 k).take (4 * k + 6) = (m1Tail3 k).take (4 * k + 6)
  | 0 => rfl
  | k + 1 => by
    unfold m1Tail0 m1Tail3
    have haux : ∀ m : Nat,
        (repWord4 m ([.B0, .B0, .B1, .B1] : List MixedSRSSym) ++
          ([.B0, .B0, .B1, .R] : List MixedSRSSym)).take (4 * m + 1) =
          (repWord4 m ([.B0, .B0, .B1, .B1] : List MixedSRSSym) ++
            ([.B0, .B1, .B0, .R] : List MixedSRSSym)).take (4 * m + 1) := by
      intro m; induction m with
      | zero => rfl
      | succ m' ihm =>
        rw [show 4 * (m' + 1) + 1 = (4 * m' + 1) + 4 by omega]
        simp only [repWord4, List.cons_append, List.nil_append, List.take_succ_cons, ihm]
    rw [show 4 * (k + 1) + 6 = (4 * (k + 1) + 1) + 5 by omega]
    simp only [List.cons_append, List.nil_append, List.take_succ_cons]
    exact congrArg (fun l => .B1 :: .B1 :: .B0 :: .B1 :: .B1 :: l) (haux (k + 1))

private theorem m1Tail0_eval_eq (k : Nat) :
    let w0 := .B1 :: ([.B1, .B1, .B0, .B1, .B1] ++ repWord4 k [.B0, .B0, .B1, .B1] ++ [.B0, .B0, .B1])
    (∀ s ∈ w0, isBinaryInteriorSym s = true) ∧
    5 * srsEvalInterior w0 = 2 ^ (4 * k + 12) + 19 := by
  dsimp only
  have hbin_rep : ∀ m : Nat, ∀ s ∈ repWord4 m ([.B0, .B0, .B1, .B1] : List MixedSRSSym),
      isBinaryInteriorSym s = true := by
    intro m; induction m with
    | zero => intro _ hs; cases hs
    | succ m' ih =>
      intro s hs
      rcases List.mem_append.mp hs with h1 | h2
      · simp at h1; rcases h1 with rfl | rfl | rfl | rfl <;> rfl
      · exact ih s h2
  refine ⟨?_, ?_⟩
  · intro s hs
    simp only [List.cons_append, List.nil_append, List.mem_cons] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | hrest
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rcases List.mem_append.mp hrest with hrep | htail
      · exact hbin_rep k s hrep
      · simp at htail; rcases htail with rfl | rfl | rfl <;> rfl
  · -- Induction on `k` for `5 * srsEvalInterior (repWord4 k [.B0, .B0, .B1, .B1] ++ [.B0, .B0, .B1]) + 4 = 2^(4k + 6)`:
    have hrep_eval : ∀ m : Nat,
        5 * srsEvalInterior (repWord4 m [.B0, .B0, .B1, .B1] ++ [.B0, .B0, .B1]) + 4 =
          2 ^ (4 * m + 6) := by
      intro m; induction m with
      | zero => decide
      | succ m' ih =>
        simp only [repWord4, List.cons_append, List.nil_append, srsEvalInterior]
        have hp : 2 ^ (4 * (m' + 1) + 6) = 16 * 2 ^ (4 * m' + 6) := by
          rw [show 4 * (m' + 1) + 6 = (4 * m' + 6) + 4 by omega, Nat.pow_add, Nat.mul_comm]
        rw [hp]
        omega
    have h0 := hrep_eval k
    simp only [List.cons_append, List.nil_append, srsEvalInterior]
    have hp : 2 ^ (4 * k + 12) = 64 * 2 ^ (4 * k + 6) := by
      rw [show 4 * k + 12 = (4 * k + 6) + 6 by omega, Nat.pow_add, Nat.mul_comm]
    rw [hp]
    omega

/--
  Theorem W12.1d (`m1_19_over_5_823_and_4919_omit_r3_cert`, `[]` axioms):
  Explicit `Z^+` `R3`-Free `M1 = 19/5` 2-Adic Prefix Trajectory Certificate:
  - `n_2 = 823 = (2^12 + 19) / 5` steps `823 -> 1235 -> 1853 -> 2780 -> 1390 -> 695` (`86` compressed
    steps to `1`), preserving `(encodePosBin 823).take 7 = (encodePosBin 695).take 7`!
  - `n'_2 = 4919 = (6 * 2^12 + 19) / 5` steps `4919 -> 7379 -> 11069 -> 16604 -> 8302 -> 4151`,
    preserving `(encodePosBin 4919).take 7 = (encodePosBin 4151).take 7`!
-/
theorem m1_19_over_5_823_and_4919_omit_r3_cert :
    5 * 823 = 2 ^ 12 + 19 ∧
    collatzStep 823 = 1235 ∧
    collatzStep 1235 = 1853 ∧
    collatzIter 3 1853 = 695 ∧
    (encodePosBin 823).take 7 = (encodePosBin 695).take 7 ∧
    5 * 4919 = 6 * 2 ^ 12 + 19 ∧
    collatzIter 5 4919 = 4151 ∧
    (encodePosBin 4919).take 7 = (encodePosBin 4151).take 7 := by decide

def all11OmitR2OmitR3List : List (List MixedSRSSym × List MixedSRSSym) :=
  all11OmitR2List.filter (fun p => decide (p.1 ≠ [.T0, .B0]))

def step2Targets (rules : List (List MixedSRSSym × List MixedSRSSym)) :
    List MixedSRSSym -> List (List MixedSRSSym)
  | [] => []
  | [_] => []
  | x :: y :: tl =>
    (rules.filter (fun p => decide (p.1 = [x, y]))).map (fun p => p.2 ++ tl) ++
      (step2Targets rules (y :: tl)).map (x :: ·)

private theorem srsStepFromList_of_mem_step2Targets
    (rules : List (List MixedSRSSym × List MixedSRSSym)) :
    ∀ {w w' : List MixedSRSSym},
      w' ∈ step2Targets rules w -> srsStepFromList rules w w'
  | [], _, h => by simp [step2Targets] at h
  | [_], _, h => by simp [step2Targets] at h
  | x :: y :: tl, w', h => by
    simp only [step2Targets, List.mem_append, List.mem_map, List.mem_filter] at h
    rcases h with ⟨⟨l, r⟩, ⟨hmem, hl_eq⟩, hw'⟩ | ⟨u', hu', hw'⟩
    · have hl : l = [x, y] := of_decide_eq_true hl_eq
      subst hl; subst hw'
      exact ⟨[], [x, y], r, tl, hmem, rfl, rfl⟩
    · subst hw'
      rcases srsStepFromList_of_mem_step2Targets rules hu' with ⟨p, l, r, sfx, hmem, hy, hu⟩
      refine ⟨x :: p, l, r, sfx, hmem, ?_, ?_⟩
      · simpa [List.cons_append] using congrArg (x :: ·) hy
      · simpa [List.cons_append] using congrArg (x :: ·) hu

private theorem srsStepFromList_mem_step2Targets
    (rules : List (List MixedSRSSym × List MixedSRSSym))
    (hlen2 : ∀ q ∈ rules, q.1.length = 2) :
    ∀ {w w' : List MixedSRSSym},
      srsStepFromList rules w w' -> w' ∈ step2Targets rules w := by
  intro w w' ⟨p, l, r, sfx, hmem, hw, hw'⟩
  subst hw; subst hw'
  have hl2 := hlen2 (l, r) hmem
  cases l with
  | nil => simp at hl2
  | cons a tl1 =>
    cases tl1 with
    | nil => simp at hl2
    | cons b tl2 =>
      cases tl2 with
      | cons _ _ => simp at hl2
      | nil =>
        induction p with
        | nil =>
          simp only [List.nil_append, List.cons_append, step2Targets, List.mem_append]
          apply Or.inl
          rw [List.mem_map]
          refine ⟨([a, b], r), ?_, rfl⟩
          rw [List.mem_filter]
          exact ⟨hmem, decide_eq_true rfl⟩
        | cons c ps ih =>
          cases htail : ps ++ [a, b] ++ sfx with
          | nil =>
            have hlen_t := congrArg List.length htail
            simp at hlen_t
          | cons d ds =>
            have hw_eq : (c :: ps) ++ [a, b] ++ sfx = c :: d :: ds := by
              simpa [List.cons_append, List.append_assoc] using congrArg (c :: ·) htail
            rw [hw_eq]
            simp only [step2Targets, List.mem_append]
            apply Or.inr
            rw [List.mem_map]
            refine ⟨ps ++ r ++ sfx, ?_, by simp [List.cons_append]⟩
            rw [← htail]
            exact ih

def validStepChainBool (rules : List (List MixedSRSSym × List MixedSRSSym)) :
    List MixedSRSSym -> List (List MixedSRSSym) -> List MixedSRSSym -> Bool
  | cur, [], target => decide (cur = target)
  | cur, nxt :: rest, target =>
    decide (nxt ∈ step2Targets rules cur) && validStepChainBool rules nxt rest target

private theorem validStepChainBool_sound
    (rules : List (List MixedSRSSym × List MixedSRSSym)) :
    ∀ (cur : List MixedSRSSym) (chain : List (List MixedSRSSym)) (target : List MixedSRSSym),
      validStepChainBool rules cur chain target = true ->
      srsReachesFromList rules cur target
  | cur, [], target, hb => by
    rw [of_decide_eq_true hb]; exact .refl _
  | cur, nxt :: rest, target, hb => by
    rcases bool_and_split hb with ⟨hstep_b, hrest⟩
    exact .step
      (srsStepFromList_of_mem_step2Targets rules (of_decide_eq_true hstep_b))
      (validStepChainBool_sound rules nxt rest target hrest)

def m129Tail825 : List MixedSRSSym := [.B0, .B0, .B1, .B1, .B1, .B0, .B0, .B1, .R]
def m129Tail619 : List MixedSRSSym := [.B1, .B0, .B1, .B0, .B1, .B1, .B0, .B0, .R]
def m129Tail929 : List MixedSRSSym := [.B0, .B0, .B0, .B0, .B1, .B0, .B1, .B1, .R]
def m129Tail697 : List MixedSRSSym := [.B0, .B0, .B1, .B1, .B1, .B0, .B1, .B0, .R]

private def m129Chain1 : List (List MixedSRSSym) :=
  [ [.L, .B0, .T1, .B0, .B1, .B1, .B1, .B0, .B0, .B1, .R],
    [.L, .T1, .B0, .B1, .B1, .B1, .B0, .B0, .B1, .R],
    [.L, .B1, .T0, .B1, .B1, .B1, .B0, .B0, .B1, .R],
    [.L, .B1, .B1, .T1, .B1, .B1, .B0, .B0, .B1, .R],
    [.L, .B1, .B1, .B0, .T2, .B1, .B0, .B0, .B1, .R],
    [.L, .B1, .B1, .B0, .B1, .T2, .B0, .B0, .B1, .R],
    [.L, .B1, .B1, .B0, .B1, .B0, .T1, .B0, .B1, .R],
    [.L, .B1, .B1, .B0, .B1, .B0, .B1, .T0, .B1, .R],
    [.L, .B1, .B1, .B0, .B1, .B0, .B1, .B1, .T1, .R],
    [.L, .B1, .B1, .B0, .B1, .B0, .B1, .B1, .B0, .B0, .R] ]

private def m129Chain2 : List (List MixedSRSSym) :=
  [ [.L, .B1, .T2, .B0, .B1, .B0, .B1, .B1, .B0, .B0, .R],
    [.L, .B1, .B0, .T1, .B1, .B0, .B1, .B1, .B0, .B0, .R],
    [.L, .B1, .B0, .B0, .T2, .B0, .B1, .B1, .B0, .B0, .R],
    [.L, .B1, .B0, .B0, .B0, .T1, .B1, .B1, .B0, .B0, .R],
    [.L, .B1, .B0, .B0, .B0, .B0, .T2, .B1, .B0, .B0, .R],
    [.L, .B1, .B0, .B0, .B0, .B0, .B1, .T2, .B0, .B0, .R],
    [.L, .B1, .B0, .B0, .B0, .B0, .B1, .B0, .T1, .B0, .R],
    [.L, .B1, .B0, .B0, .B0, .B0, .B1, .B0, .B1, .T0, .R],
    [.L, .B1, .B0, .B0, .B0, .B0, .B1, .B0, .B1, .B1, .R] ]

private def m129Chain3 : List (List MixedSRSSym) :=
  [ [.L, .B0, .T1, .B0, .B0, .B0, .B1, .B0, .B1, .B1, .R],
    [.L, .T1, .B0, .B0, .B0, .B1, .B0, .B1, .B1, .R],
    [.L, .B1, .T0, .B0, .B0, .B1, .B0, .B1, .B1, .R],
    [.L, .B1, .B0, .T0, .B0, .B1, .B0, .B1, .B1, .R],
    [.L, .B1, .B0, .B0, .T0, .B1, .B0, .B1, .B1, .R],
    [.L, .B1, .B0, .B0, .B1, .T1, .B0, .B1, .B1, .R],
    [.L, .B1, .B0, .B0, .B1, .B1, .T0, .B1, .B1, .R],
    [.L, .B1, .B0, .B0, .B1, .B1, .B1, .T1, .B1, .R],
    [.L, .B1, .B0, .B0, .B1, .B1, .B1, .B0, .T2, .R],
    [.L, .B1, .B0, .B0, .B1, .B1, .B1, .B0, .B1, .B0, .R] ]

private def m129FiveReach929 : List (List MixedSRSSym) :=
  [ [.L, .T2, .B0, .B0, .B0, .B0, .B1, .B0, .B1, .B1, .R],
    [.L, .B0, .T1, .B0, .B0, .B0, .B1, .B0, .B1, .B1, .R],
    [.L, .T1, .B0, .B0, .B0, .B1, .B0, .B1, .B1, .R],
    [.L, .B0, .B1, .T0, .B0, .B0, .B1, .B0, .B1, .B1, .R],
    [.L, .B1, .T0, .B0, .B0, .B1, .B0, .B1, .B1, .R] ]

/--
  Theorem W12.1d' (`m1_29_over_5_825_r3_firing_dp2_contrast`,
  `zero custom axioms`):
  Exact `R3`-Firing Separation Between `M1 = 29/5` and `M1 = 19/5` Under `leftAnchoredDP2Step`
  (`Branch P4.3`, `W12_H2`):
  1. **2-Adic `M1 = 29/5` `Z^+` Prefix Trajectory (`825 -> 1238 -> 619 -> 929 -> 1394 -> 697`)**:
     `n'_0 = 825 = (2^12 + 29) / 5` executes `3` consecutive `leftAnchoredDP2Step` transitions
     (`m129Tail825 -> m129Tail619 -> m129Tail929 -> m129Tail697`) preserving
     `(encodePosBin 825).take 7 = (encodePosBin 697).take 7` and `(m129Tail825).take 6 = (m129Tail697).take 6`!
  2. **Provable `R3` Necessity on `929` (Separating `29/5` from `R3`-Free `19/5`)**:
     Whereas `19/5` (`823 -> 695`) executes 100% inside `all11OmitR3List`, at `929` (`m129Tail929`)
     EVERY word reachable from `[.L, .T2] ++ m129Tail929` under `all11OmitR2OmitR3List` (`all11 \ {R2, R3}`)
     still contains an unresolved carry symbol in `{.T0, .T1, .T2}` (blocking `[.L, .B1] ++ m129Tail697`
     unless `R3 : [.T0, .B0] -> [.B0, .T0]` fires)!
  3. **Universal Parametric `29/5` Family (`∀ k : Nat`)**:
     `5 * ((2 ^ (4 * k + 12) + 29) / 5) = 2 ^ (4 * k + 12) + 29` and
     `5 * ((27 * 2 ^ (4 * k + 7) + 29) / 5) = 27 * 2 ^ (4 * k + 7) + 29`!
-/
theorem m1_29_over_5_825_r3_firing_dp2_contrast :
    5 * 825 = 2 ^ 12 + 29 ∧
    collatzStep 825 = 1238 ∧
    collatzStep 1238 = 619 ∧
    collatzStep 619 = 929 ∧
    collatzIter 2 929 = 697 ∧
    (encodePosBin 825).take 7 = (encodePosBin 697).take 7 ∧
    encodePosBin 825 ++ [.R] = .B1 :: m129Tail825 ∧
    encodePosBin 929 ++ [.R] = .B1 :: m129Tail929 ∧
    encodePosBin 697 ++ [.R] = .B1 :: m129Tail697 ∧
    leftAnchoredDP2Step m129Tail825 m129Tail619 ∧
    leftAnchoredDP2Step m129Tail619 m129Tail929 ∧
    leftAnchoredDP2Step m129Tail929 m129Tail697 ∧
    (m129Tail825).take 6 = (m129Tail697).take 6 ∧
    (∀ w : List MixedSRSSym,
      srsReachesFromList all11OmitR2OmitR3List ([.L, .T2] ++ m129Tail929) w ->
      .T0 ∈ w ∨ .T1 ∈ w ∨ .T2 ∈ w) ∧
    ¬ srsReachesFromList all11OmitR2OmitR3List
        ([.L, .T2] ++ m129Tail929) ([.L, .B1] ++ m129Tail697) ∧
    (∀ k : Nat,
      5 * ((2 ^ (4 * k + 12) + 29) / 5) = 2 ^ (4 * k + 12) + 29 ∧
      5 * ((27 * 2 ^ (4 * k + 7) + 29) / 5) = 27 * 2 ^ (4 * k + 7) + 29) := by
  have hdp1 : leftAnchoredDP2Step m129Tail825 m129Tail619 :=
    ⟨by decide, by decide,
     validStepChainBool_sound all11OmitR2List
       ([.L, .T2] ++ m129Tail825) m129Chain1 ([.L, .B1] ++ m129Tail619) (by decide)⟩
  have hdp2 : leftAnchoredDP2Step m129Tail619 m129Tail929 :=
    ⟨by decide, by decide,
     validStepChainBool_sound all11OmitR2List
       ([.L, .T2] ++ m129Tail619) m129Chain2 ([.L, .B1] ++ m129Tail929) (by decide)⟩
  have hdp3 : leftAnchoredDP2Step m129Tail929 m129Tail697 :=
    ⟨by decide, by decide,
     validStepChainBool_sound all11OmitR2List
       ([.L, .T2] ++ m129Tail929) m129Chain3 ([.L, .B1] ++ m129Tail697) (by decide)⟩
  have hlen2 : ∀ q ∈ all11OmitR2OmitR3List, q.1.length = 2 := by decide
  have hclosed : ∀ w ∈ m129FiveReach929, ∀ w' ∈ step2Targets all11OmitR2OmitR3List w,
      w' ∈ m129FiveReach929 := by decide
  have hcarry5 : ∀ w ∈ m129FiveReach929, .T0 ∈ w ∨ .T1 ∈ w ∨ .T2 ∈ w := by decide
  have hreach_in5 : ∀ {a b : List MixedSRSSym},
      srsReachesFromList all11OmitR2OmitR3List a b ->
      a ∈ m129FiveReach929 -> b ∈ m129FiveReach929 := by
    intro a b hr
    induction hr with
    | refl _ => exact id
    | step hs _ ih =>
      intro ha
      exact ih (hclosed _ ha _ (srsStepFromList_mem_step2Targets all11OmitR2OmitR3List hlen2 hs))
  have hall_carry : ∀ w : List MixedSRSSym,
      srsReachesFromList all11OmitR2OmitR3List ([.L, .T2] ++ m129Tail929) w ->
      .T0 ∈ w ∨ .T1 ∈ w ∨ .T2 ∈ w :=
    fun w hr => hcarry5 w (hreach_in5 hr (by decide))
  have hnot_697 : ¬ srsReachesFromList all11OmitR2OmitR3List
      ([.L, .T2] ++ m129Tail929) ([.L, .B1] ++ m129Tail697) := by
    intro hr
    have hc := hall_carry _ hr
    revert hc; decide
  have hmod5 : ∀ k : Nat,
      2 ^ (4 * k + 12) % 5 = 1 ∧ 2 ^ (4 * k + 7) % 5 = 3 := by
    intro k; induction k with
    | zero => decide
    | succ k' ih =>
      have hp1 : 2 ^ (4 * (k' + 1) + 12) = 16 * 2 ^ (4 * k' + 12) := by
        rw [show 4 * (k' + 1) + 12 = (4 * k' + 12) + 4 by omega, Nat.pow_add, Nat.mul_comm]
      have hp2 : 2 ^ (4 * (k' + 1) + 7) = 16 * 2 ^ (4 * k' + 7) := by
        rw [show 4 * (k' + 1) + 7 = (4 * k' + 7) + 4 by omega, Nat.pow_add, Nat.mul_comm]
      rw [hp1, hp2]; omega
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide,
          by decide, by decide, by decide, hdp1, hdp2, hdp3, by decide,
          hall_carry, hnot_697, ?_⟩
  intro k
  rcases hmod5 k with ⟨hm1, hm2⟩
  omega

/--
  Theorem W12.1e (`left_anchored_dp2_m1_bounded_prefix_impossibility`,
  `zero custom axioms`):
  Universal `M1 = 19/5` `R3`-Free 3-Step `leftAnchoredDP2Step` Prefix-Preservation &
  Bounded-Prefix Ranking Impossibility (`Branch P4.3`, `W12_H2`):
  1. **Constructive `Z^+` Integer Encoding & `R3`-Free 3-Step `DP2` Chain (`∀ k : Nat`, `n_k = (2^(4k+12) + 19)/5`)**:
     For EVERY `k : Nat`, `m1Tail0 k`, `m1Tail1 k`, `m1Tail2 k`, `m1Tail3 k` satisfy:
     - `encodePosBin ((2 ^ (4 * k + 12) + 19) / 5) ++ [.R] = .B1 :: m1Tail0 k`,
     - `leftAnchoredDP2Step (m1Tail0 k) (m1Tail1 k) ∧ leftAnchoredDP2Step (m1Tail1 k) (m1Tail2 k) ∧
        leftAnchoredDP2Step (m1Tail2 k) (m1Tail3 k)`,
     - ALL THREE carry sweeps ALSO lie 100% inside `all11OmitR3List` (`R3 : [.T0, .B0] -> [.B0, .T0]` NEVER fires!), AND
     - `(m1Tail0 k).take (4 * k + 6) = (m1Tail3 k).take (4 * k + 6)`!
  2. **Universal Root-Local Bounded-Prefix Ranking Impossibility (`∀ W_pref : Nat`)**:
     NO root-local bounded-prefix ranking function `V : List MixedSRSSym -> Nat` depending on the
     first `W_pref` symbols after `.L` can strictly orient `leftAnchoredDP2Step`:
       `∀ (W_pref : Nat) (V : List MixedSRSSym -> Nat),
          ¬ (∀ u1 u2 : List MixedSRSSym, leftAnchoredDP2Step u1 u2 -> V (u2.take W_pref) < V (u1.take W_pref))`!
-/
theorem left_anchored_dp2_m1_bounded_prefix_impossibility :
    (∀ k : Nat,
      let n_k := (2 ^ (4 * k + 12) + 19) / 5
      5 * n_k = 2 ^ (4 * k + 12) + 19 ∧
      encodePosBin n_k ++ [.R] = .B1 :: m1Tail0 k ∧
      leftAnchoredDP2Step (m1Tail0 k) (m1Tail1 k) ∧
      leftAnchoredDP2Step (m1Tail1 k) (m1Tail2 k) ∧
      leftAnchoredDP2Step (m1Tail2 k) (m1Tail3 k) ∧
      srsReachesFromList all11OmitR3List ([.L, .T2] ++ m1Tail0 k) ([.L, .B1] ++ m1Tail1 k) ∧
      srsReachesFromList all11OmitR3List ([.L, .T2] ++ m1Tail1 k) ([.L, .B1] ++ m1Tail2 k) ∧
      srsReachesFromList all11OmitR3List ([.L, .T2] ++ m1Tail2 k) ([.L, .B1] ++ m1Tail3 k) ∧
      (m1Tail0 k).take (4 * k + 6) = (m1Tail3 k).take (4 * k + 6)) ∧
    (∀ (W_pref : Nat) (V : List MixedSRSSym -> Nat),
      ¬ (∀ u1 u2 : List MixedSRSSym,
          leftAnchoredDP2Step u1 u2 -> V (u2.take W_pref) < V (u1.take W_pref))) := by
  have hchain : ∀ k : Nat,
      let n_k := (2 ^ (4 * k + 12) + 19) / 5
      5 * n_k = 2 ^ (4 * k + 12) + 19 ∧
      encodePosBin n_k ++ [.R] = .B1 :: m1Tail0 k ∧
      leftAnchoredDP2Step (m1Tail0 k) (m1Tail1 k) ∧
      leftAnchoredDP2Step (m1Tail1 k) (m1Tail2 k) ∧
      leftAnchoredDP2Step (m1Tail2 k) (m1Tail3 k) ∧
      srsReachesFromList all11OmitR3List ([.L, .T2] ++ m1Tail0 k) ([.L, .B1] ++ m1Tail1 k) ∧
      srsReachesFromList all11OmitR3List ([.L, .T2] ++ m1Tail1 k) ([.L, .B1] ++ m1Tail2 k) ∧
      srsReachesFromList all11OmitR3List ([.L, .T2] ++ m1Tail2 k) ([.L, .B1] ++ m1Tail3 k) ∧
      (m1Tail0 k).take (4 * k + 6) = (m1Tail3 k).take (4 * k + 6) := by
    intro k
    dsimp only
    let w0 := .B1 :: ([.B1, .B1, .B0, .B1, .B1] ++ repWord4 k [.B0, .B0, .B1, .B1] ++ [.B0, .B0, .B1])
    rcases m1Tail0_eval_eq k with ⟨hw0_bin, hw0_5⟩
    have hn_eq : (2 ^ (4 * k + 12) + 19) / 5 = srsEvalInterior w0 := by
      rw [← hw0_5, Nat.mul_div_right _ (by decide : 0 < 5)]
    have hn_5 : 5 * ((2 ^ (4 * k + 12) + 19) / 5) = 2 ^ (4 * k + 12) + 19 := by omega
    have hn_pos : (2 ^ (4 * k + 12) + 19) / 5 ≥ 1 := by
      rw [hn_eq]; exact srsEvalInterior_pos w0
    rcases encodePosBin_spec ((2 ^ (4 * k + 12) + 19) / 5) hn_pos with ⟨heval_nk, hbin_nk⟩
    have hw0_eq_enc : encodePosBin ((2 ^ (4 * k + 12) + 19) / 5) = w0 :=
      binary_interior_unique _ w0 hbin_nk hw0_bin (by omega)
    have henc_R : encodePosBin ((2 ^ (4 * k + 12) + 19) / 5) ++ [.R] = .B1 :: m1Tail0 k := by
      rw [hw0_eq_enc]; simp [w0, m1Tail0, List.append_assoc]
    have hno0 : .L ∉ m1Tail0 k := by
      unfold m1Tail0
      intro hm
      rcases List.mem_append.mp hm with h1 | h2
      · rcases List.mem_append.mp h1 with hpre | hrep
        · simp at hpre
        · exact no_L_repWord4 [.B0, .B0, .B1, .B1] (by decide) k hrep
      · simp at h2
    have hno1 : .L ∉ m1Tail1 k := by
      unfold m1Tail1
      intro hm
      rcases List.mem_append.mp hm with h1 | h2
      · rcases List.mem_append.mp h1 with hpre | hrep
        · simp at hpre
        · exact no_L_repWord4 [.B0, .B1, .B1, .B0] (by decide) k hrep
      · simp at h2
    have hno2 : .L ∉ m1Tail2 k := by
      unfold m1Tail2
      intro hm
      rcases List.mem_append.mp hm with h1 | h2
      · rcases List.mem_append.mp h1 with hpre | hrep
        · simp at hpre
        · exact no_L_repWord4 [.B0, .B0, .B1, .B1] (by decide) k hrep
      · simp at h2
    have hno3 : .L ∉ m1Tail3 k := by
      unfold m1Tail3
      intro hm
      rcases List.mem_append.mp hm with h1 | h2
      · rcases List.mem_append.mp h1 with hpre | hrep
        · simp at hpre
        · exact no_L_repWord4 [.B0, .B0, .B1, .B1] (by decide) k hrep
      · simp at h2
    -- Sweep 0 (`m1Tail0 k -> m1Tail1 k`):
    let r0_tail := repWord4 k [.B0, .B0, .B1, .B1] ++ [.B0, .B0, .B1, .R]
    have s0_1 := srsStep_to_reaches_both (a := [.L, .T2] ++ m1Tail0 k)
      [.L] [.T2, .B1] [.B1, .T2] ([.B1, .B0, .B1, .B1] ++ r0_tail)
      (by decide) (by decide) (by simp [m1Tail0, r0_tail]) rfl
    have s0_2 := srsStep_to_reaches_both [.L, .B1] [.T2, .B1] [.B1, .T2] ([.B0, .B1, .B1] ++ r0_tail)
      (by decide) (by decide) rfl rfl
    have s0_3 := srsStep_to_reaches_both [.L, .B1, .B1] [.T2, .B0] [.B0, .T1] ([.B1, .B1] ++ r0_tail)
      (by decide) (by decide) rfl rfl
    have s0_4 := srsStep_to_reaches_both [.L, .B1, .B1, .B0] [.T1, .B1] [.B0, .T2] ([.B1] ++ r0_tail)
      (by decide) (by decide) rfl rfl
    have s0_5 := srsStep_to_reaches_both [.L, .B1, .B1, .B0, .B0] [.T2, .B1] [.B1, .T2] r0_tail
      (by decide) (by decide) rfl rfl
    have s0_pre := srsReaches_both_trans s0_1 (srsReaches_both_trans s0_2
      (srsReaches_both_trans s0_3 (srsReaches_both_trans s0_4 s0_5)))
    have s0_mid := sweep_T2_0011_both k [.L, .B1, .B1, .B0, .B0, .B1] [.B0, .B0, .B1, .R]
    let p0_end := [.L, .B1, .B1, .B0, .B0, .B1] ++ repWord4 k [.B0, .B1, .B1, .B0]
    have s0_e1 := srsStep_to_reaches_both p0_end [.T2, .B0] [.B0, .T1] [.B0, .B1, .R]
      (by decide) (by decide) rfl rfl
    have s0_e2 := srsStep_to_reaches_both (p0_end ++ [.B0]) [.T1, .B0] [.B1, .T0] [.B1, .R]
      (by decide) (by decide) rfl rfl
    have s0_e3 := srsStep_to_reaches_both (p0_end ++ [.B0, .B1]) [.T0, .B1] [.B1, .T1] [.R]
      (by decide) (by decide) rfl rfl
    have s0_e4 := srsStep_to_reaches_both (p0_end ++ [.B0, .B1, .B1]) [.T1, .R] [.B0, .B0, .R] []
      (by decide) (by decide) rfl rfl
    have s0_suf := srsReaches_both_trans
      (by simpa [p0_end, List.append_assoc] using s0_e1)
      (srsReaches_both_trans
        (by simpa [p0_end, List.append_assoc] using s0_e2)
        (srsReaches_both_trans
          (by simpa [p0_end, List.append_assoc] using s0_e3)
          (by simpa [p0_end, List.append_assoc] using s0_e4)))
    have hsw0 : srsReachesFromList all11OmitR2List ([.L, .T2] ++ m1Tail0 k) ([.L, .B1] ++ m1Tail1 k) ∧
        srsReachesFromList all11OmitR3List ([.L, .T2] ++ m1Tail0 k) ([.L, .B1] ++ m1Tail1 k) := by
      have hc := srsReaches_both_trans s0_pre (srsReaches_both_trans
        (by simpa [r0_tail, List.append_assoc] using s0_mid)
        (by simpa [p0_end, List.append_assoc] using s0_suf))
      simpa [m1Tail0, m1Tail1, p0_end, r0_tail, List.append_assoc] using hc
    -- Sweep 1 (`m1Tail1 k -> m1Tail2 k`):
    let r1_tail := repWord4 k [.B0, .B1, .B1, .B0] ++ [.B0, .B1, .B1, .B0, .B0, .R]
    have s1_1 := srsStep_to_reaches_both (a := [.L, .T2] ++ m1Tail1 k)
      [.L] [.T2, .B1] [.B1, .T2] ([.B0, .B0, .B1] ++ r1_tail)
      (by decide) (by decide) (by simp [m1Tail1, r1_tail]) rfl
    have s1_2 := srsStep_to_reaches_both [.L, .B1] [.T2, .B0] [.B0, .T1] ([.B0, .B1] ++ r1_tail)
      (by decide) (by decide) rfl rfl
    have s1_3 := srsStep_to_reaches_both [.L, .B1, .B0] [.T1, .B0] [.B1, .T0] ([.B1] ++ r1_tail)
      (by decide) (by decide) rfl rfl
    have s1_4 := srsStep_to_reaches_both [.L, .B1, .B0, .B1] [.T0, .B1] [.B1, .T1] r1_tail
      (by decide) (by decide) rfl rfl
    have s1_pre := srsReaches_both_trans s1_1 (srsReaches_both_trans s1_2 (srsReaches_both_trans s1_3 s1_4))
    have s1_mid := sweep_T1_0110_both k [.L, .B1, .B0, .B1, .B1] [.B0, .B1, .B1, .B0, .B0, .R]
    let p1_end := [.L, .B1, .B0, .B1, .B1] ++ repWord4 k [.B1, .B1, .B0, .B0]
    have s1_e1 := srsStep_to_reaches_both p1_end [.T1, .B0] [.B1, .T0] [.B1, .B1, .B0, .B0, .R]
      (by decide) (by decide) rfl rfl
    have s1_e2 := srsStep_to_reaches_both (p1_end ++ [.B1]) [.T0, .B1] [.B1, .T1] [.B1, .B0, .B0, .R]
      (by decide) (by decide) rfl rfl
    have s1_e3 := srsStep_to_reaches_both (p1_end ++ [.B1, .B1]) [.T1, .B1] [.B0, .T2] [.B0, .B0, .R]
      (by decide) (by decide) rfl rfl
    have s1_e4 := srsStep_to_reaches_both (p1_end ++ [.B1, .B1, .B0]) [.T2, .B0] [.B0, .T1] [.B0, .R]
      (by decide) (by decide) rfl rfl
    have s1_e5 := srsStep_to_reaches_both (p1_end ++ [.B1, .B1, .B0, .B0]) [.T1, .B0] [.B1, .T0] [.R]
      (by decide) (by decide) rfl rfl
    have s1_e6 := srsStep_to_reaches_both (p1_end ++ [.B1, .B1, .B0, .B0, .B1]) [.T0, .R] [.B1, .R] []
      (by decide) (by decide) rfl rfl
    have s1_suf := srsReaches_both_trans
      (by simpa [p1_end, List.append_assoc] using s1_e1)
      (srsReaches_both_trans
        (by simpa [p1_end, List.append_assoc] using s1_e2)
        (srsReaches_both_trans
          (by simpa [p1_end, List.append_assoc] using s1_e3)
          (srsReaches_both_trans
            (by simpa [p1_end, List.append_assoc] using s1_e4)
            (srsReaches_both_trans
              (by simpa [p1_end, List.append_assoc] using s1_e5)
              (by simpa [p1_end, List.append_assoc] using s1_e6)))))
    have hm1Tail2_eq : [.L, .B1] ++ m1Tail2 k =
        p1_end ++ [.B1, .B1, .B0, .B0, .B1, .B1, .R] := by
      have hsh := repWord4_shift_1100_to_0011 k
      dsimp only [m1Tail2, p1_end]
      have hlhs : [.L, .B1] ++ ([.B0, .B1, .B1, .B1, .B1] ++ repWord4 k [.B0, .B0, .B1, .B1] ++ [.B0, .B0, .B1, .B1, .R]) =
          [.L, .B1, .B0, .B1, .B1] ++ ([.B1, .B1] ++ repWord4 k [.B0, .B0, .B1, .B1] ++ [.B0, .B0]) ++ [.B1, .B1, .R] := by
        simp [List.append_assoc]
      rw [hlhs, hsh]
      simp [List.append_assoc]
    have hsw1 : srsReachesFromList all11OmitR2List ([.L, .T2] ++ m1Tail1 k) ([.L, .B1] ++ m1Tail2 k) ∧
        srsReachesFromList all11OmitR3List ([.L, .T2] ++ m1Tail1 k) ([.L, .B1] ++ m1Tail2 k) := by
      rw [hm1Tail2_eq]
      have hc := srsReaches_both_trans s1_pre (srsReaches_both_trans
        (by simpa [r1_tail, List.append_assoc] using s1_mid)
        (by simpa [p1_end, List.append_assoc] using s1_suf))
      simpa [m1Tail1, p1_end, r1_tail, List.append_assoc] using hc
    -- Sweep 2 (`m1Tail2 k -> [.L, .B0, .B0, .B1] ++ m1Tail3 k -> [.L, .B1] ++ m1Tail3 k` via `R1` twice!):
    let r2_tail := repWord4 k [.B0, .B0, .B1, .B1] ++ [.B0, .B0, .B1, .B1, .R]
    have s2_1 := srsStep_to_reaches_both (a := [.L, .T2] ++ m1Tail2 k)
      [.L] [.T2, .B0] [.B0, .T1] ([.B1, .B1, .B1, .B1] ++ r2_tail)
      (by decide) (by decide) (by simp [m1Tail2, r2_tail]) rfl
    have s2_2 := srsStep_to_reaches_both [.L, .B0] [.T1, .B1] [.B0, .T2] ([.B1, .B1, .B1] ++ r2_tail)
      (by decide) (by decide) rfl rfl
    have s2_3 := srsStep_to_reaches_both [.L, .B0, .B0] [.T2, .B1] [.B1, .T2] ([.B1, .B1] ++ r2_tail)
      (by decide) (by decide) rfl rfl
    have s2_4 := srsStep_to_reaches_both [.L, .B0, .B0, .B1] [.T2, .B1] [.B1, .T2] ([.B1] ++ r2_tail)
      (by decide) (by decide) rfl rfl
    have s2_5 := srsStep_to_reaches_both [.L, .B0, .B0, .B1, .B1] [.T2, .B1] [.B1, .T2] r2_tail
      (by decide) (by decide) rfl rfl
    have s2_pre := srsReaches_both_trans s2_1 (srsReaches_both_trans s2_2
      (srsReaches_both_trans s2_3 (srsReaches_both_trans s2_4 s2_5)))
    have s2_mid := sweep_T2_0011_both k [.L, .B0, .B0, .B1, .B1, .B1] [.B0, .B0, .B1, .B1, .R]
    let p2_end := [.L, .B0, .B0, .B1, .B1, .B1] ++ repWord4 k [.B0, .B1, .B1, .B0]
    have s2_e1 := srsStep_to_reaches_both p2_end [.T2, .B0] [.B0, .T1] [.B0, .B1, .B1, .R]
      (by decide) (by decide) rfl rfl
    have s2_e2 := srsStep_to_reaches_both (p2_end ++ [.B0]) [.T1, .B0] [.B1, .T0] [.B1, .B1, .R]
      (by decide) (by decide) rfl rfl
    have s2_e3 := srsStep_to_reaches_both (p2_end ++ [.B0, .B1]) [.T0, .B1] [.B1, .T1] [.B1, .R]
      (by decide) (by decide) rfl rfl
    have s2_e4 := srsStep_to_reaches_both (p2_end ++ [.B0, .B1, .B1]) [.T1, .B1] [.B0, .T2] [.R]
      (by decide) (by decide) rfl rfl
    have s2_e5 := srsStep_to_reaches_both (p2_end ++ [.B0, .B1, .B1, .B0]) [.T2, .R] [.B1, .B0, .R] []
      (by decide) (by decide) rfl rfl
    -- Now drain two leading `.B0`s at `.L` via `R1` (`[.L, .B0] -> [.L]`):
    have hm1Tail3_shift : p2_end ++ [.B0, .B1, .B1, .B0, .B1, .B0, .R] =
        [.L, .B0, .B0, .B1] ++ m1Tail3 k := by
      have hsh_core : ∀ m : Nat,
          repWord4 m ([.B0, .B1, .B1, .B0] : List MixedSRSSym) ++ [.B0, .B1, .B1, .B0] =
            [.B0, .B1, .B1] ++ repWord4 m [.B0, .B0, .B1, .B1] ++ [.B0] := by
        intro m; induction m with
        | zero => rfl
        | succ m' ihm =>
          simp only [repWord4, List.cons_append, List.nil_append] at ihm ⊢
          exact congrArg (fun l => .B0 :: .B1 :: .B1 :: .B0 :: l) ihm
      dsimp only [p2_end, m1Tail3]
      have hlhs : ([.L, .B0, .B0, .B1, .B1, .B1] ++ repWord4 k [.B0, .B1, .B1, .B0]) ++
            [.B0, .B1, .B1, .B0, .B1, .B0, .R] =
          [.L, .B0, .B0, .B1, .B1, .B1] ++ (repWord4 k [.B0, .B1, .B1, .B0] ++ [.B0, .B1, .B1, .B0]) ++
            [.B1, .B0, .R] := by
        simp [List.append_assoc]
      rw [hlhs, hsh_core k]
      simp [List.append_assoc]
    have s2_dr1 := srsStep_to_reaches_both [] [.L, .B0] [.L] ([.B0, .B1] ++ m1Tail3 k)
      (by decide) (by decide) rfl rfl
    have s2_dr2 := srsStep_to_reaches_both [] [.L, .B0] [.L] ([.B1] ++ m1Tail3 k)
      (by decide) (by decide) rfl rfl
    have s2_suf := srsReaches_both_trans
      (by simpa [p2_end, List.append_assoc] using s2_e1)
      (srsReaches_both_trans
        (by simpa [p2_end, List.append_assoc] using s2_e2)
        (srsReaches_both_trans
          (by simpa [p2_end, List.append_assoc] using s2_e3)
          (srsReaches_both_trans
            (by simpa [p2_end, List.append_assoc] using s2_e4)
            (by simpa [p2_end, List.append_assoc] using s2_e5))))
    have hsw2_pre : srsReachesFromList all11OmitR2List ([.L, .T2] ++ m1Tail2 k) ([.L, .B0, .B0, .B1] ++ m1Tail3 k) ∧
        srsReachesFromList all11OmitR3List ([.L, .T2] ++ m1Tail2 k) ([.L, .B0, .B0, .B1] ++ m1Tail3 k) := by
      rw [← hm1Tail3_shift]
      have hc := srsReaches_both_trans s2_pre (srsReaches_both_trans
        (by simpa [r2_tail, List.append_assoc] using s2_mid)
        (by simpa [p2_end, List.append_assoc] using s2_suf))
      simpa [m1Tail2, p2_end, r2_tail, List.append_assoc] using hc
    have hsw2 := srsReaches_both_trans hsw2_pre (srsReaches_both_trans
      (by simpa [List.append_assoc] using s2_dr1)
      (by simpa [List.append_assoc] using s2_dr2))
    exact ⟨hn_5, henc_R,
           ⟨hno0, hno1, hsw0.1⟩, ⟨hno1, hno2, hsw1.1⟩, ⟨hno2, hno3, hsw2.1⟩,
           hsw0.2, hsw1.2, hsw2.2, m1Tail0_take_eq_m1Tail3 k⟩
  refine ⟨hchain, ?_⟩
  intro W_pref V hstrict
  rcases hchain W_pref with ⟨_, _, hdp0, hdp1, hdp2, _, _, _, htake_eq⟩
  have h1 := hstrict _ _ hdp0
  have h2 := hstrict _ _ hdp1
  have h3 := hstrict _ _ hdp2
  have htake_le : (m1Tail0 W_pref).take W_pref = (m1Tail3 W_pref).take W_pref := by
    have hsub : ∀ (a b : List MixedSRSSym) (n m : Nat),
        m ≤ n -> a.take n = b.take n -> a.take m = b.take m := by
      intro a b n m hle heq
      have h := congrArg (List.take m) heq
      have ht : ∀ (l : List MixedSRSSym) (x y : Nat), y ≤ x -> (l.take x).take y = l.take y := by
        intro l; induction l with
        | nil => intros; simp
        | cons _ xs ih =>
          intro x y hyx
          cases y with
          | zero => simp
          | succ y' =>
            cases x with
            | zero => omega
            | succ x' =>
              simp only [List.take_succ_cons]
              exact congrArg (List.cons _) (ih x' y' (by omega))
      rwa [ht a _ _ hle, ht b _ _ hle] at h
    exact hsub (m1Tail0 W_pref) (m1Tail3 W_pref) (4 * W_pref + 6) W_pref (by omega) htake_eq
  rw [htake_le] at h1
  omega

-- ============================================================================
-- SECTION 2: Front B (Branches P3.3 & P3.4) — Universal Arbitrary-`T` Confluent
--            `2^(T*(T-1)/2 * u) * (2^u - 1)^(T^2)` Divisibility, `4 × 4` Multi-`u`
--            Zero-Multiplicity `≤ 1`, Rank-3 `9 × 9` `(T = 3, U = 3)` Non-Vanishing &
--            Cone Positivity, `q ≡ 1 (mod 24)` `ℓ^r` Sylow Biconditional, & `m`-Block Cascades
-- ============================================================================

-- ----------------------------------------------------------------------------
-- Section 2A: Universal Order-`T` Confluent Divisibility (`∀ L, T, u ≥ 1`)
-- ----------------------------------------------------------------------------

def natSumUpTo : Nat -> (Nat -> Nat) -> Nat
  | 0, _ => 0
  | n + 1, f => natSumUpTo n f + f n

private theorem natSumUpTo_congr (n : Nat) (f g : Nat -> Nat)
    (heq : ∀ i : Nat, i < n -> f i = g i) :
    natSumUpTo n f = natSumUpTo n g := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    simp only [natSumUpTo, ih (fun i hi => heq i (by omega)), heq n' (Nat.lt_succ_self n')]

private theorem natSumUpTo_zero (n : Nat) (f : Nat -> Nat)
    (hz : ∀ i : Nat, i < n -> f i = 0) :
    natSumUpTo n f = 0 := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    simp only [natSumUpTo, ih (fun i hi => hz i (by omega)), hz n' (Nat.lt_succ_self n')]

private theorem natSumUpTo_mul_left (c n : Nat) (f : Nat -> Nat) :
    c * natSumUpTo n f = natSumUpTo n (fun i => c * f i) := by
  induction n with
  | zero => simp [natSumUpTo]
  | succ n' ih =>
    simp only [natSumUpTo, Nat.mul_add, ih]

private theorem natSumUpTo_add_split (a b : Nat) (f : Nat -> Nat) :
    natSumUpTo (a + b) f = natSumUpTo a f + natSumUpTo b (fun i => f (a + i)) := by
  induction b with
  | zero => simp [natSumUpTo]
  | succ b' ih =>
    rw [Nat.add_succ a b']
    simp only [natSumUpTo, ih, Nat.add_assoc]

private theorem natSumUpTo_add_fn (n : Nat) (f g : Nat -> Nat) :
    natSumUpTo n (fun i => f i + g i) = natSumUpTo n f + natSumUpTo n g := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    simp only [natSumUpTo, ih]
    omega

private theorem natSumUpTo_swap (m n : Nat) (F : Nat -> Nat -> Nat) :
    natSumUpTo m (fun i => natSumUpTo n (fun j => F i j)) =
      natSumUpTo n (fun j => natSumUpTo m (fun i => F i j)) := by
  induction m with
  | zero =>
    exact (natSumUpTo_zero n _ (fun _ _ => rfl)).symm
  | succ m' ih =>
    simp only [natSumUpTo]
    rw [ih, ← natSumUpTo_add_fn]

private theorem binom_mul_binom_sub :
    ∀ (x k m : Nat),
      laurentInterpBinom x k * laurentInterpBinom (x - k) m =
        laurentInterpBinom x (k + m) * laurentInterpBinom (k + m) k
  | 0, 0, 0 => rfl
  | 0, 0, _ + 1 => by simp [laurentInterpBinom]
  | 0, k + 1, m => by
    rw [laurentInterpBinom_gt_zero 0 (k + 1) (by omega),
        laurentInterpBinom_gt_zero 0 (k + 1 + m) (by omega)]
    simp
  | x + 1, 0, m => by
    simp [laurentInterpBinom_zero_right]
  | x + 1, k + 1, m => by
    rw [Nat.succ_sub_succ]
    by_cases hlt : x < k
    · rw [laurentInterpBinom_gt_zero (x + 1) (k + 1) (by omega),
          laurentInterpBinom_gt_zero (x + 1) (k + 1 + m) (by omega)]
      simp
    · by_cases heq : x = k
      · subst heq
        cases m with
        | zero =>
          rw [Nat.sub_self]
          simp [laurentInterpBinom_self]
        | succ m' =>
          rw [Nat.sub_self]
          change laurentInterpBinom (x + 1) (x + 1) * 0 = _
          rw [laurentInterpBinom_gt_zero (x + 1) (x + 1 + (m' + 1)) (by omega)]
          simp
      · have hgt : k + 1 ≤ x := by omega
        cases m with
        | zero =>
          simp [laurentInterpBinom_zero_right, laurentInterpBinom_self]
        | succ m' =>
          have hsub_succ : x - k = (x - (k + 1)) + 1 := by omega
          have h1 : laurentInterpBinom (x + 1) (k + 1) =
              laurentInterpBinom x k + laurentInterpBinom x (k + 1) := rfl
          have h2 : laurentInterpBinom (x - k) (m' + 1) =
              laurentInterpBinom (x - (k + 1)) m' + laurentInterpBinom (x - (k + 1)) (m' + 1) := by
            rw [hsub_succ]; rfl
          rw [h1, Nat.add_mul, binom_mul_binom_sub x k (m' + 1),
              h2, Nat.mul_add,
              binom_mul_binom_sub x (k + 1) m',
              binom_mul_binom_sub x (k + 1) (m' + 1)]
          have he1 : k + (m' + 1) = k + m' + 1 := by omega
          have he2 : k + 1 + m' = k + m' + 1 := by omega
          have he3 : k + 1 + (m' + 1) = (k + m' + 1) + 1 := by omega
          rw [he1, he2, he3]
          have hpas1 : laurentInterpBinom (k + m' + 1 + 1) (k + 1) =
              laurentInterpBinom (k + m' + 1) k + laurentInterpBinom (k + m' + 1) (k + 1) := rfl
          have hpas2 : laurentInterpBinom (x + 1) (k + m' + 1 + 1) =
              laurentInterpBinom x (k + m' + 1) + laurentInterpBinom x (k + m' + 1 + 1) := rfl
          rw [hpas2, Nat.add_mul, hpas1, Nat.mul_add, Nat.mul_add]
          omega

private theorem pow_one_add_eq_natSumUpTo (B : Nat) :
    ∀ y : Nat, (1 + B) ^ y = natSumUpTo (y + 1) (fun m => laurentInterpBinom y m * B ^ m)
  | 0 => by simp [natSumUpTo, laurentInterpBinom_zero_right]
  | y + 1 => by
    rw [Nat.pow_succ (1 + B) y, Nat.mul_add ((1 + B) ^ y) 1 B, Nat.mul_one,
        pow_one_add_eq_natSumUpTo B y]
    -- `B * ∑_{m=0}^y C(y, m) B^m = ∑_{m=0}^y C(y, m) B^(m+1)`:
    have hB_in : ∀ n : Nat,
        natSumUpTo n (fun m => laurentInterpBinom y m * B ^ m) * B =
          natSumUpTo n (fun m => laurentInterpBinom y m * B ^ (m + 1)) := by
      intro n; induction n with
      | zero => simp [natSumUpTo]
      | succ n' ih =>
        simp only [natSumUpTo, Nat.add_mul, ih, Nat.pow_succ, Nat.mul_assoc]
    rw [hB_in (y + 1)]
    -- Prove prefix identity for `k ≤ y + 1`:
    -- `natSumUpTo (k + 1) (fun m => C(y+1, m) B^m) = natSumUpTo (k + 1) (fun m => C(y, m) B^m) + natSumUpTo k (fun m => C(y, m) B^(m+1))`:
    have hpref : ∀ k : Nat,
        natSumUpTo (k + 1) (fun m => laurentInterpBinom (y + 1) m * B ^ m) =
          natSumUpTo (k + 1) (fun m => laurentInterpBinom y m * B ^ m) +
            natSumUpTo k (fun m => laurentInterpBinom y m * B ^ (m + 1)) := by
      intro k; induction k with
      | zero => simp [natSumUpTo, laurentInterpBinom_zero_right]
      | succ k' ih =>
        calc
          natSumUpTo (k' + 1 + 1) (fun m => laurentInterpBinom (y + 1) m * B ^ m)
              = natSumUpTo (k' + 1) (fun m => laurentInterpBinom (y + 1) m * B ^ m) +
                  (laurentInterpBinom y k' + laurentInterpBinom y (k' + 1)) * B ^ (k' + 1) := rfl
          _ = (natSumUpTo (k' + 1) (fun m => laurentInterpBinom y m * B ^ m) +
                natSumUpTo k' (fun m => laurentInterpBinom y m * B ^ (m + 1))) +
                (laurentInterpBinom y k' * B ^ (k' + 1) +
                  laurentInterpBinom y (k' + 1) * B ^ (k' + 1)) := by rw [ih, Nat.add_mul]
          _ = natSumUpTo (k' + 1 + 1) (fun m => laurentInterpBinom y m * B ^ m) +
                natSumUpTo (k' + 1) (fun m => laurentInterpBinom y m * B ^ (m + 1)) := by
                simp only [natSumUpTo]; omega
    rw [hpref (y + 1)]
    simp only [natSumUpTo, laurentInterpBinom_gt_zero y (y + 1) (Nat.lt_succ_self y),
               Nat.zero_mul, Nat.add_zero]

private theorem vandermondeSum_eq_natSumUpTo (a b t : Nat) :
    ∀ m : Nat, vandermondeSum a b t m =
      natSumUpTo m (fun s => laurentInterpBinom a s * laurentInterpBinom b (t - s))
  | 0 => rfl
  | m + 1 => by simp [vandermondeSum, natSumUpTo, vandermondeSum_eq_natSumUpTo a b t m]

def confluentTail (x T B s : Nat) : Nat :=
  natSumUpTo (x + 1) (fun q =>
    laurentInterpBinom x (T + q) * laurentInterpBinom q s * B ^ (q - s))

private theorem confluent_col_decomp (x T P B k : Nat)
    (h1B : 1 + B = P) (hk : k < T) :
    laurentInterpBinom x k * P ^ x =
      natSumUpTo T (fun t => P ^ k * laurentInterpBinom t k * B ^ (t - k) * laurentInterpBinom x t) +
      natSumUpTo k (fun s => P ^ k * laurentInterpBinom T (k - s) * B ^ (T - k + s) * confluentTail x T B s) +
      (P ^ k * B ^ T) * confluentTail x T B k := by
  have htail_zero_of_lt : x < T -> ∀ s : Nat, confluentTail x T B s = 0 := by
    intro hxT s
    unfold confluentTail
    apply natSumUpTo_zero
    intro q _
    rw [laurentInterpBinom_gt_zero x (T + q) (by omega), Nat.zero_mul, Nat.zero_mul]
  by_cases hxk : x < k
  · rw [laurentInterpBinom_gt_zero x k hxk, Nat.zero_mul]
    have hs1 : natSumUpTo T (fun t => P ^ k * laurentInterpBinom t k * B ^ (t - k) * laurentInterpBinom x t) = 0 := by
      apply natSumUpTo_zero; intro t _
      by_cases htk : t < k
      · rw [laurentInterpBinom_gt_zero t k htk]; simp
      · rw [laurentInterpBinom_gt_zero x t (by omega)]; simp
    have hs2 : natSumUpTo k (fun s => P ^ k * laurentInterpBinom T (k - s) * B ^ (T - k + s) * confluentTail x T B s) = 0 := by
      apply natSumUpTo_zero; intro s _
      rw [htail_zero_of_lt (by omega) s, Nat.mul_zero]
    rw [hs1, hs2, htail_zero_of_lt (by omega) k, Nat.mul_zero]
  · -- Now `k ≤ x`:
    have hpx : P ^ x = P ^ k * (1 + B) ^ (x - k) := by
      conv => lhs; rw [show x = k + (x - k) by omega, Nat.pow_add]
      rw [h1B]
    have hexp1 : laurentInterpBinom x k * P ^ x =
        P ^ k * natSumUpTo (x - k + 1)
          (fun m => laurentInterpBinom x (k + m) * laurentInterpBinom (k + m) k * B ^ m) := by
      rw [hpx, ← Nat.mul_assoc, Nat.mul_comm (laurentInterpBinom x k) (P ^ k),
          Nat.mul_assoc (P ^ k), pow_one_add_eq_natSumUpTo B (x - k),
          natSumUpTo_mul_left (laurentInterpBinom x k)]
      apply congrArg (P ^ k * ·)
      apply natSumUpTo_congr; intro m _
      rw [← Nat.mul_assoc, binom_mul_binom_sub x k m]
    rw [hexp1]
    by_cases hxT : x < T
    · -- `k ≤ x < T`: `confluentTail = 0`, and `natSumUpTo T` matches `m = t - k`:
      have hs2 : natSumUpTo k (fun s => P ^ k * laurentInterpBinom T (k - s) * B ^ (T - k + s) * confluentTail x T B s) = 0 := by
        apply natSumUpTo_zero; intro s _; rw [htail_zero_of_lt hxT s, Nat.mul_zero]
      rw [hs2, htail_zero_of_lt hxT k, Nat.mul_zero, Nat.add_zero, Nat.add_zero]
      rw [show T = k + ((x - k + 1) + (T - (x + 1))) by omega,
          natSumUpTo_add_split k, natSumUpTo_add_split (x - k + 1)]
      have hz_pre : natSumUpTo k (fun t => P ^ k * laurentInterpBinom t k * B ^ (t - k) * laurentInterpBinom x t) = 0 := by
        apply natSumUpTo_zero; intro t ht; rw [laurentInterpBinom_gt_zero t k ht]; simp
      have hz_post : natSumUpTo (T - (x + 1)) (fun i =>
          P ^ k * laurentInterpBinom (k + (x - k + 1 + i)) k *
            B ^ (k + (x - k + 1 + i) - k) * laurentInterpBinom x (k + (x - k + 1 + i))) = 0 := by
        apply natSumUpTo_zero; intro i _
        rw [laurentInterpBinom_gt_zero x (k + (x - k + 1 + i)) (by omega), Nat.mul_zero]
      rw [hz_pre, Nat.zero_add, hz_post, Nat.add_zero, natSumUpTo_mul_left (P ^ k)]
      apply natSumUpTo_congr; intro m _
      have hsub_m : k + m - k = m := by omega
      rw [hsub_m]
      ac_rfl
    · -- Main case `T ≤ x`: split `x - k + 1 = (T - k) + (x - T + 1)`:
      rw [show x - k + 1 = (T - k) + (x - T + 1) by omega,
          natSumUpTo_add_split (T - k), Nat.mul_add (P ^ k)]
      -- Part A: `P^k * natSumUpTo (T - k) ... = natSumUpTo T ...`:
      have hpartA : P ^ k * natSumUpTo (T - k)
            (fun m => laurentInterpBinom x (k + m) * laurentInterpBinom (k + m) k * B ^ m) =
          natSumUpTo T (fun t => P ^ k * laurentInterpBinom t k * B ^ (t - k) * laurentInterpBinom x t) := by
        rw [natSumUpTo_mul_left (P ^ k)]
        conv => rhs; rw [show T = k + (T - k) by omega, natSumUpTo_add_split k]
        have hz_pre : natSumUpTo k (fun t => P ^ k * laurentInterpBinom t k * B ^ (t - k) * laurentInterpBinom x t) = 0 := by
          apply natSumUpTo_zero; intro t ht; rw [laurentInterpBinom_gt_zero t k ht]; simp
        rw [hz_pre, Nat.zero_add]
        apply natSumUpTo_congr; intro m _
        rw [show k + m - k = m by omega]
        ac_rfl
      -- Part B: pad `x - T + 1` to `x + 1` (since `binom(x, T + q) = 0` for `q > x - T`), then Vandermonde + swap!
      have hpad : natSumUpTo (x - T + 1)
            (fun q => laurentInterpBinom x (k + (T - k + q)) * laurentInterpBinom (k + (T - k + q)) k * B ^ (T - k + q)) =
          natSumUpTo (x + 1)
            (fun q => laurentInterpBinom x (T + q) * laurentInterpBinom (q + T) k * B ^ (T - k + q)) := by
        conv => rhs; rw [show x + 1 = (x - T + 1) + T by omega, natSumUpTo_add_split (x - T + 1)]
        have hz_hi : natSumUpTo T (fun i =>
            laurentInterpBinom x (T + (x - T + 1 + i)) * laurentInterpBinom (x - T + 1 + i + T) k *
              B ^ (T - k + (x - T + 1 + i))) = 0 := by
          apply natSumUpTo_zero; intro i _
          rw [laurentInterpBinom_gt_zero x (T + (x - T + 1 + i)) (by omega)]; simp
        rw [hz_hi, Nat.add_zero]
        apply natSumUpTo_congr; intro q _
        have h1 : k + (T - k + q) = T + q := by omega
        have h2 : T + q = q + T := Nat.add_comm T q
        rw [h1]; conv => lhs; lhs; rhs; rw [h2]
      have hpartB : P ^ k * natSumUpTo (x + 1)
            (fun q => laurentInterpBinom x (T + q) * laurentInterpBinom (q + T) k * B ^ (T - k + q)) =
          natSumUpTo k (fun s => P ^ k * laurentInterpBinom T (k - s) * B ^ (T - k + s) * confluentTail x T B s) +
            (P ^ k * B ^ T) * confluentTail x T B k := by
        have hinner : ∀ q : Nat,
            laurentInterpBinom x (T + q) * laurentInterpBinom (q + T) k * B ^ (T - k + q) =
              natSumUpTo (k + 1) (fun s =>
                laurentInterpBinom T (k - s) * B ^ (T - k + s) *
                  (laurentInterpBinom x (T + q) * laurentInterpBinom q s * B ^ (q - s))) := by
          intro q
          rw [laurentInterpBinom_add q T k, vandermondeSum_eq_natSumUpTo q T k]
          -- Pull `laurentInterpBinom x (T + q)` inside and `B^(T - k + q)` inside:
          have hmul_r : ∀ n : Nat,
              laurentInterpBinom x (T + q) * natSumUpTo n (fun s => laurentInterpBinom q s * laurentInterpBinom T (k - s)) * B ^ (T - k + q) =
                natSumUpTo n (fun s =>
                  laurentInterpBinom x (T + q) * (laurentInterpBinom q s * laurentInterpBinom T (k - s)) * B ^ (T - k + q)) := by
            intro n; induction n with
            | zero => simp [natSumUpTo]
            | succ n' ih =>
              simp only [natSumUpTo, Nat.mul_add, Nat.add_mul, ih]
          rw [hmul_r (k + 1)]
          apply natSumUpTo_congr; intro s hs_lt
          by_cases hqs : q < s
          · rw [laurentInterpBinom_gt_zero q s hqs]; simp
          · have hpow_B : B ^ (T - k + q) = B ^ (T - k + s) * B ^ (q - s) := by
              rw [← Nat.pow_add, show (T - k + s) + (q - s) = T - k + q by omega]
            rw [hpow_B]
            ac_rfl
        have hrew : natSumUpTo (x + 1)
              (fun q => laurentInterpBinom x (T + q) * laurentInterpBinom (q + T) k * B ^ (T - k + q)) =
            natSumUpTo (k + 1) (fun s =>
              laurentInterpBinom T (k - s) * B ^ (T - k + s) * confluentTail x T B s) := by
          rw [natSumUpTo_congr (x + 1) _ _ (fun q _ => hinner q),
              natSumUpTo_swap (x + 1) (k + 1)]
          apply natSumUpTo_congr; intro s _
          rw [← natSumUpTo_mul_left (laurentInterpBinom T (k - s) * B ^ (T - k + s))]
          rfl
        rw [hrew, natSumUpTo_mul_left (P ^ k)]
        simp only [natSumUpTo]
        have htop : P ^ k * (laurentInterpBinom T (k - k) * B ^ (T - k + k) * confluentTail x T B k) =
            (P ^ k * B ^ T) * confluentTail x T B k := by
          rw [Nat.sub_self, laurentInterpBinom_zero_right, Nat.one_mul,
              show T - k + k = T by omega, Nat.mul_assoc]
        rw [htop]
        apply congrArg (· + (P ^ k * B ^ T) * confluentTail x T B k)
        apply natSumUpTo_congr; intro s _; ac_rfl
      rw [hpartA, hpad, hpartB, Nat.add_assoc]

def findIdxUBelow {L : Nat} (idxU : Nat -> Fin L) : Nat -> Fin L -> Option Nat
  | 0, _ => none
  | m + 1, j => if j = idxU m then some m else findIdxUBelow idxU m j

private theorem findIdxUBelow_hit {L : Nat} (idxU : Nat -> Fin L) (T : Nat)
    (hinj : ∀ t1 t2 : Nat, t1 < T -> t2 < T -> idxU t1 = idxU t2 -> t1 = t2) :
    ∀ (m s : Nat), m ≤ T -> s < m -> findIdxUBelow idxU m (idxU s) = some s
  | 0, _, _, hs => by omega
  | m + 1, s, hmT, hs => by
    unfold findIdxUBelow
    by_cases hsm : s = m
    · subst hsm; simp
    · have hne : idxU s ≠ idxU m := fun heq => hsm (hinj s m (by omega) (by omega) heq)
      rw [ite_false_of_w10 hne]
      exact findIdxUBelow_hit idxU T hinj m s (by omega) (by omega)

private theorem findIdxUBelow_miss {L : Nat} (idxU : Nat -> Fin L) :
    ∀ (m : Nat) (j : Fin L),
      (∀ s : Nat, s < m -> j ≠ idxU s) -> findIdxUBelow idxU m j = none
  | 0, _, _ => rfl
  | m + 1, j, hmiss => by
    unfold findIdxUBelow
    rw [ite_false_of_w10 (hmiss m (Nat.lt_succ_self m))]
    exact findIdxUBelow_miss idxU m j (fun s hs => hmiss s (by omega))

def triNumNat : Nat -> Nat
  | 0 => 0
  | m + 1 => triNumNat m + m

private theorem two_mul_triNumNat : ∀ m : Nat, 2 * triNumNat m = m * (m - 1)
  | 0 => rfl
  | m + 1 => by
    simp only [triNumNat, Nat.add_sub_cancel]
    have ih := two_mul_triNumNat m
    cases m with
    | zero => simp [triNumNat]
    | succ m' =>
      simp only [Nat.add_sub_cancel] at ih
      rw [Nat.mul_add 2 (triNumNat (m' + 1)) (m' + 1), ih]
      rw [Nat.mul_add (m' + 1 + 1) m' 1, Nat.add_mul (m' + 1) 1 m']
      omega

private theorem triNumNat_eq_div2 (m : Nat) : triNumNat m = m * (m - 1) / 2 := by
  rw [← two_mul_triNumNat m, Nat.mul_div_right _ (by decide : 0 < 2)]

def laurentColsRank2OrderT (T u : Nat) (j : Fin (2 * T)) : Nat × Nat :=
  if j.val < T then (j.val, 0) else (j.val - T, u)

/--
  Theorem W12.2a (`laurent_general_order_T_confluent_divisibility`,
  `zero custom axioms`):
  Universal Arbitrary-`T` Confluent `2^(T*(T-1)/2 * u) * (2^u - 1)^(T^2)` Zero-Gap Determinant
  Divisibility & `(2T) × (2T)` Rank-2 Two-Base Congruence (`Branch P3.3`):
  1. **Universal `L × L` Arbitrary-`T` Confluent Divisibility (`∀ W, K, L, T, u`, `T ≥ 1, u ≥ 1`)**:
     Whenever `idx0, idxU : Nat -> Fin L` index two disjoint injective `T`-blocks of columns
     `(t, 0)` and `(t, u)` (`0 ≤ t < T`) in ANY `L × L` zero-gap evaluation matrix `M0`:
       `((2 ^ ((T * (T - 1) / 2) * u) * (2 ^ u - 1) ^ (T * T) : Nat) : Int) ∣ intDet L M0`!
  2. **Canonical `(2T) × (2T)` Rank-2 Two-Base Specialization (`∀ W, K, T, u ≥ 1`, `3^W < 2^K`)**:
     On `M_W := laurentInterpMat W K (2 * T) rows (laurentColsRank2OrderT T (W * u))` and `M0` at `u`:
       `((2 ^ K - 3 ^ W : Nat) : Int) ∣ (intDet (2 * T) M_W - intDet (2 * T) M0)` AND
       `((2 ^ ((T * (T - 1) / 2) * u) * (2 ^ u - 1) ^ (T * T) : Nat) : Int) ∣ intDet (2 * T) M0`!
-/
theorem laurent_general_order_T_confluent_divisibility :
    (∀ (W K L T u : Nat) (rows cols : Fin L -> Nat × Nat) (idx0 idxU : Nat -> Fin L),
      T ≥ 1 -> u ≥ 1 ->
      (∀ t : Nat, t < T -> cols (idx0 t) = (t, 0)) ->
      (∀ t : Nat, t < T -> cols (idxU t) = (t, u)) ->
      (∀ t1 t2 : Nat, t1 < T -> t2 < T -> idxU t1 = idxU t2 -> t1 = t2) ->
      (∀ t1 t2 : Nat, t1 < T -> t2 < T -> idx0 t1 ≠ idxU t2) ->
      let M0 : Fin L -> Fin L -> Int := fun i j =>
        (laurentZeroGapIntEntry W K (rows i).1 (rows i).2 (cols j).1 (cols j).2 : Int)
      ((2 ^ ((T * (T - 1) / 2) * u) * (2 ^ u - 1) ^ (T * T) : Nat) : Int) ∣ intDet L M0) ∧
    (∀ (W K T u : Nat) (rows : Fin (2 * T) -> Nat × Nat),
      T ≥ 1 -> u ≥ 1 -> 3 ^ W < 2 ^ K ->
      let M_W := laurentInterpMat W K (2 * T) rows (laurentColsRank2OrderT T (W * u))
      let M0 : Fin (2 * T) -> Fin (2 * T) -> Int := fun i j =>
        (laurentZeroGapIntEntry W K (rows i).1 (rows i).2
          (laurentColsRank2OrderT T u j).1 (laurentColsRank2OrderT T u j).2 : Int)
      (((2 ^ K - 3 ^ W : Nat) : Int) ∣ (intDet (2 * T) M_W - intDet (2 * T) M0)) ∧
      (((2 ^ ((T * (T - 1) / 2) * u) * (2 ^ u - 1) ^ (T * T) : Nat) : Int) ∣ intDet (2 * T) M0)) := by
  have hgen : ∀ (W K L T u : Nat) (rows cols : Fin L -> Nat × Nat) (idx0 idxU : Nat -> Fin L),
      T ≥ 1 -> u ≥ 1 ->
      (∀ t : Nat, t < T -> cols (idx0 t) = (t, 0)) ->
      (∀ t : Nat, t < T -> cols (idxU t) = (t, u)) ->
      (∀ t1 t2 : Nat, t1 < T -> t2 < T -> idxU t1 = idxU t2 -> t1 = t2) ->
      (∀ t1 t2 : Nat, t1 < T -> t2 < T -> idx0 t1 ≠ idxU t2) ->
      let M0 : Fin L -> Fin L -> Int := fun i j =>
        (laurentZeroGapIntEntry W K (rows i).1 (rows i).2 (cols j).1 (cols j).2 : Int)
      ((2 ^ ((T * (T - 1) / 2) * u) * (2 ^ u - 1) ^ (T * T) : Nat) : Int) ∣ intDet L M0 := by
    intro W K L T u rows cols idx0 idxU _hT hu hc0 hcU hinjU hdisj
    dsimp only
    let M0 : Fin L -> Fin L -> Int := fun i j =>
      (laurentZeroGapIntEntry W K (rows i).1 (rows i).2 (cols j).1 (cols j).2 : Int)
    let P : Nat := 2 ^ u
    let B : Nat := P - 1
    have hP_ge2 : P ≥ 2 := by dsimp [P]; simpa using pow2_mono_nat hu
    have h1B : 1 + B = P := by dsimp [B]; omega
    let M_red : Nat -> Fin L -> Fin L -> Int := fun m i j =>
      match findIdxUBelow idxU m j with
      | some s => Int.ofNat (confluentTail ((rows i).1 * W + (rows i).2 * K) T B s)
      | none => M0 i j
    have hstep_all : ∀ m : Nat, m ≤ T ->
        intDet L M0 =
          Int.ofNat (2 ^ (triNumNat m * u) * B ^ (m * T)) * intDet L (M_red m) := by
      intro m hmT; induction m with
      | zero =>
        simp [triNumNat, M_red, findIdxUBelow]
      | succ k ih =>
        have hk_lt : k < T := hmT
        rw [ih (Nat.le_of_lt hmT)]
        let idxC : Nat -> Fin L := fun r => if r < T then idx0 r else idxU (r - T)
        let coefC : Nat -> Int := fun r =>
          if r < T then
            Int.ofNat (P ^ k * laurentInterpBinom r k * B ^ (r - k))
          else
            Int.ofNat (P ^ k * laurentInterpBinom T (k - (r - T)) * B ^ (T - k + (r - T)))
        have hneC : ∀ r : Nat, r < T + k -> idxC r ≠ idxU k := by
          intro r hr
          dsimp [idxC]
          by_cases hrT : r < T
          · rw [ite_true_of_w10 hrT]
            exact hdisj r k hrT hk_lt
          · rw [ite_false_of_w10 hrT]
            intro heq
            have hse := hinjU (r - T) k (by omega) hk_lt heq
            omega
        rw [intDet_sub_col_prefix_invariant L (idxU k) (M_red k) (T + k) idxC coefC hneC]
        -- Show the subtracted matrix equals `(if j = idxU k then Int.ofNat (P^k * B^T) * M_red (k+1) i j else M_red (k+1) i j)`:
        have hcol_eq :
            (fun i j : Fin L =>
              if j = idxU k then M_red k i (idxU k) - colPrefixComb (M_red k) idxC coefC i (T + k)
              else M_red k i j) =
            (fun i j : Fin L =>
              if j = idxU k then Int.ofNat (P ^ k * B ^ T) * M_red (k + 1) i (idxU k)
              else M_red (k + 1) i j) := by
          funext i j
          let x := (rows i).1 * W + (rows i).2 * K
          by_cases hjk : j = idxU k
          · subst hjk
            rw [ite_true_of_w10 rfl, ite_true_of_w10 rfl]
            -- Evaluate `M_red k i (idxU k)`:
            have hmiss_k : findIdxUBelow idxU k (idxU k) = none :=
              findIdxUBelow_miss idxU k (idxU k) (fun s hs heq => by
                have := hinjU k s hk_lt (by omega) heq; omega)
            have hMk_uk : M_red k i (idxU k) = Int.ofNat (laurentInterpBinom x k * P ^ x) := by
              dsimp only [M_red]; rw [hmiss_k]
              dsimp only [M0]; rw [hcU k hk_lt]
              unfold laurentZeroGapIntEntry; apply congrArg Int.ofNat
              change laurentInterpBinom x k * 2 ^ (x * u) = _
              rw [Nat.mul_comm x u, ← pow_pow_eq_mul_w5 2 u x]
            -- Evaluate `M_red (k + 1) i (idxU k)`:
            have hMk1_uk : M_red (k + 1) i (idxU k) = Int.ofNat (confluentTail x T B k) := by
              dsimp only [M_red, findIdxUBelow]; rw [ite_true_of_w10 rfl]
            -- Evaluate `colPrefixComb (M_red k) idxC coefC i (T + k)`:
            have hcomb_T : ∀ n : Nat, n ≤ T ->
                colPrefixComb (M_red k) idxC coefC i n =
                  Int.ofNat (natSumUpTo n (fun t =>
                    P ^ k * laurentInterpBinom t k * B ^ (t - k) * laurentInterpBinom x t)) := by
              intro n hn; induction n with
              | zero => rfl
              | succ n' ihn =>
                unfold colPrefixComb natSumUpTo
                rw [ihn (by omega)]
                have hn'_T : n' < T := hn
                have hi_n : idxC n' = idx0 n' := by dsimp [idxC]; rw [ite_true_of_w10 hn'_T]
                have hc_n : coefC n' = Int.ofNat (P ^ k * laurentInterpBinom n' k * B ^ (n' - k)) := by
                  dsimp [coefC]; rw [ite_true_of_w10 hn'_T]
                have hmiss0 : findIdxUBelow idxU k (idx0 n') = none :=
                  findIdxUBelow_miss idxU k (idx0 n') (fun s hs => hdisj n' s hn'_T (by omega))
                have hM_n : M_red k i (idx0 n') = Int.ofNat (laurentInterpBinom x n') := by
                  dsimp only [M_red]; rw [hmiss0]
                  dsimp only [M0]; rw [hc0 n' hn'_T]
                  unfold laurentZeroGapIntEntry
                  change Int.ofNat (laurentInterpBinom x n' * 2 ^ (x * 0)) = _
                  simp
                rw [hi_n, hc_n, hM_n]
                simp only [Int.ofNat_eq_natCast, ← Int.natCast_mul, ← Int.natCast_add]
            have hcomb_Tk : ∀ q : Nat, q ≤ k ->
                colPrefixComb (M_red k) idxC coefC i (T + q) =
                  Int.ofNat (natSumUpTo T (fun t =>
                    P ^ k * laurentInterpBinom t k * B ^ (t - k) * laurentInterpBinom x t) +
                    natSumUpTo q (fun s =>
                      P ^ k * laurentInterpBinom T (k - s) * B ^ (T - k + s) * confluentTail x T B s)) := by
              intro q hq; induction q with
              | zero =>
                rw [Nat.add_zero, hcomb_T T (Nat.le_refl T)]; rfl
              | succ s ihq =>
                rw [Nat.add_succ T s]
                unfold colPrefixComb
                rw [ihq (by omega)]
                have hs_k : s < k := hq
                have hnT : ¬ (T + s < T) := by omega
                have hsubT : T + s - T = s := by omega
                have hi_s : idxC (T + s) = idxU s := by
                  dsimp [idxC]; rw [ite_false_of_w10 hnT, hsubT]
                have hc_s : coefC (T + s) =
                    Int.ofNat (P ^ k * laurentInterpBinom T (k - s) * B ^ (T - k + s)) := by
                  dsimp [coefC]; rw [ite_false_of_w10 hnT, hsubT]
                have hhit_s : findIdxUBelow idxU k (idxU s) = some s :=
                  findIdxUBelow_hit idxU T hinjU k s (by omega) hs_k
                have hM_s : M_red k i (idxU s) = Int.ofNat (confluentTail x T B s) := by
                  dsimp only [M_red]; rw [hhit_s]
                rw [hi_s, hc_s, hM_s]
                simp only [natSumUpTo, Int.ofNat_eq_natCast, ← Int.natCast_mul, ← Int.natCast_add,
                           Nat.add_assoc]
            rw [hMk_uk, hMk1_uk, hcomb_Tk k (Nat.le_refl k),
                confluent_col_decomp x T P B k h1B hk_lt]
            simp only [Int.ofNat_eq_natCast, Int.natCast_add, Int.natCast_mul]
            omega
          · rw [ite_false_of_w10 hjk, ite_false_of_w10 hjk]
            dsimp only [M_red, findIdxUBelow]
            rw [ite_false_of_w10 hjk]
        rw [hcol_eq, intDet_col_scale (Int.ofNat (P ^ k * B ^ T)) L (idxU k) (M_red (k + 1))]
        -- Combine `2^(triNumNat k * u) * B^(k * T) * (P^k * B^T) = 2^(triNumNat (k + 1) * u) * B^((k + 1) * T)`:
        have hfac : (2 ^ (triNumNat k * u) * B ^ (k * T)) * (P ^ k * B ^ T) =
            2 ^ (triNumNat (k + 1) * u) * B ^ ((k + 1) * T) := by
          have hpk : P ^ k = 2 ^ (k * u) := by
            dsimp [P]; rw [pow_pow_eq_mul_w5 2 u k, Nat.mul_comm u k]
          have htri : triNumNat (k + 1) * u = triNumNat k * u + k * u :=
            Nat.add_mul (triNumNat k) k u
          have hbt : (k + 1) * T = k * T + T := by rw [Nat.add_mul, Nat.one_mul]
          rw [hpk, htri, hbt, Nat.pow_add 2, Nat.pow_add B]
          ac_rfl
        simp only [Int.ofNat_eq_natCast]
        rw [← Int.mul_assoc, ← Int.natCast_mul, hfac]
    refine ⟨intDet L (M_red T), ?_⟩
    rw [hstep_all T (Nat.le_refl T), triNumNat_eq_div2 T]
    rfl
  refine ⟨hgen, ?_⟩
  intro W K T u rows hT hu hgt
  dsimp only
  have hdvd_diff := (laurent_wdilated_zero_gap_entry_and_det_congruence.2
    W K (2 * T) rows (laurentColsRank2OrderT T u) hgt).1
  have hMW_eq : (fun i j : Fin (2 * T) =>
      (laurentInterpEntry W K (rows i).1 (rows i).2
        (laurentColsRank2OrderT T u j).1 (W * (laurentColsRank2OrderT T u j).2) : Int)) =
      laurentInterpMat W K (2 * T) rows (laurentColsRank2OrderT T (W * u)) := by
    funext i j
    unfold laurentInterpMat laurentColsRank2OrderT
    by_cases hlt : j.val < T
    · rw [ite_true_of_w10 hlt, ite_true_of_w10 hlt]; simp
    · rw [ite_false_of_w10 hlt, ite_false_of_w10 hlt]
  rw [hMW_eq] at hdvd_diff
  have hdvd_flip : ((2 ^ K - 3 ^ W : Nat) : Int) ∣
      (intDet (2 * T) (laurentInterpMat W K (2 * T) rows (laurentColsRank2OrderT T (W * u))) -
       intDet (2 * T) (fun i j =>
         (laurentZeroGapIntEntry W K (rows i).1 (rows i).2
           (laurentColsRank2OrderT T u j).1 (laurentColsRank2OrderT T u j).2 : Int))) := by
    rcases hdvd_diff with ⟨c, hc⟩
    exact ⟨-c, by rw [Int.mul_neg]; omega⟩
  let z0 : Fin (2 * T) := ⟨0, by omega⟩
  let idx0 : Nat -> Fin (2 * T) := fun t => if h : t < 2 * T then ⟨t, h⟩ else z0
  let idxU : Nat -> Fin (2 * T) := fun t => if h : T + t < 2 * T then ⟨T + t, h⟩ else z0
  refine ⟨hdvd_flip, hgen W K (2 * T) T u rows (laurentColsRank2OrderT T u) idx0 idxU hT hu ?_ ?_ ?_ ?_⟩
  · intro t ht
    have ht2 : t < 2 * T := by omega
    dsimp [idx0, laurentColsRank2OrderT]
    simp only [ht2, dite_true, ht, ite_true]
  · intro t ht
    have ht2 : T + t < 2 * T := by omega
    have hnot : ¬ (T + t < T) := by omega
    dsimp [idxU, laurentColsRank2OrderT]
    simp only [ht2, dite_true, hnot, ite_false]
    rw [show T + t - T = t by omega]
  · intro t1 t2 ht1 ht2 heq
    have h1 : T + t1 < 2 * T := by omega
    have h2 : T + t2 < 2 * T := by omega
    dsimp [idxU] at heq
    simp only [h1, h2, dite_true] at heq
    have hv := congrArg Fin.val heq; dsimp at hv; omega
  · intro t1 t2 ht1 ht2 heq
    have h1 : t1 < 2 * T := by omega
    have h2 : T + t2 < 2 * T := by omega
    dsimp [idx0, idxU] at heq
    simp only [h1, h2, dite_true] at heq
    have hv := congrArg Fin.val heq; dsimp at hv; omega

private theorem confluent_block_factor_from_untouched
    (L T v : Nat) (rowExp : Fin L -> Nat) (A : Fin L -> Fin L -> Int)
    (idx0 idxV : Nat -> Fin L)
    (_hT : T ≥ 1) (hv : v ≥ 1)
    (hA0 : ∀ (i : Fin L) (t : Nat), t < T -> A i (idx0 t) = Int.ofNat (laurentInterpBinom (rowExp i) t))
    (hAV : ∀ (i : Fin L) (t : Nat), t < T ->
      A i (idxV t) = Int.ofNat (laurentInterpBinom (rowExp i) t * 2 ^ (rowExp i * v)))
    (hinjV : ∀ t1 t2 : Nat, t1 < T -> t2 < T -> idxV t1 = idxV t2 -> t1 = t2)
    (hdisj : ∀ t1 t2 : Nat, t1 < T -> t2 < T -> idx0 t1 ≠ idxV t2) :
    ∃ A' : Fin L -> Fin L -> Int,
      (∀ (j : Fin L), (∀ t : Nat, t < T -> j ≠ idxV t) -> ∀ i : Fin L, A' i j = A i j) ∧
      intDet L A = Int.ofNat (2 ^ ((T * (T - 1) / 2) * v) * (2 ^ v - 1) ^ (T * T)) * intDet L A' := by
  let P : Nat := 2 ^ v
  let B : Nat := P - 1
  have hP_ge2 : P ≥ 2 := by dsimp [P]; simpa using pow2_mono_nat hv
  have h1B : 1 + B = P := by dsimp [B]; omega
  let A_red : Nat -> Fin L -> Fin L -> Int := fun m i j =>
    match findIdxUBelow idxV m j with
    | some s => Int.ofNat (confluentTail (rowExp i) T B s)
    | none => A i j
  have hstep_all : ∀ m : Nat, m ≤ T ->
      intDet L A =
        Int.ofNat (2 ^ (triNumNat m * v) * B ^ (m * T)) * intDet L (A_red m) := by
    intro m hmT; induction m with
    | zero => simp [triNumNat, A_red, findIdxUBelow]
    | succ k ih =>
      have hk_lt : k < T := hmT
      rw [ih (Nat.le_of_lt hmT)]
      let idxC : Nat -> Fin L := fun r => if r < T then idx0 r else idxV (r - T)
      let coefC : Nat -> Int := fun r =>
        if r < T then
          Int.ofNat (P ^ k * laurentInterpBinom r k * B ^ (r - k))
        else
          Int.ofNat (P ^ k * laurentInterpBinom T (k - (r - T)) * B ^ (T - k + (r - T)))
      have hneC : ∀ r : Nat, r < T + k -> idxC r ≠ idxV k := by
        intro r hr
        dsimp [idxC]
        by_cases hrT : r < T
        · rw [ite_true_of_w10 hrT]; exact hdisj r k hrT hk_lt
        · rw [ite_false_of_w10 hrT]
          intro heq
          have hse := hinjV (r - T) k (by omega) hk_lt heq
          omega
      rw [intDet_sub_col_prefix_invariant L (idxV k) (A_red k) (T + k) idxC coefC hneC]
      have hcol_eq :
          (fun i j : Fin L =>
            if j = idxV k then A_red k i (idxV k) - colPrefixComb (A_red k) idxC coefC i (T + k)
            else A_red k i j) =
          (fun i j : Fin L =>
            if j = idxV k then Int.ofNat (P ^ k * B ^ T) * A_red (k + 1) i (idxV k)
            else A_red (k + 1) i j) := by
        funext i j
        let x := rowExp i
        by_cases hjk : j = idxV k
        · subst hjk
          rw [ite_true_of_w10 rfl, ite_true_of_w10 rfl]
          have hmiss_k : findIdxUBelow idxV k (idxV k) = none :=
            findIdxUBelow_miss idxV k (idxV k) (fun s hs heq => by
              have := hinjV k s hk_lt (by omega) heq; omega)
          have hAk_vk : A_red k i (idxV k) = Int.ofNat (laurentInterpBinom x k * P ^ x) := by
            dsimp only [A_red]; rw [hmiss_k, hAV i k hk_lt]
            apply congrArg Int.ofNat
            change laurentInterpBinom x k * 2 ^ (x * v) = _
            rw [Nat.mul_comm x v, ← pow_pow_eq_mul_w5 2 v x]
          have hAk1_vk : A_red (k + 1) i (idxV k) = Int.ofNat (confluentTail x T B k) := by
            dsimp only [A_red, findIdxUBelow]; rw [ite_true_of_w10 rfl]
          have hcomb_T : ∀ n : Nat, n ≤ T ->
              colPrefixComb (A_red k) idxC coefC i n =
                Int.ofNat (natSumUpTo n (fun t =>
                  P ^ k * laurentInterpBinom t k * B ^ (t - k) * laurentInterpBinom x t)) := by
            intro n hn; induction n with
            | zero => rfl
            | succ n' ihn =>
              unfold colPrefixComb natSumUpTo
              rw [ihn (by omega)]
              have hn'_T : n' < T := hn
              have hi_n : idxC n' = idx0 n' := by dsimp [idxC]; rw [ite_true_of_w10 hn'_T]
              have hc_n : coefC n' = Int.ofNat (P ^ k * laurentInterpBinom n' k * B ^ (n' - k)) := by
                dsimp [coefC]; rw [ite_true_of_w10 hn'_T]
              have hmiss0 : findIdxUBelow idxV k (idx0 n') = none :=
                findIdxUBelow_miss idxV k (idx0 n') (fun s hs => hdisj n' s hn'_T (by omega))
              have hA_n : A_red k i (idx0 n') = Int.ofNat (laurentInterpBinom x n') := by
                dsimp only [A_red]; rw [hmiss0, hA0 i n' hn'_T]
              rw [hi_n, hc_n, hA_n]
              simp only [Int.ofNat_eq_natCast, ← Int.natCast_mul, ← Int.natCast_add]
          have hcomb_Tk : ∀ q : Nat, q ≤ k ->
              colPrefixComb (A_red k) idxC coefC i (T + q) =
                Int.ofNat (natSumUpTo T (fun t =>
                  P ^ k * laurentInterpBinom t k * B ^ (t - k) * laurentInterpBinom x t) +
                  natSumUpTo q (fun s =>
                    P ^ k * laurentInterpBinom T (k - s) * B ^ (T - k + s) * confluentTail x T B s)) := by
            intro q hq; induction q with
            | zero => rw [Nat.add_zero, hcomb_T T (Nat.le_refl T)]; rfl
            | succ s ihq =>
              rw [Nat.add_succ T s]
              unfold colPrefixComb
              rw [ihq (by omega)]
              have hs_k : s < k := hq
              have hnT : ¬ (T + s < T) := by omega
              have hsubT : T + s - T = s := by omega
              have hi_s : idxC (T + s) = idxV s := by
                dsimp [idxC]; rw [ite_false_of_w10 hnT, hsubT]
              have hc_s : coefC (T + s) =
                  Int.ofNat (P ^ k * laurentInterpBinom T (k - s) * B ^ (T - k + s)) := by
                dsimp [coefC]; rw [ite_false_of_w10 hnT, hsubT]
              have hhit_s : findIdxUBelow idxV k (idxV s) = some s :=
                findIdxUBelow_hit idxV T hinjV k s (by omega) hs_k
              have hA_s : A_red k i (idxV s) = Int.ofNat (confluentTail x T B s) := by
                dsimp only [A_red]; rw [hhit_s]
              rw [hi_s, hc_s, hA_s]
              simp only [natSumUpTo, Int.ofNat_eq_natCast, ← Int.natCast_mul, ← Int.natCast_add,
                         Nat.add_assoc]
          rw [hAk_vk, hAk1_vk, hcomb_Tk k (Nat.le_refl k),
              confluent_col_decomp x T P B k h1B hk_lt]
          simp only [Int.ofNat_eq_natCast, Int.natCast_add, Int.natCast_mul]
          omega
        · rw [ite_false_of_w10 hjk, ite_false_of_w10 hjk]
          dsimp only [A_red, findIdxUBelow]
          rw [ite_false_of_w10 hjk]
      rw [hcol_eq, intDet_col_scale (Int.ofNat (P ^ k * B ^ T)) L (idxV k) (A_red (k + 1))]
      have hfac : (2 ^ (triNumNat k * v) * B ^ (k * T)) * (P ^ k * B ^ T) =
          2 ^ (triNumNat (k + 1) * v) * B ^ ((k + 1) * T) := by
        have hpk : P ^ k = 2 ^ (k * v) := by
          dsimp [P]; rw [pow_pow_eq_mul_w5 2 v k, Nat.mul_comm v k]
        have htri : triNumNat (k + 1) * v = triNumNat k * v + k * v :=
          Nat.add_mul (triNumNat k) k v
        have hbt : (k + 1) * T = k * T + T := by rw [Nat.add_mul, Nat.one_mul]
        rw [hpk, htri, hbt, Nat.pow_add 2, Nat.pow_add B]
        ac_rfl
      simp only [Int.ofNat_eq_natCast]
      rw [← Int.mul_assoc, ← Int.natCast_mul, hfac]
  refine ⟨A_red T, ?_, ?_⟩
  · intro j hmiss i
    dsimp only [A_red]
    rw [findIdxUBelow_miss idxV T j hmiss]
  · rw [hstep_all T (Nat.le_refl T), triNumNat_eq_div2 T]

-- ----------------------------------------------------------------------------
-- Section 2B: Universal `4 × 4` Multi-`u` Zero-Multiplicity `≤ 1` (`∀ 1 ≤ u1 < u2`)
-- ----------------------------------------------------------------------------

/--
  Theorem W12.2b (`laurent_4x4_multi_u_zero_multiplicity_le_one`,
  `zero custom axioms`):
  Universal `4 × 4` Two-Base `(T = 2, U = 2)` Multi-`u` Zero-Multiplicity Ceiling `≤ 1` (`Branch P3.3`):
  1. **Universal At-Most-One-Zero Theorem (`∀ W, K ≥ 1`, `∀ 1 ≤ u1 < u2`)**:
     For EVERY pair of positive dimensions `W ≥ 1, K ≥ 1` (EVEN WITHOUT `3^W < 2^K`!) and EVERY
     pair of distinct positive shifts `1 ≤ u1 < u2`:
       `¬ (intDet 4 (laurentTwoBaseMat4 W K u1) = 0 ∧ intDet 4 (laurentTwoBaseMat4 W K u2) = 0)`!
  2. **Sharpness Certificate (`(W, K) = (9, 16)`, `u1 = 2` vs `u2 = 4`)**:
     `intDet 4 (laurentTwoBaseMat4 9 16 2) = 0` while `intDet 4 (laurentTwoBaseMat4 9 16 4) = 3628800 > 0`!
-/
theorem laurent_4x4_multi_u_zero_multiplicity_le_one :
    (∀ (W K u1 u2 : Nat),
      W ≥ 1 -> K ≥ 1 -> 1 ≤ u1 -> u1 < u2 ->
      ¬ (intDet 4 (laurentTwoBaseMat4 W K u1) = 0 ∧
         intDet 4 (laurentTwoBaseMat4 W K u2) = 0)) ∧
    (intDet 4 (laurentTwoBaseMat4 9 16 2) = 0 ∧
     intDet 4 (laurentTwoBaseMat4 9 16 4) = 3628800) := by
  refine ⟨?_, ⟨by decide, by decide⟩⟩
  intro W K u1 u2 hW hK hu1 hu_lt ⟨hz1, hz2⟩
  rcases laurent_4x4_confluent_and_twobase_nonvanishing with ⟨_, _, hclosed, _, hodd_nz, _⟩
  -- Both `u1` and `u2` must be even (`u1 = 2 * m1`, `u2 = 2 * m2`, `1 ≤ m1 < m2`):
  have hev_of_zero : ∀ u : Nat, u ≥ 1 -> intDet 4 (laurentTwoBaseMat4 W K u) = 0 ->
      ∃ m : Nat, m ≥ 1 ∧ u = 2 * m ∧
        W * (2 ^ m * (9 ^ m - 1)) = K * (3 ^ m * (4 ^ m - 1)) := by
    intro u hu hz
    by_cases hodd : u % 2 = 1
    · have hu_o : u = 2 * (u / 2) + 1 := by omega
      rw [hu_o] at hz
      exact False.elim (hodd_nz W K (u / 2) hW hK hz)
    · let m := u / 2
      have hm1 : m ≥ 1 := by dsimp [m]; omega
      have hu_ev : u = 2 * m := by dsimp [m]; omega
      have hd := hclosed W K u
      rw [hz, hu_ev] at hd
      -- `0 = (W^2 * 2^(2m) * (3^(2m) - 1)^2 : Int) - (K^2 * 3^(2m) * (2^(2m) - 1)^2 : Int)`
      have hsq_nat : W ^ 2 * 2 ^ (2 * m) * (3 ^ (2 * m) - 1) ^ 2 =
          K ^ 2 * 3 ^ (2 * m) * (2 ^ (2 * m) - 1) ^ 2 := by omega
      have hp9 : 3 ^ (2 * m) = 9 ^ m := (pow_pow_eq_mul_w5 3 2 m).symm
      have hp4 : 2 ^ (2 * m) = 4 ^ m := (pow_pow_eq_mul_w5 2 2 m).symm
      let L := W * (2 ^ m * (9 ^ m - 1))
      let R := K * (3 ^ m * (4 ^ m - 1))
      have hL_sq : L * L = W ^ 2 * 2 ^ (2 * m) * (3 ^ (2 * m) - 1) ^ 2 := by
        dsimp [L]
        have h22 : 2 ^ m * 2 ^ m = 2 ^ (2 * m) := by rw [← Nat.pow_add, ← Nat.two_mul]
        rw [hp9, Nat.pow_two W, Nat.pow_two (9 ^ m - 1), ← h22]
        ac_rfl
      have hR_sq : R * R = K ^ 2 * 3 ^ (2 * m) * (2 ^ (2 * m) - 1) ^ 2 := by
        dsimp [R]
        have h33 : 3 ^ m * 3 ^ m = 3 ^ (2 * m) := by rw [← Nat.pow_add, ← Nat.two_mul]
        rw [hp4, Nat.pow_two K, Nat.pow_two (4 ^ m - 1), ← h33]
        ac_rfl
      have heq_sq : L * L = R * R := by rw [hL_sq, hR_sq, hsq_nat]
      have hLR : L = R := by
        by_cases hlt : L < R
        · exfalso
          have h1 := Nat.mul_le_mul_right L (Nat.le_of_lt hlt)
          have h2 := Nat.mul_lt_mul_of_pos_left hlt (by omega : 0 < R)
          omega
        · by_cases hgt : R < L
          · exfalso
            have h1 := Nat.mul_le_mul_right R (Nat.le_of_lt hgt)
            have h2 := Nat.mul_lt_mul_of_pos_left hgt (by omega : 0 < L)
            omega
          · omega
      exact ⟨m, hm1, hu_ev, hLR⟩
  rcases hev_of_zero u1 hu1 hz1 with ⟨m1, hm1, hu1_eq, heq1⟩
  rcases hev_of_zero u2 (by omega) hz2 with ⟨m2, _, hu2_eq, heq2⟩
  have hm_lt : m1 < m2 := by omega
  let seqA : Nat -> Nat := fun m => 2 ^ m * (9 ^ m - 1)
  let seqB : Nat -> Nat := fun m => 3 ^ m * (4 ^ m - 1)
  have hseq_pos : ∀ m : Nat, m ≥ 1 -> seqA m ≥ 1 ∧ seqB m ≥ 1 := by
    intro m hm
    have hp2 := nat_pow_pos_of_pos 2 (by decide) m
    have hp3 := nat_pow_pos_of_pos 3 (by decide) m
    have hp9 : 9 ^ m ≥ 9 := by
      simpa using nat_pow_mono_exp_pos 9 1 m (by decide) hm
    have hp4 : 4 ^ m ≥ 4 := by
      simpa using nat_pow_mono_exp_pos 4 1 m (by decide) hm
    have hA1 := Nat.mul_le_mul hp2 (by omega : 1 ≤ 9 ^ m - 1)
    have hB1 := Nat.mul_le_mul hp3 (by omega : 1 ≤ 4 ^ m - 1)
    exact ⟨by dsimp [seqA]; omega, by dsimp [seqB]; omega⟩
  -- Adjacent strict inequality `seqA m * seqB (m + 1) < seqA (m + 1) * seqB m` for all `m ≥ 1`:
  have hstep_lt : ∀ m : Nat, m ≥ 1 -> seqA m * seqB (m + 1) < seqA (m + 1) * seqB m := by
    intro m hm
    let A := 9 ^ m
    let B := 4 ^ m
    have hA9 : A ≥ 9 := by dsimp [A]; simpa using nat_pow_mono_exp_pos 9 1 m (by decide) hm
    have hB4 : B ≥ 4 := by dsimp [B]; simpa using nat_pow_mono_exp_pos 4 1 m (by decide) hm
    have core_lt : 3 * (A - 1) * (4 * B - 1) < 2 * (9 * A - 1) * (B - 1) := by
      -- Prove via `A = a + 9`, `B = b + 4`:
      let a := A - 9
      let b := B - 4
      have hA_eq : A = a + 9 := by omega
      have hB_eq : B = b + 4 := by omega
      have h1 : A - 1 = a + 8 := by omega
      have h2 : 4 * B - 1 = 4 * b + 15 := by omega
      have h3 : 9 * A - 1 = 9 * a + 80 := by omega
      have h4 : B - 1 = b + 3 := by omega
      rw [h1, h2, h3, h4]
      -- LHS = `(3*a + 24)*(4*b + 15) = 12*a*b + 45*a + 96*b + 360`
      -- RHS = `(18*a + 160)*(b + 3) = 18*a*b + 54*a + 160*b + 480`
      have hl : 3 * (a + 8) * (4 * b + 15) = 12 * (a * b) + 45 * a + 96 * b + 360 := by
        rw [Nat.mul_add 3 a 8, Nat.add_mul, Nat.mul_add, Nat.mul_add]
        have : 3 * a * (4 * b) = 12 * (a * b) := by ac_rfl
        omega
      have hr : 2 * (9 * a + 80) * (b + 3) = 18 * (a * b) + 54 * a + 160 * b + 480 := by
        rw [Nat.mul_add 2 (9 * a) 80, Nat.add_mul, Nat.mul_add, Nat.mul_add]
        have : 2 * (9 * a) * b = 18 * (a * b) := by ac_rfl
        omega
      rw [hl, hr]
      omega
    have hfacL : seqA m * seqB (m + 1) = (2 ^ m * 3 ^ m) * (3 * (A - 1) * (4 * B - 1)) := by
      dsimp [seqA, seqB, A, B]
      rw [Nat.pow_succ 3 m, Nat.pow_succ 4 m, Nat.mul_comm (4 ^ m) 4]
      ac_rfl
    have hfacR : seqA (m + 1) * seqB m = (2 ^ m * 3 ^ m) * (2 * (9 * A - 1) * (B - 1)) := by
      dsimp [seqA, seqB, A, B]
      rw [Nat.pow_succ 2 m, Nat.pow_succ 9 m, Nat.mul_comm (9 ^ m) 9]
      ac_rfl
    have hp23 : 0 < 2 ^ m * 3 ^ m := by
      have hp2 := nat_pow_pos_of_pos 2 (by decide) m
      have hp3 := nat_pow_pos_of_pos 3 (by decide) m
      have hm_p := Nat.mul_le_mul hp2 hp3
      omega
    rw [hfacL, hfacR]
    exact Nat.mul_lt_mul_of_pos_left core_lt hp23
  -- Extend from `m -> m + 1` to `m1 < m2` (`m2 = m1 + (d + 1)`):
  have hlt_any : ∀ d : Nat, seqA m1 * seqB (m1 + (d + 1)) < seqA (m1 + (d + 1)) * seqB m1 := by
    intro d; induction d with
    | zero => simpa using hstep_lt m1 hm1
    | succ d' ih =>
      let cur := m1 + (d' + 1)
      have hcur1 : cur ≥ 1 := by dsimp [cur]; omega
      have hst := hstep_lt cur hcur1
      rcases hseq_pos cur hcur1 with ⟨hAc, hBc⟩
      have hm1_lt : (seqA m1 * seqB cur) * seqB (cur + 1) < (seqA cur * seqB m1) * seqB (cur + 1) :=
        Nat.mul_lt_mul_of_pos_right ih (hseq_pos (cur + 1) (by omega)).2
      have hm2_lt : seqA cur * (seqB (cur + 1) * seqB m1) < seqA (cur + 1) * (seqB cur * seqB m1) := by
        have h := Nat.mul_lt_mul_of_pos_right hst (hseq_pos m1 hm1).2
        simpa [Nat.mul_assoc] using h
      have hmid : (seqA cur * seqB m1) * seqB (cur + 1) = seqA cur * (seqB (cur + 1) * seqB m1) := by ac_rfl
      have hcomb : (seqA m1 * seqB (cur + 1)) * seqB cur < (seqA (cur + 1) * seqB m1) * seqB cur := by
        calc
          (seqA m1 * seqB (cur + 1)) * seqB cur
              = (seqA m1 * seqB cur) * seqB (cur + 1) := by ac_rfl
          _ < (seqA cur * seqB m1) * seqB (cur + 1) := hm1_lt
          _ = seqA cur * (seqB (cur + 1) * seqB m1) := hmid
          _ < seqA (cur + 1) * (seqB cur * seqB m1) := hm2_lt
          _ = (seqA (cur + 1) * seqB m1) * seqB cur := by ac_rfl
      by_cases hgoal : seqA m1 * seqB (cur + 1) < seqA (cur + 1) * seqB m1
      · simpa [cur, Nat.add_assoc] using hgoal
      · exfalso
        have hge : seqA (cur + 1) * seqB m1 ≤ seqA m1 * seqB (cur + 1) := by omega
        have hle := Nat.mul_le_mul_right (seqB cur) hge
        exact absurd hcomb (Nat.not_lt_of_ge hle)
  have hstrict_12 : seqA m1 * seqB m2 < seqA m2 * seqB m1 := by
    have hd := hlt_any (m2 - m1 - 1)
    rwa [show m1 + (m2 - m1 - 1 + 1) = m2 by omega] at hd
  -- Yet `W * seqA m1 = K * seqB m1` and `W * seqA m2 = K * seqB m2`:
  change W * seqA m1 = K * seqB m1 at heq1
  change W * seqA m2 = K * seqB m2 at heq2
  have hcross : (W * K) * (seqA m1 * seqB m2) = (W * K) * (seqA m2 * seqB m1) := by
    calc
      (W * K) * (seqA m1 * seqB m2) = (W * seqA m1) * (K * seqB m2) := by ac_rfl
      _ = (K * seqB m1) * (W * seqA m2) := by rw [heq1, ← heq2]
      _ = (W * K) * (seqA m2 * seqB m1) := by ac_rfl
  have hWK_pos : 0 < W * K := by have := Nat.mul_le_mul hW hK; omega
  have hcross_lt := Nat.mul_lt_mul_of_pos_left hstrict_12 hWK_pos
  omega

-- ----------------------------------------------------------------------------
-- Section 2C: Rank-3 `9 × 9` `(T = 3, U = 3)` Closed Form, `P^1(F_61)` Universal
--             Non-Vanishing, `2^569 < 3^359` Cone Positivity, & `(1, 3, 1)` Sign-Flip
-- ----------------------------------------------------------------------------

private theorem intDet_pivot_row0 (L : Nat) (B : Fin (L + 1) -> Fin (L + 1) -> Int)
    (p : Fin (L + 1)) (hp : B ⟨0, Nat.zero_lt_succ L⟩ p = 1) :
    intDet (L + 1) B =
      (if p.val % 2 = 0 then (1 : Int) else -1) *
        intDet L (intSubMat (fun i j =>
          if j = p then B i j else B i j - B ⟨0, Nat.zero_lt_succ L⟩ j * B i p) p) := by
  let z0 : Fin (L + 1) := ⟨0, Nat.zero_lt_succ L⟩
  have hcol : ∀ (M_cur : Fin (L + 1) -> Fin (L + 1) -> Int) (c : Fin (L + 1)),
      c ≠ p ->
      (∀ i : Fin (L + 1), M_cur i p = B i p) ->
      intDet (L + 1) M_cur = intDet (L + 1) (fun i j =>
        if j = c then M_cur i c - B z0 c * B i p else M_cur i j) := by
    intro M_cur c hc hpeq
    let idx_p : Nat -> Fin (L + 1) := fun _ => p
    let coef_p : Nat -> Int := fun _ => B z0 c
    have hs := intDet_sub_col_prefix_invariant (L + 1) c M_cur 1 idx_p coef_p
      (fun s hs => by rw [show s = 0 by omega]; exact hc.symm)
    rw [hs]; congr 1; funext i j
    simp [colPrefixComb, idx_p, coef_p, hpeq i]
  have hstep_lt : ∀ k : Nat, k ≤ L + 1 ->
      intDet (L + 1) B = intDet (L + 1) (fun i j =>
        if j.val < k ∧ j ≠ p then B i j - B z0 j * B i p else B i j) := by
    intro k hk; induction k with
    | zero =>
      apply congrArg (intDet (L + 1)); funext i j
      have hf : ¬ (j.val < 0 ∧ j ≠ p) := fun h => by omega
      rw [ite_false_of_w10 hf]
    | succ k' ih =>
      rw [ih (Nat.le_of_lt hk)]
      let M_k : Fin (L + 1) -> Fin (L + 1) -> Int := fun i j =>
        if j.val < k' ∧ j ≠ p then B i j - B z0 j * B i p else B i j
      change intDet (L + 1) M_k = _
      by_cases hkp : k' = p.val
      · congr 1; funext i j
        dsimp [M_k]
        by_cases hjp : j = p
        · have hf1 : ¬ (j.val < k' ∧ j ≠ p) := fun h => h.2 hjp
          have hf2 : ¬ (j.val < k' + 1 ∧ j ≠ p) := fun h => h.2 hjp
          rw [ite_false_of_w10 hf1, ite_false_of_w10 hf2]
        · have hjv : j.val ≠ k' := fun hv => hjp (Fin.ext (hv.trans hkp))
          by_cases hlt : j.val < k'
          · rw [ite_true_of_w10 ⟨hlt, hjp⟩, ite_true_of_w10 ⟨by omega, hjp⟩]
          · rw [ite_false_of_w10 (fun h => hlt h.1), ite_false_of_w10 (fun h => by have := h.1; omega)]
      · let c : Fin (L + 1) := ⟨k', hk⟩
        have hcp : c ≠ p := fun h => hkp (congrArg Fin.val h)
        have hMp : ∀ i : Fin (L + 1), M_k i p = B i p := by
          intro i; dsimp [M_k]; rw [ite_false_of_w10 (fun h => h.2 rfl)]
        rw [hcol M_k c hcp hMp]
        congr 1; funext i j
        by_cases hjc : j = c
        · rw [ite_true_of_w10 hjc, hjc]
          have h1 : ¬ (c.val < k' ∧ c ≠ p) := by dsimp [c]; omega
          have h2 : c.val < k' + 1 ∧ c ≠ p := ⟨by dsimp [c]; omega, hcp⟩
          dsimp [M_k]; rw [ite_false_of_w10 h1, ite_true_of_w10 h2]
        · rw [ite_false_of_w10 hjc]
          have hjv_ne : j.val ≠ k' := fun hv => hjc (Fin.ext hv)
          dsimp [M_k]
          by_cases hlt : j.val < k' ∧ j ≠ p
          · rw [ite_true_of_w10 hlt, ite_true_of_w10 ⟨by omega, hlt.2⟩]
          · rw [ite_false_of_w10 hlt, ite_false_of_w10 (fun h => hlt ⟨by omega, h.2⟩)]
  let B_flat : Fin (L + 1) -> Fin (L + 1) -> Int := fun i j =>
    if j = p then B i j else B i j - B z0 j * B i p
  have hflat : intDet (L + 1) B = intDet (L + 1) B_flat := by
    rw [hstep_lt (L + 1) (Nat.le_refl _)]
    congr 1; funext i j
    dsimp [B_flat]
    by_cases hjp : j = p
    · rw [ite_false_of_w10 (fun h => h.2 hjp), ite_true_of_w10 hjp]
    · rw [ite_true_of_w10 ⟨j.isLt, hjp⟩, ite_false_of_w10 hjp]
  rw [hflat, intDet_succ_single_row0 L B_flat p]
  · have h0p : B_flat z0 p = 1 := by dsimp [B_flat]; rw [ite_true_of_w10 rfl, hp]
    rw [h0p, Int.mul_one]
  · intro j hjp
    dsimp [B_flat, z0] at *
    rw [ite_false_of_w10 hjp, hp, Int.mul_one, Int.sub_self]

def laurentRowsTwoBase9 (i : Fin 9) : Nat × Nat :=
  if i.val = 0 then (0, 0)
  else if i.val = 1 then (1, 0)
  else if i.val = 2 then (2, 0)
  else if i.val = 3 then (0, 1)
  else if i.val = 4 then (1, 1)
  else if i.val = 5 then (2, 1)
  else if i.val = 6 then (0, 2)
  else if i.val = 7 then (1, 2)
  else (2, 2)

def laurentColsC33_9 (u : Nat) (j : Fin 9) : Nat × Nat :=
  if j.val = 0 then (0, 0)
  else if j.val = 1 then (1, 0)
  else if j.val = 2 then (2, 0)
  else if j.val = 3 then (0, u)
  else if j.val = 4 then (1, u)
  else if j.val = 5 then (2, u)
  else if j.val = 6 then (0, 2 * u)
  else if j.val = 7 then (1, 2 * u)
  else (2, 2 * u)

def laurentTwoBaseT3U3Mat9 (W K u : Nat) : Fin 9 -> Fin 9 -> Int :=
  laurentInterpMat W K 9 laurentRowsTwoBase9 (laurentColsC33_9 u)

def p9PosNat (W K : Nat) : Nat :=
  2097152 * W ^ 9 + 8974080 * W ^ 6 * K ^ 3 + 4121712 * W ^ 4 * K ^ 5 + 647136 * W ^ 2 * K ^ 7

def p9NegNat (W K : Nat) : Nat :=
  7279104 * W ^ 7 * K ^ 2 + 5968128 * W ^ 5 * K ^ 4 + 2404800 * W ^ 3 * K ^ 6 + 19683 * K ^ 9

def p9PolyInt (W K : Nat) : Int :=
  (p9PosNat W K : Int) - (p9NegNat W K : Int)

def p9Expr (W K : Expr4) : Expr4 :=
  let tpos := Expr4.add
    (.add (.mul (.const 2097152) (expr4Pow W 9))
          (.mul (.const 8974080) (.mul (expr4Pow W 6) (expr4Pow K 3))))
    (.add (.mul (.const 4121712) (.mul (expr4Pow W 4) (expr4Pow K 5)))
          (.mul (.const 647136) (.mul (expr4Pow W 2) (expr4Pow K 7))))
  let tneg := Expr4.add
    (.add (.mul (.const 7279104) (.mul (expr4Pow W 7) (expr4Pow K 2)))
          (.mul (.const 5968128) (.mul (expr4Pow W 5) (expr4Pow K 4))))
    (.add (.mul (.const 2404800) (.mul (expr4Pow W 3) (expr4Pow K 6)))
          (.mul (.const 19683) (expr4Pow K 9)))
  .sub tpos tneg

-- Symbolic `9 × 9 -> 8 × 8 -> 7 × 7` Expr4 reduction at `u = 1` (`8 * intDet 9 = intDet 7 = 1728 * P_9`):
def t3u3ScaledExprMat9 (i j : Fin 9) : Expr4 :=
  let rs := laurentRowsTwoBase9 i
  let r := rs.1
  let s := rs.2
  let n : Expr4 := .add (.mul (.const (r : Int)) .v0) (.mul (.const (s : Int)) .v1)
  let pq1 : Int := ((2 ^ r * 3 ^ s : Nat) : Int)
  let pq2 : Int := pq1 * pq1
  let b2 : Expr4 := .mul n (.sub n (.const 1))
  if j.val = 0 then .const 1
  else if j.val = 1 then n
  else if j.val = 2 then b2
  else if j.val = 3 then .const pq1
  else if j.val = 4 then .mul (.const pq1) n
  else if j.val = 5 then .mul (.const pq1) b2
  else if j.val = 6 then .const pq2
  else if j.val = 7 then .mul (.const pq2) n
  else .mul (.const pq2) b2

def t3u3ReducedExprMat8 (i j : Fin 8) : Expr4 :=
  let r9 : Fin 9 := ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
  let c9 : Fin 9 := ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
  if j.val = 2 || j.val = 5 then
    .sub (t3u3ScaledExprMat9 r9 c9) (.const 1)
  else
    t3u3ScaledExprMat9 r9 c9

def t3u3ReducedExprMat7 (i j : Fin 7) : Expr4 :=
  let r8 : Fin 8 := ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
  let c8 : Fin 8 := skipFinIdx ⟨2, by decide⟩ j
  .sub (t3u3ReducedExprMat8 r8 c8)
       (.mul (t3u3ReducedExprMat8 ⟨0, by decide⟩ c8) (t3u3ReducedExprMat8 r8 ⟨2, by decide⟩))

private def t3u3MinorTerm7 (j : Fin 7) : List Mono4 :=
  let P : Fin 7 -> Fin 7 -> List Mono4 := fun r c => normExpr4 (t3u3ReducedExprMat7 r c)
  match P ⟨0, Nat.zero_lt_succ 6⟩ j with
  | [] => []
  | p0j =>
    let signed := if j.val % 2 = 0 then p0j else negPoly4 p0j
    mulPoly4 signed (poly4Det 6 (poly4SubMat P j))

set_option maxRecDepth 32768 in
private theorem t3u3_term7_0 :
    t3u3MinorTerm7 ⟨0, by decide⟩ =
      [(1, 7, 0, 0, 5668704), (1, 8, 0, 0, -17006112), (2, 6, 0, 0, -430821504),
       (2, 7, 0, 0, 491287680), (3, 5, 0, 0, 2163625344), (3, 6, 0, 0, -2337465600),
       (4, 4, 0, 0, -3341502720), (4, 5, 0, 0, 4874432256), (5, 3, 0, 0, 152098560),
       (5, 4, 0, 0, -6645680640), (6, 2, 0, 0, 2279798784), (6, 3, 0, 0, 6884932608),
       (7, 1, 0, 0, 1803534336), (7, 2, 0, 0, -1985679360), (8, 0, 0, 0, -3057647616),
       (8, 1, 0, 0, -4359536640), (9, 0, 0, 0, 3057647616)] := by decide

set_option maxRecDepth 32768 in
private theorem t3u3_term7_1 :
    t3u3MinorTerm7 ⟨1, by decide⟩ =
      [(1, 7, 0, 0, -5668704), (2, 6, 0, 0, 430821504), (2, 7, 0, 0, -5668704),
       (3, 5, 0, 0, -2163625344), (3, 6, 0, 0, 430821504), (4, 4, 0, 0, 3341502720),
       (4, 5, 0, 0, -2163625344), (5, 3, 0, 0, -152098560), (5, 4, 0, 0, 3341502720),
       (6, 2, 0, 0, -2279798784), (6, 3, 0, 0, -152098560), (7, 1, 0, 0, -1803534336),
       (7, 2, 0, 0, -2279798784), (8, 0, 0, 0, 3057647616), (8, 1, 0, 0, -1803534336),
       (9, 0, 0, 0, 3057647616)] := by decide

set_option maxRecDepth 32768 in
private theorem t3u3_term7_2 :
    t3u3MinorTerm7 ⟨2, by decide⟩ =
      [(1, 7, 0, 0, 17006112), (1, 8, 0, 0, -51018336), (2, 6, 0, 0, -222969024),
       (2, 7, 0, 0, 234306432), (3, 5, 0, 0, 835935552), (3, 6, 0, 0, -948703104),
       (4, 4, 0, 0, -1456911360), (4, 5, 0, 0, 4577793408), (5, 3, 0, 0, 2126269440),
       (5, 4, 0, 0, -11658401280), (6, 2, 0, 0, -3326220288), (6, 3, 0, 0, 10638480384),
       (7, 1, 0, 0, 2845310976), (7, 2, 0, 0, 3015677952), (8, 0, 0, 0, -679477248),
       (8, 1, 0, 0, -7346847744), (9, 0, 0, 0, 679477248)] := by decide

set_option maxRecDepth 32768 in
private theorem t3u3_term7_3 :
    t3u3MinorTerm7 ⟨3, by decide⟩ =
      [(1, 7, 0, 0, -17006112), (2, 6, 0, 0, 222969024), (2, 7, 0, 0, 85030560),
       (3, 5, 0, 0, -835935552), (3, 6, 0, 0, -1114845120), (4, 4, 0, 0, 1456911360),
       (4, 5, 0, 0, 4179677760), (5, 3, 0, 0, -2126269440), (5, 4, 0, 0, -7284556800),
       (6, 2, 0, 0, 3326220288), (6, 3, 0, 0, 10631347200), (7, 1, 0, 0, -2845310976),
       (7, 2, 0, 0, -16631101440), (8, 0, 0, 0, 679477248), (8, 1, 0, 0, 14226554880),
       (9, 0, 0, 0, -3397386240)] := by decide

set_option maxRecDepth 32768 in
private theorem t3u3_term7_4 :
    t3u3MinorTerm7 ⟨4, by decide⟩ =
      [(0, 9, 0, 0, -34012224), (1, 8, 0, 0, -102036672), (2, 7, 0, 0, 377633664),
       (3, 6, 0, 0, 1315185984), (4, 5, 0, 0, -3205967040), (5, 4, 0, 0, -984006144),
       (6, 3, 0, 0, 3947470848), (7, 2, 0, 0, -51757056), (8, 1, 0, 0, -907739136)] := by decide

set_option maxRecDepth 32768 in
private theorem t3u3_term7_5 :
    t3u3MinorTerm7 ⟨5, by decide⟩ =
      [(1, 7, 0, 0, -56687040), (1, 8, 0, 0, 170061120), (2, 6, 0, 0, 89112960),
       (2, 7, 0, 0, 83047680), (3, 5, 0, 0, 373714560), (3, 6, 0, 0, -1732181760),
       (4, 4, 0, 0, -223430400), (4, 5, 0, 0, -2111650560), (5, 3, 0, 0, -2544825600),
       (5, 4, 0, 0, 13499136000), (6, 2, 0, 0, 4444968960), (6, 3, 0, 0, -9826375680),
       (7, 1, 0, 0, -2202992640), (7, 2, 0, 0, -6202552320), (8, 0, 0, 0, 141557760),
       (8, 1, 0, 0, 5918883840), (9, 0, 0, 0, -141557760)] := by decide

set_option maxRecDepth 32768 in
private theorem t3u3_term7_6 :
    t3u3MinorTerm7 ⟨6, by decide⟩ =
      [(1, 7, 0, 0, 56687040), (2, 6, 0, 0, -89112960), (2, 7, 0, 0, -147386304),
       (3, 5, 0, 0, -373714560), (3, 6, 0, 0, 231693696), (4, 4, 0, 0, 223430400),
       (4, 5, 0, 0, 971657856), (5, 3, 0, 0, 2544825600), (5, 4, 0, 0, -580919040),
       (6, 2, 0, 0, -4444968960), (6, 3, 0, 0, -6616546560), (7, 1, 0, 0, 2202992640),
       (7, 2, 0, 0, 11556919296), (8, 0, 0, 0, -141557760), (8, 1, 0, 0, -5727780864),
       (9, 0, 0, 0, 368050176)] := by decide

private theorem poly4SumPrefix_seven (f : Fin 7 -> List Mono4) :
    poly4SumPrefix 7 f 7 =
      addPoly4 (addPoly4 (addPoly4 (addPoly4 (addPoly4 (addPoly4 (addPoly4 []
        (f ⟨0, by decide⟩)) (f ⟨1, by decide⟩)) (f ⟨2, by decide⟩))
        (f ⟨3, by decide⟩)) (f ⟨4, by decide⟩)) (f ⟨5, by decide⟩))
        (f ⟨6, by decide⟩) := by
  simp only [poly4SumPrefix, dite_true,
             (by decide : 0 < 7), (by decide : 1 < 7), (by decide : 2 < 7),
             (by decide : 3 < 7), (by decide : 4 < 7), (by decide : 5 < 7), (by decide : 6 < 7)]

private theorem t3u3_poly7_identity :
    addPoly4 (poly4Det 7 (fun i j => normExpr4 (t3u3ReducedExprMat7 i j)))
      (negPoly4 (normExpr4 (.mul (.const 1728) (p9Expr .v0 .v1)))) = [] := by
  have hdet_step : poly4Det 7 (fun i j => normExpr4 (t3u3ReducedExprMat7 i j)) =
      poly4SumPrefix 7 t3u3MinorTerm7 7 := rfl
  rw [hdet_step, poly4SumPrefix_seven t3u3MinorTerm7,
      t3u3_term7_0, t3u3_term7_1, t3u3_term7_2, t3u3_term7_3,
      t3u3_term7_4, t3u3_term7_5, t3u3_term7_6]
  decide

def t3u3ConeExprW : Expr4 :=
  .add (.mul (.const 3) (.add (.const 1) .v0)) (.mul (.const 359) .v1)

def t3u3ConeExprK : Expr4 :=
  .add (.mul (.const 5) (.add (.const 1) .v0)) (.mul (.const 569) .v1)

set_option maxRecDepth 65536 in
private theorem t3u3_cone_nonneg_and_homog88 :
    checkAllNonnegMono4 (normExpr4 (p9Expr t3u3ConeExprW t3u3ConeExprK)) = true ∧
    evalPoly4 0 0 0 0 (normExpr4 (p9Expr t3u3ConeExprW t3u3ConeExprK)) = 4322241 ∧
    normExpr4 (.sub
      (.mul (expr4Pow (.const 88) 9) (p9Expr .v0 .v1))
      (p9Expr (.mul (.const 88) .v0) (.mul (.const 88) .v1))) = [] := by decide

private theorem checkP9Mod61OnlyZero :
    ∀ a b : Fin 61,
      p9PosNat a.val b.val % 61 = p9NegNat a.val b.val % 61 ->
      a.val = 0 ∧ b.val = 0 := by decide

private theorem pow_mod_eq_mod_pow_w12 (m a : Nat) :
    ∀ k : Nat, a ^ k % m = (a % m) ^ k % m
  | 0 => rfl
  | k + 1 => by
    rw [Nat.pow_succ a k, Nat.pow_succ (a % m) k,
        Nat.mul_mod (a ^ k) a m, pow_mod_eq_mod_pow_w12 m a k,
        Nat.mul_mod ((a % m) ^ k % m) (a % m) m, Nat.mod_mod, ← Nat.mul_mod]

set_option exponentiation.threshold 1024 in
/--
  Theorem W12.2c (`laurent_9x9_t3u3_factorization_nonzero_and_cone_positivity`,
  `zero custom axioms`):
  Rank-3 Two-Base `9 × 9` `(T = 3, U = 3)` Exact Closed Form, Universal `P^1(F_61)` Non-Vanishing,
  `2^569 < 3^359` Convergent-Cone Positivity, & Outer `(1, 3, 1)` Sign-Flip (`Branch P3.3`, `W12_H3`):
  1. **Exact `u = 1` Closed Form (`∀ W, K : Nat`) & `(2^K - 3^W)` Zero-Gap Congruence (`∀ u : Nat`)**:
     `intDet 9 (laurentTwoBaseT3U3Mat9 W K 1) = 216 * p9PolyInt W K`, AND when `3 ^ W < 2 ^ K`,
     `((2 ^ K - 3 ^ W : Nat) : Int) ∣ (intDet 9 (laurentTwoBaseT3U3Mat9 W K (W * u)) - intDet 9 M_{0,9}(u))`!
  2. **Universal Non-Vanishing Across ALL Positive `(W, K)` (`∀ W, K ≥ 1`, EVEN WITHOUT `3^W < 2^K`)**:
     Because `P_9(W, K) ≡ 0 (mod 61) -> 61 ∣ W ∧ 61 ∣ K` (`P^1(F_61)` has zero projective roots!),
     infinite `61`-adic descent proves `intDet 9 (laurentTwoBaseT3U3Mat9 W K 1) ≠ 0` for ALL `W, K ≥ 1`!
  3. **Strict Positivity Across the Entire `3^W < 2^K ∧ 3 * K ≤ 5 * W` Collatz Cone (`2^569 < 3^359`)**:
     `∀ W, K ≥ 1, 3 ^ W < 2 ^ K -> 3 * K ≤ 5 * W -> intDet 9 (laurentTwoBaseT3U3Mat9 W K 1) > 0`!
  4. **Outer `(1, 3, 1)` Sign-Flip vs `(3, 5, 1)` & `(5, 8, 1)` Cone Certificates (`W12_H3`)**:
     `intDet 9 (laurentTwoBaseT3U3Mat9 1 3 1) = -6089090328 < 0` (`gcd(1, 3) = 1, 3^1 < 2^3`), while
     `intDet 9 (laurentTwoBaseT3U3Mat9 3 5 1) = 933604056 > 0` and
     `intDet 9 (laurentTwoBaseT3U3Mat9 5 8 1) = 2880700416 > 0`!
-/
theorem laurent_9x9_t3u3_factorization_nonzero_and_cone_positivity :
    (∀ W K : Nat,
      intDet 9 (laurentTwoBaseT3U3Mat9 W K 1) = 216 * p9PolyInt W K) ∧
    (∀ W K u : Nat, 3 ^ W < 2 ^ K ->
      ((2 ^ K - 3 ^ W : Nat) : Int) ∣
        (intDet 9 (laurentTwoBaseT3U3Mat9 W K (W * u)) -
         intDet 9 (fun i j =>
           (laurentZeroGapIntEntry W K (laurentRowsTwoBase9 i).1 (laurentRowsTwoBase9 i).2
             (laurentColsC33_9 u j).1 (laurentColsC33_9 u j).2 : Int)))) ∧
    (∀ W K : Nat, W ≥ 1 -> K ≥ 1 ->
      intDet 9 (laurentTwoBaseT3U3Mat9 W K 1) ≠ 0) ∧
    (∀ W K : Nat, W ≥ 1 -> K ≥ 1 -> 3 ^ W < 2 ^ K -> 3 * K ≤ 5 * W ->
      intDet 9 (laurentTwoBaseT3U3Mat9 W K 1) > 0) ∧
    (intDet 9 (laurentTwoBaseT3U3Mat9 1 3 1) = -6089090328 ∧
     intDet 9 (laurentTwoBaseT3U3Mat9 3 5 1) = 933604056 ∧
     intDet 9 (laurentTwoBaseT3U3Mat9 5 8 1) = 2880700416) := by
  -- Helper: `(2 * binom(n, 2) : Int) = (n : Int) * ((n : Int) - 1)` for all `n : Nat`:
  have h2binom2 : ∀ n : Nat, ((2 * laurentInterpBinom n 2 : Nat) : Int) = (n : Int) * ((n : Int) - 1) := by
    intro n
    cases n with
    | zero => rfl
    | succ m =>
      have h := laurentInterpBinom_succ_mul m 1
      rw [laurentInterpBinom_one_right m] at h
      change 2 * laurentInterpBinom (m + 1) 2 = (m + 1) * m at h
      rw [h, Int.natCast_mul]
      have hm_sub : ((m + 1 : Nat) : Int) - 1 = (m : Int) := by omega
      rw [hm_sub]
  -- Helper: `evalExpr4 (W : Int) (K : Int) 0 0 (p9Expr .v0 .v1) = p9PolyInt W K`:
  have heval_p9 : ∀ W K : Nat, evalExpr4 (W : Int) (K : Int) 0 0 (p9Expr .v0 .v1) = p9PolyInt W K := by
    intro W K
    have hp_cast : ∀ (x : Nat) (e : Nat),
        evalExpr4 (W : Int) (K : Int) 0 0 (expr4Pow (if x = 0 then .v0 else .v1) e) =
          (((if x = 0 then W else K) ^ e : Nat) : Int) := by
      intro x e; induction e with
      | zero => simp [expr4Pow, evalExpr4]
      | succ e' ih =>
        simp only [expr4Pow, evalExpr4, ih, Nat.pow_succ]
        by_cases hx : x = 0
        · simp only [hx, ite_true, evalExpr4, Int.natCast_mul]; ac_rfl
        · simp only [hx, ite_false, evalExpr4, Int.natCast_mul]; ac_rfl
    have hw_p := fun e => hp_cast 0 e
    have hk_p := fun e => hp_cast 1 e
    simp only [ite_true] at hw_p
    have hf10 : ¬ ((1 : Nat) = 0) := by decide
    simp only [hf10, ite_false] at hk_p
    dsimp only [p9Expr, evalExpr4, p9PolyInt, p9PosNat, p9NegNat]
    rw [hw_p 9, hw_p 6, hk_p 3, hw_p 4, hk_p 5, hw_p 2, hk_p 7,
        hw_p 7, hk_p 2, hw_p 5, hk_p 4, hw_p 3, hk_p 6, hk_p 9]
    simp only [Int.natCast_add, Int.natCast_mul]
    rw [show ((2097152 : Nat) : Int) = 2097152 from rfl,
        show ((8974080 : Nat) : Int) = 8974080 from rfl,
        show ((4121712 : Nat) : Int) = 4121712 from rfl,
        show ((647136 : Nat) : Int) = 647136 from rfl,
        show ((7279104 : Nat) : Int) = 7279104 from rfl,
        show ((5968128 : Nat) : Int) = 5968128 from rfl,
        show ((2404800 : Nat) : Int) = 2404800 from rfl,
        show ((19683 : Nat) : Int) = 19683 from rfl]
    have hc3 : ∀ (c x y : Int), c * (x * y) = c * x * y :=
      fun c x y => (Int.mul_assoc c x y).symm
    rw [hc3 8974080, hc3 4121712, hc3 647136, hc3 7279104, hc3 5968128, hc3 2404800]
    omega
  -- Part 1: Exact `u = 1` Closed Form `intDet 9 (laurentTwoBaseT3U3Mat9 W K 1) = 216 * p9PolyInt W K`:
  have hdet9_closed : ∀ W K : Nat,
      intDet 9 (laurentTwoBaseT3U3Mat9 W K 1) = 216 * p9PolyInt W K := by
    intro W K
    let M9 := laurentTwoBaseT3U3Mat9 W K 1
    let A9 : Fin 9 -> Fin 9 -> Int := fun i j =>
      evalExpr4 (W : Int) (K : Int) 0 0 (t3u3ScaledExprMat9 i j)
    let c2_9 : Fin 9 := ⟨2, by decide⟩
    let c5_9 : Fin 9 := ⟨5, by decide⟩
    let c8_9 : Fin 9 := ⟨8, by decide⟩
    let M9_a : Fin 9 -> Fin 9 -> Int := fun i j => if j = c2_9 then 2 * M9 i c2_9 else M9 i j
    let M9_b : Fin 9 -> Fin 9 -> Int := fun i j => if j = c5_9 then 2 * M9_a i c5_9 else M9_a i j
    let M9_c : Fin 9 -> Fin 9 -> Int := fun i j => if j = c8_9 then 2 * M9_b i c8_9 else M9_b i j
    have hA9_eq : A9 = M9_c := by
      funext i j
      let r := (laurentRowsTwoBase9 i).1
      let s := (laurentRowsTwoBase9 i).2
      let n := r * W + s * K
      have hn_ev : ((r : Int) * (W : Int) + (s : Int) * (K : Int)) = (n : Int) := by
        simp [n, Int.natCast_add, Int.natCast_mul]
      have h2b := h2binom2 n
      have hsq_pq : (2 ^ r * 3 ^ s) * (2 ^ r * 3 ^ s) = 2 ^ (r * 2) * 3 ^ (s * 2) := by
        have h2r : 2 ^ r * 2 ^ r = 2 ^ (r * 2) := by rw [← Nat.pow_add, show r + r = r * 2 by omega]
        have h3s : 3 ^ s * 3 ^ s = 3 ^ (s * 2) := by rw [← Nat.pow_add, show s + s = s * 2 by omega]
        calc
          (2 ^ r * 3 ^ s) * (2 ^ r * 3 ^ s) = (2 ^ r * 2 ^ r) * (3 ^ s * 3 ^ s) := by ac_rfl
          _ = 2 ^ (r * 2) * 3 ^ (s * 2) := by rw [h2r, h3s]
      rcases (by have := j.isLt; omega :
        j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 ∨ j.val = 4 ∨
        j.val = 5 ∨ j.val = 6 ∨ j.val = 7 ∨ j.val = 8) with
        hj | hj | hj | hj | hj | hj | hj | hj | hj
      · have hje : j = ⟨0, by decide⟩ := Fin.ext hj; subst hje
        change 1 = M9 i ⟨0, by decide⟩
        unfold M9 laurentTwoBaseT3U3Mat9 laurentInterpMat
        rw [show laurentColsC33_9 1 ⟨0, by decide⟩ = (0, 0) from rfl]
        unfold laurentInterpEntry; simp [laurentInterpBinom_zero_right]
      · have hje : j = ⟨1, by decide⟩ := Fin.ext hj; subst hje
        change (r : Int) * (W : Int) + (s : Int) * (K : Int) = M9 i ⟨1, by decide⟩
        rw [hn_ev]
        unfold M9 laurentTwoBaseT3U3Mat9 laurentInterpMat
        rw [show laurentColsC33_9 1 ⟨1, by decide⟩ = (1, 0) from rfl]
        unfold laurentInterpEntry; dsimp only
        rw [laurentInterpBinom_one_right, Nat.mul_zero, Nat.mul_zero, Nat.pow_zero,
            Nat.mul_one, Nat.mul_one]
      · have hje : j = ⟨2, by decide⟩ := Fin.ext hj; subst hje
        change ((r : Int) * (W : Int) + (s : Int) * (K : Int)) *
            (((r : Int) * (W : Int) + (s : Int) * (K : Int)) - 1) = 2 * M9 i ⟨2, by decide⟩
        rw [hn_ev, ← h2b, Int.natCast_mul]
        unfold M9 laurentTwoBaseT3U3Mat9 laurentInterpMat
        rw [show laurentColsC33_9 1 ⟨2, by decide⟩ = (2, 0) from rfl]
        unfold laurentInterpEntry; dsimp only
        rw [Nat.mul_zero, Nat.mul_zero, Nat.pow_zero, Nat.mul_one, Nat.mul_one]
        rfl
      · have hje : j = ⟨3, by decide⟩ := Fin.ext hj; subst hje
        change ((2 ^ r * 3 ^ s : Nat) : Int) = M9 i ⟨3, by decide⟩
        unfold M9 laurentTwoBaseT3U3Mat9 laurentInterpMat
        rw [show laurentColsC33_9 1 ⟨3, by decide⟩ = (0, 1) from rfl]
        unfold laurentInterpEntry; dsimp only
        rw [laurentInterpBinom_zero_right, Nat.mul_one, Nat.mul_one, Nat.one_mul]
      · have hje : j = ⟨4, by decide⟩ := Fin.ext hj; subst hje
        change ((2 ^ r * 3 ^ s : Nat) : Int) * ((r : Int) * (W : Int) + (s : Int) * (K : Int)) =
          M9 i ⟨4, by decide⟩
        rw [hn_ev, ← Int.natCast_mul]
        unfold M9 laurentTwoBaseT3U3Mat9 laurentInterpMat
        rw [show laurentColsC33_9 1 ⟨4, by decide⟩ = (1, 1) from rfl]
        unfold laurentInterpEntry; dsimp only
        rw [laurentInterpBinom_one_right, Nat.mul_one, Nat.mul_one]
        apply congrArg Nat.cast
        show (2 ^ r * 3 ^ s) * n = n * 2 ^ r * 3 ^ s
        ac_rfl
      · have hje : j = ⟨5, by decide⟩ := Fin.ext hj; subst hje
        change ((2 ^ r * 3 ^ s : Nat) : Int) *
            (((r : Int) * (W : Int) + (s : Int) * (K : Int)) *
              (((r : Int) * (W : Int) + (s : Int) * (K : Int)) - 1)) = 2 * M9 i ⟨5, by decide⟩
        rw [hn_ev, ← h2b, ← Int.natCast_mul]
        unfold M9 laurentTwoBaseT3U3Mat9 laurentInterpMat
        rw [show laurentColsC33_9 1 ⟨5, by decide⟩ = (2, 1) from rfl]
        unfold laurentInterpEntry; dsimp only
        rw [Nat.mul_one, Nat.mul_one, show (2 : Int) = ((2 : Nat) : Int) from rfl, ← Int.natCast_mul]
        apply congrArg Nat.cast
        show (2 ^ r * 3 ^ s) * (2 * laurentInterpBinom n 2) = 2 * (laurentInterpBinom n 2 * 2 ^ r * 3 ^ s)
        ac_rfl
      · have hje : j = ⟨6, by decide⟩ := Fin.ext hj; subst hje
        change ((2 ^ r * 3 ^ s : Nat) : Int) * ((2 ^ r * 3 ^ s : Nat) : Int) = M9 i ⟨6, by decide⟩
        rw [← Int.natCast_mul, hsq_pq]
        unfold M9 laurentTwoBaseT3U3Mat9 laurentInterpMat
        rw [show laurentColsC33_9 1 ⟨6, by decide⟩ = (0, 2) from rfl]
        unfold laurentInterpEntry; dsimp only
        rw [laurentInterpBinom_zero_right, Nat.one_mul]
      · have hje : j = ⟨7, by decide⟩ := Fin.ext hj; subst hje
        change (((2 ^ r * 3 ^ s : Nat) : Int) * ((2 ^ r * 3 ^ s : Nat) : Int)) *
            ((r : Int) * (W : Int) + (s : Int) * (K : Int)) = M9 i ⟨7, by decide⟩
        rw [hn_ev, ← Int.natCast_mul, ← Int.natCast_mul, hsq_pq]
        unfold M9 laurentTwoBaseT3U3Mat9 laurentInterpMat
        rw [show laurentColsC33_9 1 ⟨7, by decide⟩ = (1, 2) from rfl]
        unfold laurentInterpEntry; dsimp only
        rw [laurentInterpBinom_one_right]
        apply congrArg Nat.cast
        show (2 ^ (r * 2) * 3 ^ (s * 2)) * n = n * 2 ^ (r * 2) * 3 ^ (s * 2)
        ac_rfl
      · have hje : j = ⟨8, by decide⟩ := Fin.ext hj; subst hje
        change (((2 ^ r * 3 ^ s : Nat) : Int) * ((2 ^ r * 3 ^ s : Nat) : Int)) *
            (((r : Int) * (W : Int) + (s : Int) * (K : Int)) *
              (((r : Int) * (W : Int) + (s : Int) * (K : Int)) - 1)) = 2 * M9 i ⟨8, by decide⟩
        rw [hn_ev, ← h2b, ← Int.natCast_mul, ← Int.natCast_mul, hsq_pq]
        unfold M9 laurentTwoBaseT3U3Mat9 laurentInterpMat
        rw [show laurentColsC33_9 1 ⟨8, by decide⟩ = (2, 2) from rfl]
        unfold laurentInterpEntry; dsimp only
        rw [show (2 : Int) = ((2 : Nat) : Int) from rfl, ← Int.natCast_mul]
        apply congrArg Nat.cast
        show (2 ^ (r * 2) * 3 ^ (s * 2)) * (2 * laurentInterpBinom n 2) =
          2 * (laurentInterpBinom n 2 * 2 ^ (r * 2) * 3 ^ (s * 2))
        ac_rfl
    have h8_det : intDet 9 A9 = 8 * intDet 9 M9 := by
      rw [hA9_eq,
          intDet_col_scale 2 9 c8_9 M9_b,
          intDet_col_scale 2 9 c5_9 M9_a,
          intDet_col_scale 2 9 c2_9 M9]
      omega
    -- Pivot Row 0 of `A9` at col `0` (`A9 0 0 = 1, A9 0 3 = 1, A9 0 6 = 1`, else `0`):
    have hA9_00 : A9 ⟨0, by decide⟩ ⟨0, by decide⟩ = 1 := rfl
    rw [intDet_pivot_row0 8 A9 ⟨0, by decide⟩ hA9_00] at h8_det
    let B8 : Fin 8 -> Fin 8 -> Int := fun i j =>
      evalExpr4 (W : Int) (K : Int) 0 0 (t3u3ReducedExprMat8 i j)
    have hsub9_eq_B8 : intSubMat (fun i j =>
        if j = ⟨0, by decide⟩ then A9 i j else A9 i j - A9 ⟨0, by decide⟩ j * A9 i ⟨0, by decide⟩)
        ⟨0, by decide⟩ = B8 := by
      funext i j
      let r9 : Fin 9 := ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
      let c9 : Fin 9 := ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
      have hskip0 : skipFinIdx ⟨0, by decide⟩ j = c9 := by
        revert j; decide
      have hc9_ne0 : c9 ≠ ⟨0, by decide⟩ := fun h => by have := congrArg Fin.val h; dsimp [c9] at this; omega
      have hA9_i0 : A9 r9 ⟨0, by decide⟩ = 1 := rfl
      change (if skipFinIdx ⟨0, by decide⟩ j = ⟨0, by decide⟩ then _ else _) = B8 i j
      rw [hskip0, ite_false_of_w10 hc9_ne0, hA9_i0, Int.mul_one]
      have h0_eq : ∀ c : Fin 9,
          A9 ⟨0, by decide⟩ c =
            if c.val = 0 ∨ c.val = 3 ∨ c.val = 6 then 1 else 0 := by
        intro c
        rcases (by have := c.isLt; omega :
          c.val = 0 ∨ c.val = 1 ∨ c.val = 2 ∨ c.val = 3 ∨ c.val = 4 ∨
          c.val = 5 ∨ c.val = 6 ∨ c.val = 7 ∨ c.val = 8) with
          hc | hc | hc | hc | hc | hc | hc | hc | hc
        · have hce : c = ⟨0, by decide⟩ := Fin.ext hc; subst hce; rfl
        · have hce : c = ⟨1, by decide⟩ := Fin.ext hc; subst hce
          change (0 : Int) * (W : Int) + (0 : Int) * (K : Int) = 0; simp
        · have hce : c = ⟨2, by decide⟩ := Fin.ext hc; subst hce
          change ((0 : Int) * (W : Int) + (0 : Int) * (K : Int)) *
            (((0 : Int) * (W : Int) + (0 : Int) * (K : Int)) - 1) = 0; simp
        · have hce : c = ⟨3, by decide⟩ := Fin.ext hc; subst hce; rfl
        · have hce : c = ⟨4, by decide⟩ := Fin.ext hc; subst hce
          change 1 * ((0 : Int) * (W : Int) + (0 : Int) * (K : Int)) = 0; simp
        · have hce : c = ⟨5, by decide⟩ := Fin.ext hc; subst hce
          change 1 * (((0 : Int) * (W : Int) + (0 : Int) * (K : Int)) *
            (((0 : Int) * (W : Int) + (0 : Int) * (K : Int)) - 1)) = 0; simp
        · have hce : c = ⟨6, by decide⟩ := Fin.ext hc; subst hce; rfl
        · have hce : c = ⟨7, by decide⟩ := Fin.ext hc; subst hce
          change (1 * 1) * ((0 : Int) * (W : Int) + (0 : Int) * (K : Int)) = 0; simp
        · have hce : c = ⟨8, by decide⟩ := Fin.ext hc; subst hce
          change (1 * 1) * (((0 : Int) * (W : Int) + (0 : Int) * (K : Int)) *
            (((0 : Int) * (W : Int) + (0 : Int) * (K : Int)) - 1)) = 0; simp
      change A9 r9 c9 - A9 ⟨0, by decide⟩ c9 = B8 i j
      rw [h0_eq c9]
      dsimp only [B8, t3u3ReducedExprMat8, A9, r9, c9]
      rcases (by have := j.isLt; omega :
        j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 ∨ j.val = 4 ∨ j.val = 5 ∨ j.val = 6 ∨ j.val = 7) with
        hj | hj | hj | hj | hj | hj | hj | hj
      · simp [hj]
      · simp [hj]
      · simp [hj, evalExpr4]
      · simp [hj]
      · simp [hj]
      · simp [hj, evalExpr4]
      · simp [hj]
      · simp [hj]
    have hev0 : (⟨0, by decide⟩ : Fin 9).val % 2 = 0 := rfl
    rw [ite_true_of_w10 hev0, Int.one_mul, hsub9_eq_B8] at h8_det
    -- Pivot Row 0 of `B8` at col `2` (`B8 0 2 = 2 - 1 = 1`!):
    have hB8_02 : B8 ⟨0, by decide⟩ ⟨2, by decide⟩ = 1 := rfl
    rw [intDet_pivot_row0 7 B8 ⟨2, by decide⟩ hB8_02] at h8_det
    let C7 : Fin 7 -> Fin 7 -> Int := fun i j =>
      evalExpr4 (W : Int) (K : Int) 0 0 (t3u3ReducedExprMat7 i j)
    have hsub8_eq_C7 : intSubMat (fun i j =>
        if j = ⟨2, by decide⟩ then B8 i j else B8 i j - B8 ⟨0, by decide⟩ j * B8 i ⟨2, by decide⟩)
        ⟨2, by decide⟩ = C7 := by
      funext i j
      have hne2 : skipFinIdx ⟨2, by decide⟩ j ≠ ⟨2, by decide⟩ := by
        revert j; decide
      change (if skipFinIdx ⟨2, by decide⟩ j = ⟨2, by decide⟩ then _ else _) = C7 i j
      rw [ite_false_of_w10 hne2]
      rfl
    have hev2 : (⟨2, by decide⟩ : Fin 8).val % 2 = 0 := rfl
    rw [ite_true_of_w10 hev2, Int.one_mul, hsub8_eq_C7] at h8_det
    -- Evaluate `intDet 7 C7` via `poly4Det_eq_of_sub_nil` and `t3u3_poly7_identity`:
    have hdet7_eq : intDet 7 C7 = 1728 * p9PolyInt W K := by
      have hp7 := poly4Det_eq_of_sub_nil t3u3ReducedExprMat7 (.mul (.const 1728) (p9Expr .v0 .v1))
        t3u3_poly7_identity (W : Int) (K : Int) 0 0
      change intDet 7 C7 = 1728 * evalExpr4 (W : Int) (K : Int) 0 0 (p9Expr .v0 .v1) at hp7
      rwa [heval_p9 W K] at hp7
    rw [hdet7_eq] at h8_det
    dsimp only [M9] at h8_det
    omega
  -- Part 2: `(2^K - 3^W)` zero-gap congruence across all `W * u`:
  have hcong9 : ∀ W K u : Nat, 3 ^ W < 2 ^ K ->
      ((2 ^ K - 3 ^ W : Nat) : Int) ∣
        (intDet 9 (laurentTwoBaseT3U3Mat9 W K (W * u)) -
         intDet 9 (fun i j =>
           (laurentZeroGapIntEntry W K (laurentRowsTwoBase9 i).1 (laurentRowsTwoBase9 i).2
             (laurentColsC33_9 u j).1 (laurentColsC33_9 u j).2 : Int))) := by
    intro W K u hgt
    have hdvd := (laurent_wdilated_zero_gap_entry_and_det_congruence.2
      W K 9 laurentRowsTwoBase9 (laurentColsC33_9 u) hgt).1
    have hMW_eq : (fun i j : Fin 9 =>
        (laurentInterpEntry W K (laurentRowsTwoBase9 i).1 (laurentRowsTwoBase9 i).2
          (laurentColsC33_9 u j).1 (W * (laurentColsC33_9 u j).2) : Int)) =
        laurentTwoBaseT3U3Mat9 W K (W * u) := by
      funext i j
      unfold laurentTwoBaseT3U3Mat9 laurentInterpMat laurentColsC33_9
      rcases (by have := j.isLt; omega :
        j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 ∨ j.val = 4 ∨
        j.val = 5 ∨ j.val = 6 ∨ j.val = 7 ∨ j.val = 8) with
        h | h | h | h | h | h | h | h | h
      · simp [h]
      · simp [h]
      · simp [h]
      · simp [h]
      · simp [h]
      · simp [h]
      · simp [h, Nat.mul_left_comm]
      · simp [h, Nat.mul_left_comm]
      · simp [h, Nat.mul_left_comm]
    rw [hMW_eq] at hdvd
    rcases hdvd with ⟨c, hc⟩
    exact ⟨-c, by rw [Int.mul_neg]; omega⟩
  -- Part 3: Universal `P^1(F_61)` non-vanishing across ALL `W, K ≥ 1` via infinite descent on `W + K`:
  have hnonzero9 : ∀ W K : Nat, W ≥ 1 -> K ≥ 1 ->
      intDet 9 (laurentTwoBaseT3U3Mat9 W K 1) ≠ 0 := by
    have hp9_scale : ∀ c W K : Nat,
        p9PosNat (c * W) (c * K) = c ^ 9 * p9PosNat W K ∧
        p9NegNat (c * W) (c * K) = c ^ 9 * p9NegNat W K := by
      intro c W K
      have hhom : ∀ a b : Nat, a + b = 9 -> (c * W) ^ a * (c * K) ^ b = c ^ 9 * (W ^ a * K ^ b) := by
        intro a b hab
        rw [mul_pow_w12 c W a, mul_pow_w12 c K b]
        calc
          (c ^ a * W ^ a) * (c ^ b * K ^ b) = (c ^ a * c ^ b) * (W ^ a * K ^ b) := by ac_rfl
          _ = c ^ 9 * (W ^ a * K ^ b) := by rw [← Nat.pow_add c a b, hab]
      have h90 := mul_pow_w12 c W 9
      have h09 := mul_pow_w12 c K 9
      refine ⟨?_, ?_⟩
      · unfold p9PosNat
        have t1 : 2097152 * (c * W) ^ 9 = c ^ 9 * (2097152 * W ^ 9) := by rw [h90]; ac_rfl
        have t2 : 8974080 * (c * W) ^ 6 * (c * K) ^ 3 = c ^ 9 * (8974080 * W ^ 6 * K ^ 3) := by
          rw [Nat.mul_assoc 8974080, hhom 6 3 rfl]; ac_rfl
        have t3 : 4121712 * (c * W) ^ 4 * (c * K) ^ 5 = c ^ 9 * (4121712 * W ^ 4 * K ^ 5) := by
          rw [Nat.mul_assoc 4121712, hhom 4 5 rfl]; ac_rfl
        have t4 : 647136 * (c * W) ^ 2 * (c * K) ^ 7 = c ^ 9 * (647136 * W ^ 2 * K ^ 7) := by
          rw [Nat.mul_assoc 647136, hhom 2 7 rfl]; ac_rfl
        rw [t1, t2, t3, t4, ← Nat.mul_add, ← Nat.mul_add, ← Nat.mul_add]
      · unfold p9NegNat
        have t1 : 7279104 * (c * W) ^ 7 * (c * K) ^ 2 = c ^ 9 * (7279104 * W ^ 7 * K ^ 2) := by
          rw [Nat.mul_assoc 7279104, hhom 7 2 rfl]; ac_rfl
        have t2 : 5968128 * (c * W) ^ 5 * (c * K) ^ 4 = c ^ 9 * (5968128 * W ^ 5 * K ^ 4) := by
          rw [Nat.mul_assoc 5968128, hhom 5 4 rfl]; ac_rfl
        have t3 : 2404800 * (c * W) ^ 3 * (c * K) ^ 6 = c ^ 9 * (2404800 * W ^ 3 * K ^ 6) := by
          rw [Nat.mul_assoc 2404800, hhom 3 6 rfl]; ac_rfl
        have t4 : 19683 * (c * K) ^ 9 = c ^ 9 * (19683 * K ^ 9) := by rw [h09]; ac_rfl
        rw [t1, t2, t3, t4, ← Nat.mul_add, ← Nat.mul_add, ← Nat.mul_add]
    have hdesc : ∀ (fuel W K : Nat), W ≥ 1 -> K ≥ 1 -> W + K ≤ fuel ->
        p9PosNat W K ≠ p9NegNat W K := by
      intro fuel; induction fuel with
      | zero => intros; omega
      | succ fuel' ih =>
        intro W K hW hK hle heq
        -- Reduce `p9PosNat W K % 61 = p9NegNat W K % 61`:
        have hadd4_mod : ∀ (a b c d : Nat),
            (a + b + c + d) % 61 = (a % 61 + b % 61 + c % 61 + d % 61) % 61 :=
          fun a b c d => by simp [Nat.add_mod]
        have ht : ∀ (cf a b : Nat),
            (cf * W ^ a * K ^ b) % 61 = (cf * (W % 61) ^ a * (K % 61) ^ b) % 61 := by
          intro cf a b
          rw [Nat.mul_assoc cf, Nat.mul_assoc cf,
              Nat.mul_mod cf _ 61, Nat.mul_mod (W ^ a) (K ^ b) 61,
              pow_mod_eq_mod_pow_w12 61 W a, pow_mod_eq_mod_pow_w12 61 K b,
              ← Nat.mul_mod ((W % 61) ^ a) ((K % 61) ^ b) 61,
              ← Nat.mul_mod cf]
        have hpos61 : p9PosNat W K % 61 = p9PosNat (W % 61) (K % 61) % 61 := by
          unfold p9PosNat
          rw [hadd4_mod, hadd4_mod (2097152 * (W % 61) ^ 9),
              Nat.mul_mod 2097152 (W ^ 9) 61, pow_mod_eq_mod_pow_w12 61 W 9, ← Nat.mul_mod 2097152,
              ht 8974080 6 3, ht 4121712 4 5, ht 647136 2 7]
        have hneg61 : p9NegNat W K % 61 = p9NegNat (W % 61) (K % 61) % 61 := by
          unfold p9NegNat
          rw [hadd4_mod, hadd4_mod (7279104 * (W % 61) ^ 7 * (K % 61) ^ 2),
              ht 7279104 7 2, ht 5968128 5 4, ht 2404800 3 6,
              Nat.mul_mod 19683 (K ^ 9) 61, pow_mod_eq_mod_pow_w12 61 K 9, ← Nat.mul_mod 19683]
        have hm_eq : p9PosNat (W % 61) (K % 61) % 61 = p9NegNat (W % 61) (K % 61) % 61 := by
          rw [← hpos61, ← hneg61, heq]
        rcases checkP9Mod61OnlyZero ⟨W % 61, Nat.mod_lt W (by decide)⟩
          ⟨K % 61, Nat.mod_lt K (by decide)⟩ hm_eq with ⟨hw0, hk0⟩
        dsimp at hw0 hk0
        let W' := W / 61
        let K' := K / 61
        have hW_eq : W = 61 * W' := by dsimp [W']; omega
        have hK_eq : K = 61 * K' := by dsimp [K']; omega
        have hW'1 : W' ≥ 1 := by omega
        have hK'1 : K' ≥ 1 := by omega
        rw [hW_eq, hK_eq] at heq
        rcases hp9_scale 61 W' K' with ⟨hs_pos, hs_neg⟩
        rw [hs_pos, hs_neg] at heq
        have hc61_pos : 0 < 61 ^ 9 := by decide
        have heq' := Nat.eq_of_mul_eq_mul_left hc61_pos heq
        exact ih W' K' hW'1 hK'1 (by omega) heq'
    intro W K hW hK hzero
    rw [hdet9_closed W K] at hzero
    have hp_eq : p9PosNat W K = p9NegNat W K := by dsimp [p9PolyInt] at hzero; omega
    exact hdesc (W + K) W K hW hK (Nat.le_refl _) hp_eq
  -- Part 4: Strict cone positivity on `3^W < 2^K ∧ 3 * K ≤ 5 * W` via `2^569 < 3^359`:
  have hcone9 : ∀ W K : Nat, W ≥ 1 -> K ≥ 1 -> 3 ^ W < 2 ^ K -> 3 * K ≤ 5 * W ->
      intDet 9 (laurentTwoBaseT3U3Mat9 W K 1) > 0 := by
    have hconv : 2 ^ 569 < 3 ^ 359 := by
      have h2 : 2 ^ 569 = 2 ^ 200 * (2 ^ 200 * 2 ^ 169) := by
        rw [show (569 : Nat) = 200 + (200 + 169) from rfl,
            Nat.pow_add 2 200 (200 + 169), Nat.pow_add 2 200 169]
      have h3 : 3 ^ 359 = 3 ^ 180 * 3 ^ 179 := by
        rw [show (359 : Nat) = 180 + 179 from rfl, Nat.pow_add 3 180 179]
      rw [h2, h3]; decide
    rcases t3u3_cone_nonneg_and_homog88 with ⟨hnn_c, hval_0, hhom88⟩
    intro W K _ _ hgt hcone
    rw [hdet9_closed W K]
    -- First show `569 * W < 359 * K`:
    have hslope : 569 * W < 359 * K := by
      by_cases hsl : 569 * W < 359 * K
      · exact hsl
      · exfalso
        have hge : 359 * K ≤ 569 * W := by omega
        -- `2^(359 * K) ≤ 2^(569 * W) = (2^569)^W ≤ (3^359)^W = 3^(359 * W) < 2^(359 * K)`!
        have hp1 : 2 ^ (359 * K) ≤ 2 ^ (569 * W) :=
          nat_pow_mono_exp_pos 2 _ _ (by decide) hge
        have hp2 : 2 ^ (569 * W) = (2 ^ 569) ^ W := (pow_pow_eq_mul_w5 2 569 W).symm
        have hp3 : (2 ^ 569) ^ W ≤ (3 ^ 359) ^ W :=
          pow_mono_base_w12 (2 ^ 569) (3 ^ 359) (Nat.le_of_lt hconv) W
        have hp4 : (3 ^ 359) ^ W = 3 ^ (359 * W) := pow_pow_eq_mul_w5 3 359 W
        have hp5 : (3 ^ W) ^ 359 < (2 ^ K) ^ 359 := by
          -- Strict power monotonicity for exponent `359 ≥ 1`:
          have hst : ∀ (a b n : Nat), a < b -> a ^ (n + 1) < b ^ (n + 1) := by
            intro a b n hab; induction n with
            | zero => simpa using hab
            | succ n' ih =>
              rw [Nat.pow_succ a (n' + 1), Nat.pow_succ b (n' + 1)]
              have hb_pos : 0 < b ^ (n' + 1) := nat_pow_pos_of_pos b (by omega) (n' + 1)
              have hle1 := Nat.mul_le_mul_right a (Nat.le_of_lt ih)
              have hlt2 := Nat.mul_lt_mul_of_pos_left hab hb_pos
              exact Nat.lt_of_le_of_lt hle1 hlt2
          rw [show (359 : Nat) = 358 + 1 from rfl]
          exact hst (3 ^ W) (2 ^ K) 358 hgt
        rw [pow_pow_eq_mul_w5 3 W 359, Nat.mul_comm W 359,
            pow_pow_eq_mul_w5 2 K 359, Nat.mul_comm K 359] at hp5
        exact Nat.not_le_of_gt hp5 (Nat.le_trans hp1 (by rw [hp2, ← hp4]; exact hp3))
    let A := 359 * K - 569 * W
    let B := 5 * W - 3 * K
    have hA_ge1 : A ≥ 1 := by omega
    let x := ((A - 1 : Nat) : Int)
    let y := (B : Int)
    have hx_nn : 0 ≤ x := Int.natCast_nonneg _
    have hy_nn : 0 ≤ y := Int.natCast_nonneg _
    have h88W : (88 * (W : Int)) = 3 * (1 + x) + 359 * y := by
      dsimp [x, y, A, B]; omega
    have h88K : (88 * (K : Int)) = 5 * (1 + x) + 569 * y := by
      dsimp [x, y, A, B]; omega
    -- Relate `(88 ^ 9 : Int) * p9PolyInt W K` to `evalPoly4 x y 0 0 (normExpr4 (p9Expr t3u3ConeExprW t3u3ConeExprK))`:
    have hhom_ev := congrArg (evalPoly4 (W : Int) (K : Int) 0 0) hhom88
    rw [evalPoly4_normExpr4] at hhom_ev
    change evalExpr4 (W : Int) (K : Int) 0 0 (expr4Pow (.const 88) 9) *
        evalExpr4 (W : Int) (K : Int) 0 0 (p9Expr .v0 .v1) -
      evalExpr4 (W : Int) (K : Int) 0 0 (p9Expr (.mul (.const 88) .v0) (.mul (.const 88) .v1)) = 0 at hhom_ev
    -- Note `evalExpr4 W K 0 0 (p9Expr (88*v0) (88*v1)) = evalExpr4 (88*W) (88*K) 0 0 (p9Expr v0 v1)`!
    have hsubst_p9 : ∀ (e1 e2 : Expr4) (u0 u1 : Int),
        evalExpr4 u0 u1 0 0 (p9Expr e1 e2) =
          evalExpr4 (evalExpr4 u0 u1 0 0 e1) (evalExpr4 u0 u1 0 0 e2) 0 0 (p9Expr .v0 .v1) := by
      intro e1 e2 u0 u1
      have hp1_e : ∀ d : Nat,
          evalExpr4 u0 u1 0 0 (expr4Pow e1 d) =
            evalExpr4 (evalExpr4 u0 u1 0 0 e1) (evalExpr4 u0 u1 0 0 e2) 0 0 (expr4Pow .v0 d) := by
        intro d; induction d with
        | zero => rfl
        | succ d' ih => simp [expr4Pow, evalExpr4, ih]
      have hp2_e : ∀ d : Nat,
          evalExpr4 u0 u1 0 0 (expr4Pow e2 d) =
            evalExpr4 (evalExpr4 u0 u1 0 0 e1) (evalExpr4 u0 u1 0 0 e2) 0 0 (expr4Pow .v1 d) := by
        intro d; induction d with
        | zero => rfl
        | succ d' ih => simp [expr4Pow, evalExpr4, ih]
      dsimp only [p9Expr, evalExpr4]
      rw [hp1_e 9, hp1_e 6, hp2_e 3, hp1_e 4, hp2_e 5, hp1_e 2, hp2_e 7,
          hp1_e 7, hp2_e 2, hp1_e 5, hp2_e 4, hp1_e 3, hp2_e 6, hp2_e 9]
    have hc_ev : evalExpr4 x y 0 0 (p9Expr t3u3ConeExprW t3u3ConeExprK) =
        evalExpr4 (W : Int) (K : Int) 0 0 (p9Expr (.mul (.const 88) .v0) (.mul (.const 88) .v1)) := by
      rw [hsubst_p9 t3u3ConeExprW t3u3ConeExprK x y,
          hsubst_p9 (.mul (.const 88) .v0) (.mul (.const 88) .v1) (W : Int) (K : Int)]
      have hw1 : evalExpr4 x y 0 0 t3u3ConeExprW = 88 * (W : Int) := by
        dsimp [t3u3ConeExprW, evalExpr4]; omega
      have hk1 : evalExpr4 x y 0 0 t3u3ConeExprK = 88 * (K : Int) := by
        dsimp [t3u3ConeExprK, evalExpr4]; omega
      have hw2 : evalExpr4 (W : Int) (K : Int) 0 0 (.mul (.const 88) .v0) = 88 * (W : Int) := rfl
      have hk2 : evalExpr4 (W : Int) (K : Int) 0 0 (.mul (.const 88) .v1) = 88 * (K : Int) := rfl
      rw [hw1, hk1, hw2, hk2]
    have hmono := evalPoly4_mono_of_nonneg 0 0 0 0 x y 0 0
      (Int.le_refl 0) hx_nn (Int.le_refl 0) hy_nn
      (Int.le_refl 0) (Int.le_refl 0) (Int.le_refl 0) (Int.le_refl 0)
      (normExpr4 (p9Expr t3u3ConeExprW t3u3ConeExprK)) hnn_c
    rw [hval_0, evalPoly4_normExpr4, hc_ev] at hmono
    rw [heval_p9 W K] at hhom_ev
    have h88_9 : evalExpr4 (W : Int) (K : Int) 0 0 (expr4Pow (.const 88) 9) = 316478381828866048 := rfl
    rw [h88_9] at hhom_ev
    omega
  refine ⟨hdet9_closed, hcong9, hnonzero9, hcone9, ?_⟩
  rw [hdet9_closed 1 3, hdet9_closed 3 5, hdet9_closed 5 8]
  exact ⟨by decide, by decide, by decide⟩

def laurentColsRank3OrderT (T u : Nat) (j : Fin (3 * T)) : Nat × Nat :=
  if j.val < T then (j.val, 0)
  else if j.val < 2 * T then (j.val - T, u)
  else (j.val - 2 * T, 2 * u)

/--
  Theorem W12.2c' (`laurent_rank3_order_T_u3_confluent_divisibility`,
  `zero custom axioms`):
  Universal Three-Block `(U = 3)` Order-`T` Confluent
  `2^(3*(T*(T-1)/2)*u) * (2^u - 1)^(2*T^2) * (2^u + 1)^(T^2)` Zero-Gap Divisibility &
  `9 × 9` `(T = 3, U = 3)` Specialization (`Branch P3.3`):
  1. **Universal `(3T) × (3T)` Three-Block Confluent Divisibility (`∀ W, K, T, u ≥ 1`)**:
     On `laurentColsRank3OrderT T u` (`(0..T-1, 0), (0..T-1, u), (0..T-1, 2*u)`):
       `((2 ^ (3 * (T * (T - 1) / 2) * u) * (2 ^ u - 1) ^ (2 * (T * T)) * (2 ^ u + 1) ^ (T * T) : Nat) : Int)
         ∣ intDet (3 * T) M0`!
  2. **Rank-3 `9 × 9` `(T = 3, U = 3)` Zero-Gap Divisibility (`∀ W, K : Nat, ∀ u ≥ 1`)**:
     On the canonical `9 × 9` zero-gap matrix `M_{0,t3u3}`:
       `((2 ^ (9 * u) * (2 ^ u - 1) ^ 18 * (2 ^ u + 1) ^ 9 : Nat) : Int) ∣ intDet 9 M_{0,t3u3}`!
-/
theorem laurent_rank3_order_T_u3_confluent_divisibility :
    (∀ (W K T u : Nat) (rows : Fin (3 * T) -> Nat × Nat),
      T ≥ 1 -> u ≥ 1 ->
      let M0 : Fin (3 * T) -> Fin (3 * T) -> Int := fun i j =>
        (laurentZeroGapIntEntry W K (rows i).1 (rows i).2
          (laurentColsRank3OrderT T u j).1 (laurentColsRank3OrderT T u j).2 : Int)
      ((2 ^ (3 * (T * (T - 1) / 2) * u) * (2 ^ u - 1) ^ (2 * (T * T)) *
          (2 ^ u + 1) ^ (T * T) : Nat) : Int) ∣ intDet (3 * T) M0) ∧
    (∀ (W K u : Nat), u ≥ 1 ->
      let M0_9 : Fin 9 -> Fin 9 -> Int := fun i j =>
        (laurentZeroGapIntEntry W K (laurentRowsTwoBase9 i).1 (laurentRowsTwoBase9 i).2
          (laurentColsC33_9 u j).1 (laurentColsC33_9 u j).2 : Int)
      ((2 ^ (9 * u) * (2 ^ u - 1) ^ 18 * (2 ^ u + 1) ^ 9 : Nat) : Int) ∣ intDet 9 M0_9) := by
  have hgen3 : ∀ (W K T u : Nat) (rows : Fin (3 * T) -> Nat × Nat),
      T ≥ 1 -> u ≥ 1 ->
      let M0 : Fin (3 * T) -> Fin (3 * T) -> Int := fun i j =>
        (laurentZeroGapIntEntry W K (rows i).1 (rows i).2
          (laurentColsRank3OrderT T u j).1 (laurentColsRank3OrderT T u j).2 : Int)
      ((2 ^ (3 * (T * (T - 1) / 2) * u) * (2 ^ u - 1) ^ (2 * (T * T)) *
          (2 ^ u + 1) ^ (T * T) : Nat) : Int) ∣ intDet (3 * T) M0 := by
    intro W K T u rows hT hu
    dsimp only
    let L := 3 * T
    let rowExp : Fin L -> Nat := fun i => (rows i).1 * W + (rows i).2 * K
    let M0 : Fin L -> Fin L -> Int := fun i j =>
      (laurentZeroGapIntEntry W K (rows i).1 (rows i).2
        (laurentColsRank3OrderT T u j).1 (laurentColsRank3OrderT T u j).2 : Int)
    let z0 : Fin L := ⟨0, by dsimp [L]; omega⟩
    let idx0 : Nat -> Fin L := fun t => if h : t < L then ⟨t, h⟩ else z0
    let idx1 : Nat -> Fin L := fun t => if h : T + t < L then ⟨T + t, h⟩ else z0
    let idx2 : Nat -> Fin L := fun t => if h : 2 * T + t < L then ⟨2 * T + t, h⟩ else z0
    have hM0_0 : ∀ (i : Fin L) (t : Nat), t < T ->
        M0 i (idx0 t) = Int.ofNat (laurentInterpBinom (rowExp i) t) := by
      intro i t ht
      have htL : t < L := by dsimp [L]; omega
      dsimp only [M0, idx0, laurentColsRank3OrderT, rowExp]
      simp only [htL, dite_true, ht, ite_true]
      unfold laurentZeroGapIntEntry
      change Int.ofNat (laurentInterpBinom _ t * 2 ^ (_ * 0)) = _
      simp
    have hM0_1 : ∀ (i : Fin L) (t : Nat), t < T ->
        M0 i (idx1 t) = Int.ofNat (laurentInterpBinom (rowExp i) t * 2 ^ (rowExp i * u)) := by
      intro i t ht
      have htL : T + t < L := by dsimp [L]; omega
      have hn0 : ¬ (T + t < T) := by omega
      have ht2 : T + t < 2 * T := by omega
      dsimp only [M0, idx1, laurentColsRank3OrderT, rowExp]
      simp only [htL, dite_true, hn0, ite_false, ht2, ite_true]
      rw [show T + t - T = t by omega]
      rfl
    have hM0_2 : ∀ (i : Fin L) (t : Nat), t < T ->
        M0 i (idx2 t) = Int.ofNat (laurentInterpBinom (rowExp i) t * 2 ^ (rowExp i * (2 * u))) := by
      intro i t ht
      have htL : 2 * T + t < L := by dsimp [L]; omega
      have hn0 : ¬ (2 * T + t < T) := by omega
      have hn1 : ¬ (2 * T + t < 2 * T) := by omega
      dsimp only [M0, idx2, laurentColsRank3OrderT, rowExp]
      simp only [htL, dite_true, hn0, hn1, ite_false]
      rw [show 2 * T + t - 2 * T = t by omega]
      rfl
    have hinj1 : ∀ t1 t2 : Nat, t1 < T -> t2 < T -> idx1 t1 = idx1 t2 -> t1 = t2 := by
      intro t1 t2 ht1 ht2 heq
      have h1 : T + t1 < L := by dsimp [L]; omega
      have h2 : T + t2 < L := by dsimp [L]; omega
      dsimp [idx1] at heq; simp only [h1, h2, dite_true] at heq
      have hv := congrArg Fin.val heq; dsimp at hv; omega
    have hdisj01 : ∀ t1 t2 : Nat, t1 < T -> t2 < T -> idx0 t1 ≠ idx1 t2 := by
      intro t1 t2 ht1 ht2 heq
      have h1 : t1 < L := by dsimp [L]; omega
      have h2 : T + t2 < L := by dsimp [L]; omega
      dsimp [idx0, idx1] at heq; simp only [h1, h2, dite_true] at heq
      have hv := congrArg Fin.val heq; dsimp at hv; omega
    rcases confluent_block_factor_from_untouched L T u rowExp M0 idx0 idx1 hT hu
      hM0_0 hM0_1 hinj1 hdisj01 with ⟨A1, hA1_keep, hdet_A1⟩
    have hinj2 : ∀ t1 t2 : Nat, t1 < T -> t2 < T -> idx2 t1 = idx2 t2 -> t1 = t2 := by
      intro t1 t2 ht1 ht2 heq
      have h1 : 2 * T + t1 < L := by dsimp [L]; omega
      have h2 : 2 * T + t2 < L := by dsimp [L]; omega
      dsimp [idx2] at heq; simp only [h1, h2, dite_true] at heq
      have hv := congrArg Fin.val heq; dsimp at hv; omega
    have hdisj02 : ∀ t1 t2 : Nat, t1 < T -> t2 < T -> idx0 t1 ≠ idx2 t2 := by
      intro t1 t2 ht1 ht2 heq
      have h1 : t1 < L := by dsimp [L]; omega
      have h2 : 2 * T + t2 < L := by dsimp [L]; omega
      dsimp [idx0, idx2] at heq; simp only [h1, h2, dite_true] at heq
      have hv := congrArg Fin.val heq; dsimp at hv; omega
    have hdisj21 : ∀ t1 t2 : Nat, t1 < T -> t2 < T -> idx2 t1 ≠ idx1 t2 := by
      intro t1 t2 ht1 ht2 heq
      have h1 : 2 * T + t1 < L := by dsimp [L]; omega
      have h2 : T + t2 < L := by dsimp [L]; omega
      dsimp [idx2, idx1] at heq; simp only [h1, h2, dite_true] at heq
      have hv := congrArg Fin.val heq; dsimp at hv; omega
    have hA1_0 : ∀ (i : Fin L) (t : Nat), t < T ->
        A1 i (idx0 t) = Int.ofNat (laurentInterpBinom (rowExp i) t) := by
      intro i t ht
      rw [hA1_keep (idx0 t) (fun s hs => hdisj01 t s ht hs) i]
      exact hM0_0 i t ht
    have hA1_2 : ∀ (i : Fin L) (t : Nat), t < T ->
        A1 i (idx2 t) = Int.ofNat (laurentInterpBinom (rowExp i) t * 2 ^ (rowExp i * (2 * u))) := by
      intro i t ht
      rw [hA1_keep (idx2 t) (fun s hs => hdisj21 t s ht hs) i]
      exact hM0_2 i t ht
    rcases confluent_block_factor_from_untouched L T (2 * u) rowExp A1 idx0 idx2 hT (by omega)
      hA1_0 hA1_2 hinj2 hdisj02 with ⟨A2, _, hdet_A2⟩
    rw [hdet_A2] at hdet_A1
    refine ⟨intDet L A2, ?_⟩
    rw [hdet_A1]
    simp only [Int.ofNat_eq_natCast]
    rw [← Int.mul_assoc, ← Int.natCast_mul]
    apply congrArg (· * intDet L A2)
    apply congrArg Nat.cast
    let S := T * (T - 1) / 2
    let Q := T * T
    change (2 ^ (S * u) * (2 ^ u - 1) ^ Q) * (2 ^ (S * (2 * u)) * (2 ^ (2 * u) - 1) ^ Q) =
      2 ^ (3 * S * u) * (2 ^ u - 1) ^ (2 * Q) * (2 ^ u + 1) ^ Q
    have h2u_diff : 2 ^ (2 * u) - 1 = (2 ^ u - 1) * (2 ^ u + 1) := by
      have hp : 2 ^ (2 * u) = 2 ^ u * 2 ^ u := by
        rw [Nat.two_mul, Nat.pow_add]
      have hge1 : 2 ^ u ≥ 1 := nat_pow_pos_of_pos 2 (by decide) u
      rw [hp, Nat.mul_add (2 ^ u - 1) (2 ^ u) 1, Nat.sub_mul, Nat.one_mul, Nat.mul_one]
      have hge_sq : 2 ^ u * 2 ^ u ≥ 2 ^ u := Nat.le_mul_of_pos_right _ hge1
      omega
    have hpow_diff : (2 ^ (2 * u) - 1) ^ Q = (2 ^ u - 1) ^ Q * (2 ^ u + 1) ^ Q := by
      rw [h2u_diff, mul_pow_w12]
    have hpow_2Q : (2 ^ u - 1) ^ (2 * Q) = (2 ^ u - 1) ^ Q * (2 ^ u - 1) ^ Q := by
      rw [Nat.two_mul, Nat.pow_add]
    have hpow_3S : 2 ^ (3 * S * u) = 2 ^ (S * u) * 2 ^ (S * (2 * u)) := by
      rw [← Nat.pow_add, show 3 * S * u = S * u + S * (2 * u) by
        calc
          3 * S * u = (1 + 2) * (S * u) := by ac_rfl
          _ = S * u + 2 * (S * u) := by rw [Nat.add_mul, Nat.one_mul]
          _ = S * u + S * (2 * u) := by ac_rfl]
    rw [hpow_diff, hpow_2Q, hpow_3S]
    ac_rfl
  refine ⟨hgen3, ?_⟩
  intro W K u hu
  dsimp only
  have h9 := hgen3 W K 3 u laurentRowsTwoBase9 (by decide) hu
  have hcols_eq : laurentColsRank3OrderT 3 u = laurentColsC33_9 u := by
    funext j
    rcases (by have := j.isLt; omega :
      j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 ∨ j.val = 4 ∨
      j.val = 5 ∨ j.val = 6 ∨ j.val = 7 ∨ j.val = 8) with
      hj | hj | hj | hj | hj | hj | hj | hj | hj
    · have hje : j = ⟨0, by decide⟩ := Fin.ext hj; subst hje; rfl
    · have hje : j = ⟨1, by decide⟩ := Fin.ext hj; subst hje; rfl
    · have hje : j = ⟨2, by decide⟩ := Fin.ext hj; subst hje; rfl
    · have hje : j = ⟨3, by decide⟩ := Fin.ext hj; subst hje; rfl
    · have hje : j = ⟨4, by decide⟩ := Fin.ext hj; subst hje; rfl
    · have hje : j = ⟨5, by decide⟩ := Fin.ext hj; subst hje; rfl
    · have hje : j = ⟨6, by decide⟩ := Fin.ext hj; subst hje; rfl
    · have hje : j = ⟨7, by decide⟩ := Fin.ext hj; subst hje; rfl
    · have hje : j = ⟨8, by decide⟩ := Fin.ext hj; subst hje; rfl
  simpa only [show 3 * (3 * (3 - 1) / 2) = 9 from rfl,
              show 2 * (3 * 3) = 18 from rfl,
              show 3 * 3 = 9 from rfl,
              hcols_eq] using h9

-- ----------------------------------------------------------------------------
-- Section 2D: Exact Prime-Power `ℓ^r` Sylow Biconditional (`q ≡ 1 (mod 24)`) &
--             `313 / 457 / 601 / p_3 = 45,661,129` Certificates
-- ----------------------------------------------------------------------------

def powModFast (q b : Nat) : Nat -> Nat -> Nat
  | 0, _ => 1 % q
  | _ + 1, 0 => 1 % q
  | fuel + 1, exp =>
    let half := powModFast q ((b * b) % q) fuel (exp / 2)
    if exp % 2 = 0 then half else (b * half) % q

theorem powModFast_eq (q : Nat) (hq : q ≥ 1) :
    ∀ (fuel b exp : Nat), exp < 2 ^ fuel -> powModFast q b fuel exp = b ^ exp % q
  | 0, _, exp, hlt => by
    have hz : exp = 0 := by simp at hlt; exact hlt
    subst hz; simp [powModFast]
  | fuel + 1, b, 0, _ => by simp [powModFast]
  | fuel + 1, b, exp + 1, hlt => by
    simp only [powModFast]
    have hpow : 2 ^ (fuel + 1) = 2 * 2 ^ fuel := by rw [Nat.pow_succ, Nat.mul_comm]
    have hdiv_lt : (exp + 1) / 2 < 2 ^ fuel := by omega
    have ih := powModFast_eq q hq fuel ((b * b) % q) ((exp + 1) / 2) hdiv_lt
    -- `((b * b) % q) ^ m % q = (b * b) ^ m % q = b ^ (2 * m) % q`:
    have hsq_pow : (((b * b) % q) ^ ((exp + 1) / 2)) % q = b ^ (2 * ((exp + 1) / 2)) % q := by
      rw [← pow_mod_eq_mod_pow_w12 q (b * b) ((exp + 1) / 2)]
      have hbb : b * b = b ^ 2 := (Nat.pow_two b).symm
      rw [hbb, pow_pow_eq_mul_w5 b 2 ((exp + 1) / 2)]
    rw [ih, hsq_pow]
    by_cases hev : (exp + 1) % 2 = 0
    · rw [ite_true_of_w10 hev]
      have hexp_eq : 2 * ((exp + 1) / 2) = exp + 1 := by omega
      rw [hexp_eq]
    · rw [ite_false_of_w10 hev]
      have hexp_eq : 2 * ((exp + 1) / 2) + 1 = exp + 1 := by omega
      rw [Nat.mul_mod b (b ^ _ % q) q, Nat.mod_mod, ← Nat.mul_mod,
          Nat.mul_comm b (b ^ _), ← Nat.pow_succ, Nat.succ_eq_add_one, hexp_eq]

private theorem prime_pow_peel_dvd (ell m : Nat) (hell : IsPrimeNat ell) :
    ∀ (t s x : Nat),
      ¬ (ell ^ (t + 1) ∣ x) ->
      x ∣ (ell ^ t * (ell ^ s * m)) ->
      x ∣ (ell ^ t * m)
  | 0, s, x, hnot, hdvd => by
    simp only [Nat.pow_zero, Nat.zero_add, Nat.pow_one, Nat.one_mul] at hnot hdvd ⊢
    have hell2 := hell.1
    have hgcd1 : Nat.gcd x ell = 1 := by
      let g := Nat.gcd x ell
      have hg_ell : g ∣ ell := Nat.gcd_dvd_right x ell
      have hg_x : g ∣ x := Nat.gcd_dvd_left x ell
      have hg_pos : g ≥ 1 := Nat.gcd_pos_of_pos_right x (by omega)
      by_cases hg1 : g = 1
      · exact hg1
      · by_cases hge : g = ell
        · exact False.elim (hnot (hge ▸ hg_x))
        · have hg_le : g ≤ ell := Nat.le_of_dvd (by omega) hg_ell
          exact False.elim (hell.2 g (by omega) (by omega) hg_ell)
    have hpeel : ∀ k : Nat, x ∣ (ell ^ k * m) -> x ∣ m := by
      intro k; induction k with
      | zero => simp
      | succ k' ih =>
        intro hk
        rw [Nat.pow_succ ell k', Nat.mul_comm (ell ^ k') ell, Nat.mul_assoc ell] at hk
        exact ih (coprime_dvd_of_dvd_mul_aux (x + ell) x ell (ell ^ k' * m) (Nat.le_refl _) hgcd1 hk)
    exact hpeel s hdvd
  | t + 1, s, x, hnot, hdvd => by
    have hell2 := hell.1
    by_cases hdiv1 : ell ∣ x
    · rcases hdiv1 with ⟨x', hx'⟩
      subst hx'
      have hnot' : ¬ (ell ^ (t + 1) ∣ x') := by
        rintro ⟨c, hc⟩
        apply hnot
        refine ⟨c, ?_⟩
        rw [hc, Nat.pow_succ ell (t + 1), Nat.mul_comm (ell ^ (t + 1)) ell, Nat.mul_assoc]
      have hdvd' : x' ∣ (ell ^ t * (ell ^ s * m)) := by
        rcases hdvd with ⟨c, hc⟩
        refine ⟨c, ?_⟩
        have hm_eq : ell * (x' * c) = ell * (ell ^ t * (ell ^ s * m)) := by
          have hp : ell ^ (t + 1) * (ell ^ s * m) = ell * (ell ^ t * (ell ^ s * m)) := by
            rw [Nat.pow_succ ell t, Nat.mul_comm (ell ^ t) ell, Nat.mul_assoc]
          rw [← hp, hc, Nat.mul_assoc]
        exact (Nat.eq_of_mul_eq_mul_left (by omega : 0 < ell) hm_eq).symm
      rcases prime_pow_peel_dvd ell m hell t s x' hnot' hdvd' with ⟨q_x, hqx⟩
      refine ⟨q_x, ?_⟩
      calc
        ell ^ (t + 1) * m = ell * (ell ^ t * m) := by
          rw [Nat.pow_succ, Nat.mul_comm (ell ^ t) ell, Nat.mul_assoc]
        _ = ell * (x' * q_x) := by rw [hqx]
        _ = ell * x' * q_x := (Nat.mul_assoc ell x' q_x).symm
    · -- `¬ (ell ∣ x)` -> `x ∣ m` -> `x ∣ ell^(t+1) * m`!
      have hnot0 : ¬ (ell ^ 1 ∣ x) := by simpa using hdiv1
      have hdvd0 : x ∣ (ell ^ 0 * (ell ^ (t + 1 + s) * m)) := by
        simp only [Nat.pow_zero, Nat.one_mul]
        rwa [← Nat.mul_assoc, ← Nat.pow_add ell (t + 1) s] at hdvd
      rcases prime_pow_peel_dvd ell m hell 0 (t + 1 + s) x hnot0 hdvd0 with ⟨q_m, hqm⟩
      simp only [Nat.pow_zero, Nat.one_mul] at hqm
      exact ⟨ell ^ (t + 1) * q_m, by rw [hqm]; ac_rfl⟩

/--
  Theorem W12.2d (`exact_prime_sylow_order_lock_biconditional`,
  choice-free `zero custom axioms`):
  Universal Prime-Power `ℓ^r` Sylow Order-Lock Biconditional & Quarter-Totient `2^(e - 1)` Criterion
  (`Branch P3.4`, `W12_H3`):
  For EVERY prime `q ≥ 5`, EVERY prime `ℓ`, `e ≥ 1, m ≥ 1`, and `1 ≤ r ≤ e` with
  `q - 1 = ℓ ^ e * m` and `¬ (ℓ ∣ m)`:
  1. **Single-Base Exact `ℓ^r` Biconditional**:
     Whenever `¬ (q ∣ b)` and `IsExactMultOrderMod q b d`:
       `ℓ ^ r ∣ d ↔ b ^ (ℓ ^ (r - 1) * m) % q ≠ 1`.
  2. **Simultaneous `(2, 3/2)` Exact `ℓ^r` GCD Biconditional**:
     Whenever `IsExactMultOrderMod q 2 d2` and `IsExactMultOrderMod q (ratio32Mod q) d32`:
       `ℓ ^ r ∣ Nat.gcd d2 d32 ↔
          (2 ^ (ℓ ^ (r - 1) * m) % q ≠ 1 ∧
           2 ^ (ℓ ^ (r - 1) * m) % q ≠ 3 ^ (ℓ ^ (r - 1) * m) % q)`.
  3. **Quarter-Totient `q ≡ 1 (mod 8)` (`e ≥ 3`) `2^(e - 1)` & `4 ∣ gcd` Lock**:
     Whenever `q - 1 = 2 ^ e * m` (`e ≥ 3`, `¬ (2 ∣ m)`):
       `(2 ^ (2 ^ (e - 2) * m) % q ≠ 1 ∧
         2 ^ (2 ^ (e - 2) * m) % q ≠ 3 ^ (2 ^ (e - 2) * m) % q) ->
        2 ^ (e - 1) ∣ Nat.gcd d2 d32 ∧ 4 ∣ Nat.gcd d2 d32`!
-/
theorem exact_prime_sylow_order_lock_biconditional :
    (∀ (q ell e m r b d : Nat),
      IsPrimeNat q -> q ≥ 5 -> IsPrimeNat ell ->
      e ≥ 1 -> m ≥ 1 -> 1 ≤ r -> r ≤ e ->
      q - 1 = ell ^ e * m -> ¬ (ell ∣ m) ->
      ¬ (q ∣ b) -> IsExactMultOrderMod q b d ->
      (ell ^ r ∣ d ↔ b ^ (ell ^ (r - 1) * m) % q ≠ 1)) ∧
    (∀ (q ell e m r d2 d32 : Nat),
      IsPrimeNat q -> q ≥ 5 -> IsPrimeNat ell ->
      e ≥ 1 -> m ≥ 1 -> 1 ≤ r -> r ≤ e ->
      q - 1 = ell ^ e * m -> ¬ (ell ∣ m) ->
      IsExactMultOrderMod q 2 d2 ->
      IsExactMultOrderMod q (ratio32Mod q) d32 ->
      (ell ^ r ∣ Nat.gcd d2 d32 ↔
        (2 ^ (ell ^ (r - 1) * m) % q ≠ 1 ∧
         2 ^ (ell ^ (r - 1) * m) % q ≠ 3 ^ (ell ^ (r - 1) * m) % q))) ∧
    (∀ (q e m d2 d32 : Nat),
      IsPrimeNat q -> q ≥ 5 -> e ≥ 3 -> m ≥ 1 ->
      q - 1 = 2 ^ e * m -> ¬ (2 ∣ m) ->
      IsExactMultOrderMod q 2 d2 ->
      IsExactMultOrderMod q (ratio32Mod q) d32 ->
      2 ^ (2 ^ (e - 2) * m) % q ≠ 1 ->
      2 ^ (2 ^ (e - 2) * m) % q ≠ 3 ^ (2 ^ (e - 2) * m) % q ->
      2 ^ (e - 1) ∣ Nat.gcd d2 d32 ∧ 4 ∣ Nat.gcd d2 d32) := by
  have hsingle : ∀ (q ell e m r b d : Nat),
      IsPrimeNat q -> q ≥ 5 -> IsPrimeNat ell ->
      e ≥ 1 -> m ≥ 1 -> 1 ≤ r -> r ≤ e ->
      q - 1 = ell ^ e * m -> ¬ (ell ∣ m) ->
      ¬ (q ∣ b) -> IsExactMultOrderMod q b d ->
      (ell ^ r ∣ d ↔ b ^ (ell ^ (r - 1) * m) % q ≠ 1) := by
    intro q ell e m r b d hq hq5 hell _he _hm hr1 hre hqm1 hnd_ell hnd_b hord
    have hell2 := hell.1
    constructor
    · intro hlr hp1
      have hd_sub := exactMultOrderMod_dvd_of_pow_eq_one q b d (ell ^ (r - 1) * m) hord hp1
      have hlr_sub : ell ^ r ∣ (ell ^ (r - 1) * m) := Nat.dvd_trans hlr hd_sub
      rcases hlr_sub with ⟨c, hc⟩
      have hpr : ell ^ r = ell ^ (r - 1) * ell := by
        conv => lhs; rw [show r = (r - 1) + 1 by omega, Nat.pow_succ]
      rw [hpr, Nat.mul_assoc] at hc
      have hp_pos : 0 < ell ^ (r - 1) := nat_pow_pos_of_pos ell (by omega) (r - 1)
      have hm_eq := Nat.eq_of_mul_eq_mul_left hp_pos hc.symm
      exact hnd_ell ⟨c, hm_eq.symm⟩
    · intro hne1
      have hd_tot : d ∣ (ell ^ (r - 1) * (ell ^ (e - (r - 1)) * m)) := by
        have htot := exactMultOrderMod_dvd_of_pow_eq_one q b d (q - 1) hord
          (fermat_little_mod_prime q b hq hnd_b)
        rw [hqm1] at htot
        have hexp : ell ^ e * m = ell ^ (r - 1) * (ell ^ (e - (r - 1)) * m) := by
          rw [← Nat.mul_assoc, ← Nat.pow_add, show (r - 1) + (e - (r - 1)) = e by omega]
        rwa [← hexp]
      by_cases hdiv : ell ^ r ∣ d
      · exact hdiv
      · exfalso
        have hnot' : ¬ (ell ^ ((r - 1) + 1) ∣ d) := by rwa [show (r - 1) + 1 = r by omega]
        have hd_m := prime_pow_peel_dvd ell m hell (r - 1) (e - (r - 1)) d hnot' hd_tot
        rcases hd_m with ⟨c, hc⟩
        rw [hc, ← pow_pow_eq_mul_w5 b d c,
            pow_mod_eq_of_mod_eq_w5 q (b ^ d) 1
              (by rw [hord.2.2.1, Nat.mod_eq_of_lt (by omega : 1 < q)]) c,
            Nat.one_pow, Nat.mod_eq_of_lt (by omega : 1 < q)] at hne1
        exact hne1 rfl
  have hnd2_of : ∀ q : Nat, q ≥ 5 -> ¬ (q ∣ 2) := by
    intro q hq5 ⟨c, hc⟩; cases c with
    | zero => simp at hc
    | succ c' => have := Nat.mul_le_mul_left q (by omega : 1 ≤ c' + 1); omega
  have hnd32_of : ∀ q : Nat, q % 2 = 1 -> q ≥ 5 -> ¬ (q ∣ ratio32Mod q) := by
    intro q hqo hq5 ⟨c, hc⟩
    have h2r := two_mul_ratio32Mod_eq_three q hqo hq5
    rw [hc, ← Nat.mul_assoc 2 q c, Nat.mul_comm 2 q, Nat.mul_assoc q 2 c, Nat.mul_mod_right] at h2r
    omega
  have hpair : ∀ (q ell e m r d2 d32 : Nat),
      IsPrimeNat q -> q ≥ 5 -> IsPrimeNat ell ->
      e ≥ 1 -> m ≥ 1 -> 1 ≤ r -> r ≤ e ->
      q - 1 = ell ^ e * m -> ¬ (ell ∣ m) ->
      IsExactMultOrderMod q 2 d2 ->
      IsExactMultOrderMod q (ratio32Mod q) d32 ->
      (ell ^ r ∣ Nat.gcd d2 d32 ↔
        (2 ^ (ell ^ (r - 1) * m) % q ≠ 1 ∧
         2 ^ (ell ^ (r - 1) * m) % q ≠ 3 ^ (ell ^ (r - 1) * m) % q)) := by
    intro q ell e m r d2 d32 hq hq5 hell he hm hr1 hre hqm1 hnd_ell hd2 hd32
    have hqo : q % 2 = 1 := by
      by_cases hev : q % 2 = 0
      · exact False.elim (hq.2 2 (Nat.le_refl 2) (by omega) (Nat.dvd_of_mod_eq_zero hev))
      · omega
    let E := ell ^ (r - 1) * m
    have hb2 := hsingle q ell e m r 2 d2 hq hq5 hell he hm hr1 hre hqm1 hnd_ell (hnd2_of q hq5) hd2
    have hb32 := hsingle q ell e m r (ratio32Mod q) d32 hq hq5 hell he hm hr1 hre hqm1 hnd_ell
      (hnd32_of q hqo hq5) hd32
    -- Relate `(ratio32Mod q)^E % q = 1 ↔ 2^E % q = 3^E % q`:
    have h2r := two_mul_ratio32Mod_eq_three q hqo hq5
    have h2E_3E : (ratio32Mod q) ^ E % q = 1 ↔ 2 ^ E % q = 3 ^ E % q := by
      have hmul_E : (2 ^ E * (ratio32Mod q) ^ E) % q = 3 ^ E % q := by
        rw [← pow_mul_mod_distrib_w11 q 2 (ratio32Mod q) E]
        exact pow_mod_eq_of_mod_eq_w5 q (2 * ratio32Mod q) 3
          (by rw [h2r, Nat.mod_eq_of_lt (by omega)]) E
      constructor
      · intro hr1_eq
        rw [Nat.mul_mod (2 ^ E) _ q, hr1_eq, Nat.mul_one, Nat.mod_mod] at hmul_E
        exact hmul_E
      · intro h23_eq
        have hnd_2E : ¬ (q ∣ 2 ^ E) := by
          rintro ⟨c, hc⟩
          have hm0 : 2 ^ E % q = 0 := by rw [hc, Nat.mul_mod_right]
          exact odd_mod_pow2_nonzero_w5 q (by omega) hqo E hm0
        have hm1 : (2 ^ E * (ratio32Mod q) ^ E) % q = (2 ^ E * 1) % q := by
          rw [hmul_E, ← h23_eq, Nat.mul_one]
        have hc := cancel_mul_mod_prime q (2 ^ E) ((ratio32Mod q) ^ E) 1 hq hnd_2E hm1
        rwa [Nat.mod_eq_of_lt (by omega : 1 < q)] at hc
    constructor
    · intro hg
      have h1 := hb2.mp (Nat.dvd_trans hg (Nat.gcd_dvd_left d2 d32))
      have h2 := hb32.mp (Nat.dvd_trans hg (Nat.gcd_dvd_right d2 d32))
      exact ⟨h1, fun heq => h2 (h2E_3E.mpr heq)⟩
    · rintro ⟨h1, h2⟩
      exact Nat.dvd_gcd (hb2.mpr h1) (hb32.mpr (fun hr1_eq => h2 (h2E_3E.mp hr1_eq)))
  refine ⟨hsingle, hpair, ?_⟩
  intro q e m d2 d32 hq hq5 he3 hm hqm1 hnd2 hd2 hd32 h2ne1 h2ne3
  have hr_le : e - 1 ≤ e := by omega
  have hr_ge : 1 ≤ e - 1 := by omega
  have hr_sub : (e - 1) - 1 = e - 2 := by omega
  have hp2 := checkSmallPrimeBool_sound 2 (by decide)
  have hdiv_e1 : 2 ^ (e - 1) ∣ Nat.gcd d2 d32 := by
    apply (hpair q 2 e m (e - 1) d2 d32 hq hq5 hp2 (by omega) hm hr_ge hr_le hqm1 hnd2 hd2 hd32).mpr
    rw [hr_sub]
    exact ⟨h2ne1, h2ne3⟩
  have h4_div : 4 ∣ 2 ^ (e - 1) := ⟨2 ^ (e - 3), by
    conv => lhs; rw [show e - 1 = 2 + (e - 3) by omega, Nat.pow_add]; rfl⟩
  exact ⟨hdiv_e1, Nat.dvd_trans h4_div hdiv_e1⟩

/--
  Theorem W12.2d' (`mod24_1_quarter_totient_457_601_and_p3_certs`, choice-free `zero custom axioms`):
  Explicit `q ≡ 1 (mod 24)` Sylow Separation Certificates (`q = 313, 457, 601, p_3 = 45,661,129`, `W12_H3`):
  1. `q = 313` (`313 - 1 = 2^3 * 3 * 13`): quarter-totient `78` (`2^78 ≡ 312 ≠ 1`, `3^78 ≡ 1`) AND
     `3`-Sylow `104` (`2^104 ≡ 214 ≠ 98 ≡ 3^104`) BOTH lock (`12 ∣ gcd(d2, d32)`);
  2. `q = 457` (`457 - 1 = 2^3 * 3 * 19`, `W12_H3` witness): `2`-Sylow FAILS (`2^57 ≡ 3^57 ≡ 348`),
     `3`-Sylow FAILS (`2^152 ≡ 1`), `5 ∤ 456`, YET `19`-Sylow (`t_19 = 24`: `2^24 ≡ 289 ≠ 215 ≡ 3^24`) locks!
  3. `q = 601` (`601 - 1 = 2^3 * 3 * 5^2`, `601 ≡ 1 (mod 120)`): escapes `{2, 3}`-Sylow (`2^25 ≡ 1` and
     `3^75 ≡ 1`), YET `5^2`-Sylow (`t_{5,2} = 120`: `2^120 ≡ 432 ≠ 1` and `3^120 ≡ 314 ≠ 432`) locks `25 ∣ gcd`!
  4. `p_3 = 45,661,129` (`p_3 - 1 = 2^3 * 3 * 461 * 4127`, `W12_H3` witness):
     `2^12381 % 45661129 = 1` (`12381 = 3 * 4127`) AND `(ratio32Mod 45661129)^1844 % 45661129 = 1`
     (`1844 = 4 * 461`) with `Nat.gcd 12381 1844 = 1`, AND `2^5707641 % 45661129 = 1`!
-/
theorem mod24_1_quarter_totient_457_601_and_p3_certs :
    (313 % 24 = 1 ∧ 2 ^ 78 % 313 = 312 ∧ 3 ^ 78 % 313 = 1 ∧
     2 ^ 104 % 313 = 214 ∧ 3 ^ 104 % 313 = 98) ∧
    (457 % 24 = 1 ∧ 457 - 1 = 2 ^ 3 * 3 * 19 ∧
     2 ^ 57 % 457 = 348 ∧ 3 ^ 57 % 457 = 348 ∧
     2 ^ 152 % 457 = 1 ∧
     2 ^ 24 % 457 = 289 ∧ 3 ^ 24 % 457 = 215) ∧
    (601 % 120 = 1 ∧ 601 - 1 = 2 ^ 3 * 3 * 5 ^ 2 ∧
     2 ^ 25 % 601 = 1 ∧ 3 ^ 75 % 601 = 1 ∧
     2 ^ 120 % 601 = 432 ∧ 3 ^ 120 % 601 = 314) ∧
    (45661129 % 24 = 1 ∧
     45661129 - 1 = 2 ^ 3 * 3 * 461 * 4127 ∧
     2 ^ 12381 % 45661129 = 1 ∧
     (ratio32Mod 45661129) ^ 1844 % 45661129 = 1 ∧
     Nat.gcd 12381 1844 = 1 ∧
     2 ^ 5707641 % 45661129 = 1) := by
  have hp3_12 : 2 ^ 12381 % 45661129 = powModFast 45661129 2 15 12381 :=
    (powModFast_eq 45661129 (by decide) 15 2 12381 (by decide)).symm
  have hp3_r : (ratio32Mod 45661129) ^ 1844 % 45661129 =
      powModFast 45661129 (ratio32Mod 45661129) 15 1844 :=
    (powModFast_eq 45661129 (by decide) 15 (ratio32Mod 45661129) 1844 (by decide)).symm
  have hp3_57 : 2 ^ 5707641 % 45661129 = powModFast 45661129 2 25 5707641 :=
    (powModFast_eq 45661129 (by decide) 25 2 5707641 (by decide)).symm
  refine ⟨by decide, by decide, by decide, ?_⟩
  rw [hp3_12, hp3_r, hp3_57]
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

-- ----------------------------------------------------------------------------
-- Section 2E: Universal `∀ m ≥ 1` `m`-Block Companion-Prime Quotient Cascades
-- ----------------------------------------------------------------------------

private theorem mem_of_mem_rotBlocks {α : Type} (j : Nat) :
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

private theorem broxSpiralCarry_dvd_of_mersenne (d : Nat) :
    ∀ bs : List (Nat × Nat),
      (∀ b ∈ bs, d ∣ (2 ^ b.2 - 1)) -> d ∣ broxSpiralCarry bs
  | [], _ => Nat.dvd_zero d
  | [b0], hall => hall b0 List.mem_cons_self
  | b0 :: b1 :: tail, hall => by
    simp only [broxSpiralCarry]
    rcases hall b0 List.mem_cons_self with ⟨c0, hc0⟩
    rcases broxSpiralCarry_dvd_of_mersenne d (b1 :: tail)
      (fun b hb => hall b (List.mem_cons_of_mem b0 hb)) with ⟨ct, hct⟩
    refine ⟨3 ^ blockWeightSum (b1 :: tail) * c0 + 2 ^ (b0.2 + b1.1) * ct, ?_⟩
    rw [hc0, hct, Nat.mul_add]
    ac_rfl

/--
  Theorem W12.2e (`m_block_companion_prime_quotient_cascades`,
  choice-free `zero custom axioms`):
  Universal `∀ m ≥ 1` `m`-Block Companion-Prime Dichotomy & Quotient Cascades (`Branch P3.4`):
  1. **Universal `∀ m ≥ 1` Block-Quotient Cascades (`blocks = b0 :: rest`, `W := blockWeightSum blocks`)**:
     For ANY `m = blocks.length ≥ 1` blocks with `∀ b ∈ blocks, b.1 ≥ 1 ∧ b.2 ≥ 1`, `3 ^ W < 2 ^ K`,
     and ANY quotient vector `qs` (`qs.length = m`, `∀ j < m, D * natAt qs j = broxSpiralCarry (rotBlocks j blocks)`):
     - `¬ (3 ∣ D)` ALWAYS, and `(∀ b ∈ blocks, 2 ∣ b.2) -> 3 ∣ natListGcd qs`;
     - `(∀ b ∈ blocks, 4 ∣ b.2) -> (2 ∣ W ∨ (¬ (5 ∣ D) ∧ 15 ∣ natListGcd qs))`;
     - `(∀ b ∈ blocks, 8 ∣ b.2) -> (2 ∣ W ∨ (¬ (5 ∣ D) ∧ ¬ (17 ∣ D) ∧ 255 ∣ natListGcd qs))` AND
       `(∀ b ∈ blocks, 8 ∣ b.2) -> (16 ∣ W ∨ (¬ (17 ∣ D) ∧ 51 ∣ natListGcd qs))`;
     - `(∀ b ∈ blocks, 3 ∣ b.2) -> (6 ∣ W ∨ (¬ (7 ∣ D) ∧ 7 ∣ natListGcd qs))`;
     - `(∀ b ∈ blocks, 5 ∣ b.2) -> (30 ∣ W ∨ (¬ (31 ∣ D) ∧ 31 ∣ natListGcd qs))`;
     - `(∀ b ∈ blocks, 9 ∣ b.2) -> (6 ∣ W ∨ (¬ (7 ∣ D) ∧ ¬ (73 ∣ D) ∧ 511 ∣ natListGcd qs))` AND
       `(∀ b ∈ blocks, 9 ∣ b.2) -> (36 ∣ W ∨ (¬ (73 ∣ D) ∧ 73 ∣ natListGcd qs))`!
  2. **Multi-Block Weight-Divisibility Sharpness (`m = 2`, `blocks = [(1, 4), (1, 4)]`)**:
     At `blocks = [(1, 4), (1, 4)]`, `4 ∣ b.2` holds for all blocks and `W = 2` (`2 ∣ W`),
     with `D = 2^10 - 3^2 = 1015` satisfying `5 ∣ 1015` (proving `2 ∣ W` cannot be dropped for `m ≥ 2`!)!
-/
theorem m_block_companion_prime_quotient_cascades :
    (∀ (b0 : Nat × Nat) (rest : List (Nat × Nat)) (qs : List Nat),
      let blocks := b0 :: rest
      let W := blockWeightSum blocks
      let K := blockStepSum blocks
      let D := 2 ^ K - 3 ^ W
      (∀ b ∈ blocks, b.1 ≥ 1 ∧ b.2 ≥ 1) ->
      3 ^ W < 2 ^ K ->
      qs.length = blocks.length ->
      (∀ j : Nat, j < blocks.length -> D * natAt qs j = broxSpiralCarry (rotBlocks j blocks)) ->
      ¬ (3 ∣ D) ∧
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
    (let blocks2 : List (Nat × Nat) := [(1, 4), (1, 4)]
     blockWeightSum blocks2 = 2 ∧
     2 ^ blockStepSum blocks2 - 3 ^ blockWeightSum blocks2 = 1015 ∧
     5 ∣ 1015) := by
  refine ⟨?_, ⟨by decide, by decide, by decide⟩⟩
  intro b0 rest qs; dsimp only; intro hpos hgt hq_len hqs_eq
  let blocks := b0 :: rest
  let W := blockWeightSum blocks
  let K := blockStepSum blocks
  let D := 2 ^ K - 3 ^ W
  have hW_ge1 : W ≥ 1 := by
    have hb0 := (hpos b0 List.mem_cons_self).1
    dsimp [W, blocks, blockWeightSum]; omega
  -- `¬ (3 ∣ D)` for all `W ≥ 1`:
  have hnd3 : ¬ (3 ∣ D) := by
    rintro ⟨c, hc⟩
    have hp3_dvd : 3 ∣ 3 ^ W := ⟨3 ^ (W - 1), by
      conv => lhs; rw [show W = (W - 1) + 1 by omega]
      rw [Nat.pow_succ, Nat.mul_comm]⟩
    rcases hp3_dvd with ⟨c3, hc3⟩
    have h2_3 : 3 ∣ 2 ^ K := ⟨c + c3, by
      have hlt : 3 ^ W < 2 ^ K := hgt
      change 2 ^ K - 3 ^ W = 3 * c at hc
      rw [Nat.mul_add]; generalize 2 ^ K = P2, 3 ^ W = P3 at hlt hc hc3 ⊢; omega⟩
    have h2m3 : 2 ^ K % 3 = 0 := by rcases h2_3 with ⟨u, hu⟩; rw [hu, Nat.mul_mod_right]
    have h2_nz : ∀ n : Nat, 2 ^ n % 3 ≠ 0 := by
      intro n; induction n with
      | zero => decide
      | succ n' ih => rw [Nat.pow_succ, Nat.mul_mod]; omega
    exact h2_nz K h2m3
  -- Master helper 1: If `p ∣ D` and `∀ b ∈ blocks, d_a ∣ b.2` and `p ∣ (2^d_a - 1)`, then `ord_p(3/2) ∣ W`:
  have hdvd_W_of_pD : ∀ (p d_a d_W : Nat),
      IsPrimeNat p -> p ≥ 5 -> d_a ≥ 1 ->
      p ∣ (2 ^ d_a - 1) ->
      IsExactMultOrderMod p (ratio32Mod p) d_W ->
      (∀ b ∈ blocks, d_a ∣ b.2) ->
      p ∣ D -> d_W ∣ W := by
    intro p d_a d_W hp hp5 _hda hp_mers hord hall hpD
    have hpo : p % 2 = 1 := by
      by_cases hev : p % 2 = 0
      · exact False.elim (hp.2 2 (Nat.le_refl 2) (by omega) (Nat.dvd_of_mod_eq_zero hev))
      · omega
    have h2b_mod1 : ∀ b ∈ blocks, 2 ^ b.2 % p = 1 := by
      intro b hb
      rcases hall b hb with ⟨kb, hkb⟩
      have hd_b : (2 ^ d_a - 1) ∣ (2 ^ b.2 - 1) := by
        rw [hkb]; simpa using pow_sub_pow_mul_dvd_w8 2 1 d_a (by decide) kb
      rcases Nat.dvd_trans hp_mers hd_b with ⟨kp, hkp⟩
      have hp2_ge2 : 2 ^ b.2 ≥ 2 := by simpa using pow2_mono_nat (hpos b hb).2
      rw [show 2 ^ b.2 = 1 + p * kp by omega, Nat.add_mul_mod_self_left,
          Nat.mod_eq_of_lt (by omega)]
    have h2K_2W : 2 ^ K % p = 2 ^ W % p :=
      pow2_stepSum_mod_eq_weightSum_mod_w6 p (by omega) blocks h2b_mod1
    have h2K_3W : 2 ^ K % p = 3 ^ W % p := by
      rcases hpD with ⟨kd, hkd⟩
      have hlt_kw : 3 ^ W < 2 ^ K := hgt
      have hrew : 2 ^ K = 3 ^ W + p * kd := by
        change 2 ^ K - 3 ^ W = p * kd at hkd
        omega
      rw [hrew, Nat.add_mul_mod_self_left]
    have h2r := two_mul_ratio32Mod_eq_three p hpo hp5
    have hmul_W : (2 ^ W * (ratio32Mod p) ^ W) % p = (2 ^ W * 1) % p := by
      rw [← pow_mul_mod_distrib_w11 p 2 (ratio32Mod p) W,
          pow_mod_eq_of_mod_eq_w5 p (2 * ratio32Mod p) 3
            (by rw [h2r, Nat.mod_eq_of_lt (by omega)]) W,
          ← h2K_3W, h2K_2W, Nat.mul_one]
    have hnd_2W : ¬ (p ∣ 2 ^ W) := by
      rintro ⟨c, hc⟩
      have hm0 : 2 ^ W % p = 0 := by rw [hc, Nat.mul_mod_right]
      exact odd_mod_pow2_nonzero_w5 p (by omega) hpo W hm0
    have hr32_W : (ratio32Mod p) ^ W % p = 1 := by
      have hc := cancel_mul_mod_prime p (2 ^ W) ((ratio32Mod p) ^ W) 1 hp hnd_2W hmul_W
      rwa [Nat.mod_eq_of_lt (by omega : 1 < p)] at hc
    exact exactMultOrderMod_dvd_of_pow_eq_one p (ratio32Mod p) d_W W hord hr32_W
  -- Master helper 2: Cancel `D` on EVERY `natAt qs j` (`j < m`) via `prime_list_cancel_dvd_w8`:
  have hqs_cascade : ∀ (d_a : Nat) (ps : List Nat),
      (∀ b ∈ blocks, d_a ∣ b.2) ->
      natProdList ps ∣ (2 ^ d_a - 1) ->
      (∀ p ∈ ps, p ≤ 160 ∧ checkUnitsGrid16x10 p ∧ ¬ (p ∣ D)) ->
      natProdList ps ∣ natListGcd qs := by
    intro d_a ps hall hprod_dvd hp_ok
    apply dvd_natListGcd_of_forall (natProdList ps) qs
    intro q_val hq_mem
    rcases mem_imp_exists_natAt_w6 qs q_val hq_mem with ⟨j, hj_lt, hqj⟩
    rw [hq_len] at hj_lt
    have hm_rot : ∀ b ∈ rotBlocks j blocks, (2 ^ d_a - 1) ∣ (2 ^ b.2 - 1) := by
      intro b hb_rot
      have hb_in : b ∈ blocks := mem_of_mem_rotBlocks j blocks b hb_rot
      rcases hall b hb_in with ⟨kb, hkb⟩
      rw [hkb]
      simpa using pow_sub_pow_mul_dvd_w8 2 1 d_a (by decide) kb
    have hdvd_H : natProdList ps * 1 ∣ D * q_val := by
      rw [Nat.mul_one, ← hqj, hqs_eq j hj_lt]
      exact Nat.dvd_trans hprod_dvd (broxSpiralCarry_dvd_of_mersenne (2 ^ d_a - 1) (rotBlocks j blocks) hm_rot)
    exact prime_list_cancel_dvd_w8 D ps q_val 1 hp_ok hdvd_H
  refine ⟨hnd3, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `2 ∣ b.2 -> 3 ∣ natListGcd qs`:
    intro h2
    simpa [natProdList] using hqs_cascade 2 [3] h2 (by decide)
      (fun p hp => by simp at hp; subst hp; exact ⟨by decide, by decide, hnd3⟩)
  · -- `4 ∣ b.2 -> 2 ∣ W ∨ (¬(5 ∣ D) ∧ 15 ∣ natListGcd qs)`:
    intro h4
    by_cases h2W : 2 ∣ W
    · exact Or.inl h2W
    · right
      have hnd5 : ¬ (5 ∣ D) := fun h5D => h2W (hdvd_W_of_pD 5 4 2
        (checkSmallPrimeBool_sound 5 (by decide)) (by decide) (by decide) (by decide) (by decide) h4 h5D)
      refine ⟨hnd5, ?_⟩
      simpa [natProdList] using hqs_cascade 4 [3, 5] h4 (by decide) (fun p hp => by
        simp at hp; rcases hp with rfl | rfl
        · exact ⟨by decide, by decide, hnd3⟩
        · exact ⟨by decide, by decide, hnd5⟩)
  · -- `8 ∣ b.2`: both `(2 ∣ W ∨ ... 255)` and `(16 ∣ W ∨ ... 51)`:
    intro h8
    refine ⟨?_, ?_⟩
    · by_cases h2W : 2 ∣ W
      · exact Or.inl h2W
      · right
        have hnd5 : ¬ (5 ∣ D) := fun h5D => h2W (hdvd_W_of_pD 5 8 2
          (checkSmallPrimeBool_sound 5 (by decide)) (by decide) (by decide) (by decide) (by decide) h8 h5D)
        have hnd17 : ¬ (17 ∣ D) := fun h17D => by
          have h16W := hdvd_W_of_pD 17 8 16
            (checkSmallPrimeBool_sound 17 (by decide)) (by decide) (by decide) (by decide) (by decide) h8 h17D
          exact h2W (Nat.dvd_trans (by decide : 2 ∣ 16) h16W)
        refine ⟨hnd5, hnd17, ?_⟩
        simpa [natProdList] using hqs_cascade 8 [3, 5, 17] h8 (by decide) (fun p hp => by
          simp at hp; rcases hp with rfl | rfl | rfl
          · exact ⟨by decide, by decide, hnd3⟩
          · exact ⟨by decide, by decide, hnd5⟩
          · exact ⟨by decide, by decide, hnd17⟩)
    · by_cases h16W : 16 ∣ W
      · exact Or.inl h16W
      · right
        have hnd17 : ¬ (17 ∣ D) := fun h17D => h16W (hdvd_W_of_pD 17 8 16
          (checkSmallPrimeBool_sound 17 (by decide)) (by decide) (by decide) (by decide) (by decide) h8 h17D)
        refine ⟨hnd17, ?_⟩
        simpa [natProdList] using hqs_cascade 8 [3, 17] h8 (by decide) (fun p hp => by
          simp at hp; rcases hp with rfl | rfl
          · exact ⟨by decide, by decide, hnd3⟩
          · exact ⟨by decide, by decide, hnd17⟩)
  · -- `3 ∣ b.2 -> 6 ∣ W ∨ (¬(7 ∣ D) ∧ 7 ∣ natListGcd qs)`:
    intro h3
    by_cases h6W : 6 ∣ W
    · exact Or.inl h6W
    · right
      have hnd7 : ¬ (7 ∣ D) := fun h7D => h6W (hdvd_W_of_pD 7 3 6
        (checkSmallPrimeBool_sound 7 (by decide)) (by decide) (by decide) (by decide) (by decide) h3 h7D)
      refine ⟨hnd7, ?_⟩
      simpa [natProdList] using hqs_cascade 3 [7] h3 (by decide)
        (fun p hp => by simp at hp; subst hp; exact ⟨by decide, by decide, hnd7⟩)
  · -- `5 ∣ b.2 -> 30 ∣ W ∨ (¬(31 ∣ D) ∧ 31 ∣ natListGcd qs)`:
    intro h5
    by_cases h30W : 30 ∣ W
    · exact Or.inl h30W
    · right
      have hnd31 : ¬ (31 ∣ D) := fun h31D => h30W (hdvd_W_of_pD 31 5 30
        (checkSmallPrimeBool_sound 31 (by decide)) (by decide) (by decide) (by decide) (by decide) h5 h31D)
      refine ⟨hnd31, ?_⟩
      simpa [natProdList] using hqs_cascade 5 [31] h5 (by decide)
        (fun p hp => by simp at hp; subst hp; exact ⟨by decide, by decide, hnd31⟩)
  · -- `9 ∣ b.2`: both `(6 ∣ W ∨ ... 511)` and `(36 ∣ W ∨ ... 73)`:
    intro h9
    refine ⟨?_, ?_⟩
    · by_cases h6W : 6 ∣ W
      · exact Or.inl h6W
      · right
        have hnd7 : ¬ (7 ∣ D) := fun h7D => h6W (hdvd_W_of_pD 7 9 6
          (checkSmallPrimeBool_sound 7 (by decide)) (by decide) (by decide) (by decide) (by decide) h9 h7D)
        have hnd73 : ¬ (73 ∣ D) := fun h73D => by
          have h36W := hdvd_W_of_pD 73 9 36
            (checkSmallPrimeBool_sound 73 (by decide)) (by decide) (by decide) (by decide) (by decide) h9 h73D
          exact h6W (Nat.dvd_trans (by decide : 6 ∣ 36) h36W)
        refine ⟨hnd7, hnd73, ?_⟩
        simpa [natProdList] using hqs_cascade 9 [7, 73] h9 (by decide) (fun p hp => by
          simp at hp; rcases hp with rfl | rfl
          · exact ⟨by decide, by decide, hnd7⟩
          · exact ⟨by decide, by decide, hnd73⟩)
    · by_cases h36W : 36 ∣ W
      · exact Or.inl h36W
      · right
        have hnd73 : ¬ (73 ∣ D) := fun h73D => h36W (hdvd_W_of_pD 73 9 36
          (checkSmallPrimeBool_sound 73 (by decide)) (by decide) (by decide) (by decide) (by decide) h9 h73D)
        refine ⟨hnd73, ?_⟩
        simpa [natProdList] using hqs_cascade 9 [73] h9 (by decide)
          (fun p hp => by simp at hp; subst hp; exact ⟨by decide, by decide, hnd73⟩)

end CollatzFormal
