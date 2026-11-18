/-
  CollatzFormal/Wave8WholeSpace.lean
  Wave 8 Whole-Space Mathematical & CS Proof Loop:
  1. Front A — Pushing `7/11 -> 10/11` Mixed `(2, 3)` Positive Collatz SRS via `2D`
     Non-Triangular Hofbauer–Waldmann Towers, Universal `ω^k` Soundness -> `CollatzConjectureStandard`,
     Arts–Giesl Shifted Semantic DP, & All-Dimension `ω^k` Matrix Tower Barriers (Branch P4.3)
  2. Front B — Cyclotomic Companion-Prime Quotient Forcing Against `p = 331`, Closed Mod-8
     Subgroup Obstruction, 2-Block `(99, 159)` Floor, & Pure-Integer Laurent Binomial-Taylor
     Column Extrapolation `(2^u - 1)^T ∣ det M_0` (Branches P3.4 & P3.3)
  3. Front C — Base-2 Ripple-Carry Cascade Collapse, Non-Separable Multivariate Preimage Barrier,
     Universal `∀ W_win ≥ 1` Sliding-Window `k`-Gram Barrier, & 5th Solvable Cousin `T_diamond5`
     (Branches P1.2 & P5)
  4. Front D — Exact Cross-Scale (`|u_1| < |u_2|`) `q = 0` Leaf Collision Biconditional,
     Unconditional Multi-Scale `NoDupNat`, & Markov Skew-Product Bijectivity / Forbidden
     `5 mod 6` Law (Branches P5.3 & P2.2)

  Zero external dependencies (pure Lean 4.35.0 Core), zero `sorry`,
  zero `native_decide`, zero custom `axiom`.
-/

import CollatzFormal.Wave7WholeSpace

namespace CollatzFormal

-- ============================================================================
-- SECTION 1: Front A (Branch P4.3) — `10/11` Non-Triangular Hofbauer–Waldmann
--            Matrix Certificates & Rule-Removal Towers, Universal `ω^k` Tower
--            Soundness, Arts–Giesl Semantic DP, & `∀ d ≥ 1, ∀ k` Tower Barriers
-- ============================================================================

/-- Entrywise weak orientation `A ≥ B` on `d`-dimensional natural matrix interpretations. -/
def weakOrientsNatAffineDim (d : Nat) (A B : NatAffineDim d) : Prop :=
  (∀ i j : Fin d, A.M i j ≥ B.M i j) ∧
  (∀ i : Fin d, A.v i ≥ B.v i)

/-- Single rewrite step `p ++ l ++ q -> p ++ r ++ q` over an explicit list of SRS rules. -/
def srsStepFromList (rules : List (List MixedSRSSym × List MixedSRSSym))
    (w1 w2 : List MixedSRSSym) : Prop :=
  ∃ p l r q : List MixedSRSSym,
    (l, r) ∈ rules ∧ w1 = p ++ l ++ q ∧ w2 = p ++ r ++ q

/-- Reflexive-transitive closure over `srsStepFromList rules`. -/
inductive srsReachesFromList (rules : List (List MixedSRSSym × List MixedSRSSym)) :
    List MixedSRSSym -> List MixedSRSSym -> Prop where
  | refl (w : List MixedSRSSym) : srsReachesFromList rules w w
  | step {w1 w2 w3 : List MixedSRSSym} :
      srsStepFromList rules w1 w2 ->
      srsReachesFromList rules w2 w3 ->
      srsReachesFromList rules w1 w3

/-- Non-empty (`≥ 1` step) rewrite derivation over `rules`. -/
def srsPlusFromList (rules : List (List MixedSRSSym × List MixedSRSSym))
    (w1 w3 : List MixedSRSSym) : Prop :=
  ∃ w2 : List MixedSRSSym,
    srsStepFromList rules w1 w2 ∧ srsReachesFromList rules w2 w3

/--
  `k`-level Zantema–Hofbauer–Waldmann `ω^k` natural matrix rule-removal tower in dimension `d ≥ 1`:
  At each level, `interp` satisfies Hofbauer–Waldmann top-left positivity `(M_s)_{0,0} ≥ 1` across
  all symbols, weakly orients every active rule (`weakOrientsNatAffineDim`), keeps all non-strictly
  oriented rules in `rem`, and terminates at `[]` in `≤ k` levels.
-/
def OmegaHofbauerWaldmannTower (d : Nat) (hd : 0 < d) :
    Nat -> List (List MixedSRSSym × List MixedSRSSym) -> Prop
  | 0, rules => rules = []
  | k + 1, rules =>
    rules = [] ∨
    ∃ (rem : List (List MixedSRSSym × List MixedSRSSym))
      (interp : MixedSRSSym -> NatAffineDim d),
      (∀ s : MixedSRSSym, (interp s).M ⟨0, hd⟩ ⟨0, hd⟩ ≥ 1) ∧
      (∀ r ∈ rules, weakOrientsNatAffineDim d
        (evalWordNatAffineDim d interp r.1) (evalWordNatAffineDim d interp r.2)) ∧
      (∀ r ∈ rules, ¬ orientsNatAffineDim d hd
        (evalWordNatAffineDim d interp r.1) (evalWordNatAffineDim d interp r.2) -> r ∈ rem) ∧
      OmegaHofbauerWaldmannTower d hd k rem

theorem natMatVec_add_w8 (d : Nat) (A : Fin d -> Fin d -> Nat)
    (u v : Fin d -> Nat) (i : Fin d) :
    natMatVec d A (fun k => u k + v k) i = natMatVec d A u i + natMatVec d A v i := by
  have hmul : ∀ n : Nat,
      natSumPrefix d (fun k => A i k * (u k + v k)) n =
        natSumPrefix d (fun k => A i k * u k + A i k * v k) n :=
    fun n => natSumPrefix_congr d _ _ (fun k => Nat.mul_add (A i k) (u k) (v k)) n
  unfold natMatVec natSumFin
  rw [hmul d, natSumPrefix_add]

theorem natMatVec_mul_w8 (d : Nat) (A B : Fin d -> Fin d -> Nat)
    (u : Fin d -> Nat) (i : Fin d) :
    natMatVec d (natMatMul d A B) u i = natMatVec d A (natMatVec d B u) i := by
  have hzero : ∀ m : Nat, natSumPrefix d (fun _ => 0) m = 0 := natSumPrefix_zero_w6 d
  have hmul_r : ∀ (f : Fin d -> Nat) (c n : Nat),
      natSumPrefix d f n * c = natSumPrefix d (fun k => f k * c) n := by
    intro f c n
    induction n with
    | zero => simp [natSumPrefix]
    | succ n' ih =>
      simp only [natSumPrefix]
      by_cases hn : n' < d
      · simp only [hn, dite_true, Nat.add_mul, ih]
      · simp only [hn, dite_false, Nat.add_zero, ih]
  have hmul_l : ∀ (c : Nat) (f : Fin d -> Nat) (n : Nat),
      c * natSumPrefix d f n = natSumPrefix d (fun k => c * f k) n := by
    intro c f n
    induction n with
    | zero => simp [natSumPrefix]
    | succ n' ih =>
      simp only [natSumPrefix]
      by_cases hn : n' < d
      · simp only [hn, dite_true, Nat.mul_add, ih]
      · simp only [hn, dite_false, Nat.add_zero, ih]
  have hswap : ∀ (F : Fin d -> Fin d -> Nat) (m n : Nat),
      natSumPrefix d (fun q => natSumPrefix d (fun p => F p q) m) n =
        natSumPrefix d (fun p => natSumPrefix d (fun q => F p q) n) m := by
    intro F m n
    induction n with
    | zero => simp only [natSumPrefix]; exact (hzero m).symm
    | succ n' ihn =>
      simp only [natSumPrefix]
      by_cases hn : n' < d
      · simp only [hn, dite_true, ihn, ← natSumPrefix_add]
      · simp only [hn, dite_false, Nat.add_zero, ihn]
  unfold natMatVec natMatMul natSumFin
  have hl : natSumPrefix d (fun q => natSumPrefix d (fun p => A i p * B p q) d * u q) d =
      natSumPrefix d (fun q => natSumPrefix d (fun p => A i p * B p q * u q) d) d :=
    natSumPrefix_congr d _ _ (fun q => hmul_r (fun p => A i p * B p q) (u q) d) d
  have hr : natSumPrefix d (fun p => A i p * natSumPrefix d (fun q => B p q * u q) d) d =
      natSumPrefix d (fun p => natSumPrefix d (fun q => A i p * B p q * u q) d) d :=
    natSumPrefix_congr d _ _ (fun p =>
      (hmul_l (A i p) (fun q => B p q * u q) d).trans
        (natSumPrefix_congr d _ _ (fun q => (Nat.mul_assoc _ _ _).symm) d)) d
  rw [hl, hr, hswap]

theorem compNatAffineDim_assoc_w8 (d : Nat) (A B C : NatAffineDim d) :
    (∀ i j : Fin d, (compNatAffineDim d (compNatAffineDim d A B) C).M i j =
      (compNatAffineDim d A (compNatAffineDim d B C)).M i j) ∧
    (∀ i : Fin d, (compNatAffineDim d (compNatAffineDim d A B) C).v i =
      (compNatAffineDim d A (compNatAffineDim d B C)).v i) := by
  refine ⟨fun i j => natMatMul_assoc_w5 d A.M B.M C.M i j, ?_⟩
  intro i
  simp only [compNatAffineDim]
  rw [natMatVec_mul_w8 d A.M B.M C.v i, natMatVec_add_w8 d A.M (natMatVec d B.M C.v) B.v i]
  omega

theorem evalWordNatAffineDim_append_w8 (d : Nat) (interp : MixedSRSSym -> NatAffineDim d) :
    ∀ (u v : List MixedSRSSym),
      (∀ i j : Fin d, (evalWordNatAffineDim d interp (u ++ v)).M i j =
        (compNatAffineDim d (evalWordNatAffineDim d interp u) (evalWordNatAffineDim d interp v)).M i j) ∧
      (∀ i : Fin d, (evalWordNatAffineDim d interp (u ++ v)).v i =
        (compNatAffineDim d (evalWordNatAffineDim d interp u) (evalWordNatAffineDim d interp v)).v i)
  | [], v => by
    refine ⟨?_, ?_⟩
    · intro i j
      simp only [List.nil_append, evalWordNatAffineDim, compNatAffineDim]
      exact (natMatMul_left_id_w5 d _ i j).symm
    · intro i
      simp only [List.nil_append, evalWordNatAffineDim, compNatAffineDim, Nat.add_zero]
      exact (natMatVec_id d _ i).symm
  | s :: u, v => by
    rcases evalWordNatAffineDim_append_w8 d interp u v with ⟨hm_uv, hv_uv⟩
    rcases compNatAffineDim_assoc_w8 d (interp s)
      (evalWordNatAffineDim d interp u) (evalWordNatAffineDim d interp v) with ⟨hm_a, hv_a⟩
    refine ⟨?_, ?_⟩
    · intro i j
      simp only [List.cons_append, evalWordNatAffineDim]
      have hc : (compNatAffineDim d (interp s) (evalWordNatAffineDim d interp (u ++ v))).M i j =
          (compNatAffineDim d (interp s)
            (compNatAffineDim d (evalWordNatAffineDim d interp u)
              (evalWordNatAffineDim d interp v))).M i j :=
        natSumPrefix_congr d _ _ (fun k => by rw [hm_uv k j]) d
      exact hc.trans (hm_a i j).symm
    · intro i
      simp only [List.cons_append, evalWordNatAffineDim]
      have hc : (compNatAffineDim d (interp s) (evalWordNatAffineDim d interp (u ++ v))).v i =
          (compNatAffineDim d (interp s)
            (compNatAffineDim d (evalWordNatAffineDim d interp u)
              (evalWordNatAffineDim d interp v))).v i := by
        have hmv : natMatVec d (interp s).M (evalWordNatAffineDim d interp (u ++ v)).v i =
            natMatVec d (interp s).M
              (compNatAffineDim d (evalWordNatAffineDim d interp u)
                (evalWordNatAffineDim d interp v)).v i :=
          natSumPrefix_congr d _ _ (fun k => by rw [hv_uv k]) d
        exact congrArg (· + (interp s).v i) hmv
      exact hc.trans (hv_a i).symm

theorem evalWord_topLeft_ge_one_w8 (d : Nat) (hd : 0 < d)
    (interp : MixedSRSSym -> NatAffineDim d)
    (htop : ∀ s : MixedSRSSym, (interp s).M ⟨0, hd⟩ ⟨0, hd⟩ ≥ 1) :
    ∀ u : List MixedSRSSym, (evalWordNatAffineDim d interp u).M ⟨0, hd⟩ ⟨0, hd⟩ ≥ 1
  | [] => by simp [evalWordNatAffineDim, natMatId]
  | s :: u => by
    have ih := evalWord_topLeft_ge_one_w8 d hd interp htop u
    simp only [evalWordNatAffineDim, compNatAffineDim]
    have hge : (interp s).M ⟨0, hd⟩ ⟨0, hd⟩ * (evalWordNatAffineDim d interp u).M ⟨0, hd⟩ ⟨0, hd⟩ ≤
        natMatMul d (interp s).M (evalWordNatAffineDim d interp u).M ⟨0, hd⟩ ⟨0, hd⟩ := by
      have hk : ∀ k : Fin d,
          (if k.val = 0 then (interp s).M ⟨0, hd⟩ ⟨0, hd⟩ * (evalWordNatAffineDim d interp u).M ⟨0, hd⟩ ⟨0, hd⟩ else 0) ≤
            (interp s).M ⟨0, hd⟩ k * (evalWordNatAffineDim d interp u).M k ⟨0, hd⟩ := by
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

theorem natMatVec_mono_vec_w8 (d : Nat) (A : Fin d -> Fin d -> Nat)
    (u v : Fin d -> Nat) (huv : ∀ k : Fin d, u k ≥ v k) (i : Fin d) :
    natMatVec d A u i ≥ natMatVec d A v i :=
  natSumPrefix_mono_w5 d (fun k => A i k * v k) (fun k => A i k * u k)
    (fun k => Nat.mul_le_mul_left (A i k) (huv k)) d

theorem natMatVec_mono_mat_w8 (d : Nat) (A B : Fin d -> Fin d -> Nat)
    (u : Fin d -> Nat) (hAB : ∀ i j : Fin d, A i j ≥ B i j) (i : Fin d) :
    natMatVec d A u i ≥ natMatVec d B u i :=
  natSumPrefix_mono_w5 d (fun k => B i k * u k) (fun k => A i k * u k)
    (fun k => Nat.mul_le_mul_right (u k) (hAB i k)) d

theorem natMatVec_strict_top_w8 (d : Nat) (hd : 0 < d) (A : Fin d -> Fin d -> Nat)
    (u v : Fin d -> Nat)
    (hA00 : A ⟨0, hd⟩ ⟨0, hd⟩ ≥ 1)
    (huv : ∀ k : Fin d, u k ≥ v k)
    (hgt0 : u ⟨0, hd⟩ > v ⟨0, hd⟩) :
    natMatVec d A u ⟨0, hd⟩ > natMatVec d A v ⟨0, hd⟩ := by
  have hk_ge : ∀ k : Fin d,
      A ⟨0, hd⟩ k * u k ≥ A ⟨0, hd⟩ k * v k + (if k.val = 0 then 1 else 0) := by
    intro k
    by_cases hk0 : k.val = 0
    · have hkz : k = ⟨0, hd⟩ := Fin.ext hk0
      subst hkz
      simp
      have hm := Nat.mul_le_mul_left (A ⟨0, hd⟩ ⟨0, hd⟩) (by omega : v ⟨0, hd⟩ + 1 ≤ u ⟨0, hd⟩)
      rw [Nat.mul_add, Nat.mul_one] at hm
      omega
    · simp only [hk0, ite_false, Nat.add_zero]
      exact Nat.mul_le_mul_left (A ⟨0, hd⟩ k) (huv k)
  have hsum := natSumPrefix_mono_w5 d
    (fun k => A ⟨0, hd⟩ k * v k + (if k.val = 0 then 1 else 0))
    (fun k => A ⟨0, hd⟩ k * u k) hk_ge d
  rw [natSumPrefix_add, natSumPrefix_single d ⟨0, hd⟩ 1 d] at hsum
  simp [hd] at hsum
  unfold natMatVec natSumFin
  omega

theorem compNatAffineDim_weak_mono_w8 (d : Nat) (A1 A2 B1 B2 : NatAffineDim d)
    (hA : weakOrientsNatAffineDim d A1 A2)
    (hB : weakOrientsNatAffineDim d B1 B2) :
    weakOrientsNatAffineDim d (compNatAffineDim d A1 B1) (compNatAffineDim d A2 B2) := by
  refine ⟨?_, ?_⟩
  · intro i j
    simp only [compNatAffineDim]
    exact Nat.le_trans
      (natMatMul_mono_right_w5 d A2.M B1.M B2.M hB.1 i j)
      (natMatMul_mono_left_w5 d A1.M A2.M B1.M hA.1 i j)
  · intro i
    simp only [compNatAffineDim]
    have hm1 := natMatVec_mono_vec_w8 d A1.M B1.v B2.v hB.2 i
    have hm2 := natMatVec_mono_mat_w8 d A1.M A2.M B2.v hA.1 i
    have hv := hA.2 i
    omega

theorem hofbauer_waldmann_context_monotonicity
    (d : Nat) (hd : 0 < d) (interp : MixedSRSSym -> NatAffineDim d)
    (htop : ∀ s : MixedSRSSym, (interp s).M ⟨0, hd⟩ ⟨0, hd⟩ ≥ 1)
    (p l r q : List MixedSRSSym) :
    (weakOrientsNatAffineDim d
      (evalWordNatAffineDim d interp l) (evalWordNatAffineDim d interp r) ->
      weakOrientsNatAffineDim d
        (evalWordNatAffineDim d interp (p ++ l ++ q))
        (evalWordNatAffineDim d interp (p ++ r ++ q))) ∧
    (orientsNatAffineDim d hd
      (evalWordNatAffineDim d interp l) (evalWordNatAffineDim d interp r) ->
      orientsNatAffineDim d hd
        (evalWordNatAffineDim d interp (p ++ l ++ q))
        (evalWordNatAffineDim d interp (p ++ r ++ q))) := by
  let EP := evalWordNatAffineDim d interp p
  let EL := evalWordNatAffineDim d interp l
  let ER := evalWordNatAffineDim d interp r
  let EQ := evalWordNatAffineDim d interp q
  have hrefl_P : weakOrientsNatAffineDim d EP EP := ⟨fun _ _ => Nat.le_refl _, fun _ => Nat.le_refl _⟩
  have hrefl_Q : weakOrientsNatAffineDim d EQ EQ := ⟨fun _ _ => Nat.le_refl _, fun _ => Nat.le_refl _⟩
  rcases evalWordNatAffineDim_append_w8 d interp (p ++ l) q with ⟨hm_plq1, hv_plq1⟩
  rcases evalWordNatAffineDim_append_w8 d interp p l with ⟨hm_pl, hv_pl⟩
  rcases evalWordNatAffineDim_append_w8 d interp (p ++ r) q with ⟨hm_prq1, hv_prq1⟩
  rcases evalWordNatAffineDim_append_w8 d interp p r with ⟨hm_pr, hv_pr⟩
  have hweak_ctx : weakOrientsNatAffineDim d EL ER ->
      weakOrientsNatAffineDim d
        (evalWordNatAffineDim d interp (p ++ l ++ q))
        (evalWordNatAffineDim d interp (p ++ r ++ q)) := by
    intro hlr
    have hpl : weakOrientsNatAffineDim d (evalWordNatAffineDim d interp (p ++ l))
        (evalWordNatAffineDim d interp (p ++ r)) := by
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
  -- Rewrite `(p ++ l) ++ q = p ++ (l ++ q)` to expose left-multiplication by `EP`:
  have hassoc_l : p ++ l ++ q = p ++ (l ++ q) := List.append_assoc p l q
  have hassoc_r : p ++ r ++ q = p ++ (r ++ q) := List.append_assoc p r q
  rcases evalWordNatAffineDim_append_w8 d interp p (l ++ q) with ⟨_, hv_p_lq⟩
  rcases evalWordNatAffineDim_append_w8 d interp p (r ++ q) with ⟨_, hv_p_rq⟩
  rcases evalWordNatAffineDim_append_w8 d interp l q with ⟨_, hv_lq⟩
  rcases evalWordNatAffineDim_append_w8 d interp r q with ⟨_, hv_rq⟩
  have hw_lq_rq : ∀ k : Fin d,
      (evalWordNatAffineDim d interp (l ++ q)).v k ≥
        (evalWordNatAffineDim d interp (r ++ q)).v k := by
    intro k
    have hc := (compNatAffineDim_weak_mono_w8 d EL ER EQ EQ hw_lr hrefl_Q).2 k
    rw [hv_lq k, hv_rq k]; exact hc
  have hgt_lq_rq : (evalWordNatAffineDim d interp (l ++ q)).v ⟨0, hd⟩ >
      (evalWordNatAffineDim d interp (r ++ q)).v ⟨0, hd⟩ := by
    rw [hv_lq ⟨0, hd⟩, hv_rq ⟨0, hd⟩]
    simp only [compNatAffineDim]
    have hm_q := natMatVec_mono_mat_w8 d
      (evalWordNatAffineDim d interp l).M
      (evalWordNatAffineDim d interp r).M
      (evalWordNatAffineDim d interp q).v hstrict.1 ⟨0, hd⟩
    have hv0_gt : (evalWordNatAffineDim d interp l).v ⟨0, hd⟩ >
        (evalWordNatAffineDim d interp r).v ⟨0, hd⟩ := hstrict.2.2
    omega
  have hp_top := evalWord_topLeft_ge_one_w8 d hd interp htop p
  have hmv_gt := natMatVec_strict_top_w8 d hd (evalWordNatAffineDim d interp p).M
    (evalWordNatAffineDim d interp (l ++ q)).v
    (evalWordNatAffineDim d interp (r ++ q)).v
    hp_top hw_lq_rq hgt_lq_rq
  rw [hassoc_l, hassoc_r, hv_p_lq ⟨0, hd⟩, hv_p_rq ⟨0, hd⟩]
  simp only [compNatAffineDim]
  omega

theorem srsPlus_preserves_weak_and_rem_w8
    (d : Nat) (hd : 0 < d)
    (rules rem : List (List MixedSRSSym × List MixedSRSSym))
    (interp : MixedSRSSym -> NatAffineDim d)
    (htop : ∀ s : MixedSRSSym, (interp s).M ⟨0, hd⟩ ⟨0, hd⟩ ≥ 1)
    (hweak : ∀ r ∈ rules, weakOrientsNatAffineDim d
      (evalWordNatAffineDim d interp r.1) (evalWordNatAffineDim d interp r.2))
    (hkeep : ∀ r ∈ rules, ¬ orientsNatAffineDim d hd
      (evalWordNatAffineDim d interp r.1) (evalWordNatAffineDim d interp r.2) -> r ∈ rem) :
    (∀ w1 w3 : List MixedSRSSym,
      srsReachesFromList rules w1 w3 ->
      (evalWordNatAffineDim d interp w1).v ⟨0, hd⟩ ≥
        (evalWordNatAffineDim d interp w3).v ⟨0, hd⟩ ∧
      ((evalWordNatAffineDim d interp w1).v ⟨0, hd⟩ =
        (evalWordNatAffineDim d interp w3).v ⟨0, hd⟩ ->
        srsReachesFromList rem w1 w3)) ∧
    (∀ w1 w3 : List MixedSRSSym,
      srsPlusFromList rules w1 w3 ->
      (evalWordNatAffineDim d interp w1).v ⟨0, hd⟩ ≥
        (evalWordNatAffineDim d interp w3).v ⟨0, hd⟩ ∧
      ((evalWordNatAffineDim d interp w1).v ⟨0, hd⟩ =
        (evalWordNatAffineDim d interp w3).v ⟨0, hd⟩ ->
        srsPlusFromList rem w1 w3)) := by
  have hstep_prop : ∀ w1 w2 : List MixedSRSSym,
      srsStepFromList rules w1 w2 ->
      (evalWordNatAffineDim d interp w1).v ⟨0, hd⟩ ≥ (evalWordNatAffineDim d interp w2).v ⟨0, hd⟩ ∧
      ((evalWordNatAffineDim d interp w1).v ⟨0, hd⟩ = (evalWordNatAffineDim d interp w2).v ⟨0, hd⟩ ->
        srsStepFromList rem w1 w2) := by
    intro w1 w2 ⟨p, l, r, q, hmem, hw1, hw2⟩
    rcases hofbauer_waldmann_context_monotonicity d hd interp htop p l r q with ⟨hw_c, hs_c⟩
    have hw_step := hw_c (hweak (l, r) hmem)
    rw [← hw1, ← hw2] at hw_step
    refine ⟨hw_step.2 ⟨0, hd⟩, ?_⟩
    intro heq_z
    have hnot_strict : ¬ orientsNatAffineDim d hd
        (evalWordNatAffineDim d interp l) (evalWordNatAffineDim d interp r) := by
      intro hstr
      have hsc := hs_c hstr
      rw [← hw1, ← hw2] at hsc
      have hgt := hsc.2.2
      omega
    exact ⟨p, l, r, q, hkeep (l, r) hmem hnot_strict, hw1, hw2⟩
  have hreach_prop : ∀ w1 w3 : List MixedSRSSym,
      srsReachesFromList rules w1 w3 ->
      (evalWordNatAffineDim d interp w1).v ⟨0, hd⟩ ≥ (evalWordNatAffineDim d interp w3).v ⟨0, hd⟩ ∧
      ((evalWordNatAffineDim d interp w1).v ⟨0, hd⟩ = (evalWordNatAffineDim d interp w3).v ⟨0, hd⟩ ->
        srsReachesFromList rem w1 w3) := by
    intro w1 w3 hr
    induction hr with
    | refl w => exact ⟨Nat.le_refl _, fun _ => srsReachesFromList.refl w⟩
    | @step a b c hs _ ih =>
      rcases hstep_prop a b hs with ⟨hge1, hrem1⟩
      rcases ih with ⟨hge2, hrem2⟩
      refine ⟨Nat.le_trans hge2 hge1, ?_⟩
      intro heq_ac
      have heq_ab : (evalWordNatAffineDim d interp a).v ⟨0, hd⟩ =
          (evalWordNatAffineDim d interp b).v ⟨0, hd⟩ := by omega
      have heq_bc : (evalWordNatAffineDim d interp b).v ⟨0, hd⟩ =
          (evalWordNatAffineDim d interp c).v ⟨0, hd⟩ := by omega
      exact srsReachesFromList.step (hrem1 heq_ab) (hrem2 heq_bc)
  refine ⟨hreach_prop, ?_⟩
  intro w1 w3 ⟨w2, hs12, hr23⟩
  rcases hstep_prop w1 w2 hs12 with ⟨hge1, hrem1⟩
  rcases hreach_prop w2 w3 hr23 with ⟨hge2, hrem2⟩
  refine ⟨Nat.le_trans hge2 hge1, ?_⟩
  intro heq_13
  have heq_12 : (evalWordNatAffineDim d interp w1).v ⟨0, hd⟩ =
      (evalWordNatAffineDim d interp w2).v ⟨0, hd⟩ := by omega
  have heq_23 : (evalWordNatAffineDim d interp w2).v ⟨0, hd⟩ =
      (evalWordNatAffineDim d interp w3).v ⟨0, hd⟩ := by omega
  exact ⟨w2, hrem1 heq_12, hrem2 heq_23⟩

/--
  Theorem W8.1a (`hofbauer_waldmann_tower_implies_no_infinite_srs_chain`, zero custom axioms):
  Universal Soundness of `d`-Dimensional `ω^k` Hofbauer–Waldmann Rule-Removal Towers:
  For EVERY `d ≥ 1` and EVERY `k : Nat`, if `OmegaHofbauerWaldmannTower d hd k rules` holds,
  then `rules` admits NO infinite rewrite derivation `seq 0 ->+ seq 1 ->+ seq 2 ->+ ...`
  (including single-step infinite chains `seq 0 -> seq 1 -> seq 2 -> ...`)!
-/
theorem hofbauer_waldmann_tower_implies_no_infinite_srs_chain :
    ∀ (d : Nat) (hd : 0 < d) (k : Nat)
      (rules : List (List MixedSRSSym × List MixedSRSSym)),
      OmegaHofbauerWaldmannTower d hd k rules ->
      (∀ seq : Nat -> List MixedSRSSym,
        ¬ (∀ t : Nat, srsPlusFromList rules (seq t) (seq (t + 1)))) ∧
      (∀ seq : Nat -> List MixedSRSSym,
        ¬ (∀ t : Nat, srsStepFromList rules (seq t) (seq (t + 1)))) := by
  intro d hd k
  have hno_plus : ∀ (lvl : Nat) (rules : List (List MixedSRSSym × List MixedSRSSym)),
      OmegaHofbauerWaldmannTower d hd lvl rules ->
      ∀ seq : Nat -> List MixedSRSSym,
        ¬ (∀ t : Nat, srsPlusFromList rules (seq t) (seq (t + 1))) := by
    intro lvl
    induction lvl with
    | zero =>
      intro rules h0 seq hinf
      rw [OmegaHofbauerWaldmannTower] at h0
      subst h0
      rcases hinf 0 with ⟨_, ⟨_, _, _, _, hm, _, _⟩, _⟩
      cases hm
    | succ lvl' ih =>
      intro rules hsucc seq hinf
      rcases hsucc with rfl | ⟨rem, interp, htop, hweak, hkeep, hrem_tower⟩
      · rcases hinf 0 with ⟨_, ⟨_, _, _, _, hm, _, _⟩, _⟩
        cases hm
      · have hpres := (srsPlus_preserves_weak_and_rem_w8 d hd rules rem interp htop hweak hkeep).2
        have hdesc : ∀ (B : Nat) (f : Nat -> List MixedSRSSym),
            (evalWordNatAffineDim d interp (f 0)).v ⟨0, hd⟩ ≤ B ->
            ¬ (∀ t : Nat, srsPlusFromList rules (f t) (f (t + 1))) := by
          intro B
          induction B with
          | zero =>
            intro f hf0 hchain
            have hall_zero : ∀ t : Nat, (evalWordNatAffineDim d interp (f t)).v ⟨0, hd⟩ = 0 := by
              intro t
              induction t with
              | zero => omega
              | succ t' iht =>
                have hge := (hpres (f t') (f (t' + 1)) (hchain t')).1
                omega
            have hrem_chain : ∀ t : Nat, srsPlusFromList rem (f t) (f (t + 1)) := by
              intro t
              exact (hpres (f t) (f (t + 1)) (hchain t)).2 (by rw [hall_zero t, hall_zero (t + 1)])
            exact ih rem hrem_tower f hrem_chain
          | succ B' ihB =>
            intro f hf0 hchain
            have hle_all : ∀ t : Nat,
                (evalWordNatAffineDim d interp (f t)).v ⟨0, hd⟩ ≤
                  (evalWordNatAffineDim d interp (f 0)).v ⟨0, hd⟩ := by
              intro t
              induction t with
              | zero => exact Nat.le_refl _
              | succ s ihs =>
                exact Nat.le_trans (hpres (f s) (f (s + 1)) (hchain s)).1 ihs
            by_cases hdrop : ∃ t0 : Nat,
                (evalWordNatAffineDim d interp (f (t0 + 1))).v ⟨0, hd⟩ <
                  (evalWordNatAffineDim d interp (f t0)).v ⟨0, hd⟩
            · rcases hdrop with ⟨t0, hlt_t0⟩
              have hle_t0 := hle_all t0
              let f' : Nat -> List MixedSRSSym := fun s => f (t0 + 1 + s)
              have hf'0 : (evalWordNatAffineDim d interp (f' 0)).v ⟨0, hd⟩ ≤ B' := by
                dsimp [f']; rw [Nat.add_zero]; omega
              have hchain' : ∀ s : Nat, srsPlusFromList rules (f' s) (f' (s + 1)) := by
                intro s
                dsimp [f']
                rw [show t0 + 1 + (s + 1) = (t0 + 1 + s) + 1 by omega]
                exact hchain (t0 + 1 + s)
              exact ihB f' hf'0 hchain'
            · have hrem_chain : ∀ t : Nat, srsPlusFromList rem (f t) (f (t + 1)) := by
                intro t
                have hge := (hpres (f t) (f (t + 1)) (hchain t)).1
                have hnlt : ¬ ((evalWordNatAffineDim d interp (f (t + 1))).v ⟨0, hd⟩ <
                    (evalWordNatAffineDim d interp (f t)).v ⟨0, hd⟩) :=
                  fun hlt => hdrop ⟨t, hlt⟩
                exact (hpres (f t) (f (t + 1)) (hchain t)).2 (by omega)
              exact ih rem hrem_tower f hrem_chain
        exact hdesc ((evalWordNatAffineDim d interp (seq 0)).v ⟨0, hd⟩) seq (Nat.le_refl _) hinf
  intro rules htower
  refine ⟨hno_plus k rules htower, ?_⟩
  intro seq hstep_inf
  exact hno_plus k rules htower seq (fun t => ⟨seq (t + 1), hstep_inf t, .refl _⟩)

/-- Complete 11-rule positive Collatz SRS list (`R1`–`R11` from `MixedSRSBaseRule`). -/
def all11RuleList : List (List MixedSRSSym × List MixedSRSSym) :=
  [([.L, .B0], [.L]),
   ([.L, .B1], [.L, .T2]),
   ([.T0, .B0], [.B0, .T0]),
   ([.T0, .B1], [.B1, .T1]),
   ([.T1, .B0], [.B1, .T0]),
   ([.T1, .B1], [.B0, .T2]),
   ([.T2, .B0], [.B0, .T1]),
   ([.T2, .B1], [.B1, .T2]),
   ([.T0, .R], [.B1, .R]),
   ([.T1, .R], [.B0, .B0, .R]),
   ([.T2, .R], [.B1, .B0, .R])]

theorem mixedSRSBaseRule_mem_all11 {l r : List MixedSRSSym}
    (h : MixedSRSBaseRule l r) : (l, r) ∈ all11RuleList := by
  cases h <;> decide

theorem mixedSRSReaches_to_srsReachesFromList {w1 w2 : List MixedSRSSym}
    (h : MixedSRSReaches w1 w2) : srsReachesFromList all11RuleList w1 w2 := by
  induction h with
  | refl w => exact .refl w
  | step hs _ ih =>
    rcases hs with ⟨p, l, r, q, hrule, hw1, hw2⟩
    exact .step ⟨p, l, r, q, mixedSRSBaseRule_mem_all11 hrule, hw1, hw2⟩ ih

theorem encodePosBin_simulates_srsPlus_all11 (n : Nat) (hn : n ≥ 2) :
    srsPlusFromList all11RuleList
      ([.L] ++ encodePosBin n ++ [.R])
      ([.L] ++ encodePosBin (collatzStep n) ++ [.R]) := by
  rcases encodePosBin_spec n (by omega) with ⟨heval_n, hbin_n⟩
  cases hu : encodePosBin n with
  | nil =>
    rw [hu] at heval_n; simp [srsEvalInterior] at heval_n; omega
  | cons b u =>
    rw [hu] at heval_n hbin_n
    have hb := hbin_n b List.mem_cons_self
    have hu_bin : ∀ s, s ∈ u -> isBinaryInteriorSym s = true :=
      fun s hs => hbin_n s (List.mem_cons_of_mem b hs)
    cases b <;> simp [isBinaryInteriorSym] at hb
    · simp only [srsEvalInterior] at heval_n
      have hev : (n % 2 == 0) = true := decide_eq_true (by omega)
      have hcstep : collatzStep n = srsEvalInterior u := by
        simp only [collatzStep, hev, ite_true]; omega
      have hu_eq : u = encodePosBin (collatzStep n) := by
        rcases encodePosBin_spec (collatzStep n) (by rw [hcstep]; exact srsEvalInterior_pos u) with
          ⟨_, hbin_c⟩
        exact binary_interior_unique u (encodePosBin (collatzStep n)) hu_bin hbin_c (by omega)
      rw [← hu_eq]
      exact ⟨[.L] ++ u ++ [.R],
             ⟨[], [.L, .B0], [.L], u ++ [.R], by decide, rfl, rfl⟩,
             .refl _⟩
    · simp only [srsEvalInterior] at heval_n
      have hodd : (n % 2 == 0) = false := decide_eq_false (by omega)
      have hcstep : collatzStep n = 3 * srsEvalInterior u + 2 := by
        simp only [collatzStep, hodd, Bool.false_eq_true, ite_false]; omega
      rcases carry_propagate_reaches_binary u .T2 hu_bin (Or.inr (Or.inr rfl)) with
        ⟨v, hv_bin, hv_eval, hv_reach⟩
      simp only [srsEvalInterior] at hv_eval
      have hv_eq : v = encodePosBin (collatzStep n) := by
        rcases encodePosBin_spec (collatzStep n) (by omega) with ⟨_, hbin_c⟩
        exact binary_interior_unique v (encodePosBin (collatzStep n)) hv_bin hbin_c (by omega)
      have hs2 := mixedSRS_prepend_context [.L] hv_reach
      rw [hv_eq] at hs2
      exact ⟨[.L] ++ ([.T2] ++ u ++ [.R]),
             ⟨[], [.L, .B1], [.L, .T2], u ++ [.R], by decide, rfl, rfl⟩,
             mixedSRSReaches_to_srsReachesFromList hs2⟩

/--
  Inductive Well-Foundedness (`Acc`) of `srsPlusFromList` under any `ω^k` Hofbauer–Waldmann Tower:
  Proved by nested induction on tower height `k`, outer induction on `v_0 ≤ B`,
  and inner `Acc` induction on the residual rule set `rem` (zero custom axioms).
-/
theorem hofbauer_waldmann_tower_acc_srsPlus
    (d : Nat) (hd : 0 < d) :
    ∀ (k : Nat) (rules : List (List MixedSRSSym × List MixedSRSSym)),
      OmegaHofbauerWaldmannTower d hd k rules ->
      ∀ w : List MixedSRSSym, Acc (fun w2 w1 => srsPlusFromList rules w1 w2) w
  | 0, rules, h0, w => by
    rw [OmegaHofbauerWaldmannTower] at h0
    subst h0
    refine Acc.intro w ?_
    intro _ ⟨_, ⟨_, _, _, _, hm, _, _⟩, _⟩
    cases hm
  | k + 1, rules, hsucc, w0 => by
    rcases hsucc with rfl | ⟨rem, interp, htop, hweak, hkeep, hrem_tower⟩
    · refine Acc.intro w0 ?_
      intro _ ⟨_, ⟨_, _, _, _, hm, _, _⟩, _⟩
      cases hm
    · have hpres := (srsPlus_preserves_weak_and_rem_w8 d hd rules rem interp htop hweak hkeep).2
      have ih_rem : ∀ u : List MixedSRSSym, Acc (fun w2 w1 => srsPlusFromList rem w1 w2) u :=
        hofbauer_waldmann_tower_acc_srsPlus d hd k rem hrem_tower
      have hacc_bound : ∀ (B : Nat) (u : List MixedSRSSym),
          (evalWordNatAffineDim d interp u).v ⟨0, hd⟩ ≤ B ->
          Acc (fun w2 w1 => srsPlusFromList rules w1 w2) u := by
        intro B
        induction B with
        | zero =>
          intro u hu0
          have hrem_zero : ∀ x : List MixedSRSSym,
              Acc (fun w2 w1 => srsPlusFromList rem w1 w2) x ->
              (evalWordNatAffineDim d interp x).v ⟨0, hd⟩ = 0 ->
              Acc (fun w2 w1 => srsPlusFromList rules w1 w2) x := by
            intro x hacc_x
            induction hacc_x with
            | intro x _ ih_x =>
              intro hx0
              refine Acc.intro x ?_
              intro y hxy
              rcases hpres x y hxy with ⟨hge, hto_rem⟩
              have hy0 : (evalWordNatAffineDim d interp y).v ⟨0, hd⟩ = 0 := by omega
              exact ih_x y (hto_rem (by omega)) hy0
          exact hrem_zero u (ih_rem u) (by omega)
        | succ B' ihB =>
          intro u huB
          have hrem_B : ∀ x : List MixedSRSSym,
              Acc (fun w2 w1 => srsPlusFromList rem w1 w2) x ->
              (evalWordNatAffineDim d interp x).v ⟨0, hd⟩ ≤ B' + 1 ->
              Acc (fun w2 w1 => srsPlusFromList rules w1 w2) x := by
            intro x hacc_x
            induction hacc_x with
            | intro x _ ih_x =>
              intro hxB
              refine Acc.intro x ?_
              intro y hxy
              rcases hpres x y hxy with ⟨hge, hto_rem⟩
              by_cases hlt : (evalWordNatAffineDim d interp y).v ⟨0, hd⟩ <
                  (evalWordNatAffineDim d interp x).v ⟨0, hd⟩
              · exact ihB y (by omega)
              · exact ih_x y (hto_rem (by omega)) (by omega)
          exact hrem_B u (ih_rem u) huB
      exact hacc_bound ((evalWordNatAffineDim d interp w0).v ⟨0, hd⟩) w0 (Nat.le_refl _)

/--
  Theorem W8.1b (`all11_hofbauer_waldmann_tower_implies_collatz_standard`, zero custom axioms):
  Forward Bridge to `CollatzConjectureStandard`:
  Any `k`-level `d`-dimensional (`d ≥ 1`, `k : Nat`) Hofbauer–Waldmann rule-removal tower
  orienting `all11RuleList` (`R1`–`R11`) unconditionally implies `CollatzConjectureStandard`!
-/
theorem all11_hofbauer_waldmann_tower_implies_collatz_standard
    (d : Nat) (hd : 0 < d) (k : Nat)
    (htower : OmegaHofbauerWaldmannTower d hd k all11RuleList) :
    CollatzConjectureStandard := by
  rw [collatz_standard_iff_compressed]
  intro n hn
  have hstep_pos : ∀ m : Nat, m ≥ 1 -> collatzStep m ≥ 1 := by
    intro m hm
    by_cases he : (m % 2 == 0) = true
    · have hm2 : m % 2 = 0 := of_decide_eq_true he
      simp only [collatzStep, he, ite_true]; omega
    · have hm2 : m % 2 = 1 := by
        have hne : ¬ (m % 2 = 0) := fun h => he (decide_eq_true h)
        omega
      have hef : (m % 2 == 0) = false := decide_eq_false (by omega)
      simp only [collatzStep, hef, Bool.false_eq_true, ite_false]; omega
  let enc : Nat -> List MixedSRSSym := fun m => [.L] ++ encodePosBin m ++ [.R]
  have hacc_enc : ∀ w : List MixedSRSSym,
      Acc (fun w2 w1 => srsPlusFromList all11RuleList w1 w2) w ->
      ∀ m : Nat, m ≥ 1 -> enc m = w -> ∃ t : Nat, collatzIter t m = 1 := by
    intro w hacc
    induction hacc with
    | intro w _ ih =>
      intro m hm1 hmw
      by_cases hm_eq1 : m = 1
      · subst hm_eq1; exact ⟨0, rfl⟩
      · have hplus : srsPlusFromList all11RuleList w (enc (collatzStep m)) := by
          rw [← hmw]
          exact encodePosBin_simulates_srsPlus_all11 m (by omega)
        rcases ih (enc (collatzStep m)) hplus (collatzStep m) (hstep_pos m hm1) rfl with ⟨t, ht⟩
        exact ⟨t + 1, ht⟩
  exact hacc_enc (enc n)
    (hofbauer_waldmann_tower_acc_srsPlus d hd k all11RuleList htower (enc n))
    n hn rfl

-- ----------------------------------------------------------------------------
-- Explicit `[]`-Axiom `10/11` `2D` Hofbauer–Waldmann Certificates & Towers
-- ----------------------------------------------------------------------------

def weakOrients2DBool (A B : NatAffineDim 2) : Bool :=
  let idx0 : Fin 2 := ⟨0, by decide⟩
  let idx1 : Fin 2 := ⟨1, by decide⟩
  decide (A.M idx0 idx0 ≥ B.M idx0 idx0) &&
  decide (A.M idx0 idx1 ≥ B.M idx0 idx1) &&
  decide (A.M idx1 idx0 ≥ B.M idx1 idx0) &&
  decide (A.M idx1 idx1 ≥ B.M idx1 idx1) &&
  decide (A.v idx0 ≥ B.v idx0) &&
  decide (A.v idx1 ≥ B.v idx1)

theorem weakOrients2DBool_sound (A B : NatAffineDim 2)
    (hb : weakOrients2DBool A B = true) :
    weakOrientsNatAffineDim 2 A B := by
  unfold weakOrients2DBool at hb
  rcases bool_and_split hb with ⟨hb5, hv1_b⟩
  rcases bool_and_split hb5 with ⟨hb4, hv0_b⟩
  rcases bool_and_split hb4 with ⟨hb3, hm11_b⟩
  rcases bool_and_split hb3 with ⟨hb2, hm10_b⟩
  rcases bool_and_split hb2 with ⟨hm00_b, hm01_b⟩
  refine ⟨?_, ?_⟩
  · intro ⟨i, hi⟩ ⟨j, hj⟩
    match i, j with
    | 0, 0 => exact of_decide_eq_true hm00_b
    | 0, 1 => exact of_decide_eq_true hm01_b
    | 1, 0 => exact of_decide_eq_true hm10_b
    | 1, 1 => exact of_decide_eq_true hm11_b
    | k + 2, _ => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 2 k) hi)
    | _, k + 2 => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 2 k) hj)
  · intro ⟨i, hi⟩
    match i with
    | 0 => exact of_decide_eq_true hv0_b
    | 1 => exact of_decide_eq_true hv1_b
    | k + 2 => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 2 k) hi)

def checkTopLeft2DBool (interp : MixedSRSSym -> NatAffineDim 2) : Bool :=
  let z : Fin 2 := ⟨0, by decide⟩
  decide ((interp .L).M z z ≥ 1) &&
  decide ((interp .R).M z z ≥ 1) &&
  decide ((interp .B0).M z z ≥ 1) &&
  decide ((interp .B1).M z z ≥ 1) &&
  decide ((interp .T0).M z z ≥ 1) &&
  decide ((interp .T1).M z z ≥ 1) &&
  decide ((interp .T2).M z z ≥ 1)

theorem checkTopLeft2DBool_sound (interp : MixedSRSSym -> NatAffineDim 2)
    (hb : checkTopLeft2DBool interp = true) :
    ∀ s : MixedSRSSym, (interp s).M ⟨0, by decide⟩ ⟨0, by decide⟩ ≥ 1 := by
  unfold checkTopLeft2DBool at hb
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

def checkAllWeak2DBool (interp : MixedSRSSym -> NatAffineDim 2) :
    List (List MixedSRSSym × List MixedSRSSym) -> Bool
  | [] => true
  | r :: rs =>
    weakOrients2DBool (evalWordNatAffineDim 2 interp r.1) (evalWordNatAffineDim 2 interp r.2) &&
    checkAllWeak2DBool interp rs

theorem checkAllWeak2DBool_sound (interp : MixedSRSSym -> NatAffineDim 2) :
    ∀ (rules : List (List MixedSRSSym × List MixedSRSSym)),
      checkAllWeak2DBool interp rules = true ->
      ∀ r ∈ rules, weakOrientsNatAffineDim 2
        (evalWordNatAffineDim 2 interp r.1) (evalWordNatAffineDim 2 interp r.2)
  | [], _, _, hm => by cases hm
  | r0 :: rs, hb, r, hm => by
    rcases bool_and_split hb with ⟨hw0, hrest⟩
    cases hm with
    | head => exact weakOrients2DBool_sound _ _ hw0
    | tail _ hrs => exact checkAllWeak2DBool_sound interp rs hrest r hrs

def checkAllStrict2DBool (interp : MixedSRSSym -> NatAffineDim 2) :
    List (List MixedSRSSym × List MixedSRSSym) -> Bool
  | [] => true
  | r :: rs =>
    orients2DBool (evalWordNatAffineDim 2 interp r.1) (evalWordNatAffineDim 2 interp r.2) &&
    checkAllStrict2DBool interp rs

theorem checkAllStrict2DBool_sound (interp : MixedSRSSym -> NatAffineDim 2) :
    ∀ (rules : List (List MixedSRSSym × List MixedSRSSym)),
      checkAllStrict2DBool interp rules = true ->
      ∀ r ∈ rules, orientsNatAffineDim 2 (by decide)
        (evalWordNatAffineDim 2 interp r.1) (evalWordNatAffineDim 2 interp r.2)
  | [], _, _, hm => by cases hm
  | r0 :: rs, hb, r, hm => by
    rcases bool_and_split hb with ⟨hs0, hrest⟩
    cases hm with
    | head => exact orients2DBool_sound _ _ hs0
    | tail _ hrs => exact checkAllStrict2DBool_sound interp rs hrest r hrs

def filterUnoriented2D (interp : MixedSRSSym -> NatAffineDim 2) :
    List (List MixedSRSSym × List MixedSRSSym) -> List (List MixedSRSSym × List MixedSRSSym)
  | [] => []
  | r :: rs =>
    match orients2DBool (evalWordNatAffineDim 2 interp r.1) (evalWordNatAffineDim 2 interp r.2) with
    | true => filterUnoriented2D interp rs
    | false => r :: filterUnoriented2D interp rs

theorem mem_filterUnoriented2D_of_not_strict (interp : MixedSRSSym -> NatAffineDim 2) :
    ∀ (rules : List (List MixedSRSSym × List MixedSRSSym))
      (r : List MixedSRSSym × List MixedSRSSym),
      r ∈ rules ->
      ¬ orientsNatAffineDim 2 (by decide)
        (evalWordNatAffineDim 2 interp r.1) (evalWordNatAffineDim 2 interp r.2) ->
      r ∈ filterUnoriented2D interp rules
  | [], _, hm, _ => by cases hm
  | r0 :: rs, r, hm, hns => by
    unfold filterUnoriented2D
    cases hm with
    | head =>
      cases hb : orients2DBool (evalWordNatAffineDim 2 interp r0.1)
          (evalWordNatAffineDim 2 interp r0.2) with
      | true => exact False.elim (hns (orients2DBool_sound _ _ hb))
      | false => exact List.Mem.head _
    | tail _ hrs =>
      cases hb : orients2DBool (evalWordNatAffineDim 2 interp r0.1)
          (evalWordNatAffineDim 2 interp r0.2) with
      | true => exact mem_filterUnoriented2D_of_not_strict interp rs r hrs hns
      | false =>
        exact List.Mem.tail _ (mem_filterUnoriented2D_of_not_strict interp rs r hrs hns)

def check2DHWTowerBool :
    List (MixedSRSSym -> NatAffineDim 2) ->
    List (List MixedSRSSym × List MixedSRSSym) -> Bool
  | [], rules => rules.isEmpty
  | interp :: rest, rules =>
    checkTopLeft2DBool interp &&
    checkAllWeak2DBool interp rules &&
    check2DHWTowerBool rest (filterUnoriented2D interp rules)

theorem check2DHWTowerBool_sound :
    ∀ (certs : List (MixedSRSSym -> NatAffineDim 2))
      (rules : List (List MixedSRSSym × List MixedSRSSym)),
      check2DHWTowerBool certs rules = true ->
      OmegaHofbauerWaldmannTower 2 (by decide) certs.length rules
  | [], [], _ => rfl
  | [], _ :: _, hb => by cases hb
  | interp :: rest, rules, hb => by
    unfold check2DHWTowerBool at hb
    rcases bool_and_split hb with ⟨hb1, hrest_b⟩
    rcases bool_and_split hb1 with ⟨htop_b, hweak_b⟩
    exact Or.inr ⟨filterUnoriented2D interp rules, interp,
      checkTopLeft2DBool_sound interp htop_b,
      checkAllWeak2DBool_sound interp rules hweak_b,
      mem_filterUnoriented2D_of_not_strict interp rules,
      check2DHWTowerBool_sound rest (filterUnoriented2D interp rules) hrest_b⟩

/-- `10/11` rule subset omitting only `R2` (`{R1, R3, R4, R5, R6, R7, R8, R9, R10, R11}`). -/
def all11OmitR2List : List (List MixedSRSSym × List MixedSRSSym) :=
  [([.L, .B0], [.L]),
   ([.T0, .B0], [.B0, .T0]),
   ([.T0, .B1], [.B1, .T1]),
   ([.T1, .B0], [.B1, .T0]),
   ([.T1, .B1], [.B0, .T2]),
   ([.T2, .B0], [.B0, .T1]),
   ([.T2, .B1], [.B1, .T2]),
   ([.T0, .R], [.B1, .R]),
   ([.T1, .R], [.B0, .B0, .R]),
   ([.T2, .R], [.B1, .B0, .R])]

/-- `10/11` rule subset omitting only `R7` (`{R1, R2, R3, R4, R5, R6, R8, R9, R10, R11}`). -/
def all11OmitR7List : List (List MixedSRSSym × List MixedSRSSym) :=
  [([.L, .B0], [.L]),
   ([.L, .B1], [.L, .T2]),
   ([.T0, .B0], [.B0, .T0]),
   ([.T0, .B1], [.B1, .T1]),
   ([.T1, .B0], [.B1, .T0]),
   ([.T1, .B1], [.B0, .T2]),
   ([.T2, .B1], [.B1, .T2]),
   ([.T0, .R], [.B1, .R]),
   ([.T1, .R], [.B0, .B0, .R]),
   ([.T2, .R], [.B1, .B0, .R])]

/-- `10/11` rule subset omitting only `R5` (`{R1, R2, R3, R4, R6, R7, R8, R9, R10, R11}`). -/
def all11OmitR5List : List (List MixedSRSSym × List MixedSRSSym) :=
  [([.L, .B0], [.L]),
   ([.L, .B1], [.L, .T2]),
   ([.T0, .B0], [.B0, .T0]),
   ([.T0, .B1], [.B1, .T1]),
   ([.T1, .B1], [.B0, .T2]),
   ([.T2, .B0], [.B0, .T1]),
   ([.T2, .B1], [.B1, .T2]),
   ([.T0, .R], [.B1, .R]),
   ([.T1, .R], [.B0, .B0, .R]),
   ([.T2, .R], [.B1, .B0, .R])]

def omitR2Single2DCert : MixedSRSSym -> NatAffineDim 2
  | .L  => { M := mkMat2 (1, 0) (7, 8), v := mkVec2 1 4 }
  | .R  => { M := mkMat2 (1, 8) (7, 4), v := mkVec2 8 3 }
  | .B0 => { M := mkMat2 (1, 0) (0, 1), v := mkVec2 7 4 }
  | .B1 => { M := mkMat2 (1, 0) (0, 1), v := mkVec2 3 7 }
  | .T0 => { M := mkMat2 (1, 8) (2, 3), v := mkVec2 5 8 }
  | .T1 => { M := mkMat2 (1, 8) (2, 3), v := mkVec2 2 7 }
  | .T2 => { M := mkMat2 (1, 8) (2, 3), v := mkVec2 5 2 }

def r1r2r8r11Strict2DCert : MixedSRSSym -> NatAffineDim 2
  | .L  => { M := mkMat2 (1, 2)  (3, 6),   v := mkVec2 10 11 }
  | .R  => { M := mkMat2 (1, 10) (5, 2),   v := mkVec2 15 9 }
  | .B0 => { M := mkMat2 (1, 2)  (0, 0),   v := mkVec2 8  0 }
  | .B1 => { M := mkMat2 (1, 4)  (0, 8),   v := mkVec2 6  14 }
  | .T0 => { M := mkMat2 (1, 3)  (12, 11), v := mkVec2 7  3 }
  | .T1 => { M := mkMat2 (1, 15) (5, 15),  v := mkVec2 15 11 }
  | .T2 => { M := mkMat2 (1, 4)  (0, 6),   v := mkVec2 9  6 }

def omitR7Level1Cert2D : MixedSRSSym -> NatAffineDim 2
  | .L  => { M := mkMat2 (1, 0) (10, 0), v := mkVec2 11 13 }
  | .R  => { M := mkMat2 (1, 5) (8, 5),  v := mkVec2 12 13 }
  | .B0 => { M := mkMat2 (1, 0) (0, 1),  v := mkVec2 0  9 }
  | .B1 => { M := mkMat2 (1, 0) (0, 1),  v := mkVec2 12 15 }
  | .T0 => { M := mkMat2 (1, 1) (7, 11), v := mkVec2 5  8 }
  | .T1 => { M := mkMat2 (1, 1) (7, 11), v := mkVec2 15 10 }
  | .T2 => { M := mkMat2 (1, 0) (7, 7),  v := mkVec2 12 6 }

def omitR5Level1Cert2D : MixedSRSSym -> NatAffineDim 2
  | .L  => { M := mkMat2 (1, 0) (0, 0),  v := mkVec2 3  2 }
  | .R  => { M := mkMat2 (1, 2) (10, 3), v := mkVec2 3  3 }
  | .B0 => { M := mkMat2 (1, 0) (0, 0),  v := mkVec2 0  1 }
  | .B1 => { M := mkMat2 (1, 0) (0, 0),  v := mkVec2 3  2 }
  | .T0 => { M := mkMat2 (1, 0) (1, 11), v := mkVec2 14 2 }
  | .T1 => { M := mkMat2 (1, 0) (6, 0),  v := mkVec2 0  11 }
  | .T2 => { M := mkMat2 (1, 0) (1, 0),  v := mkVec2 3  1 }

def omitR5Level2Cert2D : MixedSRSSym -> NatAffineDim 2
  | .L  => { M := mkMat2 (1, 0)  (4, 0),  v := mkVec2 12 6 }
  | .R  => { M := mkMat2 (1, 1)  (14, 4), v := mkVec2 6  11 }
  | .B0 => { M := mkMat2 (1, 0)  (0, 1),  v := mkVec2 0  3 }
  | .B1 => { M := mkMat2 (1, 0)  (2, 3),  v := mkVec2 5  9 }
  | .T0 => { M := mkMat2 (1, 8)  (7, 15), v := mkVec2 4  11 }
  | .T1 => { M := mkMat2 (1, 11) (1, 8),  v := mkVec2 12 11 }
  | .T2 => { M := mkMat2 (1, 0)  (7, 11), v := mkVec2 5  7 }

/--
  Theorem W8.1c (`omit_r2_10_of_11_admits_single_2d_hw_cert`, `[]` axioms):
  Pushing `7/11 -> 10/11` in One Simultaneous `2 x 2` Step:
  `omitR2Single2DCert` has `(M_s)_{0,0} = 1` across all symbols and simultaneously strictly
  orients ALL `10/11` rules of `all11OmitR2List` (`{R1, R3, R4, R5, R6, R7, R8, R9, R10, R11}`,
  including ALL 4 rules `{R3, R4, R6, R10}` left open in Wave 7)!
-/
theorem omit_r2_10_of_11_admits_single_2d_hw_cert :
    all11OmitR2List.length = 10 ∧
    (∀ s : MixedSRSSym, (omitR2Single2DCert s).M ⟨0, by decide⟩ ⟨0, by decide⟩ = 1) ∧
    (∀ r ∈ all11OmitR2List,
      orientsNatAffineDim 2 (by decide)
        (evalWordNatAffineDim 2 omitR2Single2DCert r.1)
        (evalWordNatAffineDim 2 omitR2Single2DCert r.2)) ∧
    OmegaHofbauerWaldmannTower 2 (by decide) 1 all11OmitR2List := by
  refine ⟨rfl, ?_,
          checkAllStrict2DBool_sound omitR2Single2DCert all11OmitR2List (by decide),
          check2DHWTowerBool_sound [omitR2Single2DCert] all11OmitR2List (by decide)⟩
  intro s
  cases s <;> rfl

/--
  Theorem W8.1d (`omit_r7_and_omit_r5_10_of_11_admit_2d_hw_towers`, `[]` axioms):
  Pushing `7/11 -> 10/11` Keeping BOTH `{R1, R2}` AND `{R3, R4, R6, R10}` via `2D` Rule-Removal Towers:
  1. `all11OmitR7List` (`10/11` rules = `{R1, R2, R3, R4, R5, R6, R8, R9, R10, R11}`) is
     terminated in `2` levels by `[omitR7Level1Cert2D, r1r2r8r11Strict2DCert]`!
  2. `all11OmitR5List` (`10/11` rules = `{R1, R2, R3, R4, R6, R7, R8, R9, R10, R11}`) is
     terminated in `3` levels by `[omitR5Level1Cert2D, omitR5Level2Cert2D, r1r2r8r11Strict2DCert]`!
-/
theorem omit_r7_and_omit_r5_10_of_11_admit_2d_hw_towers :
    all11OmitR7List.length = 10 ∧
    all11OmitR5List.length = 10 ∧
    OmegaHofbauerWaldmannTower 2 (by decide) 2 all11OmitR7List ∧
    OmegaHofbauerWaldmannTower 2 (by decide) 3 all11OmitR5List := by
  exact ⟨rfl, rfl,
         check2DHWTowerBool_sound [omitR7Level1Cert2D, r1r2r8r11Strict2DCert]
           all11OmitR7List (by decide),
         check2DHWTowerBool_sound [omitR5Level1Cert2D, omitR5Level2Cert2D, r1r2r8r11Strict2DCert]
           all11OmitR5List (by decide)⟩

theorem all11_mem_or_omitted (r : List MixedSRSSym × List MixedSRSSym)
    (hm : r ∈ all11RuleList) :
    (r = ([.L, .B1], [.L, .T2]) ∨ r ∈ all11OmitR2List) ∧
    (r = ([.T1, .B0], [.B1, .T0]) ∨ r ∈ all11OmitR5List) ∧
    (r = ([.T2, .B0], [.B0, .T1]) ∨ r ∈ all11OmitR7List) := by
  cases hm with
  | head => exact ⟨Or.inr (by decide), Or.inr (by decide), Or.inr (by decide)⟩
  | tail _ h1 =>
    cases h1 with
    | head => exact ⟨Or.inl rfl, Or.inr (by decide), Or.inr (by decide)⟩
    | tail _ h2 =>
      cases h2 with
      | head => exact ⟨Or.inr (by decide), Or.inr (by decide), Or.inr (by decide)⟩
      | tail _ h3 =>
        cases h3 with
        | head => exact ⟨Or.inr (by decide), Or.inr (by decide), Or.inr (by decide)⟩
        | tail _ h4 =>
          cases h4 with
          | head => exact ⟨Or.inr (by decide), Or.inl rfl, Or.inr (by decide)⟩
          | tail _ h5 =>
            cases h5 with
            | head => exact ⟨Or.inr (by decide), Or.inr (by decide), Or.inr (by decide)⟩
            | tail _ h6 =>
              cases h6 with
              | head => exact ⟨Or.inr (by decide), Or.inr (by decide), Or.inl rfl⟩
              | tail _ h7 =>
                cases h7 with
                | head => exact ⟨Or.inr (by decide), Or.inr (by decide), Or.inr (by decide)⟩
                | tail _ h8 =>
                  cases h8 with
                  | head => exact ⟨Or.inr (by decide), Or.inr (by decide), Or.inr (by decide)⟩
                  | tail _ h9 =>
                    cases h9 with
                    | head => exact ⟨Or.inr (by decide), Or.inr (by decide), Or.inr (by decide)⟩
                    | tail _ h10 =>
                      cases h10 with
                      | head => exact ⟨Or.inr (by decide), Or.inr (by decide), Or.inr (by decide)⟩
                      | tail _ hnil => cases hnil

/--
  Theorem W8.1d' (`infinite_all11_srs_chain_requires_infinitely_many_r2_r5_r7`, zero custom axioms):
  Unconditional Rule-Recurrence Consequence of `10/11` `2D` Hofbauer–Waldmann Termination:
  Because `all11OmitR2List`, `all11OmitR5List`, and `all11OmitR7List` ALL terminate via explicit
  `2 x 2` non-triangular Hofbauer–Waldmann certificates/towers (`W8.1c` & `W8.1d`), EVERY infinite
  `all11RuleList` rewrite sequence `seq 0 -> seq 1 -> seq 2 -> ...` MUST apply `R2` (`[L, B1] -> [L, T2]`),
  `R5` (`[T1, B0] -> [B1, T0]`), AND `R7` (`[T2, B0] -> [B0, T1]`) infinitely many times!
-/
theorem infinite_all11_srs_chain_requires_infinitely_many_r2_r5_r7
    (seq : Nat -> List MixedSRSSym)
    (hinf : ∀ t : Nat, srsStepFromList all11RuleList (seq t) (seq (t + 1)))
    (N : Nat) :
    (∃ t : Nat, t ≥ N ∧ ∃ p q : List MixedSRSSym,
      seq t = p ++ [.L, .B1] ++ q ∧ seq (t + 1) = p ++ [.L, .T2] ++ q) ∧
    (∃ t : Nat, t ≥ N ∧ ∃ p q : List MixedSRSSym,
      seq t = p ++ [.T1, .B0] ++ q ∧ seq (t + 1) = p ++ [.B1, .T0] ++ q) ∧
    (∃ t : Nat, t ≥ N ∧ ∃ p q : List MixedSRSSym,
      seq t = p ++ [.T2, .B0] ++ q ∧ seq (t + 1) = p ++ [.B0, .T1] ++ q) := by
  have hrec : ∀ (lvl : Nat) (sub : List (List MixedSRSSym × List MixedSRSSym))
      (l0 r0 : List MixedSRSSym),
      OmegaHofbauerWaldmannTower 2 (by decide) lvl sub ->
      (∀ r ∈ all11RuleList, r = (l0, r0) ∨ r ∈ sub) ->
      ∃ t : Nat, t ≥ N ∧ ∃ p q : List MixedSRSSym,
        seq t = p ++ l0 ++ q ∧ seq (t + 1) = p ++ r0 ++ q := by
    intro lvl sub l0 r0 htower hsplit
    apply Classical.byContradiction
    intro hnone
    have htail : ∀ k : Nat, srsStepFromList sub (seq (N + k)) (seq (N + (k + 1))) := by
      intro k
      have hnk : seq (N + (k + 1)) = seq ((N + k) + 1) := by
        rw [Nat.add_assoc N k 1]
      rw [hnk]
      rcases hinf (N + k) with ⟨p, l, r, q, hmem, hw1, hw2⟩
      cases hsplit (l, r) hmem with
      | inl heq =>
        have hl : l = l0 := congrArg Prod.fst heq
        have hr : r = r0 := congrArg Prod.snd heq
        rw [hl] at hw1
        rw [hr] at hw2
        exact False.elim (hnone ⟨N + k, Nat.le_add_right N k, p, q, hw1, hw2⟩)
      | inr hsub =>
        exact ⟨p, l, r, q, hsub, hw1, hw2⟩
    exact (hofbauer_waldmann_tower_implies_no_infinite_srs_chain 2 (by decide) lvl sub htower).2
      (fun k => seq (N + k)) htail
  exact ⟨hrec 1 all11OmitR2List [.L, .B1] [.L, .T2]
           omit_r2_10_of_11_admits_single_2d_hw_cert.2.2.2
           (fun r hm => (all11_mem_or_omitted r hm).1),
         hrec 3 all11OmitR5List [.T1, .B0] [.B1, .T0]
           omit_r7_and_omit_r5_10_of_11_admit_2d_hw_towers.2.2.2
           (fun r hm => (all11_mem_or_omitted r hm).2.1),
         hrec 2 all11OmitR7List [.T2, .B0] [.B0, .T1]
           omit_r7_and_omit_r5_10_of_11_admit_2d_hw_towers.2.2.1
           (fun r hm => (all11_mem_or_omitted r hm).2.2)⟩

/--
  Arts–Giesl Shifted Semantic 1D Dependency-Pair Interpretation (`artsGieslSemanticDP1D`):
  At the marked root `L#` (represented by `.L`), constructor `.R` has `m_R = 0` (`(0, 0)`),
  while `{B0, B1, T0, T1, T2}` take their shifted base-`(2, 3)` affine semantics
  `B0 = (2, 1), B1 = (2, 2), T0 = (3, 2), T1 = (3, 3), T2 = (3, 4)`!
-/
def artsGieslSemanticDP1D : MixedSRSSym -> NatAffine1D
  | .L  => { m := 1, c := 0 }
  | .R  => { m := 0, c := 0 }
  | .B0 => { m := 2, c := 1 }
  | .B1 => { m := 2, c := 2 }
  | .T0 => { m := 3, c := 2 }
  | .T1 => { m := 3, c := 3 }
  | .T2 => { m := 3, c := 4 }

/-- All 9 interior and right-boundary base rules `R3`–`R11` of `MixedSRSBaseRule`. -/
def interiorAndRight9RuleList : List (List MixedSRSSym × List MixedSRSSym) :=
  [([.T0, .B0], [.B0, .T0]),
   ([.T0, .B1], [.B1, .T1]),
   ([.T1, .B0], [.B1, .T0]),
   ([.T1, .B1], [.B0, .T2]),
   ([.T2, .B0], [.B0, .T1]),
   ([.T2, .B1], [.B1, .T2]),
   ([.T0, .R], [.B1, .R]),
   ([.T1, .R], [.B0, .B0, .R]),
   ([.T2, .R], [.B1, .B0, .R])]

/--
  Theorem W8.1e (`arts_giesl_1d_semantic_dp_removes_dp1_rel_all_interior`, `[]` axioms):
  Exact Arts–Giesl Dependency-Pair Semantic Reduction of `DP1` Relative to `{R3..R11}`:
  Under `artsGieslSemanticDP1D`, EVERY ONE of the 9 interior/right base rules `{R3..R11}`
  satisfies exact affine identity `eval(LHS) = eval(RHS)` (hence preserves `eval` across
  arbitrary interior rewrites!), while `DP1 : [L#, B0] -> [L#]` is strictly oriented
  (`m : 2 ≥ 1` and `c : 1 > 0`), reducing relative DP termination of `all11RuleList` to the
  single dependency pair `DP2 : [L#, B1] -> [L#, T2]` modulo `{R3..R11}`!
-/
theorem arts_giesl_1d_semantic_dp_removes_dp1_rel_all_interior :
    interiorAndRight9RuleList.length = 9 ∧
    (∀ r ∈ interiorAndRight9RuleList,
      evalWordAffine1D artsGieslSemanticDP1D r.1 =
        evalWordAffine1D artsGieslSemanticDP1D r.2) ∧
    strictOrients1D
      (evalWordAffine1D artsGieslSemanticDP1D [.L, .B0])
      (evalWordAffine1D artsGieslSemanticDP1D [.L]) := by
  refine ⟨rfl, ?_, ⟨by decide, by decide⟩⟩
  intro r hr
  cases hr with
  | head => rfl
  | tail _ hr1 =>
    cases hr1 with
    | head => rfl
    | tail _ hr2 =>
      cases hr2 with
      | head => rfl
      | tail _ hr3 =>
        cases hr3 with
        | head => rfl
        | tail _ hr4 =>
          cases hr4 with
          | head => rfl
          | tail _ hr5 =>
            cases hr5 with
            | head => rfl
            | tail _ hr6 =>
              cases hr6 with
              | head => rfl
              | tail _ hr7 =>
                cases hr7 with
                | head => rfl
                | tail _ hr8 =>
                  cases hr8 with
                  | head => rfl
                  | tail _ hnil => cases hnil

/--
  Theorem W8.1f (`mixed_srs_interior_b1_and_b0_pumping_identities`, zero custom axioms):
  Universal All-Dimension (`∀ d : Nat`) Interior Carry-Pumping Identities:
  In ANY dimension `d` and ANY natural matrix interpretation `interp` (zero diagonal /
  triangularity assumptions!), weak orientation of `{R4, R5}` and `{R6, R7}` forces:
  1. `T0 · B1 · B0 ≥ B1 · B1 · T0` (`R4` followed by `R5`);
  2. `T2 · B0 · B1 ≥ B0 · B0 · T2` (`R7` followed by `R6`);
  3. `T1 · B1 · B0 ≥ B0 · B0 · T1` (`R6` followed by `R7`).
-/
theorem mixed_srs_interior_b1_and_b0_pumping_identities
    (d : Nat) (interp : MixedSRSSym -> NatAffineDim d)
    (hR4 : weakOrientsNatAffineDim d
      (evalWordNatAffineDim d interp [.T0, .B1])
      (evalWordNatAffineDim d interp [.B1, .T1]))
    (hR5 : weakOrientsNatAffineDim d
      (evalWordNatAffineDim d interp [.T1, .B0])
      (evalWordNatAffineDim d interp [.B1, .T0]))
    (hR6 : weakOrientsNatAffineDim d
      (evalWordNatAffineDim d interp [.T1, .B1])
      (evalWordNatAffineDim d interp [.B0, .T2]))
    (hR7 : weakOrientsNatAffineDim d
      (evalWordNatAffineDim d interp [.T2, .B0])
      (evalWordNatAffineDim d interp [.B0, .T1])) :
    weakOrientsNatAffineDim d
      (evalWordNatAffineDim d interp [.T0, .B1, .B0])
      (evalWordNatAffineDim d interp [.B1, .B1, .T0]) ∧
    weakOrientsNatAffineDim d
      (evalWordNatAffineDim d interp [.T2, .B0, .B1])
      (evalWordNatAffineDim d interp [.B0, .B0, .T2]) ∧
    weakOrientsNatAffineDim d
      (evalWordNatAffineDim d interp [.T1, .B1, .B0])
      (evalWordNatAffineDim d interp [.B0, .B0, .T1]) := by
  have hrefl : ∀ w : List MixedSRSSym,
      weakOrientsNatAffineDim d
        (evalWordNatAffineDim d interp w) (evalWordNatAffineDim d interp w) :=
    fun _ => ⟨fun _ _ => Nat.le_refl _, fun _ => Nat.le_refl _⟩
  have htrans : ∀ A B C : NatAffineDim d,
      weakOrientsNatAffineDim d A B ->
      weakOrientsNatAffineDim d B C ->
      weakOrientsNatAffineDim d A C :=
    fun _ _ _ hAB hBC =>
      ⟨fun i j => Nat.le_trans (hBC.1 i j) (hAB.1 i j),
       fun i => Nat.le_trans (hBC.2 i) (hAB.2 i)⟩
  have hctx_r : ∀ (l r : List MixedSRSSym) (s : MixedSRSSym),
      weakOrientsNatAffineDim d
        (evalWordNatAffineDim d interp l) (evalWordNatAffineDim d interp r) ->
      weakOrientsNatAffineDim d
        (evalWordNatAffineDim d interp (l ++ [s]))
        (evalWordNatAffineDim d interp (r ++ [s])) := by
    intro l r s hlr
    rcases evalWordNatAffineDim_append_w8 d interp l [s] with ⟨hm_l, hv_l⟩
    rcases evalWordNatAffineDim_append_w8 d interp r [s] with ⟨hm_r, hv_r⟩
    have hc := compNatAffineDim_weak_mono_w8 d _ _ _ _ hlr (hrefl [s])
    exact ⟨fun i j => by rw [hm_l i j, hm_r i j]; exact hc.1 i j,
           fun i => by rw [hv_l i, hv_r i]; exact hc.2 i⟩
  have hctx_l : ∀ (s : MixedSRSSym) (l r : List MixedSRSSym),
      weakOrientsNatAffineDim d
        (evalWordNatAffineDim d interp l) (evalWordNatAffineDim d interp r) ->
      weakOrientsNatAffineDim d
        (evalWordNatAffineDim d interp (s :: l))
        (evalWordNatAffineDim d interp (s :: r)) := by
    intro s l r hlr
    simp only [evalWordNatAffineDim]
    exact compNatAffineDim_weak_mono_w8 d (interp s) (interp s) _ _
      ⟨fun _ _ => Nat.le_refl _, fun _ => Nat.le_refl _⟩ hlr
  exact ⟨htrans _ _ _ (hctx_r [.T0, .B1] [.B1, .T1] .B0 hR4)
                      (hctx_l .B1 [.T1, .B0] [.B1, .T0] hR5),
         htrans _ _ _ (hctx_r [.T2, .B0] [.B0, .T1] .B1 hR7)
                      (hctx_l .B0 [.T1, .B1] [.B0, .T2] hR6),
         htrans _ _ _ (hctx_r [.T1, .B1] [.B0, .T2] .B0 hR6)
                      (hctx_l .B0 [.T2, .B0] [.B0, .T1] hR7)⟩

/--
  `k`-level `d`-dimensional coordinatewise-monotone (`∀ s i, (M_s)_{i,i} ≥ 1`) rule-removal tower.
-/
def OmegaCoordMonotoneMatrixTower (d : Nat) (hd : 0 < d) :
    Nat -> List (List MixedSRSSym × List MixedSRSSym) -> Prop
  | 0, rules => rules = []
  | k + 1, rules =>
    rules = [] ∨
    ∃ (rem : List (List MixedSRSSym × List MixedSRSSym))
      (interp : MixedSRSSym -> NatAffineDim d),
      (∀ (s : MixedSRSSym) (i : Fin d), (interp s).M i i ≥ 1) ∧
      (∀ r ∈ rules, weakOrientsNatAffineDim d
        (evalWordNatAffineDim d interp r.1) (evalWordNatAffineDim d interp r.2)) ∧
      (∀ r ∈ rules, ¬ orientsNatAffineDim d hd
        (evalWordNatAffineDim d interp r.1) (evalWordNatAffineDim d interp r.2) -> r ∈ rem) ∧
      OmegaCoordMonotoneMatrixTower d hd k rem

/--
  `k`-level `d`-dimensional lower-triangular (`IsLowerTriMat d (M_s)` and `(M_s)_{0,0} ≥ 1`,
  arbitrary zero lower diagonals allowed) rule-removal tower.
-/
def OmegaLowerTriMatrixTower (d : Nat) (hd : 0 < d) :
    Nat -> List (List MixedSRSSym × List MixedSRSSym) -> Prop
  | 0, rules => rules = []
  | k + 1, rules =>
    rules = [] ∨
    ∃ (rem : List (List MixedSRSSym × List MixedSRSSym))
      (interp : MixedSRSSym -> NatAffineDim d),
      (∀ s : MixedSRSSym, IsLowerTriMat d (interp s).M ∧ (interp s).M ⟨0, hd⟩ ⟨0, hd⟩ ≥ 1) ∧
      (∀ r ∈ rules, weakOrientsNatAffineDim d
        (evalWordNatAffineDim d interp r.1) (evalWordNatAffineDim d interp r.2)) ∧
      (∀ r ∈ rules, ¬ orientsNatAffineDim d hd
        (evalWordNatAffineDim d interp r.1) (evalWordNatAffineDim d interp r.2) -> r ∈ rem) ∧
      OmegaLowerTriMatrixTower d hd k rem

/--
  Theorem W8.1g (`omega_k_coord_monotone_and_lower_tri_matrix_tower_impossibility`, zero custom axioms):
  Universal All-Dimension All-Rank (`∀ d ≥ 1, ∀ k : Nat`) Matrix Rule-Removal Tower Barriers:
  In sharp contrast to our 2- and 3-level `2D` non-triangular Hofbauer–Waldmann towers on
  `10/11` rules (`omit_r7_and_omit_r5_10_of_11_admit_2d_hw_towers`), for EVERY dimension `d ≥ 1`,
  EVERY tower height `k : Nat`, and EVERY rule set `rules` containing `sub6RuleList`:
  1. `¬ OmegaCoordMonotoneMatrixTower d hd k rules` (at every level, weak orientation of `sub6`
     under `(M_s)_{i,i} ≥ 1` forces `M_s = I_d` AND `v_s = 0` across all 5 interior symbols
     `{B0, B1, T0, T1, T2}`, removing 0 rules of `sub6`!);
  2. `¬ OmegaLowerTriMatrixTower d hd k rules` (at every level, lower-triangular top-left
     decoupling forces `(M_s)_{0,0} = 1` AND `(v_s)_0 = 0` across `{B0, B1, T0, T1, T2}`,
     removing 0 rules of `sub6`!).
-/
theorem omega_k_coord_monotone_and_lower_tri_matrix_tower_impossibility
    (d : Nat) (hd : 0 < d) (k : Nat)
    (rules : List (List MixedSRSSym × List MixedSRSSym))
    (hsub : ∀ r ∈ sub6RuleList, r ∈ rules) :
    ¬ OmegaCoordMonotoneMatrixTower d hd k rules ∧
    ¬ OmegaLowerTriMatrixTower d hd k rules := by
  have hstall_coord : ∀ (lvl : Nat) (rs : List (List MixedSRSSym × List MixedSRSSym)),
      (∀ r ∈ sub6RuleList, r ∈ rs) ->
      ¬ OmegaCoordMonotoneMatrixTower d hd lvl rs := by
    intro lvl
    induction lvl with
    | zero =>
      intro rs hs ht
      rw [OmegaCoordMonotoneMatrixTower] at ht; subst ht
      cases hs ([.L, .B1], [.L, .T2]) (by decide)
    | succ lvl' ih =>
      intro rs hs ht
      rcases ht with rfl | ⟨rem, interp, hdiag_pos, hweak, hkeep, hrem_t⟩
      · cases hs ([.L, .B1], [.L, .T2]) (by decide)
      · have hw_r2  := hweak ([.L, .B1], [.L, .T2]) (hs _ (by decide))
        have hw_r5  := hweak ([.T1, .B0], [.B1, .T0]) (hs _ (by decide))
        have hw_r7  := hweak ([.T2, .B0], [.B0, .T1]) (hs _ (by decide))
        have hw_r9  := hweak ([.T0, .R], [.B1, .R]) (hs _ (by decide))
        have hw_r11 := hweak ([.T2, .R], [.B1, .B0, .R]) (hs _ (by decide))
        let ML := (interp .L).M
        let MR := (interp .R).M
        let MB0 := (interp .B0).M
        let MB1 := (interp .B1).M
        let MT0 := (interp .T0).M
        let MT1 := (interp .T1).M
        let MT2 := (interp .T2).M
        have hr2_m : ∀ i j : Fin d, natMatMul d ML MB1 i j ≥ natMatMul d ML MT2 i j := by
          intro i j; have h := hw_r2.1 i j; rwa [evalWord2_M, evalWord2_M] at h
        have hr5_m : ∀ i j : Fin d, natMatMul d MT1 MB0 i j ≥ natMatMul d MB1 MT0 i j := by
          intro i j; have h := hw_r5.1 i j; rwa [evalWord2_M, evalWord2_M] at h
        have hr7_m : ∀ i j : Fin d, natMatMul d MT2 MB0 i j ≥ natMatMul d MB0 MT1 i j := by
          intro i j; have h := hw_r7.1 i j; rwa [evalWord2_M, evalWord2_M] at h
        have hr9_m : ∀ i j : Fin d, natMatMul d MT0 MR i j ≥ natMatMul d MB1 MR i j := by
          intro i j; have h := hw_r9.1 i j; rwa [evalWord2_M, evalWord2_M] at h
        have hr11_m : ∀ i j : Fin d,
            natMatMul d MT2 MR i j ≥ natMatMul d MB1 (natMatMul d MB0 MR) i j := by
          intro i j; have h := hw_r11.1 i j; rwa [evalWord2_M, evalWord3_M] at h
        have hLB1R_ge_LT2R : ∀ i j : Fin d,
            natMatMul d (natMatMul d ML MB1) MR i j ≥ natMatMul d (natMatMul d ML MT2) MR i j :=
          natMatMul_mono_left_w5 d _ _ MR hr2_m
        have hLT2R_ge_LB1B0R : ∀ i j : Fin d,
            natMatMul d (natMatMul d ML MT2) MR i j ≥
              natMatMul d (natMatMul d (natMatMul d ML MB1) MB0) MR i j := by
          intro i j
          rw [natMatMul_assoc_w5 d ML MT2 MR i j,
              natMatMul_assoc_w5 d (natMatMul d ML MB1) MB0 MR i j,
              natMatMul_assoc_w5 d ML MB1 (natMatMul d MB0 MR) i j]
          exact natMatMul_mono_right_w5 d ML _ _ hr11_m i j
        have hLB1_diag : ∀ i : Fin d, natMatMul d ML MB1 i i ≥ 1 :=
          natMatMul_diag_ge_one_w5 d ML MB1 (hdiag_pos .L) (hdiag_pos .B1)
        have hMB0_id : ∀ i j : Fin d, MB0 i j = natMatId d i j := by
          intro i j
          have h1 := hLB1R_ge_LT2R i j
          have h2 := hLT2R_ge_LB1B0R i j
          have hprop_r := natMatMul_sandwich_excess_w5 d (natMatMul d ML MB1) MB0 MR
            hLB1_diag (hdiag_pos .B0) (hdiag_pos .R) i j
          by_cases hij : i.val = j.val
          · rw [Fin.eq_of_val_eq hij] at h1 h2 hprop_r ⊢
            have hid1 : natMatId d j j = 1 := by simp [natMatId]
            have hd1 : MB0 j j ≥ 1 := hdiag_pos .B0 j
            rw [hid1] at hprop_r ⊢; omega
          · have hid0 : natMatId d i j = 0 := by simp [natMatId, hij]
            rw [hid0] at hprop_r ⊢; omega
        have hLB1R_eq_LT2R : ∀ i j : Fin d,
            natMatMul d (natMatMul d ML MB1) MR i j = natMatMul d (natMatMul d ML MT2) MR i j := by
          intro i j
          have h1 := hLB1R_ge_LT2R i j
          have h2 := hLT2R_ge_LB1B0R i j
          have hB0_eq : ∀ p q : Fin d,
              natMatMul d (natMatMul d ML MB1) MB0 p q = natMatMul d ML MB1 p q := by
            intro p q
            have hc : ∀ k : Fin d, natMatMul d ML MB1 p k * MB0 k q =
                natMatMul d ML MB1 p k * natMatId d k q := fun k => by rw [hMB0_id]
            exact (natSumPrefix_congr d _ _ hc d).trans (natMatMul_right_id d _ p q)
          have h3 : natMatMul d (natMatMul d (natMatMul d ML MB1) MB0) MR i j =
              natMatMul d (natMatMul d ML MB1) MR i j :=
            natSumPrefix_congr d _ _ (fun k => by rw [hB0_eq]) d
          omega
        have hMT2_ge_MT1 : ∀ i j : Fin d, MT2 i j ≥ MT1 i j := by
          intro i j
          have h7 := hr7_m i j
          have hl : natMatMul d MT2 MB0 i j = MT2 i j :=
            (natSumPrefix_congr d _ _ (fun k => by rw [hMB0_id]) d).trans (natMatMul_right_id d MT2 i j)
          have hr : natMatMul d MB0 MT1 i j = MT1 i j :=
            (natSumPrefix_congr d _ _ (fun k => by rw [hMB0_id]) d).trans (natMatMul_left_id_w5 d MT1 i j)
          rwa [hl, hr] at h7
        have hMT1_ge_MB1T0 : ∀ i j : Fin d, MT1 i j ≥ natMatMul d MB1 MT0 i j := by
          intro i j
          have h5 := hr5_m i j
          have hl : natMatMul d MT1 MB0 i j = MT1 i j :=
            (natSumPrefix_congr d _ _ (fun k => by rw [hMB0_id]) d).trans (natMatMul_right_id d MT1 i j)
          rwa [hl] at h5
        have hMT2_ge_MB1T0 : ∀ i j : Fin d, MT2 i j ≥ natMatMul d MB1 MT0 i j :=
          fun i j => Nat.le_trans (hMT1_ge_MB1T0 i j) (hMT2_ge_MT1 i j)
        have hMT0_id : ∀ i j : Fin d, MT0 i j = natMatId d i j := by
          intro i j
          have hlt2_ge : natMatMul d (natMatMul d ML MT2) MR i j ≥
              natMatMul d (natMatMul d (natMatMul d ML MB1) MT0) MR i j := by
            have hm1 := natMatMul_mono_left_w5 d _ _ MR
              (natMatMul_mono_right_w5 d ML MT2 (natMatMul d MB1 MT0) hMT2_ge_MB1T0) i j
            have hassoc : natMatMul d (natMatMul d ML (natMatMul d MB1 MT0)) MR i j =
                natMatMul d (natMatMul d (natMatMul d ML MB1) MT0) MR i j :=
              natSumPrefix_congr d _ _ (fun k => by rw [← natMatMul_assoc_w5 d ML MB1 MT0 i k]) d
            rwa [hassoc] at hm1
          rw [← hLB1R_eq_LT2R i j] at hlt2_ge
          have hsum_le := natMatMul_sandwich_excess_w5 d (natMatMul d ML MB1) MT0 MR
            hLB1_diag (hdiag_pos .T0) (hdiag_pos .R) i j
          by_cases hij : i.val = j.val
          · rw [Fin.eq_of_val_eq hij] at hlt2_ge hsum_le ⊢
            have hid1 : natMatId d j j = 1 := by simp [natMatId]
            have hd1 : MT0 j j ≥ 1 := hdiag_pos .T0 j
            rw [hid1] at hsum_le ⊢; omega
          · have hid0 : natMatId d i j = 0 := by simp [natMatId, hij]
            rw [hid0] at hsum_le ⊢; omega
        have hMB1_id : ∀ i j : Fin d, MB1 i j = natMatId d i j := by
          intro i j
          have h9 := hr9_m i j
          have hl : natMatMul d MT0 MR i j = MR i j :=
            (natSumPrefix_congr d _ _ (fun k => by rw [hMT0_id]) d).trans (natMatMul_left_id_w5 d MR i j)
          rw [hl] at h9
          have hex := natMatMul_excess_left_w5 d MB1 MR (hdiag_pos .B1) (hdiag_pos .R) i j
          by_cases hij : i.val = j.val
          · rw [Fin.eq_of_val_eq hij] at h9 hex ⊢
            have hid1 : natMatId d j j = 1 := by simp [natMatId]
            have hd1 : MB1 j j ≥ 1 := hdiag_pos .B1 j
            rw [hid1] at hex ⊢; omega
          · have hid0 : natMatId d i j = 0 := by simp [natMatId, hij]
            rw [hid0] at hex ⊢; omega
        have hMT2_id : ∀ i j : Fin d, MT2 i j = natMatId d i j := by
          intro i j
          have h2 := hr2_m i j
          have hl : natMatMul d ML MB1 i j = ML i j :=
            (natSumPrefix_congr d _ _ (fun k => by rw [hMB1_id]) d).trans (natMatMul_right_id d ML i j)
          rw [hl] at h2
          have hex := natMatMul_excess_right_w5 d ML MT2 (hdiag_pos .L) (hdiag_pos .T2) i j
          by_cases hij : i.val = j.val
          · rw [Fin.eq_of_val_eq hij] at h2 hex ⊢
            have hid1 : natMatId d j j = 1 := by simp [natMatId]
            have hd1 : MT2 j j ≥ 1 := hdiag_pos .T2 j
            rw [hid1] at hex ⊢; omega
          · have hid0 : natMatId d i j = 0 := by simp [natMatId, hij]
            rw [hid0] at hex ⊢; omega
        have hMT1_id : ∀ i j : Fin d, MT1 i j = natMatId d i j := by
          intro i j
          have hge1 := hMT2_ge_MT1 i j
          have hge2 := hMT1_ge_MB1T0 i j
          have hr_id : natMatMul d MB1 MT0 i j = natMatId d i j := by
            have hc : ∀ k : Fin d, MB1 i k * MT0 k j = natMatId d i k * natMatId d k j :=
              fun k => by rw [hMB1_id, hMT0_id]
            exact (natSumPrefix_congr d _ _ hc d).trans (natMatMul_right_id d (natMatId d) i j)
          rw [hMT2_id i j] at hge1
          rw [hr_id] at hge2
          omega
        -- Helper for `.v` when left symbol(s) have `M = I_d`:
        have hvec_zero : ∀ M : Fin d -> Fin d -> Nat,
            natMatVec d M (fun _ => 0) = fun _ => 0 := by
          intro M; funext p; unfold natMatVec natSumFin
          have hc : ∀ k : Fin d, M p k * 0 = 0 := fun _ => Nat.mul_zero _
          rw [natSumPrefix_congr d _ _ hc d]
          exact natSumPrefix_zero_w6 d d
        have hmv_of_id : ∀ (M : Fin d -> Fin d -> Nat) (u : Fin d -> Nat) (i : Fin d),
            (∀ p q : Fin d, M p q = natMatId d p q) ->
            natMatVec d M u i = u i := by
          intro M u i hid
          have hc : ∀ k : Fin d, M i k * u k = natMatId d i k * u k := fun k => by rw [hid]
          exact (natSumPrefix_congr d _ _ hc d).trans (natMatVec_id d u i)
        have hv1 : ∀ s : MixedSRSSym, ∀ i : Fin d,
            (evalWordNatAffineDim d interp [s]).v i = (interp s).v i := by
          intro s i
          simp only [evalWordNatAffineDim, compNatAffineDim, hvec_zero, Nat.zero_add]
        have hv2_id : ∀ (s1 s2 : MixedSRSSym) (i : Fin d),
            (∀ p q : Fin d, (interp s1).M p q = natMatId d p q) ->
            (evalWordNatAffineDim d interp [s1, s2]).v i = (interp s2).v i + (interp s1).v i := by
          intro s1 s2 i hs1
          simp only [evalWordNatAffineDim, compNatAffineDim, hvec_zero, Nat.zero_add]
          rw [hmv_of_id (interp s1).M (interp s2).v i hs1]
        have hv3_id : ∀ (s1 s2 s3 : MixedSRSSym) (i : Fin d),
            (∀ p q : Fin d, (interp s1).M p q = natMatId d p q) ->
            (∀ p q : Fin d, (interp s2).M p q = natMatId d p q) ->
            (evalWordNatAffineDim d interp [s1, s2, s3]).v i =
              (interp s3).v i + (interp s2).v i + (interp s1).v i := by
          intro s1 s2 s3 i hs1 hs2
          have h23 := hv2_id s2 s3 i hs2
          change (compNatAffineDim d (interp s1) (evalWordNatAffineDim d interp [s2, s3])).v i = _
          simp only [compNatAffineDim]
          rw [hmv_of_id (interp s1).M (evalWordNatAffineDim d interp [s2, s3]).v i hs1, h23]
        -- Deduce `(interp .T2).v i ≥ (interp .B1).v i + (interp .B0).v i` from `R11`:
        have hv_T2_ge : ∀ i : Fin d,
            (interp .T2).v i ≥ (interp .B1).v i + (interp .B0).v i := by
          intro i
          have h := hw_r11.2 i
          rw [hv2_id .T2 .R i hMT2_id, hv3_id .B1 .B0 .R i hMB1_id hMB0_id] at h
          omega
        -- Combine with `R2` (`ML * v_B1 + v_L ≥ ML * v_T2 + v_L` and `ML i i ≥ 1`) to get `v_T2 = v_B1` and `v_B0 = 0`:
        have hv_T2_eq_B1 : ∀ i : Fin d,
            (interp .T2).v i = (interp .B1).v i ∧ (interp .B0).v i = 0 := by
          intro i
          have hr2_vi := hw_r2.2 i
          simp only [evalWordNatAffineDim, compNatAffineDim, hvec_zero, Nat.zero_add] at hr2_vi
          have hge_t2_b1 : ∀ k : Fin d, (interp .T2).v k ≥ (interp .B1).v k :=
            fun k => by have h := hv_T2_ge k; omega
          by_cases hgt : (interp .T2).v i > (interp .B1).v i
          · exfalso
            have hk_ge : ∀ k : Fin d,
                (interp .L).M i k * (interp .T2).v k ≥
                  (interp .L).M i k * (interp .B1).v k + (if k.val = i.val then 1 else 0) := by
              intro k
              by_cases hki : k.val = i.val
              · have hkeq : k = i := Fin.ext hki
                subst hkeq; simp only [ite_true]
                have hm := Nat.mul_le_mul_left ((interp .L).M k k)
                  (by omega : (interp .B1).v k + 1 ≤ (interp .T2).v k)
                rw [Nat.mul_add, Nat.mul_one] at hm
                have hd1 := hdiag_pos .L k
                omega
              · simp only [hki, ite_false, Nat.add_zero]
                exact Nat.mul_le_mul_left ((interp .L).M i k) (hge_t2_b1 k)
            have hsum := natSumPrefix_mono_w5 d
              (fun k => (interp .L).M i k * (interp .B1).v k + (if k.val = i.val then 1 else 0))
              (fun k => (interp .L).M i k * (interp .T2).v k) hk_ge d
            rw [natSumPrefix_add, natSumPrefix_single d i 1 d] at hsum
            simp [i.isLt] at hsum
            have hr2_vi' : natSumPrefix d (fun k => (interp .L).M i k * (interp .B1).v k) d + (interp .L).v i ≥
                natSumPrefix d (fun k => (interp .L).M i k * (interp .T2).v k) d + (interp .L).v i := hr2_vi
            omega
          · have h1 := hv_T2_ge i
            omega
        -- Chain `R7 + R5 + R9` to get `v_B1 = v_T0 = v_T1 = v_T2 = 0`:
        have hv_all_zero : ∀ i : Fin d,
            (interp .B0).v i = 0 ∧ (interp .B1).v i = 0 ∧
            (interp .T0).v i = 0 ∧ (interp .T1).v i = 0 ∧ (interp .T2).v i = 0 := by
          intro i
          rcases hv_T2_eq_B1 i with ⟨ht2_b1, hb0_0⟩
          have hr5_vi := hw_r5.2 i
          rw [hv2_id .T1 .B0 i hMT1_id, hv2_id .B1 .T0 i hMB1_id] at hr5_vi
          have hr7_vi := hw_r7.2 i
          rw [hv2_id .T2 .B0 i hMT2_id, hv2_id .B0 .T1 i hMB0_id] at hr7_vi
          have hr9_vi := hw_r9.2 i
          rw [hv2_id .T0 .R i hMT0_id, hv2_id .B1 .R i hMB1_id] at hr9_vi
          omega
        -- Every rule in `sub6RuleList` has equal `v_0` on LHS and RHS, so all 6 remain in `rem`!
        have hall_kept : ∀ r ∈ sub6RuleList, r ∈ rem := by
          intro r hr_mem
          apply hkeep r (hs r hr_mem)
          simp only [sub6RuleList, List.mem_cons, List.not_mem_nil, or_false] at hr_mem
          have hz := hv_all_zero ⟨0, hd⟩
          rcases hr_mem with rfl | rfl | rfl | rfl | rfl | rfl
          · intro hstr
            have hgt := hstr.2.2
            simp only [evalWordNatAffineDim, compNatAffineDim, hvec_zero, Nat.zero_add] at hgt
            have hb1z : (interp .B1).v = fun _ => 0 := funext (fun i => (hv_all_zero i).2.1)
            have ht2z : (interp .T2).v = fun _ => 0 := funext (fun i => (hv_all_zero i).2.2.2.2)
            rw [hb1z, ht2z] at hgt
            exact Nat.lt_irrefl _ hgt
          · intro hstr; have hgt := hstr.2.2
            rw [hv2_id .T1 .B0 ⟨0, hd⟩ hMT1_id, hv2_id .B1 .T0 ⟨0, hd⟩ hMB1_id] at hgt; omega
          · intro hstr; have hgt := hstr.2.2
            rw [hv2_id .T2 .B0 ⟨0, hd⟩ hMT2_id, hv2_id .B0 .T1 ⟨0, hd⟩ hMB0_id] at hgt; omega
          · intro hstr; have hgt := hstr.2.2
            rw [hv2_id .T2 .B1 ⟨0, hd⟩ hMT2_id, hv2_id .B1 .T2 ⟨0, hd⟩ hMB1_id] at hgt; omega
          · intro hstr; have hgt := hstr.2.2
            rw [hv2_id .T0 .R ⟨0, hd⟩ hMT0_id, hv2_id .B1 .R ⟨0, hd⟩ hMB1_id] at hgt; omega
          · intro hstr; have hgt := hstr.2.2
            rw [hv2_id .T2 .R ⟨0, hd⟩ hMT2_id, hv3_id .B1 .B0 .R ⟨0, hd⟩ hMB1_id hMB0_id] at hgt; omega
        exact ih rem hall_kept hrem_t
  have hstall_low : ∀ (lvl : Nat) (rs : List (List MixedSRSSym × List MixedSRSSym)),
      (∀ r ∈ sub6RuleList, r ∈ rs) ->
      ¬ OmegaLowerTriMatrixTower d hd lvl rs := by
    intro lvl
    induction lvl with
    | zero =>
      intro rs hs ht
      rw [OmegaLowerTriMatrixTower] at ht; subst ht
      cases hs ([.L, .B1], [.L, .T2]) (by decide)
    | succ lvl' ih =>
      intro rs hs ht
      rcases ht with rfl | ⟨rem, interp, hlow_top, hweak, hkeep, hrem_t⟩
      · cases hs ([.L, .B1], [.L, .T2]) (by decide)
      · let z : Fin d := ⟨0, hd⟩
        have hlow : ∀ s : MixedSRSSym, IsLowerTriMat d (interp s).M := fun s => (hlow_top s).1
        have htop : ∀ s : MixedSRSSym, (interp s).M z z ≥ 1 := fun s => (hlow_top s).2
        have h1_step : ∀ s : MixedSRSSym,
            (evalWordNatAffineDim d interp [s]).M z z = (interp s).M z z ∧
            (evalWordNatAffineDim d interp [s]).v z = (interp s).v z := by
          intro s
          rcases (evalWord_lowerTri_coord0 d hd interp hlow []).2 s with ⟨hm, hv⟩
          have hid_m : (evalWordNatAffineDim d interp []).M z z = 1 := by
            simp [evalWordNatAffineDim, natMatId]
          have hid_v : (evalWordNatAffineDim d interp []).v z = 0 := rfl
          rw [hid_m, Nat.mul_one] at hm
          rw [hid_v, Nat.mul_zero, Nat.add_zero] at hv
          exact ⟨hm, hv⟩
        have h2_step : ∀ s1 s2 : MixedSRSSym,
            (evalWordNatAffineDim d interp [s1, s2]).M z z =
              (interp s1).M z z * (interp s2).M z z ∧
            (evalWordNatAffineDim d interp [s1, s2]).v z =
              (interp s1).v z + (interp s1).M z z * (interp s2).v z := by
          intro s1 s2
          rcases (evalWord_lowerTri_coord0 d hd interp hlow [s2]).2 s1 with ⟨hm, hv⟩
          rw [(h1_step s2).1] at hm
          rw [(h1_step s2).2] at hv
          exact ⟨hm, hv⟩
        have h3_step : ∀ s1 s2 s3 : MixedSRSSym,
            (evalWordNatAffineDim d interp [s1, s2, s3]).M z z =
              (interp s1).M z z * (interp s2).M z z * (interp s3).M z z ∧
            (evalWordNatAffineDim d interp [s1, s2, s3]).v z =
              (interp s1).v z + (interp s1).M z z *
                ((interp s2).v z + (interp s2).M z z * (interp s3).v z) := by
          intro s1 s2 s3
          rcases (evalWord_lowerTri_coord0 d hd interp hlow [s2, s3]).2 s1 with ⟨hm, hv⟩
          rw [(h2_step s2 s3).1, ← Nat.mul_assoc] at hm
          rw [(h2_step s2 s3).2] at hv
          exact ⟨hm, hv⟩
        have hw_r2  := hweak ([.L, .B1], [.L, .T2]) (hs _ (by decide))
        have hw_r5  := hweak ([.T1, .B0], [.B1, .T0]) (hs _ (by decide))
        have hw_r7  := hweak ([.T2, .B0], [.B0, .T1]) (hs _ (by decide))
        have hw_r9  := hweak ([.T0, .R], [.B1, .R]) (hs _ (by decide))
        have hw_r11 := hweak ([.T2, .R], [.B1, .B0, .R]) (hs _ (by decide))
        have hr2_m := hw_r2.1 z z; rw [(h2_step .L .B1).1, (h2_step .L .T2).1] at hr2_m
        have hr5_m := hw_r5.1 z z; rw [(h2_step .T1 .B0).1, (h2_step .B1 .T0).1] at hr5_m
        have hr7_m := hw_r7.1 z z; rw [(h2_step .T2 .B0).1, (h2_step .B0 .T1).1] at hr7_m
        have hr9_m := hw_r9.1 z z; rw [(h2_step .T0 .R).1, (h2_step .B1 .R).1] at hr9_m
        have hr11_m := hw_r11.1 z z; rw [(h2_step .T2 .R).1, (h3_step .B1 .B0 .R).1] at hr11_m
        rcases upper_triangular_top_left_unit_collapse_any_dim
          ((interp .L).M z z) ((interp .R).M z z) ((interp .B0).M z z) ((interp .B1).M z z)
          ((interp .T0).M z z) ((interp .T1).M z z) ((interp .T2).M z z)
          (htop .L) (htop .R) (htop .B0) (htop .B1) (htop .T0) (htop .T1) (htop .T2)
          hr2_m hr5_m hr7_m hr9_m hr11_m with ⟨hmB0, hmB1, hmT0, hmT1, hmT2⟩
        have hr2_v := hw_r2.2 z; rw [(h2_step .L .B1).2, (h2_step .L .T2).2] at hr2_v
        have hr5_v := hw_r5.2 z; rw [(h2_step .T1 .B0).2, (h2_step .B1 .T0).2] at hr5_v
        have hr7_v := hw_r7.2 z; rw [(h2_step .T2 .B0).2, (h2_step .B0 .T1).2] at hr7_v
        have hr9_v := hw_r9.2 z; rw [(h2_step .T0 .R).2, (h2_step .B1 .R).2] at hr9_v
        have hr11_v := hw_r11.2 z; rw [(h2_step .T2 .R).2, (h3_step .B1 .B0 .R).2] at hr11_v
        simp only [hmB0, hmB1, hmT0, hmT1, hmT2, Nat.one_mul] at hr5_v hr7_v hr9_v hr11_v
        have hvB1_ge_T2 : (interp .B1).v z ≥ (interp .T2).v z :=
          nat_mul_le_cancel_left_w5 ((interp .L).M z z) _ _ (htop .L) (by omega)
        have hv_zero : (interp .B0).v z = 0 ∧ (interp .B1).v z = 0 ∧
            (interp .T0).v z = 0 ∧ (interp .T1).v z = 0 ∧ (interp .T2).v z = 0 := by omega
        rcases hv_zero with ⟨hvB0, hvB1, hvT0, hvT1, hvT2⟩
        have hall_kept : ∀ r ∈ sub6RuleList, r ∈ rem := by
          intro r hr_mem
          apply hkeep r (hs r hr_mem)
          simp only [sub6RuleList, List.mem_cons, List.not_mem_nil, or_false] at hr_mem
          rcases hr_mem with rfl | rfl | rfl | rfl | rfl | rfl
          · intro hstr; have hgt := hstr.2.2
            change (evalWordNatAffineDim d interp [.L, .B1]).v z >
              (evalWordNatAffineDim d interp [.L, .T2]).v z at hgt
            rw [(h2_step .L .B1).2, (h2_step .L .T2).2, hvB1, hvT2] at hgt; omega
          · intro hstr; have hgt := hstr.2.2
            change (evalWordNatAffineDim d interp [.T1, .B0]).v z >
              (evalWordNatAffineDim d interp [.B1, .T0]).v z at hgt
            rw [(h2_step .T1 .B0).2, (h2_step .B1 .T0).2, hvT1, hvB0, hvB1, hvT0] at hgt; omega
          · intro hstr; have hgt := hstr.2.2
            change (evalWordNatAffineDim d interp [.T2, .B0]).v z >
              (evalWordNatAffineDim d interp [.B0, .T1]).v z at hgt
            rw [(h2_step .T2 .B0).2, (h2_step .B0 .T1).2, hvT2, hvB0, hvT1] at hgt; omega
          · intro hstr; have hgt := hstr.2.2
            change (evalWordNatAffineDim d interp [.T2, .B1]).v z >
              (evalWordNatAffineDim d interp [.B1, .T2]).v z at hgt
            rw [(h2_step .T2 .B1).2, (h2_step .B1 .T2).2, hvT2, hvB1] at hgt; omega
          · intro hstr; have hgt := hstr.2.2
            change (evalWordNatAffineDim d interp [.T0, .R]).v z >
              (evalWordNatAffineDim d interp [.B1, .R]).v z at hgt
            rw [(h2_step .T0 .R).2, (h2_step .B1 .R).2, hmT0, hmB1, hvT0, hvB1] at hgt; omega
          · intro hstr; have hgt := hstr.2.2
            change (evalWordNatAffineDim d interp [.T2, .R]).v z >
              (evalWordNatAffineDim d interp [.B1, .B0, .R]).v z at hgt
            rw [(h2_step .T2 .R).2, (h3_step .B1 .B0 .R).2, hmT2, hmB1, hmB0, hvT2, hvB1, hvB0] at hgt
            omega
        exact ih rem hall_kept hrem_t
  exact ⟨hstall_coord k rules hsub, hstall_low k rules hsub⟩

-- ============================================================================
-- SECTION 2: Front B (Branch P3.4 & P3.3) — Cyclotomic Companion-Prime
--            Quotient Forcing Against `p = 331` & Pure-Integer Laurent
--            Binomial-Taylor Column-Extrapolation
-- ============================================================================

/--
  Theorem W8.2a (`one_block_exponents_coprime`, zero custom axioms):
  Universal 1-Block Exponent Coprimality (`Nat.gcd w1 a1 = 1`):
  On ANY 1-block positive cycle (`w1 ≥ 2, a1 ≥ 1, 3 ^ w1 < 2 ^ (w1 + a1)` and
  `(2 ^ (w1 + a1) - 3 ^ w1) * q0 = 2 ^ a1 - 1`), the odd-step weight `w1` and
  halving exponent `a1` are unconditionally coprime (`Nat.gcd w1 a1 = 1`)!
-/
theorem one_block_exponents_coprime
    (w1 a1 q0 : Nat)
    (hw1 : w1 ≥ 2) (ha1 : a1 ≥ 1)
    (hgt : 3 ^ w1 < 2 ^ (w1 + a1))
    (hbrox : (2 ^ (w1 + a1) - 3 ^ w1) * q0 = 2 ^ a1 - 1) :
    Nat.gcd w1 a1 = 1 := by
  let g := Nat.gcd w1 a1
  have hg_pos : g ≥ 1 := Nat.gcd_pos_of_pos_right w1 ha1
  by_cases hg2 : g ≥ 2
  · exfalso
    exact (one_block_common_divisor_impossibility g w1 a1 hg2 hw1 ha1 hgt
      (Nat.gcd_dvd_left w1 a1) (Nat.gcd_dvd_right w1 a1)).2 q0 hbrox
  · omega

theorem pow_sub_pow_mul_dvd_w8 (A B d : Nat) (hBA : B ≤ A) :
    ∀ k : Nat, (A ^ d - B ^ d) ∣ (A ^ (d * k) - B ^ (d * k))
  | 0 => by simp
  | k + 1 => by
    have hAdBd : B ^ d ≤ A ^ d := nat_pow_mono_base B A hBA d
    have hm := pow_sub_pow_dvd_w6 (A ^ d) (B ^ d) hAdBd (k + 1)
    rwa [pow_pow_eq_mul_w5 A d (k + 1), pow_pow_eq_mul_w5 B d (k + 1)] at hm

/--
  Modular-inverse prime cancellation: if `p ≥ 2` has a modular inverse for every non-zero
  residue `1 ≤ r < p` and `¬ (p ∣ D)`, then `p ∣ (D * X)` implies `p ∣ X`, and consequently
  `(p * M) ∣ (D * X)` implies `∃ X', X = p * X' ∧ M ∣ (D * X')`.
-/
def powModBinAux (p : Nat) : Nat -> Nat -> Nat -> Nat -> Nat
  | 0, _, _, acc => acc
  | fuel + 1, base, exp, acc =>
    if exp = 0 then acc
    else
      let acc' := if exp % 2 = 1 then (acc * base) % p else acc
      powModBinAux p fuel ((base * base) % p) (exp / 2) acc'

def fermatInvCand (p r : Nat) : Nat :=
  powModBinAux p 8 (r % p) (p - 2) 1

def checkUnitsGrid16x10 (p : Nat) : Prop :=
  p ≥ 2 ∧
  ∀ (a : Fin 16) (b : Fin 10),
    let r := 10 * a.val + b.val
    (1 ≤ r ∧ r < p) -> (r * fermatInvCand p r) % p = 1

instance (p : Nat) : Decidable (checkUnitsGrid16x10 p) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem checkUnitsGrid16x10_sound (p : Nat) (hp160 : p ≤ 160)
    (hc : checkUnitsGrid16x10 p) :
    p ≥ 2 ∧ ∀ r : Nat, 1 ≤ r -> r < p -> ∃ inv : Nat, (r * inv) % p = 1 := by
  rcases hc with ⟨hp2, hgrid⟩
  refine ⟨hp2, ?_⟩
  intro r hr1 hrlt
  have ha : r / 10 < 16 := by omega
  have hb : r % 10 < 10 := Nat.mod_lt r (by decide)
  have h1 := hgrid ⟨r / 10, ha⟩ ⟨r % 10, hb⟩
  dsimp only at h1
  rw [Nat.div_add_mod r 10] at h1
  exact ⟨fermatInvCand p r, h1 ⟨hr1, hrlt⟩⟩

theorem prime_unit_cancel_dvd_mul_w8 (p D X M : Nat)
    (hunit : p ≥ 2 ∧ ∀ r : Nat, 1 ≤ r -> r < p -> ∃ inv : Nat, (r * inv) % p = 1)
    (hndvd : ¬ (p ∣ D))
    (hdvd : (p * M) ∣ (D * X)) :
    ∃ X' : Nat, X = p * X' ∧ M ∣ (D * X') := by
  rcases hunit with ⟨hp2, hinv_all⟩
  have hp_pos : p > 0 := by omega
  have hr_ne0 : D % p ≠ 0 := fun hm0 => hndvd (Nat.dvd_of_mod_eq_zero hm0)
  have hr_lt : D % p < p := Nat.mod_lt D hp_pos
  rcases hinv_all (D % p) (by omega) hr_lt with ⟨inv, hinv⟩
  have hp_DX : p ∣ (D * X) := by
    rcases hdvd with ⟨k, hk⟩
    exact ⟨M * k, by rw [hk, Nat.mul_assoc]⟩
  have hDX_mod0 : (D * X) % p = 0 := Nat.mod_eq_zero_of_dvd hp_DX
  have h1 : ((D * inv) * X) % p = (D * X * inv) % p := by
    rw [Nat.mul_assoc D inv X, Nat.mul_comm inv X, ← Nat.mul_assoc D X inv]
  have h2 : ((D * inv) * X) % p = X % p := by
    have hd_inv : (D * inv) % p = 1 := by
      calc
        (D * inv) % p = ((D % p) * (inv % p)) % p := Nat.mul_mod D inv p
        _ = (((D % p) % p) * (inv % p)) % p := by rw [Nat.mod_mod]
        _ = ((D % p) * inv) % p := (Nat.mul_mod (D % p) inv p).symm
        _ = 1 := hinv
    rw [Nat.mul_mod (D * inv) X p, hd_inv, Nat.one_mul, Nat.mod_mod]
  have h3 : (D * X * inv) % p = 0 := by
    rw [Nat.mul_mod (D * X) inv p, hDX_mod0, Nat.zero_mul, Nat.zero_mod]
  have hX_mod0 : X % p = 0 := h2.symm.trans (h1.trans h3)
  rcases Nat.dvd_of_mod_eq_zero hX_mod0 with ⟨X', hX'⟩
  refine ⟨X', hX', ?_⟩
  rcases hdvd with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  have heq : p * (D * X') = p * (M * k) := by
    calc
      p * (D * X') = D * (p * X') := by
        rw [← Nat.mul_assoc p D X', Nat.mul_comm p D, Nat.mul_assoc]
      _ = D * X := by rw [← hX']
      _ = (p * M) * k := hk
      _ = p * (M * k) := Nat.mul_assoc p M k
  exact Nat.eq_of_mul_eq_mul_left hp_pos heq

/--
  Theorem W8.2b (`one_block_cyclotomic_companion_quotient_forcing`, zero custom axioms):
  Universal 1-Block Cyclotomic Companion Quotient & Seed Forcing:
  On ANY 1-block positive cycle (`w1 ≥ 2, a1 ≥ 1, 3 ^ w1 < 2 ^ (w1 + a1)`, `D := 2 ^ (w1 + a1) - 3 ^ w1`,
  `D * q0 = 2 ^ a1 - 1`), the cycle minimum `x0 := 2 ^ w1 * q0 - 1` automatically satisfies
  `D * x0 = 3 ^ w1 - 2 ^ w1`, AND whenever an odd `p ≥ 3` with exact multiplicative orders
  `d1 = ord_p(2)` and `d2 = ord_p(3/2)` divides `D`:
  1. `d1 ∣ a1` AND `d2 ∣ w1`;
  2. `(2 ^ d1 - 1) ∣ (D * q0)` AND `(3 ^ d2 - 2 ^ d2) ∣ (D * (2 ^ w1 * q0 - 1))`;
  3. Every prime list `ps_q` whose product divides `2 ^ d1 - 1` and avoids dividing `D`
     forces `natListProd ps_q ∣ q0`, and every prime list `ps_x` whose product divides
     `3 ^ d2 - 2 ^ d2` and avoids dividing `D` forces `natListProd ps_x ∣ (2 ^ w1 * q0 - 1)`!
-/
def natProdList : List Nat -> Nat
  | [] => 1
  | x :: xs => x * natProdList xs

theorem prime_list_cancel_dvd_w8 (D : Nat) :
    ∀ (ps : List Nat) (X R : Nat),
      (∀ p ∈ ps, p ≤ 160 ∧ checkUnitsGrid16x10 p ∧ ¬ (p ∣ D)) ->
      (natProdList ps * R) ∣ (D * X) ->
      natProdList ps ∣ X
  | [], X, _, _, _ => ⟨X, (Nat.one_mul X).symm⟩
  | p :: ps, X, R, hall, hdvd => by
    rcases hall p List.mem_cons_self with ⟨hp160, hcp, hndp⟩
    simp only [natProdList] at hdvd ⊢
    rw [Nat.mul_assoc p (natProdList ps) R] at hdvd
    rcases prime_unit_cancel_dvd_mul_w8 p D X (natProdList ps * R)
      (checkUnitsGrid16x10_sound p hp160 hcp) hndp hdvd with ⟨X', hX', hdvd'⟩
    rcases prime_list_cancel_dvd_w8 D ps X' R
      (fun q hq => hall q (List.mem_cons_of_mem p hq)) hdvd' with ⟨k, hk⟩
    exact ⟨k, by rw [hX', hk, Nat.mul_assoc]⟩

theorem one_block_cyclotomic_companion_quotient_forcing
    (w1 a1 q0 p d1 d2 : Nat)
    (_hw1 : w1 ≥ 2) (ha1 : a1 ≥ 1)
    (hgt : 3 ^ w1 < 2 ^ (w1 + a1))
    (hbrox : (2 ^ (w1 + a1) - 3 ^ w1) * q0 = 2 ^ a1 - 1)
    (hp3 : p ≥ 3) (hp_odd : p % 2 = 1)
    (hd1 : IsExactMultOrderMod p 2 d1)
    (hd2 : IsExactMultOrderMod p (ratio32Mod p) d2)
    (hp_D : p ∣ (2 ^ (w1 + a1) - 3 ^ w1)) :
    let D := 2 ^ (w1 + a1) - 3 ^ w1
    let x0 := 2 ^ w1 * q0 - 1
    D * x0 = 3 ^ w1 - 2 ^ w1 ∧
    d1 ∣ a1 ∧
    d2 ∣ w1 ∧
    (2 ^ d1 - 1) ∣ (D * q0) ∧
    (3 ^ d2 - 2 ^ d2) ∣ (D * x0) ∧
    (∀ (ps_q : List Nat) (Rq : Nat),
      (∀ q ∈ ps_q, q ≤ 160 ∧ checkUnitsGrid16x10 q ∧ ¬ (q ∣ D)) ->
      natProdList ps_q * Rq = 2 ^ d1 - 1 ->
      natProdList ps_q ∣ q0) ∧
    (∀ (ps_x : List Nat) (Rx : Nat),
      (∀ q ∈ ps_x, q ≤ 160 ∧ checkUnitsGrid16x10 q ∧ ¬ (q ∣ D)) ->
      natProdList ps_x * Rx = 3 ^ d2 - 2 ^ d2 ->
      natProdList ps_x ∣ x0) := by
  dsimp only
  let D := 2 ^ (w1 + a1) - 3 ^ w1
  let x0 := 2 ^ w1 * q0 - 1
  have h2a1_ge2 : 2 ^ a1 ≥ 2 := by simpa using pow2_mono_nat ha1
  have hq0_pos : q0 ≥ 1 := by
    cases q0 with
    | zero => rw [Nat.mul_zero] at hbrox; omega
    | succ _ => omega
  have h2w_pos : 2 ^ w1 ≥ 1 := pow2_pos_nat w1
  have h2w_le_3w : 2 ^ w1 ≤ 3 ^ w1 := pow2_le_pow3 w1
  -- 1. Pure algebraic identity `D * (2^w1 * q0 - 1) = 3^w1 - 2^w1`:
  have hDx0 : D * x0 = 3 ^ w1 - 2 ^ w1 := by
    have hmul_2w : D * (2 ^ w1 * q0) = 2 ^ (w1 + a1) - 2 ^ w1 := by
      calc
        D * (2 ^ w1 * q0) = (D * q0) * 2 ^ w1 := by
          rw [Nat.mul_comm (2 ^ w1) q0, ← Nat.mul_assoc D q0 (2 ^ w1)]
        _ = (2 ^ a1 - 1) * 2 ^ w1 := by rw [hbrox]
        _ = 2 ^ a1 * 2 ^ w1 - 1 * 2 ^ w1 := Nat.sub_mul (2 ^ a1) 1 (2 ^ w1)
        _ = 2 ^ (w1 + a1) - 2 ^ w1 := by rw [Nat.one_mul, ← Nat.pow_add, Nat.add_comm a1 w1]
    have hsub_D : D * (2 ^ w1 * q0 - 1) = D * (2 ^ w1 * q0) - D * 1 :=
      Nat.mul_sub_left_distrib D (2 ^ w1 * q0) 1
    dsimp [x0]
    rw [hsub_D, Nat.mul_one, hmul_2w]
    dsimp [D]
    generalize 2 ^ (w1 + a1) = p2k, 3 ^ w1 = p3w, 2 ^ w1 = p2w at hgt h2w_le_3w ⊢
    omega
  -- 2. Exact order divisibilities `d1 ∣ a1` and `d2 ∣ w1`:
  have hp_mers : p ∣ (2 ^ a1 - 1) := by
    rcases hp_D with ⟨k, hk⟩
    exact ⟨k * q0, by rw [← hbrox, hk, Nat.mul_assoc]⟩
  have h2a1_mod : 2 ^ a1 % p = 1 := by
    rcases hp_mers with ⟨m, hm⟩
    rw [show 2 ^ a1 = 1 + p * m by omega, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  have hd1_a1 : d1 ∣ a1 := exactMultOrderMod_dvd_of_pow_eq_one p 2 d1 a1 hd1 h2a1_mod
  have h2K_3w : 2 ^ (w1 + a1) % p = 3 ^ w1 % p := by
    rcases hp_D with ⟨k, hk⟩
    have hlt_kw := hgt
    have hrew : 2 ^ (w1 + a1) = 3 ^ w1 + p * k := by
      generalize 2 ^ (w1 + a1) = p2k, 3 ^ w1 = p3w at hk hlt_kw ⊢; omega
    rw [hrew, Nat.add_mul_mod_self_left]
  have h2K_2w : 2 ^ (w1 + a1) % p = 2 ^ w1 % p := by
    rw [Nat.pow_add 2 w1 a1, Nat.mul_mod, h2a1_mod, Nat.mul_one, Nat.mod_mod]
  have hd2_w1 : d2 ∣ w1 := exactMultOrderMod_dvd_of_pow_eq_one p (ratio32Mod p) d2 w1 hd2
    (ratio32Mod_pow_eq_one_of_pow3_eq_pow2 p w1 hp3 hp_odd (h2K_3w.symm.trans h2K_2w))
  -- 3. Cyclotomic divisibility `(2^d1 - 1) ∣ (2^a1 - 1)` and `(3^d2 - 2^d2) ∣ (3^w1 - 2^w1)`:
  have hdvd_mers : (2 ^ d1 - 1) ∣ (D * q0) := by
    rw [hbrox]
    rcases hd1_a1 with ⟨ka, hka⟩
    have hm := pow_sub_pow_mul_dvd_w8 2 1 d1 (by decide) ka
    simp only [Nat.one_pow, ← hka] at hm
    exact hm
  have hdvd_diff : (3 ^ d2 - 2 ^ d2) ∣ (D * x0) := by
    rw [hDx0]
    rcases hd2_w1 with ⟨kw, hkw⟩
    have hm := pow_sub_pow_mul_dvd_w8 3 2 d2 (by decide) kw
    rwa [← hkw] at hm
  refine ⟨hDx0, hd1_a1, hd2_w1, hdvd_mers, hdvd_diff, ?_, ?_⟩
  · intro ps_q Rq hall hprod
    rw [← hprod] at hdvd_mers
    exact prime_list_cancel_dvd_w8 D ps_q q0 Rq hall hdvd_mers
  · intro ps_x Rx hall hprod
    rw [← hprod] at hdvd_diff
    exact prime_list_cancel_dvd_w8 D ps_x x0 Rx hall hdvd_diff

/--
  Pure-kernel (`[]` axioms) certificate for companion primes `{11, 151}`,
  unit invertibility across `{3, 7, 11, 23, 31, 151}`, and exact factorizations of `2 ^ 30 - 1`
  and `3 ^ 11 - 2 ^ 11` at `p = 331` (all bounded recursion depth `≤ 16`).
-/
theorem prime_11_151_and_331_companion_cert :
    checkExactMultOrderBool 11 2 10 = true ∧
    checkExactMultOrderBool 11 (ratio32Mod 11) 10 = true ∧
    checkExactMultOrderBool 151 2 15 = true ∧
    checkExactMultOrderBool 151 ((ratio32Mod 151 ^ 10) ^ 5 % 151) 3 = true ∧
    checkUnitsGrid16x10 3 ∧
    checkUnitsGrid16x10 7 ∧
    checkUnitsGrid16x10 11 ∧
    checkUnitsGrid16x10 23 ∧
    checkUnitsGrid16x10 31 ∧
    checkUnitsGrid16x10 151 ∧
    natProdList [3, 3, 7, 11, 31, 151] = 3243933 ∧
    3243933 * 331 = (2 ^ 15) * (2 ^ 15) - 1 ∧
    natProdList [23, 23] = 529 ∧
    529 * 331 = 3 ^ 11 - 2 ^ 11 ∧
    331 % 8 = 3 ∧
    1210483 % 8 = 3 := by
  decide

theorem prod_mod8_in_1_or_3 :
    ∀ fs : List Nat,
      (∀ f ∈ fs, f % 8 = 1 ∨ f % 8 = 3) ->
      natProdList fs % 8 = 1 ∨ natProdList fs % 8 = 3
  | [], _ => Or.inl rfl
  | f :: fs, hall => by
    have hf := hall f List.mem_cons_self
    have ih := prod_mod8_in_1_or_3 fs (fun g hg => hall g (List.mem_cons_of_mem f hg))
    simp only [natProdList]
    rw [Nat.mul_mod]
    rcases hf with hf1 | hf3 <;> rcases ih with hi1 | hi3
    · rw [hf1, hi1]; exact Or.inl rfl
    · rw [hf1, hi3]; exact Or.inr rfl
    · rw [hf3, hi1]; exact Or.inr rfl
    · rw [hf3, hi3]; exact Or.inl rfl

theorem pow_mod8_in_1_or_3 (b : Nat) (hb : b % 8 = 1 ∨ b % 8 = 3) :
    ∀ e : Nat, (b ^ e) % 8 = 1 ∨ (b ^ e) % 8 = 3
  | 0 => Or.inl rfl
  | e + 1 => by
    have ih := pow_mod8_in_1_or_3 b hb e
    rw [Nat.pow_succ, Nat.mul_mod]
    rcases hb with hb1 | hb3 <;> rcases ih with hi1 | hi3
    · rw [hi1, hb1]; exact Or.inl rfl
    · rw [hi3, hb1]; exact Or.inr rfl
    · rw [hi1, hb3]; exact Or.inr rfl
    · rw [hi3, hb3]; exact Or.inl rfl

/--
  Theorem W8.2c (`one_block_331_companion_forcing_and_mod8_obstruction`, zero custom axioms, choice-free):
  Complete 1-Block Cyclotomic Companion Trap & Mod-8 Obstruction Against `p = 331`:
  1. Companion-Prime Exclusion: `{3, 7, 11, 23, 31, 151}` are ALL unconditionally excluded
     from dividing `D := 2 ^ (w1 + a1) - 3 ^ w1` on any 1-block positive cycle (`w1 ≥ 2`).
  2. Exact Quotient & Seed Multipliers under `331 ∣ D`:
     - `30 ∣ a1`, `11 ∣ w1`, `Nat.gcd w1 30 = 1` (`w1 % 2 = 1 ∧ w1 % 3 ≠ 0 ∧ w1 % 5 ≠ 0`);
     - **`3243933 ∣ q0`** (`3243933 = 3^2 * 7 * 11 * 31 * 151`, so `q0 ≥ 3,243,933`) AND
       **`529 ∣ (2 ^ w1 * q0 - 1)`** (`529 = 23^2`);
     - **`w1 ≥ 77 ∧ a1 ≥ 60 ∧ w1 + a1 ≥ 137`**;
     - **`D % 8 = 5`**, whereas for ALL `e1, e2 : Nat`, `(331 ^ e1 * 1210483 ^ e2) % 8 ∈ {1, 3}`,
       hence **`D ≠ 331 ^ e1 * 1210483 ^ e2`** (`D` cannot be supported purely on `{331, 1210483}`
       or any family of `≡ 1, 3 (mod 8)` primes, forcing an odd prime factor `q ∉ {331, 1210483}`
       with `q % 8 ∈ {5, 7}`!).
-/
theorem one_block_331_companion_forcing_and_mod8_obstruction
    (w1 a1 q0 : Nat)
    (hw1 : w1 ≥ 2) (ha1 : a1 ≥ 1)
    (hgt : 3 ^ w1 < 2 ^ (w1 + a1))
    (hbrox : (2 ^ (w1 + a1) - 3 ^ w1) * q0 = 2 ^ a1 - 1) :
    let D := 2 ^ (w1 + a1) - 3 ^ w1
    (¬ (3 ∣ D) ∧ ¬ (7 ∣ D) ∧ ¬ (11 ∣ D) ∧ ¬ (23 ∣ D) ∧ ¬ (31 ∣ D) ∧ ¬ (151 ∣ D)) ∧
    (331 ∣ D ->
      30 ∣ a1 ∧
      11 ∣ w1 ∧
      Nat.gcd w1 30 = 1 ∧
      3243933 ∣ q0 ∧
      529 ∣ (2 ^ w1 * q0 - 1) ∧
      w1 ≥ 77 ∧
      a1 ≥ 60 ∧
      D % 8 = 5 ∧
      (∀ e1 e2 : Nat, D ≠ 331 ^ e1 * 1210483 ^ e2) ∧
      (∀ fs : List Nat, (∀ f ∈ fs, f % 8 = 1 ∨ f % 8 = 3) -> D ≠ natProdList fs)) := by
  dsimp only
  let D := 2 ^ (w1 + a1) - 3 ^ w1
  rcases prime_11_151_and_331_companion_cert with
    ⟨h11_2, h11_32, h151_2, h151_32,
     hu3, hu7, hu11, hu23, hu31, hu151,
     hprod_q, _hmers30, hprod_x, _hdiff11, h331_m8, h1210_m8⟩
  rcases one_block_odd_order_primes_7_19_23_31_43_47_71_73_and_331_barrier with
    ⟨hexcl8, h331_2, h331_32, _⟩
  -- 1. Exclude `{3, 7, 11, 23, 31, 151}` from `D`:
  have hnd3 : ¬ (3 ∣ D) := by
    intro ⟨k, hk⟩
    have hp2_nd3 : 2 ^ (w1 + a1) % 3 ≠ 0 := by
      have hm : ∀ n : Nat, 2 ^ n % 3 = 1 ∨ 2 ^ n % 3 = 2 := by
        intro n; induction n with
        | zero => exact Or.inl rfl
        | succ n' ihn =>
          rw [Nat.pow_succ, Nat.mul_mod]
          rcases ihn with h1 | h2
          · rw [h1]; exact Or.inr rfl
          · rw [h2]; exact Or.inl rfl
      rcases hm (w1 + a1) with h1 | h2 <;> omega
    have hp3_m3 : 3 ^ w1 % 3 = 0 := by
      rw [show w1 = (w1 - 1) + 1 by omega, Nat.pow_succ, Nat.mul_mod_left]
    have hlt_kw := hgt
    have hrew : 2 ^ (w1 + a1) = 3 ^ w1 + 3 * k := by
      dsimp [D] at hk
      generalize 2 ^ (w1 + a1) = p2k, 3 ^ w1 = p3w at hk hlt_kw ⊢; omega
    have hm2 : 2 ^ (w1 + a1) % 3 = 0 := by
      rw [hrew, Nat.add_mul_mod_self_left, hp3_m3]
    exact hp2_nd3 hm2
  have hnd7 : ¬ (7 ∣ D) := hexcl8 w1 a1 q0 7 hw1 ha1 hgt hbrox (Or.inl rfl)
  have hnd23 : ¬ (23 ∣ D) := hexcl8 w1 a1 q0 23 hw1 ha1 hgt hbrox (Or.inr (Or.inr (Or.inl rfl)))
  have hnd31 : ¬ (31 ∣ D) := hexcl8 w1 a1 q0 31 hw1 ha1 hgt hbrox (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have hnd11 : ¬ (11 ∣ D) :=
    one_block_common_order_prime_exclusion w1 a1 q0 11 10 10 hw1 ha1 hgt hbrox
      (by decide) (by decide)
      (checkExactMultOrderBool_sound _ _ _ h11_2)
      (checkExactMultOrderBool_sound _ _ _ h11_32) (by decide)
  have hnd151 : ¬ (151 ∣ D) := by
    intro h151_D
    have h151_mers : 151 ∣ (2 ^ a1 - 1) := by
      rcases h151_D with ⟨k, hk⟩
      exact ⟨k * q0, by dsimp [D] at hk; rw [← hbrox, hk, Nat.mul_assoc]⟩
    have h2a1_151 : 2 ^ a1 % 151 = 1 := by
      rcases h151_mers with ⟨m, hm⟩
      have hp2a : 2 ^ a1 ≥ 2 := by simpa using pow2_mono_nat ha1
      rw [show 2 ^ a1 = 1 + 151 * m by omega, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by decide)]
    have h15_a1 : 15 ∣ a1 :=
      exactMultOrderMod_dvd_of_pow_eq_one 151 2 15 a1
        (checkExactMultOrderBool_sound _ _ _ h151_2) h2a1_151
    have h3_a1 : 3 ∣ a1 := Nat.dvd_trans ⟨5, rfl⟩ h15_a1
    have h2K_3w : 2 ^ (w1 + a1) % 151 = 3 ^ w1 % 151 := by
      rcases h151_D with ⟨k, hk⟩
      have hlt_kw := hgt
      have hrew : 2 ^ (w1 + a1) = 3 ^ w1 + 151 * k := by
        dsimp [D] at hk
        generalize 2 ^ (w1 + a1) = p2k, 3 ^ w1 = p3w at hk hlt_kw ⊢; omega
      rw [hrew, Nat.add_mul_mod_self_left]
    have h2K_2w : 2 ^ (w1 + a1) % 151 = 2 ^ w1 % 151 := by
      rw [Nat.pow_add 2 w1 a1, Nat.mul_mod, h2a1_151, Nat.mul_one, Nat.mod_mod]
    have hrat1 : (ratio32Mod 151) ^ w1 % 151 = 1 :=
      ratio32Mod_pow_eq_one_of_pow3_eq_pow2 151 w1 (by decide) (by decide) (h2K_3w.symm.trans h2K_2w)
    let g50 := (ratio32Mod 151 ^ 10) ^ 5 % 151
    have hg50_w1 : g50 ^ w1 % 151 = 1 := by
      have hp1 : g50 ^ w1 % 151 = ((ratio32Mod 151 ^ 10) ^ 5) ^ w1 % 151 :=
        pow_mod_eq_of_mod_eq_w5 151 g50 _ (Nat.mod_mod _ 151) w1
      rw [hp1, pow_pow_eq_mul_w5 (ratio32Mod 151) 10 5,
          pow_pow_eq_mul_w5 (ratio32Mod 151) (10 * 5) w1,
          Nat.mul_comm (10 * 5) w1,
          ← pow_pow_eq_mul_w5 (ratio32Mod 151) w1 (10 * 5),
          pow_mod_eq_of_mod_eq_w5 151 (ratio32Mod 151 ^ w1) 1 (by rw [hrat1]) 50,
          Nat.one_pow]
    have h3_w1 : 3 ∣ w1 :=
      exactMultOrderMod_dvd_of_pow_eq_one 151 g50 3 w1
        (checkExactMultOrderBool_sound _ _ _ h151_32) hg50_w1
    exact (one_block_common_divisor_impossibility 3 w1 a1 (by decide) hw1 ha1 hgt h3_w1 h3_a1).2 q0 hbrox
  refine ⟨⟨hnd3, hnd7, hnd11, hnd23, hnd31, hnd151⟩, ?_⟩
  intro h331_D
  rcases one_block_cyclotomic_companion_quotient_forcing
    w1 a1 q0 331 30 11 hw1 ha1 hgt hbrox (by decide) (by decide) h331_2 h331_32 h331_D with
    ⟨_, h30_a1, h11_w1, _, _, hforce_q, hforce_x⟩
  have hcop_wa : Nat.gcd w1 a1 = 1 := one_block_exponents_coprime w1 a1 q0 hw1 ha1 hgt hbrox
  have hcop_w30 : Nat.gcd w1 30 = 1 := by
    let g := Nat.gcd w1 30
    have hg_pos : g ≥ 1 := Nat.gcd_pos_of_pos_right w1 (by decide)
    have hg_w1 : g ∣ w1 := Nat.gcd_dvd_left w1 30
    have hg_a1 : g ∣ a1 := Nat.dvd_trans (Nat.gcd_dvd_right w1 30) h30_a1
    have hg_wa : g ∣ Nat.gcd w1 a1 := Nat.dvd_gcd hg_w1 hg_a1
    rw [hcop_wa] at hg_wa
    exact Nat.eq_one_of_dvd_one hg_wa
  -- Companion multiplier `3243933 ∣ q0` and `529 ∣ (2^w1 * q0 - 1)`:
  have hall_q : ∀ q ∈ ([3, 3, 7, 11, 31, 151] : List Nat),
      q ≤ 160 ∧ checkUnitsGrid16x10 q ∧ ¬ (q ∣ D) := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨by decide, hu3, hnd3⟩
    · exact ⟨by decide, hu3, hnd3⟩
    · exact ⟨by decide, hu7, hnd7⟩
    · exact ⟨by decide, hu11, hnd11⟩
    · exact ⟨by decide, hu31, hnd31⟩
    · exact ⟨by decide, hu151, hnd151⟩
  have h324_q0 : 3243933 ∣ q0 := by
    have h2_30_eq : 2 ^ 30 = (2 ^ 15) * (2 ^ 15) := by rw [← Nat.pow_add 2 15 15]
    have hf := hforce_q [3, 3, 7, 11, 31, 151] 331 hall_q
      (by rw [hprod_q, h2_30_eq])
    rwa [hprod_q] at hf
  have hall_x : ∀ q ∈ ([23, 23] : List Nat),
      q ≤ 160 ∧ checkUnitsGrid16x10 q ∧ ¬ (q ∣ D) := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> exact ⟨by decide, hu23, hnd23⟩
  have h529_x0 : 529 ∣ (2 ^ w1 * q0 - 1) := by
    have hf := hforce_x [23, 23] 331 hall_x (by rw [hprod_x])
    rwa [hprod_x] at hf
  -- `a1 ≥ 30` first:
  have ha1_ge30 : a1 ≥ 30 := by
    rcases h30_a1 with ⟨ka, hka⟩
    cases ka with
    | zero => simp at hka; omega
    | succ _ => omega
  -- `w1 ≠ 11` because `2^(11 + a1) - 3^11 > 2^a1 - 1` for `a1 ≥ 30`:
  have hw1_ne11 : w1 ≠ 11 := by
    intro hw11
    subst hw11
    have hp2_30 : 2 ^ 30 ≤ 2 ^ a1 := pow2_mono_nat ha1_ge30
    have h2_11a : 2 ^ (11 + a1) = 2048 * 2 ^ a1 := by
      rw [Nat.pow_add 2 11 a1, show (2 : Nat) ^ 11 = 2048 from rfl]
    have h3_11 : (3 : Nat) ^ 11 = 177147 := rfl
    have h2_30_val : (2 : Nat) ^ 30 = 1073741824 := rfl
    have hD_gt : 2 ^ (11 + a1) - 3 ^ 11 > 2 ^ a1 - 1 := by
      rw [h2_11a, h3_11]; omega
    cases q0 with
    | zero =>
      rw [Nat.mul_zero] at hbrox
      have hp2a : 2 ^ a1 ≥ 2 := by simpa using pow2_mono_nat ha1
      omega
    | succ q' =>
      have hm := Nat.mul_le_mul_left (2 ^ (11 + a1) - 3 ^ 11) (by omega : 1 ≤ q' + 1)
      rw [Nat.mul_one, hbrox] at hm; omega
  -- `w1 ≥ 77` since `11 ∣ w1`, `w1 ≠ 11`, and `Nat.gcd w1 30 = 1` excludes `22, 33, 44, 55, 66`:
  have hw1_ge77 : w1 ≥ 77 := by
    rcases h11_w1 with ⟨kw, hkw⟩
    match kw with
    | 0 => simp at hkw; omega
    | 1 => exact False.elim (hw1_ne11 (by omega))
    | 2 => exfalso; rw [show w1 = 22 by omega] at hcop_w30; revert hcop_w30; decide
    | 3 => exfalso; rw [show w1 = 33 by omega] at hcop_w30; revert hcop_w30; decide
    | 4 => exfalso; rw [show w1 = 44 by omega] at hcop_w30; revert hcop_w30; decide
    | 5 => exfalso; rw [show w1 = 55 by omega] at hcop_w30; revert hcop_w30; decide
    | 6 => exfalso; rw [show w1 = 66 by omega] at hcop_w30; revert hcop_w30; decide
    | _ + 7 => omega
  -- `a1 ≥ 60` from `2^107 < 3^77` (`8^35 * 4 < 9^35 * 2187`), `w1 ≥ 77`, `3^w1 < 2^(w1 + a1)`, and `30 ∣ a1`:
  have h2_107_lt_3_77 : 2 ^ 107 < 3 ^ 77 := by
    have h8_9 : (2 ^ 3) ^ 35 ≤ (3 ^ 2) ^ 35 := nat_pow_mono_base 8 9 (by decide) 35
    rw [pow_pow_eq_mul_w5 2 3 35, pow_pow_eq_mul_w5 3 2 35] at h8_9
    have hm1 : 2 ^ (3 * 35) * 2 ^ 2 < 2 ^ (3 * 35) * 3 ^ 7 :=
      Nat.mul_lt_mul_of_pos_left (by decide : 2 ^ 2 < 3 ^ 7) (pow2_pos_nat (3 * 35))
    have hm2 : 2 ^ (3 * 35) * 3 ^ 7 ≤ 3 ^ (2 * 35) * 3 ^ 7 :=
      Nat.mul_le_mul_right (3 ^ 7) h8_9
    have hlt := Nat.lt_of_lt_of_le hm1 hm2
    rwa [← Nat.pow_add 2 (3 * 35) 2, ← Nat.pow_add 3 (2 * 35) 7] at hlt
  have ha1_ge60 : a1 ≥ 60 := by
    have hgt30 : a1 > 30 := by
      by_cases hle30 : a1 ≤ 30
      · exfalso
        have h2_le : 2 ^ (w1 + a1) ≤ 2 ^ (107 + (w1 - 77)) :=
          pow2_mono_nat (by omega)
        rw [Nat.pow_add 2 107 (w1 - 77)] at h2_le
        have h2_lt_3 : 2 ^ 107 * 2 ^ (w1 - 77) < 3 ^ 77 * 3 ^ (w1 - 77) := by
          have hm1 : 2 ^ 107 * 2 ^ (w1 - 77) < 3 ^ 77 * 2 ^ (w1 - 77) :=
            Nat.mul_lt_mul_of_pos_right h2_107_lt_3_77 (pow2_pos_nat (w1 - 77))
          have hm2 : 3 ^ 77 * 2 ^ (w1 - 77) ≤ 3 ^ 77 * 3 ^ (w1 - 77) :=
            Nat.mul_le_mul_left (3 ^ 77) (pow2_le_pow3 (w1 - 77))
          omega
        rw [← Nat.pow_add 3 77 (w1 - 77), show 77 + (w1 - 77) = w1 by omega] at h2_lt_3
        omega
      · omega
    rcases h30_a1 with ⟨ka, hka⟩
    omega
  -- `w1` is odd (since `Nat.gcd w1 30 = 1`), hence `3^w1 % 8 = 3` and `D % 8 = 5`:
  have hw1_odd : w1 % 2 = 1 := by
    by_cases hev : w1 % 2 = 0
    · exfalso
      have h2_w : 2 ∣ w1 := Nat.dvd_of_mod_eq_zero hev
      have h2_30 : 2 ∣ 30 := by decide
      have h2_g : 2 ∣ Nat.gcd w1 30 := Nat.dvd_gcd h2_w h2_30
      rw [hcop_w30] at h2_g
      omega
    · omega
  have h3w_m8 : 3 ^ w1 % 8 = 3 := by
    have hsp : w1 = 2 * ((w1 - 1) / 2) + 1 := by omega
    rw [hsp, Nat.pow_succ, ← pow9_eq_pow3_double ((w1 - 1) / 2),
        Nat.mul_mod, pow9_mod8_eq_one_w5]
  have h2K_m8 : 2 ^ (w1 + a1) % 8 = 0 := by
    have hsp : w1 + a1 = 3 + (w1 + a1 - 3) := by omega
    rw [hsp, Nat.pow_add, show (2 : Nat) ^ 3 = 8 from rfl, Nat.mul_mod_right]
  have hD_m8 : D % 8 = 5 := by
    have hsum : D + 3 ^ w1 = 2 ^ (w1 + a1) := by dsimp [D]; omega
    have hm := congrArg (· % 8) hsum
    rw [Nat.add_mod, h3w_m8, h2K_m8] at hm
    have hlt8 : D % 8 < 8 := Nat.mod_lt D (by decide)
    omega
  have hnot_prod13 : ∀ fs : List Nat,
      (∀ f ∈ fs, f % 8 = 1 ∨ f % 8 = 3) -> D ≠ natProdList fs := by
    intro fs hall heq
    have hp := prod_mod8_in_1_or_3 fs hall
    rw [← heq, hD_m8] at hp
    rcases hp with h1 | h3 <;> omega
  have hnot_331_1210 : ∀ e1 e2 : Nat, D ≠ 331 ^ e1 * 1210483 ^ e2 := by
    intro e1 e2 heq
    have hm1 := pow_mod8_in_1_or_3 331 (Or.inr h331_m8) e1
    have hm2 := pow_mod8_in_1_or_3 1210483 (Or.inr h1210_m8) e2
    have hprod_eq : 331 ^ e1 * 1210483 ^ e2 = natProdList [331 ^ e1, 1210483 ^ e2] := by
      simp [natProdList]
    rw [hprod_eq] at heq
    apply hnot_prod13 [331 ^ e1, 1210483 ^ e2] _ heq
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl
    · exact hm1
    · exact hm2
  exact ⟨h30_a1, h11_w1, hcop_w30, h324_q0, h529_x0,
         hw1_ge77, ha1_ge60, hD_m8, hnot_331_1210, hnot_prod13⟩

/--
  Theorem W8.2c' (`two_block_331_shared_mersenne_floor_99_159`, zero custom axioms):
  2-Block `p = 331` Shared-Mersenne Weight Floor (`W ≥ 99 ∧ K ≥ 159`):
  Even though `gcd(ord_331(2), ord_331(3/2)) = gcd(30, 11) = 1` (where Wave 7's `W ≥ 5 * r`
  gives only `W ≥ 5`), coupling `ord_331(2) = 30` (`30 ∣ a1 ∧ 30 ∣ a2 => a1 + a2 ≥ 60`) with
  `ord_331(3/2) = 11` (`11 ∣ W`) and the `(21, 22)` 2-block convergent band (`3 * K < 5 * W`)
  forces **`w1 + w2 ≥ 99`**, **`a1 + a2 ≥ 60`**, and **`w1 + a1 + w2 + a2 ≥ 159`** on any
  `IsPrimitiveTwoBlockBroxWitness` with `331 ∣ D` and `331 ∣ (2 ^ a1 - 1)`!
-/
theorem two_block_331_shared_mersenne_floor_99_159
    (w1 a1 w2 a2 q0 q1 : Nat)
    (hprim : IsPrimitiveTwoBlockBroxWitness w1 a1 w2 a2 q0 q1)
    (h331_D : 331 ∣ (2 ^ (w1 + a1 + w2 + a2) - 3 ^ (w1 + w2)))
    (h331_a1 : 331 ∣ (2 ^ a1 - 1)) :
    30 ∣ a1 ∧
    30 ∣ a2 ∧
    11 ∣ (w1 + w2) ∧
    (2 ^ 30 - 1) ∣ (2 ^ a1 - 1) ∧
    (2 ^ 30 - 1) ∣ (2 ^ a2 - 1) ∧
    w1 + w2 ≥ 99 ∧
    a1 + a2 ≥ 60 ∧
    w1 + a1 + w2 + a2 ≥ 159 := by
  rcases one_block_odd_order_primes_7_19_23_31_43_47_71_73_and_331_barrier with
    ⟨_, h331_2, h331_32, _⟩
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
    · have hm := Nat.mul_le_mul_left (7 ^ W) (by omega : 2 ^ K ≤ 3 ^ W); omega
  have hdvd_H0 : D ∣ broxSpiralCarry [(w1, a1), (w2, a2)] := by
    have hcar_eq : broxSpiralCarry [(w1, a1), (w2, a2)] = twoBlockBroxCarry w1 a1 w2 a2 := by
      simp [broxSpiralCarry, twoBlockBroxCarry, blockWeightSum]
    rw [hcar_eq]; exact ⟨q0, hbrox0.symm⟩
  rcases (two_block_shared_mersenne_propagation_and_equal_even_exclusion
    w1 a1 w2 a2 (by omega) ha1 hw2 ha2 hgt).1 hdvd_H0 331 (by decide) h331_D with ⟨hiff_a2, h3W2W⟩
  have h331_a2 : 331 ∣ (2 ^ a2 - 1) := hiff_a2.mp h331_a1
  have h331_diffW : 331 ∣ (3 ^ W - 2 ^ W) := h3W2W h331_a1
  have h2a1 : 2 ^ a1 % 331 = 1 := by
    rcases h331_a1 with ⟨m, hm⟩
    have hp2 : 2 ^ a1 ≥ 2 := by simpa using pow2_mono_nat ha1
    rw [show 2 ^ a1 = 1 + 331 * m by omega, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by decide)]
  have h2a2 : 2 ^ a2 % 331 = 1 := by
    rcases h331_a2 with ⟨m, hm⟩
    have hp2 : 2 ^ a2 ≥ 2 := by simpa using pow2_mono_nat ha2
    rw [show 2 ^ a2 = 1 + 331 * m by omega, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by decide)]
  have h32W : 3 ^ W % 331 = 2 ^ W % 331 := by
    rcases h331_diffW with ⟨m, hm⟩
    have h2le3 : 2 ^ W ≤ 3 ^ W := pow2_le_pow3 W
    have hrew : 3 ^ W = 2 ^ W + 331 * m := by
      generalize 3 ^ W = p3, 2 ^ W = p2 at hm h2le3 ⊢; omega
    rw [hrew, Nat.add_mul_mod_self_left]
  have h30_a1 : 30 ∣ a1 := exactMultOrderMod_dvd_of_pow_eq_one 331 2 30 a1 h331_2 h2a1
  have h30_a2 : 30 ∣ a2 := exactMultOrderMod_dvd_of_pow_eq_one 331 2 30 a2 h331_2 h2a2
  have h11_W : 11 ∣ W := exactMultOrderMod_dvd_of_pow_eq_one 331 (ratio32Mod 331) 11 W h331_32
    (ratio32Mod_pow_eq_one_of_pow3_eq_pow2 331 W (by decide) (by decide) h32W)
  have hm30_a1 : (2 ^ 30 - 1) ∣ (2 ^ a1 - 1) := by
    rcases h30_a1 with ⟨k1, hk1⟩
    have hm := pow_sub_pow_mul_dvd_w8 2 1 30 (by decide) k1
    simp only [Nat.one_pow, ← hk1] at hm; exact hm
  have hm30_a2 : (2 ^ 30 - 1) ∣ (2 ^ a2 - 1) := by
    rcases h30_a2 with ⟨k2, hk2⟩
    have hm := pow_sub_pow_mul_dvd_w8 2 1 30 (by decide) k2
    simp only [Nat.one_pow, ← hk2] at hm; exact hm
  have ha1_30 : a1 ≥ 30 := by
    rcases h30_a1 with ⟨k1, hk1⟩
    cases k1 with | zero => simp at hk1; omega | succ _ => omega
  have ha2_30 : a2 ≥ 30 := by
    rcases h30_a2 with ⟨k2, hk2⟩
    cases k2 with | zero => simp at hk2; omega | succ _ => omega
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
    · have hm := pow2_mono_nat (by omega : 5 * W ≤ K * 3); omega
  have hW_gt90 : W > 90 := by dsimp [K, W] at h3K_lt_5W ⊢; omega
  have hW_ge99 : w1 + w2 ≥ 99 := by
    change W ≥ 99
    rcases h11_W with ⟨kw, hkw⟩
    omega
  exact ⟨h30_a1, h30_a2, h11_W, hm30_a1, hm30_a2, hW_ge99, by omega, by omega⟩

-- ----------------------------------------------------------------------------
-- Pure-Integer Schneider–Laurent Binomial-Taylor Column-Extrapolation (`P3.3`)
-- ----------------------------------------------------------------------------

/-- Truncated pure-`Nat` Binomial-Taylor polynomial `∑_{t = 0}^{T - 1} binom(x, t) * B ^ t`. -/
def binomTaylorSum (x B : Nat) : Nat -> Nat
  | 0 => 0
  | T + 1 => binomTaylorSum x B T + laurentInterpBinom x T * B ^ T

theorem laurentInterpBinom_eq_zero_of_lt : ∀ (x t : Nat), x < t -> laurentInterpBinom x t = 0
  | 0, 0, h => by omega
  | 0, _ + 1, _ => rfl
  | _ + 1, 0, h => by omega
  | x + 1, t + 1, h => by
    simp only [laurentInterpBinom]
    rw [laurentInterpBinom_eq_zero_of_lt x t (by omega),
        laurentInterpBinom_eq_zero_of_lt x (t + 1) (by omega)]

theorem binomTaylorSum_succ_x_telescope (x B : Nat) :
    ∀ m : Nat,
      binomTaylorSum (x + 1) B (m + 1) + laurentInterpBinom x m * B ^ (m + 1) =
        binomTaylorSum x B (m + 1) + B * binomTaylorSum x B (m + 1)
  | 0 => by
    have hb0 : ∀ n : Nat, laurentInterpBinom n 0 = 1 := fun n => by cases n <;> rfl
    simp [binomTaylorSum, hb0]
  | m + 1 => by
    have ih := binomTaylorSum_succ_x_telescope x B m
    have hstep1 : binomTaylorSum (x + 1) B (m + 2) =
        binomTaylorSum (x + 1) B (m + 1) +
          (laurentInterpBinom x m + laurentInterpBinom x (m + 1)) * B ^ (m + 1) := by
      simp [binomTaylorSum, laurentInterpBinom]
    have hstep2 : binomTaylorSum x B (m + 2) =
        binomTaylorSum x B (m + 1) + laurentInterpBinom x (m + 1) * B ^ (m + 1) := rfl
    have hpow_m2 : laurentInterpBinom x (m + 1) * B ^ (m + 2) =
        B * (laurentInterpBinom x (m + 1) * B ^ (m + 1)) := by
      rw [Nat.pow_succ B (m + 1), ← Nat.mul_assoc (laurentInterpBinom x (m + 1)),
          Nat.mul_comm (laurentInterpBinom x (m + 1) * B ^ (m + 1)) B]
    rw [hstep1, Nat.add_mul, hstep2, Nat.mul_add B, hpow_m2]
    omega

theorem one_add_pow_eq_binomTaylorSum :
    ∀ (x B : Nat), (1 + B) ^ x = binomTaylorSum x B (x + 1)
  | 0, B => by simp [binomTaylorSum, laurentInterpBinom]
  | x + 1, B => by
    have ih := one_add_pow_eq_binomTaylorSum x B
    have htel := binomTaylorSum_succ_x_telescope x B (x + 1)
    have hz : laurentInterpBinom x (x + 1) = 0 :=
      laurentInterpBinom_eq_zero_of_lt x (x + 1) (by omega)
    have hsame : binomTaylorSum x B (x + 2) = binomTaylorSum x B (x + 1) := by
      simp [binomTaylorSum, hz]
    rw [hz, Nat.zero_mul, Nat.add_zero, hsame, ← ih] at htel
    rw [Nat.pow_succ (1 + B) x, Nat.mul_add ((1 + B) ^ x) 1 B, Nat.mul_one,
        Nat.mul_comm ((1 + B) ^ x) B, htel]

theorem binomTaylorSum_eq_of_gt (x B : Nat) :
    ∀ T : Nat, x + 1 ≤ T -> binomTaylorSum x B T = binomTaylorSum x B (x + 1)
  | 0, h => by omega
  | T + 1, h => by
    by_cases heq : T + 1 = x + 1
    · rw [heq]
    · have ih := binomTaylorSum_eq_of_gt x B T (by omega)
      have hz : laurentInterpBinom x T = 0 := laurentInterpBinom_eq_zero_of_lt x T (by omega)
      simp [binomTaylorSum, hz, ih]

theorem binomTaylorSum_diff_dvd_pow (x B T : Nat) :
    ∀ N : Nat, T ≤ N ->
      binomTaylorSum x B T ≤ binomTaylorSum x B N ∧
      (B ^ T) ∣ (binomTaylorSum x B N - binomTaylorSum x B T)
  | 0, hT0 => by
    have h0 : T = 0 := by omega
    subst h0; exact ⟨Nat.le_refl _, ⟨0, by simp⟩⟩
  | N + 1, hle => by
    by_cases heq : T = N + 1
    · subst heq; exact ⟨Nat.le_refl _, ⟨0, by simp⟩⟩
    · rcases binomTaylorSum_diff_dvd_pow x B T N (by omega) with ⟨hle_N, q1, hq1⟩
      have hnext : binomTaylorSum x B (N + 1) =
          binomTaylorSum x B N + laurentInterpBinom x N * B ^ N := rfl
      have hBN : B ^ N = B ^ T * B ^ (N - T) := by
        rw [← Nat.pow_add, show T + (N - T) = N by omega]
      refine ⟨by rw [hnext]; omega, q1 + laurentInterpBinom x N * B ^ (N - T), ?_⟩
      have hdiff : binomTaylorSum x B (N + 1) - binomTaylorSum x B T =
          (binomTaylorSum x B N - binomTaylorSum x B T) + laurentInterpBinom x N * B ^ N := by
        rw [hnext]; omega
      rw [hdiff, hq1, hBN, Nat.mul_add]
      have hassoc : laurentInterpBinom x N * (B ^ T * B ^ (N - T)) =
          B ^ T * (laurentInterpBinom x N * B ^ (N - T)) := by
        rw [← Nat.mul_assoc, Nat.mul_comm (laurentInterpBinom x N) (B ^ T), Nat.mul_assoc]
      rw [hassoc]

theorem binomTaylorSum_remainder_dvd (x B T : Nat) :
    binomTaylorSum x B T ≤ (1 + B) ^ x ∧
    (B ^ T) ∣ ((1 + B) ^ x - binomTaylorSum x B T) := by
  rw [one_add_pow_eq_binomTaylorSum x B]
  by_cases hle : T ≤ x + 1
  · exact binomTaylorSum_diff_dvd_pow x B T (x + 1) hle
  · rw [binomTaylorSum_eq_of_gt x B T (by omega)]
    exact ⟨Nat.le_refl _, ⟨0, by simp⟩⟩

-- Column operations on `intDet L` (zero custom axioms):

theorem intSumPrefix_congr_w8 (L : Nat) (f g : Fin L -> Int) (hfg : ∀ j : Fin L, f j = g j) :
    ∀ k : Nat, intSumPrefix L f k = intSumPrefix L g k
  | 0 => rfl
  | k + 1 => by
    simp only [intSumPrefix, intSumPrefix_congr_w8 L f g hfg k]
    by_cases hk : k < L
    · simp [hk, hfg ⟨k, hk⟩]
    · simp [hk]

theorem intSumPrefix_dvd_all_w8 (d : Int) (L : Nat) (f : Fin L -> Int)
    (hdvd : ∀ j : Fin L, d ∣ f j) :
    ∀ k : Nat, d ∣ intSumPrefix L f k
  | 0 => ⟨0, by simp [intSumPrefix]⟩
  | k + 1 => by
    rcases intSumPrefix_dvd_all_w8 d L f hdvd k with ⟨q1, hq1⟩
    simp only [intSumPrefix]
    by_cases hk : k < L
    · simp only [hk, dite_true]
      rcases hdvd ⟨k, hk⟩ with ⟨q2, hq2⟩
      exact ⟨q1 + q2, by rw [hq1, hq2, Int.mul_add]⟩
    · simp only [hk, dite_false, Int.add_zero]
      exact ⟨q1, hq1⟩

theorem intSumPrefix_linear_w8 (coef : Int) (L : Nat) (f g : Fin L -> Int) :
    ∀ k : Nat,
      intSumPrefix L (fun j => f j + coef * g j) k =
        intSumPrefix L f k + coef * intSumPrefix L g k
  | 0 => by simp [intSumPrefix]
  | k + 1 => by
    simp only [intSumPrefix, intSumPrefix_linear_w8 coef L f g k]
    by_cases hk : k < L
    · simp only [hk, dite_true, Int.mul_add]; omega
    · simp only [hk, dite_false, Int.add_zero]

theorem intSumPrefix_zero_w8 (L : Nat) :
    ∀ k : Nat, intSumPrefix L (fun _ => (0 : Int)) k = 0
  | 0 => rfl
  | k + 1 => by
    simp only [intSumPrefix, intSumPrefix_zero_w8 L k]
    by_cases hk : k < L <;> simp [hk]

theorem intSumPrefix_pair_cancel_w8 (L : Nat) (c : Nat) (hc : c + 1 < L)
    (f : Fin L -> Int)
    (hz : ∀ j : Fin L, j.val ≠ c -> j.val ≠ c + 1 -> f j = 0)
    (hopp : f ⟨c, by omega⟩ + f ⟨c + 1, hc⟩ = 0) :
    ∀ k : Nat,
      intSumPrefix L f k =
        if k = c + 1 then f ⟨c, by omega⟩ else 0
  | 0 => by simp [intSumPrefix]
  | k + 1 => by
    have ih := intSumPrefix_pair_cancel_w8 L c hc f hz hopp k
    simp only [intSumPrefix, ih]
    by_cases hk : k < L
    · simp only [hk, dite_true]
      by_cases hkc : k = c
      · subst hkc
        have h1 : ¬ (k = k + 1) := by omega
        simp only [h1, ite_false, ite_true, Int.zero_add]
      · by_cases hkc1 : k = c + 1
        · subst hkc1
          have h1 : ¬ (c + 1 + 1 = c + 1) := by omega
          simp only [ite_true, h1, ite_false]
          exact hopp
        · have h2 : ¬ (k + 1 = c + 1) := by omega
          simp only [hkc1, h2, ite_false, hz ⟨k, hk⟩ hkc hkc1, Int.add_zero]
    · have h1 : ¬ (k = c + 1) := by omega
      have h2 : ¬ (k + 1 = c + 1) := by omega
      simp only [hk, dite_false, h1, h2, ite_false, Int.add_zero]

def unskipFinIdx {L : Nat} (j c0 : Fin (L + 1)) (hne : j ≠ c0) : Fin L :=
  if hlt : c0.val < j.val then
    ⟨c0.val, by omega⟩
  else
    have hgt : j.val < c0.val := by
      have hval_ne : j.val ≠ c0.val := fun hv => hne (Fin.ext hv)
      omega
    ⟨c0.val - 1, by omega⟩

theorem skipFinIdx_unskip {L : Nat} (j c0 : Fin (L + 1)) (hne : j ≠ c0) :
    skipFinIdx j (unskipFinIdx j c0 hne) = c0 := by
  unfold unskipFinIdx skipFinIdx
  by_cases hlt : c0.val < j.val
  · simp [hlt]
  · have hval_ne : j.val ≠ c0.val := fun hv => hne (Fin.ext hv)
    have hnl : ¬ (c0.val - 1 < j.val) := by omega
    simp only [hlt, dite_false, hnl, ite_false]
    have hv_eq : c0.val - 1 + 1 = c0.val := by omega
    exact Fin.ext hv_eq

theorem skipFinIdx_ne_self {L : Nat} (j : Fin (L + 1)) (c : Fin L) :
    skipFinIdx j c ≠ j := by
  unfold skipFinIdx
  intro heq
  have hv := congrArg Fin.val heq
  by_cases hlt : c.val < j.val <;> simp [hlt] at hv <;> omega

theorem skipFinIdx_inj {L : Nat} (j : Fin (L + 1)) (c1 c2 : Fin L)
    (heq : skipFinIdx j c1 = skipFinIdx j c2) : c1 = c2 := by
  unfold skipFinIdx at heq
  have hv := congrArg Fin.val heq
  by_cases h1 : c1.val < j.val <;> by_cases h2 : c2.val < j.val <;>
    simp [h1, h2] at hv <;> exact Fin.ext (by omega)

theorem intDet_congr_w8 :
    ∀ (L : Nat) (A B : Fin L -> Fin L -> Int),
      (∀ i j : Fin L, A i j = B i j) -> intDet L A = intDet L B
  | 0, _, _, _ => rfl
  | L + 1, A, B, hAB => by
    simp only [intDet]
    unfold intSumFin
    apply intSumPrefix_congr_w8 (L + 1)
    intro j
    rw [hAB ⟨0, Nat.zero_lt_succ L⟩ j,
        intDet_congr_w8 L (intSubMat A j) (intSubMat B j)
          (fun r c => hAB ⟨r.val + 1, by omega⟩ (skipFinIdx j c))]

theorem intDet_col_dvd (d : Int) :
    ∀ (L : Nat) (c0 : Fin L) (A : Fin L -> Fin L -> Int),
      (∀ i : Fin L, d ∣ A i c0) ->
      d ∣ intDet L A
  | 0, c0, _, _ => Fin.elim0 c0
  | L + 1, c0, A, hcol => by
    simp only [intDet]
    unfold intSumFin
    apply intSumPrefix_dvd_all_w8 d (L + 1)
    intro j
    let sgn : Int := if j.val % 2 = 0 then 1 else -1
    by_cases hj : j = c0
    · subst hj
      rcases hcol ⟨0, Nat.zero_lt_succ L⟩ with ⟨q, hq⟩
      refine ⟨sgn * q * intDet L (intSubMat A j), ?_⟩
      change sgn * A ⟨0, Nat.zero_lt_succ L⟩ j * intDet L (intSubMat A j) = _
      rw [hq]
      calc
        sgn * (d * q) * intDet L (intSubMat A j)
            = (sgn * d * q) * intDet L (intSubMat A j) := by rw [Int.mul_assoc sgn d q]
        _ = (d * sgn * q) * intDet L (intSubMat A j) := by rw [Int.mul_comm sgn d]
        _ = d * (sgn * q * intDet L (intSubMat A j)) := by
              rw [Int.mul_assoc d sgn q, Int.mul_assoc d (sgn * q)]
    · let c' := unskipFinIdx j c0 hj
      have hsub_col : ∀ r : Fin L, d ∣ intSubMat A j r c' := by
        intro r
        unfold intSubMat
        rw [skipFinIdx_unskip j c0 hj]
        exact hcol ⟨r.val + 1, by omega⟩
      rcases intDet_col_dvd d L c' (intSubMat A j) hsub_col with ⟨q, hq⟩
      refine ⟨sgn * A ⟨0, Nat.zero_lt_succ L⟩ j * q, ?_⟩
      change sgn * A ⟨0, Nat.zero_lt_succ L⟩ j * intDet L (intSubMat A j) = _
      rw [hq, ← Int.mul_assoc, Int.mul_comm (sgn * A ⟨0, Nat.zero_lt_succ L⟩ j) d, Int.mul_assoc]

theorem intDet_col_linear (coef : Int) :
    ∀ (L : Nat) (c0 : Fin L) (A B C : Fin L -> Fin L -> Int),
      (∀ i j : Fin L, j ≠ c0 -> A i j = B i j ∧ C i j = B i j) ->
      (∀ i : Fin L, A i c0 = B i c0 + coef * C i c0) ->
      intDet L A = intDet L B + coef * intDet L C
  | 0, c0, _, _, _, _, _ => Fin.elim0 c0
  | L + 1, c0, A, B, C, hother, hcol => by
    simp only [intDet]
    unfold intSumFin
    rw [← intSumPrefix_linear_w8 coef (L + 1)]
    apply intSumPrefix_congr_w8 (L + 1)
    intro j
    let sgn : Int := if j.val % 2 = 0 then 1 else -1
    by_cases hj : j = c0
    · subst hj
      have hdAB : intDet L (intSubMat A j) = intDet L (intSubMat B j) :=
        intDet_congr_w8 L _ _ (fun r c => (hother ⟨r.val + 1, by omega⟩ (skipFinIdx j c)
          (skipFinIdx_ne_self j c)).1)
      have hdCB : intDet L (intSubMat C j) = intDet L (intSubMat B j) :=
        intDet_congr_w8 L _ _ (fun r c => (hother ⟨r.val + 1, by omega⟩ (skipFinIdx j c)
          (skipFinIdx_ne_self j c)).2)
      change sgn * A ⟨0, Nat.zero_lt_succ L⟩ j * intDet L (intSubMat A j) =
        sgn * B ⟨0, Nat.zero_lt_succ L⟩ j * intDet L (intSubMat B j) +
          coef * (sgn * C ⟨0, Nat.zero_lt_succ L⟩ j * intDet L (intSubMat C j))
      rw [hdAB, hdCB, hcol ⟨0, Nat.zero_lt_succ L⟩,
          Int.mul_add sgn, Int.add_mul]
      have hcomm : sgn * (coef * C ⟨0, Nat.zero_lt_succ L⟩ j) * intDet L (intSubMat B j) =
          coef * (sgn * C ⟨0, Nat.zero_lt_succ L⟩ j * intDet L (intSubMat B j)) := by
        rw [← Int.mul_assoc sgn coef, Int.mul_comm sgn coef,
            Int.mul_assoc coef sgn, Int.mul_assoc coef]
      rw [hcomm]
    · rcases hother ⟨0, Nat.zero_lt_succ L⟩ j hj with ⟨hA0, hC0⟩
      let c' := unskipFinIdx j c0 hj
      have hother' : ∀ r c : Fin L, c ≠ c' ->
          intSubMat A j r c = intSubMat B j r c ∧ intSubMat C j r c = intSubMat B j r c := by
        intro r c hc_ne
        apply hother ⟨r.val + 1, by omega⟩ (skipFinIdx j c)
        intro hsk_eq
        apply hc_ne
        exact skipFinIdx_inj j c c' (hsk_eq.trans (skipFinIdx_unskip j c0 hj).symm)
      have hcol' : ∀ r : Fin L,
          intSubMat A j r c' = intSubMat B j r c' + coef * intSubMat C j r c' := by
        intro r
        unfold intSubMat
        rw [skipFinIdx_unskip j c0 hj]
        exact hcol ⟨r.val + 1, by omega⟩
      have ih := intDet_col_linear coef L c' (intSubMat A j) (intSubMat B j) (intSubMat C j)
        hother' hcol'
      change sgn * A ⟨0, Nat.zero_lt_succ L⟩ j * intDet L (intSubMat A j) =
        sgn * B ⟨0, Nat.zero_lt_succ L⟩ j * intDet L (intSubMat B j) +
          coef * (sgn * C ⟨0, Nat.zero_lt_succ L⟩ j * intDet L (intSubMat C j))
      rw [hA0, hC0, ih, Int.mul_add]
      have hcomm : (sgn * B ⟨0, Nat.zero_lt_succ L⟩ j) * (coef * intDet L (intSubMat C j)) =
          coef * (sgn * B ⟨0, Nat.zero_lt_succ L⟩ j * intDet L (intSubMat C j)) := by
        rw [← Int.mul_assoc, Int.mul_comm (sgn * B ⟨0, Nat.zero_lt_succ L⟩ j) coef, Int.mul_assoc]
      rw [hcomm]

theorem intDet_adj_cols_eq_zero :
    ∀ (L c : Nat) (hc : c + 1 < L) (A : Fin L -> Fin L -> Int),
      (∀ i : Fin L, A i ⟨c, by omega⟩ = A i ⟨c + 1, hc⟩) ->
      intDet L A = 0
  | 0, _, hc, _, _ => by omega
  | 1, _, hc, _, _ => by omega
  | L + 2, c, hc, A, hadj => by
    simp only [intDet]
    unfold intSumFin
    let term : Fin (L + 2) -> Int := fun j =>
      (if j.val % 2 = 0 then (1 : Int) else -1) *
        A ⟨0, Nat.zero_lt_succ (L + 1)⟩ j * intDet (L + 1) (intSubMat A j)
    have hz : ∀ j : Fin (L + 2), j.val ≠ c -> j.val ≠ c + 1 -> term j = 0 := by
      intro j hjc hjc1
      by_cases hlt : j.val < c
      · have hc_pos : c ≥ 1 := by omega
        have hc' : (c - 1) + 1 < L + 1 := by omega
        have hadj_sub : ∀ r : Fin (L + 1),
            intSubMat A j r ⟨c - 1, by omega⟩ = intSubMat A j r ⟨(c - 1) + 1, hc'⟩ := by
          intro r
          unfold intSubMat skipFinIdx
          have hnl1 : ¬ (c - 1 < j.val) := by omega
          have hnl2 : ¬ ((c - 1) + 1 < j.val) := by omega
          simp only [hnl1, hnl2, ite_false]
          have harg1 : A ⟨r.val + 1, by omega⟩ ⟨c - 1 + 1, by omega⟩ =
              A ⟨r.val + 1, by omega⟩ ⟨c, by omega⟩ :=
            congrArg (A ⟨r.val + 1, by omega⟩) (Fin.ext (by dsimp only; omega))
          have harg2 : A ⟨r.val + 1, by omega⟩ ⟨(c - 1) + 1 + 1, by omega⟩ =
              A ⟨r.val + 1, by omega⟩ ⟨c + 1, hc⟩ :=
            congrArg (A ⟨r.val + 1, by omega⟩) (Fin.ext (by dsimp only; omega))
          exact harg1.trans ((hadj ⟨r.val + 1, by omega⟩).trans harg2.symm)
        have hd0 := intDet_adj_cols_eq_zero (L + 1) (c - 1) hc' (intSubMat A j) hadj_sub
        dsimp [term]; rw [hd0, Int.mul_zero]
      · have hgt : c + 1 < j.val := by omega
        have hc' : c + 1 < L + 1 := by omega
        have hadj_sub : ∀ r : Fin (L + 1),
            intSubMat A j r ⟨c, by omega⟩ = intSubMat A j r ⟨c + 1, hc'⟩ := by
          intro r
          unfold intSubMat skipFinIdx
          have hl1 : c < j.val := by omega
          simp only [hl1, hgt, ite_true]
          exact hadj ⟨r.val + 1, by omega⟩
        have hd0 := intDet_adj_cols_eq_zero (L + 1) c hc' (intSubMat A j) hadj_sub
        dsimp [term]; rw [hd0, Int.mul_zero]
    have hsub_eq : intDet (L + 1) (intSubMat A ⟨c, by omega⟩) =
        intDet (L + 1) (intSubMat A ⟨c + 1, hc⟩) := by
      apply intDet_congr_w8 (L + 1)
      intro r k
      unfold intSubMat skipFinIdx
      by_cases hkc : k.val < c
      · have hkc1 : k.val < c + 1 := by omega
        simp [hkc, hkc1]
      · by_cases heq : k.val = c
        · have hkc1 : k.val < c + 1 := by omega
          simp only [hkc, ite_false, hkc1, ite_true]
          have harg1 : A ⟨r.val + 1, by omega⟩ ⟨k.val + 1, by omega⟩ =
              A ⟨r.val + 1, by omega⟩ ⟨c + 1, hc⟩ :=
            congrArg (A ⟨r.val + 1, by omega⟩) (Fin.ext (by dsimp only; omega))
          have harg2 : A ⟨r.val + 1, by omega⟩ ⟨k.val, by omega⟩ =
              A ⟨r.val + 1, by omega⟩ ⟨c, by omega⟩ :=
            congrArg (A ⟨r.val + 1, by omega⟩) (Fin.ext heq)
          exact harg1.trans ((hadj ⟨r.val + 1, by omega⟩).symm.trans harg2.symm)
        · have hnk1 : ¬ (k.val < c + 1) := by omega
          simp [hkc, hnk1]
    have hopp : term ⟨c, by omega⟩ + term ⟨c + 1, hc⟩ = 0 := by
      have ha0 := hadj ⟨0, Nat.zero_lt_succ (L + 1)⟩
      change (if c % 2 = 0 then (1 : Int) else -1) *
          A ⟨0, Nat.zero_lt_succ (L + 1)⟩ ⟨c, by omega⟩ * intDet (L + 1) (intSubMat A ⟨c, by omega⟩) +
        (if (c + 1) % 2 = 0 then (1 : Int) else -1) *
          A ⟨0, Nat.zero_lt_succ (L + 1)⟩ ⟨c + 1, hc⟩ * intDet (L + 1) (intSubMat A ⟨c + 1, hc⟩) = 0
      rw [ha0, hsub_eq]
      have hpm : ∀ z1 z2 : Int, (1 : Int) * z1 * z2 + (-1 : Int) * z1 * z2 = 0 ∧
          (-1 : Int) * z1 * z2 + (1 : Int) * z1 * z2 = 0 := by
        intro z1 z2
        rw [Int.mul_assoc (1 : Int), Int.mul_assoc (-1 : Int)]; constructor <;> omega
      by_cases hpar : c % 2 = 0
      · have hpar1 : ¬ ((c + 1) % 2 = 0) := by omega
        simp only [hpar, hpar1, ite_true, ite_false]
        exact (hpm _ _).1
      · have hpar1 : (c + 1) % 2 = 0 := by omega
        simp only [hpar, hpar1, ite_true, ite_false]
        exact (hpm _ _).2
    have hsum := intSumPrefix_pair_cancel_w8 (L + 2) c hc term hz hopp (L + 2)
    have hne_end : ¬ (L + 2 = c + 1) := by omega
    simp only [hne_end, ite_false] at hsum
    exact hsum

def swapAdjCols {L : Nat} (c : Nat) (hc : c + 1 < L) (A : Fin L -> Fin L -> Int) :
    Fin L -> Fin L -> Int :=
  fun i j =>
    if j.val = c then A i ⟨c + 1, hc⟩
    else if j.val = c + 1 then A i ⟨c, by omega⟩
    else A i j

theorem intDet_swap_adj_cols (L c : Nat) (hc : c + 1 < L) (A : Fin L -> Fin L -> Int) :
    intDet L (swapAdjCols c hc A) = - intDet L A := by
  let c0 : Fin L := ⟨c, by omega⟩
  let c1 : Fin L := ⟨c + 1, hc⟩
  let setTwo : (Fin L -> Int) -> (Fin L -> Int) -> Fin L -> Fin L -> Int :=
    fun u v i j => if j.val = c then u i else if j.val = c + 1 then v i else A i j
  let x : Fin L -> Int := fun i => A i c0
  let y : Fin L -> Int := fun i => A i c1
  let xy : Fin L -> Int := fun i => x i + y i
  have hnc1 : ¬ (c + 1 = c) := by omega
  have hzero_diag : ∀ u : Fin L -> Int, intDet L (setTwo u u) = 0 := by
    intro u
    apply intDet_adj_cols_eq_zero L c hc
    intro i
    change (if c = c then u i else if c = c + 1 then u i else A i ⟨c, by omega⟩) =
      (if c + 1 = c then u i else if c + 1 = c + 1 then u i else A i ⟨c + 1, hc⟩)
    simp only [hnc1, ite_true, ite_false]
  have hlin0 : ∀ v : Fin L -> Int,
      intDet L (setTwo xy v) = intDet L (setTwo x v) + 1 * intDet L (setTwo y v) := by
    intro v
    apply intDet_col_linear 1 L c0 (setTwo xy v) (setTwo x v) (setTwo y v)
    · intro i j hj
      have hjv : j.val ≠ c := fun h => hj (Fin.ext h)
      dsimp [setTwo]; simp [hjv]
    · intro i
      dsimp [setTwo, c0, xy]; simp [Int.one_mul]
  have hlin1 : ∀ u : Fin L -> Int,
      intDet L (setTwo u xy) = intDet L (setTwo u x) + 1 * intDet L (setTwo u y) := by
    intro u
    apply intDet_col_linear 1 L c1 (setTwo u xy) (setTwo u x) (setTwo u y)
    · intro i j hj
      have hjv : j.val ≠ c + 1 := fun h => hj (Fin.ext h)
      dsimp [setTwo]
      by_cases hjc : j.val = c <;> simp [hjc, hjv]
    · intro i
      change (if c + 1 = c then u i else if c + 1 = c + 1 then xy i else A i c1) =
        (if c + 1 = c then u i else if c + 1 = c + 1 then x i else A i c1) +
          1 * (if c + 1 = c then u i else if c + 1 = c + 1 then y i else A i c1)
      simp only [hnc1, ite_true, ite_false, Int.one_mul]
      rfl
  have hsum0 : intDet L (setTwo xy xy) = 0 := hzero_diag xy
  rw [hlin0 xy, Int.one_mul, hlin1 x, hlin1 y, Int.one_mul, Int.one_mul,
      hzero_diag x, hzero_diag y] at hsum0
  have heqA : intDet L (setTwo x y) = intDet L A := by
    apply intDet_congr_w8 L
    intro i j
    change (if j.val = c then A i ⟨c, by omega⟩
            else if j.val = c + 1 then A i ⟨c + 1, hc⟩
            else A i j) = A i j
    by_cases hjc : j.val = c
    · simp only [hjc, ite_true]
      exact congrArg (A i) (Fin.ext hjc.symm)
    · simp only [hjc, ite_false]
      by_cases hjc1 : j.val = c + 1
      · simp only [hjc1, ite_true]
        exact congrArg (A i) (Fin.ext hjc1.symm)
      · simp only [hjc1, ite_false]
  have heqSwap : intDet L (setTwo y x) = intDet L (swapAdjCols c hc A) := by
    apply intDet_congr_w8 L
    intro i j
    dsimp [setTwo, swapAdjCols, x, y, c0, c1]
  rw [heqA, heqSwap] at hsum0
  omega

theorem intDet_eq_cols_zero_of_lt (L : Nat) :
    ∀ (gap c1 c2 : Nat) (hc1 : c1 < L) (hc2 : c2 < L),
      c1 < c2 -> c2 - c1 = gap ->
      ∀ (A : Fin L -> Fin L -> Int),
        (∀ i : Fin L, A i ⟨c1, hc1⟩ = A i ⟨c2, hc2⟩) ->
        intDet L A = 0
  | 0, _, _, _, _, hlt, hgap, _, _ => by omega
  | 1, c1, c2, _, hc2, hlt, hgap, A, heq => by
    have hc2_eq : c2 = c1 + 1 := by omega
    subst hc2_eq
    exact intDet_adj_cols_eq_zero L c1 hc2 A heq
  | m + 2, c1, c2, hc1, hc2, hlt, hgap, A, heq => by
    have hc_adj : (c2 - 1) + 1 < L := by omega
    let A' := swapAdjCols (c2 - 1) hc_adj A
    have hswap := intDet_swap_adj_cols L (c2 - 1) hc_adj A
    have heq' : ∀ i : Fin L, A' i ⟨c1, hc1⟩ = A' i ⟨c2 - 1, by omega⟩ := by
      intro i
      dsimp [A', swapAdjCols]
      have h1 : ¬ (c1 = c2 - 1) := by omega
      have h2 : ¬ (c1 = (c2 - 1) + 1) := by omega
      simp only [h1, h2, ite_true, ite_false]
      have hf : (⟨(c2 - 1) + 1, hc_adj⟩ : Fin L) = ⟨c2, hc2⟩ := Fin.ext (by dsimp only; omega)
      rw [hf]
      exact heq i
    have hz' := intDet_eq_cols_zero_of_lt L (m + 1) c1 (c2 - 1) hc1 (by omega)
      (by omega) (by omega) A' heq'
    change intDet L A' = - intDet L A at hswap
    omega

theorem intDet_eq_cols_zero (L : Nat) (c1 c2 : Fin L) (hne : c1 ≠ c2)
    (A : Fin L -> Fin L -> Int)
    (heq : ∀ i : Fin L, A i c1 = A i c2) :
    intDet L A = 0 := by
  have hvne : c1.val ≠ c2.val := fun h => hne (Fin.ext h)
  by_cases hlt : c1.val < c2.val
  · exact intDet_eq_cols_zero_of_lt L (c2.val - c1.val) c1.val c2.val c1.isLt c2.isLt
      hlt rfl A heq
  · exact intDet_eq_cols_zero_of_lt L (c1.val - c2.val) c2.val c1.val c2.isLt c1.isLt
      (by omega) rfl A (fun i => (heq i).symm)

theorem intDet_sub_col_mul_other (L : Nat) (c0 ct : Fin L) (hne : ct ≠ c0) (coef : Int)
    (A : Fin L -> Fin L -> Int) :
    intDet L (fun i j => if j = c0 then A i c0 - coef * A i ct else A i j) = intDet L A := by
  let A' : Fin L -> Fin L -> Int := fun i j => if j = c0 then A i c0 - coef * A i ct else A i j
  let C : Fin L -> Fin L -> Int := fun i j => if j = c0 then A i ct else A i j
  have hlin := intDet_col_linear (- coef) L c0 A' A C
    (fun i j hj => by dsimp [A', C]; simp [hj])
    (fun i => by dsimp [A', C]; simp only [ite_true]; rw [Int.neg_mul, Int.sub_eq_add_neg])
  have hC0 : intDet L C = 0 := by
    apply intDet_eq_cols_zero L ct c0 hne C
    intro i
    dsimp [C]
    simp [hne]
  rw [hC0, Int.mul_zero, Int.add_zero] at hlin
  exact hlin

def colPrefixComb {L : Nat} (A : Fin L -> Fin L -> Int)
    (idx : Nat -> Fin L) (coef : Nat -> Int) (i : Fin L) : Nat -> Int
  | 0 => 0
  | t + 1 => colPrefixComb A idx coef i t + coef t * A i (idx t)

theorem intDet_sub_col_prefix_invariant (L : Nat) (c0 : Fin L)
    (A : Fin L -> Fin L -> Int) :
    ∀ (T : Nat) (idx : Nat -> Fin L) (coef : Nat -> Int),
      (∀ t : Nat, t < T -> idx t ≠ c0) ->
      intDet L A =
        intDet L (fun i j =>
          if j = c0 then A i c0 - colPrefixComb A idx coef i T else A i j)
  | 0, _, _, _ => by
    apply intDet_congr_w8 L
    intro i j
    by_cases hj : j = c0 <;> simp [hj, colPrefixComb]
  | T + 1, idx, coef, hne_all => by
    have ih := intDet_sub_col_prefix_invariant L c0 A T idx coef
      (fun t ht => hne_all t (by omega))
    let A_T : Fin L -> Fin L -> Int := fun i j =>
      if j = c0 then A i c0 - colPrefixComb A idx coef i T else A i j
    have hstep := intDet_sub_col_mul_other L c0 (idx T) (hne_all T (by omega)) (coef T) A_T
    rw [ih]
    refine hstep.symm.trans (intDet_congr_w8 L _ _ ?_)
    intro i j
    by_cases hj : j = c0
    · subst hj
      have hidx_ne : idx T ≠ j := hne_all T (by omega)
      dsimp [A_T, colPrefixComb]
      simp only [ite_true, hidx_ne, ite_false]
      omega
    · dsimp [A_T]; simp [hj]

theorem intDet_three (A : Fin 3 -> Fin 3 -> Int) :
    intDet 3 A =
      A ⟨0, by decide⟩ ⟨0, by decide⟩ *
        (A ⟨1, by decide⟩ ⟨1, by decide⟩ * A ⟨2, by decide⟩ ⟨2, by decide⟩ -
         A ⟨1, by decide⟩ ⟨2, by decide⟩ * A ⟨2, by decide⟩ ⟨1, by decide⟩) -
      A ⟨0, by decide⟩ ⟨1, by decide⟩ *
        (A ⟨1, by decide⟩ ⟨0, by decide⟩ * A ⟨2, by decide⟩ ⟨2, by decide⟩ -
         A ⟨1, by decide⟩ ⟨2, by decide⟩ * A ⟨2, by decide⟩ ⟨0, by decide⟩) +
      A ⟨0, by decide⟩ ⟨2, by decide⟩ *
        (A ⟨1, by decide⟩ ⟨0, by decide⟩ * A ⟨2, by decide⟩ ⟨1, by decide⟩ -
         A ⟨1, by decide⟩ ⟨1, by decide⟩ * A ⟨2, by decide⟩ ⟨0, by decide⟩) := by
  conv => lhs; unfold intDet
  simp only [intSumFin, intSumPrefix,
    show (0 : Nat) < 3 by decide, show (1 : Nat) < 3 by decide,
    show (2 : Nat) < 3 by decide, dite_true,
    show ¬ ((1 : Nat) % 2 = 0) by decide, ite_true, ite_false]
  rw [intDet_two (intSubMat A ⟨0, by decide⟩),
      intDet_two (intSubMat A ⟨1, by decide⟩),
      intDet_two (intSubMat A ⟨2, by decide⟩)]
  simp only [intSubMat, skipFinIdx,
    show ¬ ((0 : Nat) < 0) by decide, show ¬ ((1 : Nat) < 0) by decide,
    show (0 : Nat) < 1 by decide, show ¬ ((1 : Nat) < 1) by decide,
    show (0 : Nat) < 2 by decide, show (1 : Nat) < 2 by decide,
    ite_true, ite_false, Int.zero_add, Int.one_mul]
  have hneg : ∀ x y : Int, (-1 : Int) * x * y = -(x * y) := by
    intro x y; rw [Int.mul_assoc (-1 : Int)]; omega
  rw [hneg]
  have hring3 : ∀ a00 a01 a02 a10 a11 a12 a20 a21 a22 : Int,
      a00 * (a11 * a22 - a12 * a21) + -(a01 * (a10 * a22 - a12 * a20)) +
        a02 * (a10 * a21 - a11 * a20) =
      a00 * (a11 * a22 - a12 * a21) - a01 * (a10 * a22 - a12 * a20) +
        a02 * (a10 * a21 - a11 * a20) := by
    intro _ _ _ _ _ _ _ _ _; omega
  exact hring3 _ _ _ _ _ _ _ _ _

/--
  Theorem W8.2d (`laurent_binomial_taylor_column_extrapolation_dvd`, zero custom axioms):
  Pure-Integer Schneider–Laurent Binomial-Taylor Column-Extrapolation (`U -> U_1`):
  1. **Universal `L x L` Zero-Gap Column-Extrapolation Divisibility**:
     For ANY `W K L T u : Nat` (`u ≥ 1`), ANY `rows cols : Fin L -> Nat × Nat`, ANY polynomial
     column indices `idx : Nat -> Fin L` (`∀ t < T, cols (idx t) = (t, 0)`), and ANY exponential
     column `c0 : Fin L` (`cols c0 = (0, u)`), subtracting the first `T` Binomial-Taylor polynomial
     columns leaves `intDet L M0` invariant while making column `c0` entrywise divisible by
     `(2 ^ u - 1) ^ T`, hence:
       `(((2 ^ u - 1) ^ T : Nat) : Int) ∣ intDet L M0`!
     Combined with `W7.1b`, for `3 ^ W < 2 ^ K`, `((2 ^ K - 3 ^ W : Nat) : Int) ∣ (intDet L M0 - intDet L MW)`
     while `intDet L M0` carries the exact Taylor vanishing factor `(2 ^ u - 1) ^ T`!
  2. **Closed-Form `3 x 3` `T = 2` Derivative-Extrapolated Non-Vanishing & Resonant Splitting**:
     - On `rows = [(0, 0), (1, 0), (2, 0)]` and `cols = [(0, 0), (1, 0), (0, u)]` (`W ≥ 1, u ≥ 1`),
       `intDet 3 (laurentInterpMat W K 3 rows cols) = ((W * (2 ^ u - 1) ^ 2 : Nat) : Int) > 0`
       AND for the `W`-dilated zero-gap matrix `M0` (`cols_W = [(0, 0), (1, 0), (0, W * u)]`),
       `intDet 3 M0 = ((W * (2 ^ (W * u) - 1) ^ 2 : Nat) : Int) > 0`!
     - On resonant `rows = [(0, 0), (0, W), (K, 0)]` and `W`-dilated `cols_W = [(0, 0), (1, 0), (0, W * u)]`
       (`W ≥ 1, K ≥ 1, u ≥ 1, 3 ^ W < 2 ^ K`), the zero-gap determinant `intDet 3 M0` vanishes
       identically (`= 0`), whereas the true `W`-dilated Schneider–Laurent determinant equals
       `((W * K * ((2 ^ K) ^ (W * u) - (3 ^ W) ^ (W * u)) : Nat) : Int) > 0`!
-/
theorem laurent_binomial_taylor_column_extrapolation_dvd :
    (∀ (W K L T u : Nat) (rows cols : Fin L -> Nat × Nat)
       (idx : Nat -> Fin L) (c0 : Fin L),
      u ≥ 1 ->
      (∀ t : Nat, t < T -> cols (idx t) = (t, 0)) ->
      cols c0 = (0, u) ->
      let M0 : Fin L -> Fin L -> Int := fun i j =>
        (laurentZeroGapIntEntry W K (rows i).1 (rows i).2 (cols j).1 (cols j).2 : Int)
      (((2 ^ u - 1) ^ T : Nat) : Int) ∣ intDet L M0) ∧
    (∀ (W K u : Nat), W ≥ 1 -> u ≥ 1 ->
      let rows : Fin 3 -> Nat × Nat := fun i =>
        if i.val = 0 then (0, 0) else if i.val = 1 then (1, 0) else (2, 0)
      let cols : Fin 3 -> Nat × Nat := fun j =>
        if j.val = 0 then (0, 0) else if j.val = 1 then (1, 0) else (0, u)
      let M0 : Fin 3 -> Fin 3 -> Int := fun i j =>
        (laurentZeroGapIntEntry W K (rows i).1 (rows i).2 (cols j).1 (cols j).2 : Int)
      intDet 3 (laurentInterpMat W K 3 rows cols) =
        ((W * (2 ^ u - 1) ^ 2 : Nat) : Int) ∧
      intDet 3 (laurentInterpMat W K 3 rows cols) > 0 ∧
      intDet 3 M0 = ((W * (2 ^ (W * u) - 1) ^ 2 : Nat) : Int) ∧
      intDet 3 M0 > 0) ∧
    (∀ (W K u : Nat), W ≥ 1 -> K ≥ 1 -> u ≥ 1 -> 3 ^ W < 2 ^ K ->
      let rows : Fin 3 -> Nat × Nat := fun i =>
        if i.val = 0 then (0, 0) else if i.val = 1 then (0, W) else (K, 0)
      let cols0 : Fin 3 -> Nat × Nat := fun j =>
        if j.val = 0 then (0, 0) else if j.val = 1 then (1, 0) else (0, u)
      let colsW : Fin 3 -> Nat × Nat := fun j =>
        if j.val = 0 then (0, 0) else if j.val = 1 then (1, 0) else (0, W * u)
      let M0 : Fin 3 -> Fin 3 -> Int := fun i j =>
        (laurentZeroGapIntEntry W K (rows i).1 (rows i).2 (cols0 j).1 (cols0 j).2 : Int)
      intDet 3 M0 = 0 ∧
      intDet 3 (laurentInterpMat W K 3 rows colsW) =
        ((W * K * ((2 ^ K) ^ (W * u) - (3 ^ W) ^ (W * u)) : Nat) : Int) ∧
      intDet 3 (laurentInterpMat W K 3 rows colsW) > 0) := by
  have hb0 : ∀ n : Nat, laurentInterpBinom n 0 = 1 := fun n => by cases n <;> rfl
  have hb1 : ∀ n : Nat, laurentInterpBinom n 1 = n := by
    intro n
    induction n with
    | zero => rfl
    | succ m ihm =>
      change laurentInterpBinom m 0 + laurentInterpBinom m 1 = m + 1
      rw [hb0 m, ihm]; omega
  refine ⟨?_, ?_, ?_⟩
  · -- Part 1: Universal `L x L` Binomial-Taylor Column-Extrapolation Divisibility:
    intro W K L T u rows cols idx c0 hu hpoly hexp
    dsimp only
    let M0 : Fin L -> Fin L -> Int := fun i j =>
      (laurentZeroGapIntEntry W K (rows i).1 (rows i).2 (cols j).1 (cols j).2 : Int)
    let B : Nat := 2 ^ u - 1
    have h2u_ge2 : 2 ^ u ≥ 2 := by simpa using pow2_mono_nat hu
    have h1B : 1 + B = 2 ^ u := by dsimp [B]; omega
    have hne_all : ∀ t : Nat, t < T -> idx t ≠ c0 := by
      intro t ht heq
      have hc := hpoly t ht
      rw [heq, hexp] at hc
      injection hc with _ hu0
      omega
    let coef : Nat -> Int := fun t => ((B ^ t : Nat) : Int)
    have hinv := intDet_sub_col_prefix_invariant L c0 M0 T idx coef hne_all
    rw [hinv]
    apply intDet_col_dvd (((B ^ T : Nat) : Int)) L c0
    intro i
    simp only [ite_true]
    let x := (rows i).1 * W + (rows i).2 * K
    have hM0_c0 : M0 i c0 = Int.ofNat ((1 + B) ^ x) := by
      dsimp [M0]
      rw [hexp]
      unfold laurentZeroGapIntEntry
      apply congrArg Int.ofNat
      change laurentInterpBinom x 0 * 2 ^ (x * u) = (1 + B) ^ x
      rw [hb0 x, Nat.one_mul, Nat.mul_comm x u, ← pow_pow_eq_mul_w5 2 u x, h1B]
    have hsum_eq : ∀ m : Nat, m ≤ T ->
        colPrefixComb M0 idx coef i m = Int.ofNat (binomTaylorSum x B m) := by
      intro m hm
      induction m with
      | zero => rfl
      | succ m' ihm =>
        unfold colPrefixComb binomTaylorSum
        rw [ihm (by omega)]
        have hm0_t : M0 i (idx m') = Int.ofNat (laurentInterpBinom x m') := by
          dsimp [M0]
          rw [hpoly m' (by omega)]
          unfold laurentZeroGapIntEntry
          apply congrArg Int.ofNat
          change laurentInterpBinom x m' * 2 ^ (x * 0) = laurentInterpBinom x m'
          rw [Nat.mul_zero, Nat.pow_zero, Nat.mul_one]
        rw [hm0_t]
        dsimp [coef]
        change Int.ofNat (binomTaylorSum x B m') +
            Int.ofNat (B ^ m') * Int.ofNat (laurentInterpBinom x m') =
          Int.ofNat (binomTaylorSum x B m' + laurentInterpBinom x m' * B ^ m')
        have hmul_cast : Int.ofNat (B ^ m') * Int.ofNat (laurentInterpBinom x m') =
            Int.ofNat (laurentInterpBinom x m' * B ^ m') := by
          change ((B ^ m' : Nat) : Int) * ((laurentInterpBinom x m' : Nat) : Int) =
            ((laurentInterpBinom x m' * B ^ m' : Nat) : Int)
          rw [← natCast_mul, Nat.mul_comm]
        have hadd_cast : ∀ a b : Nat, Int.ofNat a + Int.ofNat b = Int.ofNat (a + b) := by
          intro a b
          change (a : Int) + (b : Int) = ((a + b : Nat) : Int)
          omega
        rw [hmul_cast, hadd_cast]
    rw [hM0_c0, hsum_eq T (Nat.le_refl T)]
    rcases binomTaylorSum_remainder_dvd x B T with ⟨hle_tay, q_rem, hq_rem⟩
    refine ⟨(q_rem : Int), ?_⟩
    change (((1 + B) ^ x : Nat) : Int) - ((binomTaylorSum x B T : Nat) : Int) =
      ((B ^ T : Nat) : Int) * (q_rem : Int)
    have hcast_sub : (((1 + B) ^ x : Nat) : Int) - ((binomTaylorSum x B T : Nat) : Int) =
        (((1 + B) ^ x - binomTaylorSum x B T : Nat) : Int) := by omega
    rw [hcast_sub, hq_rem, natCast_mul]
  · -- Part 2: Closed-form `3 x 3` derivative-extrapolated determinant `W * (2 ^ u - 1) ^ 2`
    --         and `W`-dilated zero-gap determinant `intDet 3 M0 = W * (2 ^ (W * u) - 1) ^ 2`:
    intro W K u hW hu
    dsimp only
    let rows : Fin 3 -> Nat × Nat := fun i =>
      if i.val = 0 then (0, 0) else if i.val = 1 then (1, 0) else (2, 0)
    have hdet_u : ∀ u' : Nat, u' ≥ 1 ->
        let cols' : Fin 3 -> Nat × Nat := fun j =>
          if j.val = 0 then (0, 0) else if j.val = 1 then (1, 0) else (0, u')
        intDet 3 (laurentInterpMat W K 3 rows cols') =
          ((W * (2 ^ u' - 1) ^ 2 : Nat) : Int) ∧
        intDet 3 (laurentInterpMat W K 3 rows cols') > 0 := by
      intro u' hu'
      dsimp only
      let cols' : Fin 3 -> Nat × Nat := fun j =>
        if j.val = 0 then (0, 0) else if j.val = 1 then (1, 0) else (0, u')
      let M := laurentInterpMat W K 3 rows cols'
      change intDet 3 M = _ ∧ intDet 3 M > 0
      rw [intDet_three M]
      have h2u_ge2 : 2 ^ u' ≥ 2 := by simpa using pow2_mono_nat hu'
      have h2_2u : 2 ^ (2 * u') = 2 ^ u' * 2 ^ u' := by
        rw [Nat.two_mul, Nat.pow_add]
      have hm00 : M ⟨0, by decide⟩ ⟨0, by decide⟩ = 1 := by
        simp [M, rows, cols', laurentInterpMat, laurentInterpEntry, hb0]
      have hm01 : M ⟨0, by decide⟩ ⟨1, by decide⟩ = 0 := by
        simp [M, rows, cols', laurentInterpMat, laurentInterpEntry, laurentInterpBinom]
      have hm02 : M ⟨0, by decide⟩ ⟨2, by decide⟩ = 1 := by
        simp [M, rows, cols', laurentInterpMat, laurentInterpEntry, hb0]
      have hm10 : M ⟨1, by decide⟩ ⟨0, by decide⟩ = 1 := by
        simp [M, rows, cols', laurentInterpMat, laurentInterpEntry, hb0]
      have hm11 : M ⟨1, by decide⟩ ⟨1, by decide⟩ = (W : Int) := by
        simp [M, rows, cols', laurentInterpMat, laurentInterpEntry, hb1]
      have hm12 : M ⟨1, by decide⟩ ⟨2, by decide⟩ = ((2 ^ u' : Nat) : Int) := by
        simp [M, rows, cols', laurentInterpMat, laurentInterpEntry, hb0]
      have hm20 : M ⟨2, by decide⟩ ⟨0, by decide⟩ = 1 := by
        simp [M, rows, cols', laurentInterpMat, laurentInterpEntry, hb0]
      have hm21 : M ⟨2, by decide⟩ ⟨1, by decide⟩ = ((2 * W : Nat) : Int) := by
        simp [M, rows, cols', laurentInterpMat, laurentInterpEntry, hb1]
      have hm22 : M ⟨2, by decide⟩ ⟨2, by decide⟩ = ((2 ^ u' * 2 ^ u' : Nat) : Int) := by
        simp [M, rows, cols', laurentInterpMat, laurentInterpEntry, hb0, h2_2u]
      rw [hm00, hm01, hm02, hm10, hm11, hm12, hm20, hm21, hm22]
      have hsq_nat : (2 ^ u' - 1) ^ 2 = (2 ^ u' - 1) * (2 ^ u' - 1) := by
        rw [Nat.pow_succ, Nat.pow_one]
      have hpos_nat : W * (2 ^ u' - 1) ^ 2 ≥ 1 := by
        rw [hsq_nat]
        simpa using Nat.mul_le_mul hW (Nat.mul_le_mul (by omega : 1 ≤ 2 ^ u' - 1) (by omega : 1 ≤ 2 ^ u' - 1))
      have hid_int :
          (1 : Int) * ((W : Int) * ((2 ^ u' * 2 ^ u' : Nat) : Int) - ((2 ^ u' : Nat) : Int) * ((2 * W : Nat) : Int)) -
          (0 : Int) * ((1 : Int) * ((2 ^ u' * 2 ^ u' : Nat) : Int) - ((2 ^ u' : Nat) : Int) * (1 : Int)) +
          (1 : Int) * ((1 : Int) * ((2 * W : Nat) : Int) - (W : Int) * (1 : Int)) =
          ((W * (2 ^ u' - 1) ^ 2 : Nat) : Int) := by
        rw [hsq_nat]
        let E : Nat := 2 ^ u'
        have hE_ge2 : E ≥ 2 := h2u_ge2
        change (1 : Int) * ((W : Int) * ((E * E : Nat) : Int) - (E : Int) * ((2 * W : Nat) : Int)) -
          (0 : Int) * ((1 : Int) * ((E * E : Nat) : Int) - (E : Int) * (1 : Int)) +
          (1 : Int) * ((1 : Int) * ((2 * W : Nat) : Int) - (W : Int) * (1 : Int)) =
          ((W * ((E - 1) * (E - 1)) : Nat) : Int)
        have hEE : ((E * E : Nat) : Int) = (E : Int) * (E : Int) := natCast_mul E E
        have h2W : ((2 * W : Nat) : Int) = 2 * (W : Int) := natCast_mul 2 W
        have hEm1 : ((E - 1 : Nat) : Int) = (E : Int) - 1 := by omega
        have hrhs : ((W * ((E - 1) * (E - 1)) : Nat) : Int) =
            (W : Int) * (((E : Int) - 1) * ((E : Int) - 1)) := by
          rw [natCast_mul W, natCast_mul (E - 1), hEm1]
        rw [hEE, h2W, hrhs]
        simp only [Int.one_mul, Int.mul_one, Int.zero_mul, Int.sub_zero]
        have hring : ∀ (w e : Int),
            (w * (e * e) - e * (2 * w)) + (2 * w - w) = w * ((e - 1) * (e - 1)) := by
          intro w e
          calc
            (w * (e * e) - e * (2 * w)) + (2 * w - w)
                = w * (e * e) - w * (2 * e) + w := by
                  have hc : e * (2 * w) = w * (2 * e) := by
                    rw [← Int.mul_assoc e 2 w, Int.mul_comm (e * 2) w, Int.mul_comm e 2]
                  rw [hc]; omega
            _ = w * (e * e - 2 * e + 1) := by
                  rw [Int.mul_add w (e * e - 2 * e) 1, Int.mul_sub w (e * e) (2 * e), Int.mul_one]
            _ = w * ((e - 1) * (e - 1)) := by
                  have hsq : (e - 1) * (e - 1) = e * e - 2 * e + 1 := by
                    rw [Int.mul_sub (e - 1) e 1, Int.sub_mul e 1 e]
                    omega
                  rw [hsq]
        exact hring (W : Int) (E : Int)
      rw [hid_int]
      exact ⟨rfl, by omega⟩
    let cols : Fin 3 -> Nat × Nat := fun j =>
      if j.val = 0 then (0, 0) else if j.val = 1 then (1, 0) else (0, u)
    let colsW : Fin 3 -> Nat × Nat := fun j =>
      if j.val = 0 then (0, 0) else if j.val = 1 then (1, 0) else (0, W * u)
    let M0 : Fin 3 -> Fin 3 -> Int := fun i j =>
      (laurentZeroGapIntEntry W K (rows i).1 (rows i).2 (cols j).1 (cols j).2 : Int)
    have hM0_eq : M0 = laurentInterpMat W K 3 rows colsW := by
      funext ⟨i, hi⟩ ⟨j, hj⟩
      match i, j with
      | 0, 0 => simp [M0, rows, cols, colsW, laurentZeroGapIntEntry, laurentInterpMat, laurentInterpEntry]
      | 0, 1 => simp [M0, rows, cols, colsW, laurentZeroGapIntEntry, laurentInterpMat, laurentInterpEntry]
      | 0, 2 => simp [M0, rows, cols, colsW, laurentZeroGapIntEntry, laurentInterpMat, laurentInterpEntry]
      | 1, 0 => simp [M0, rows, cols, colsW, laurentZeroGapIntEntry, laurentInterpMat, laurentInterpEntry]
      | 1, 1 => simp [M0, rows, cols, colsW, laurentZeroGapIntEntry, laurentInterpMat, laurentInterpEntry]
      | 1, 2 => simp [M0, rows, cols, colsW, laurentZeroGapIntEntry, laurentInterpMat, laurentInterpEntry]
      | 2, 0 => simp [M0, rows, cols, colsW, laurentZeroGapIntEntry, laurentInterpMat, laurentInterpEntry]
      | 2, 1 => simp [M0, rows, cols, colsW, laurentZeroGapIntEntry, laurentInterpMat, laurentInterpEntry]
      | 2, 2 =>
        simp [M0, rows, cols, colsW, laurentZeroGapIntEntry, laurentInterpMat, laurentInterpEntry,
          Nat.mul_assoc]
      | k + 3, _ => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 3 k) hi)
      | _, k + 3 => exact False.elim (Nat.not_lt_of_ge (Nat.le_add_left 3 k) hj)
    rcases hdet_u u hu with ⟨h1, h2⟩
    have hWu : W * u ≥ 1 := by simpa using Nat.mul_le_mul hW hu
    rcases hdet_u (W * u) hWu with ⟨h3, h4⟩
    change intDet 3 (laurentInterpMat W K 3 rows cols) = _ ∧
      intDet 3 (laurentInterpMat W K 3 rows cols) > 0 ∧
      intDet 3 M0 = _ ∧ intDet 3 M0 > 0
    rw [hM0_eq]
    exact ⟨h1, h2, h3, h4⟩
  · -- Part 3: Resonant `3 x 3` splitting (`intDet 3 M0 = 0` vs `intDet 3 MW = W * K * ((2^K)^(W*u) - (3^W)^(W*u)) > 0`):
    intro W K u hW hK hu hgt
    dsimp only
    let rows : Fin 3 -> Nat × Nat := fun i =>
      if i.val = 0 then (0, 0) else if i.val = 1 then (0, W) else (K, 0)
    let cols0 : Fin 3 -> Nat × Nat := fun j =>
      if j.val = 0 then (0, 0) else if j.val = 1 then (1, 0) else (0, u)
    let colsW : Fin 3 -> Nat × Nat := fun j =>
      if j.val = 0 then (0, 0) else if j.val = 1 then (1, 0) else (0, W * u)
    let M0 : Fin 3 -> Fin 3 -> Int := fun i j =>
      (laurentZeroGapIntEntry W K (rows i).1 (rows i).2 (cols0 j).1 (cols0 j).2 : Int)
    let MW := laurentInterpMat W K 3 rows colsW
    have hrow12_M0 : ∀ j : Fin 3, M0 ⟨1, by decide⟩ j = M0 ⟨2, by decide⟩ j := by
      intro j
      change (laurentZeroGapIntEntry W K 0 W (cols0 j).1 (cols0 j).2 : Int) =
        (laurentZeroGapIntEntry W K K 0 (cols0 j).1 (cols0 j).2 : Int)
      apply congrArg Int.ofNat
      unfold laurentZeroGapIntEntry
      simp only [Nat.zero_mul, Nat.add_zero, Nat.zero_add, Nat.mul_comm W K]
    have hdet_M0 : intDet 3 M0 = 0 := by
      rw [intDet_three M0,
          hrow12_M0 ⟨0, by decide⟩, hrow12_M0 ⟨1, by decide⟩, hrow12_M0 ⟨2, by decide⟩]
      have hz_id : ∀ a b c x y z : Int,
          a * (y * z - z * y) - b * (x * z - z * x) + c * (x * y - y * x) = 0 := by
        intro a b c x y z
        rw [Int.mul_comm z y, Int.mul_comm z x, Int.mul_comm y x,
            Int.sub_self, Int.sub_self, Int.sub_self,
            Int.mul_zero, Int.mul_zero, Int.mul_zero]
        rfl
      exact hz_id _ _ _ _ _ _
    change intDet 3 M0 = 0 ∧ intDet 3 MW = _ ∧ intDet 3 MW > 0
    refine ⟨hdet_M0, ?_⟩
    rw [intDet_three MW]
    let A2 := (2 ^ K) ^ (W * u)
    let B3 := (3 ^ W) ^ (W * u)
    have hWu_pos : W * u ≥ 1 := Nat.mul_le_mul hW hu
    have hB3_lt_A2 : B3 < A2 := by
      dsimp [A2, B3]
      have hlo := (pow_sub_pow_mean_value_sandwich (W * u) (2 ^ K) (3 ^ W) hWu_pos
        (Nat.le_of_lt hgt)).1
      have hpos : (W * u) * (3 ^ W) ^ (W * u - 1) * (2 ^ K - 3 ^ W) ≥ 1 := by
        simpa using Nat.mul_le_mul
          (Nat.mul_le_mul hWu_pos (nat_pow_pos_of_pos (3 ^ W) (pow3_pos_nat W) (W * u - 1)))
          (by omega : 1 ≤ 2 ^ K - 3 ^ W)
      omega
    have hw00 : MW ⟨0, by decide⟩ ⟨0, by decide⟩ = 1 := by
      simp [MW, rows, colsW, laurentInterpMat, laurentInterpEntry, hb0]
    have hw01 : MW ⟨0, by decide⟩ ⟨1, by decide⟩ = 0 := by
      simp [MW, rows, colsW, laurentInterpMat, laurentInterpEntry, laurentInterpBinom]
    have hw02 : MW ⟨0, by decide⟩ ⟨2, by decide⟩ = 1 := by
      simp [MW, rows, colsW, laurentInterpMat, laurentInterpEntry, hb0]
    have hw10 : MW ⟨1, by decide⟩ ⟨0, by decide⟩ = 1 := by
      simp [MW, rows, colsW, laurentInterpMat, laurentInterpEntry, hb0]
    have hw11 : MW ⟨1, by decide⟩ ⟨1, by decide⟩ = ((W * K : Nat) : Int) := by
      simp [MW, rows, colsW, laurentInterpMat, laurentInterpEntry, hb1]
    have hw12 : MW ⟨1, by decide⟩ ⟨2, by decide⟩ = (B3 : Int) := by
      change (laurentInterpEntry W K 0 W 0 (W * u) : Int) = (B3 : Int)
      apply congrArg Int.ofNat
      unfold laurentInterpEntry
      simp only [Nat.zero_mul, Nat.zero_add, Nat.pow_zero, hb0, Nat.one_mul]
      dsimp [B3]
      exact (pow_pow_eq_mul_w5 3 W (W * u)).symm
    have hw20 : MW ⟨2, by decide⟩ ⟨0, by decide⟩ = 1 := by
      simp [MW, rows, colsW, laurentInterpMat, laurentInterpEntry, hb0]
    have hw21 : MW ⟨2, by decide⟩ ⟨1, by decide⟩ = ((W * K : Nat) : Int) := by
      simp [MW, rows, colsW, laurentInterpMat, laurentInterpEntry, hb1, Nat.mul_comm K W]
    have hw22 : MW ⟨2, by decide⟩ ⟨2, by decide⟩ = (A2 : Int) := by
      change (laurentInterpEntry W K K 0 0 (W * u) : Int) = (A2 : Int)
      apply congrArg Int.ofNat
      unfold laurentInterpEntry
      simp only [Nat.zero_mul, Nat.add_zero, Nat.pow_zero, hb0, Nat.one_mul, Nat.mul_one]
      dsimp [A2]
      exact (pow_pow_eq_mul_w5 2 K (W * u)).symm
    rw [hw00, hw01, hw02, hw10, hw11, hw12, hw20, hw21, hw22]
    have hWK_pos : W * K ≥ 1 := Nat.mul_le_mul hW hK
    have hprod_pos : W * K * (A2 - B3) ≥ 1 := by
      simpa using Nat.mul_le_mul hWK_pos (by omega : 1 ≤ A2 - B3)
    have hid_mw :
        (1 : Int) * (((W * K : Nat) : Int) * (A2 : Int) - (B3 : Int) * ((W * K : Nat) : Int)) -
        (0 : Int) * ((1 : Int) * (A2 : Int) - (B3 : Int) * (1 : Int)) +
        (1 : Int) * ((1 : Int) * ((W * K : Nat) : Int) - ((W * K : Nat) : Int) * (1 : Int)) =
        ((W * K * (A2 - B3) : Nat) : Int) := by
      have hcast_rhs : ((W * K * (A2 - B3) : Nat) : Int) =
          ((W * K : Nat) : Int) * ((A2 : Int) - (B3 : Int)) := by
        rw [natCast_mul (W * K) (A2 - B3)]
        have hsub : ((A2 - B3 : Nat) : Int) = (A2 : Int) - (B3 : Int) := by omega
        rw [hsub]
      rw [hcast_rhs]
      simp only [Int.one_mul, Int.mul_one, Int.zero_mul, Int.sub_zero, Int.sub_self, Int.add_zero]
      rw [Int.mul_comm (B3 : Int) ((W * K : Nat) : Int), ← Int.mul_sub]
    rw [hid_mw]
    exact ⟨rfl, by omega⟩

-- ============================================================================
-- SECTION 3: Front C (Branch P1.2 & P5) — Non-Separable Base-2 Ripple-Carry
--            & Sliding-Window `k`-Gram Transducer Preimage Barriers, Plus
--            5th Solvable Mixed-(2,3) Cousin `T_diamond5`
-- ============================================================================

-- ----------------------------------------------------------------------------
-- Pure-`Nat` Bernoulli Power Ratio Inequality (zero custom axioms, choice-free)
-- ----------------------------------------------------------------------------

/--
  Pure-`Nat` Reverse Bernoulli Step (zero custom axioms, choice-free):
  For ALL `K M X : Nat`, whenever `K * M ≤ X`, `(X + M) ^ K * (X - K * M) ≤ X ^ (K + 1)`.
-/
theorem bernoulli_nat_pow_step :
    ∀ (K M X : Nat), K * M ≤ X -> (X + M) ^ K * (X - K * M) ≤ X ^ (K + 1)
  | 0, _, X, _ => by simp
  | K + 1, M, X, hle => by
    have hKM : K * M ≤ X := by
      have hm : K * M ≤ (K + 1) * M := Nat.mul_le_mul_right M (by omega)
      omega
    have ih := bernoulli_nat_pow_step K M X hKM
    let R := X - (K + 1) * M
    have hK1M : (K + 1) * M = K * M + M := by rw [Nat.add_mul K 1 M, Nat.one_mul]
    have hR_add : X - K * M = R + M := by dsimp [R]; omega
    have hR_le : R ≤ X := by dsimp [R]; omega
    have hcross : (X + M) * R ≤ X * (R + M) := by
      rw [Nat.add_mul X M R, Nat.mul_add X R M]
      have hm : M * R ≤ X * M := by
        rw [Nat.mul_comm X M]
        exact Nat.mul_le_mul_left M hR_le
      omega
    change (X + M) ^ (K + 1) * R ≤ X ^ (K + 2)
    rw [Nat.pow_succ (X + M) K, Nat.mul_assoc ((X + M) ^ K) (X + M) R]
    have hm1 := Nat.mul_le_mul_left ((X + M) ^ K) hcross
    have hm2 : (X + M) ^ K * (X * (R + M)) = ((X + M) ^ K * (X - K * M)) * X := by
      rw [hR_add, Nat.mul_comm X (R + M), ← Nat.mul_assoc ((X + M) ^ K) (R + M) X]
    rw [hm2] at hm1
    have hm3 := Nat.mul_le_mul_right X ih
    rw [← Nat.pow_succ X (K + 1)] at hm3
    exact Nat.le_trans hm1 hm3

/--
  Theorem W8.3a (`bernoulli_nat_ratio_lt`, zero custom axioms, choice-free):
  Universal Pure-`Nat` Asymptotic Power-Ratio Lemma:
  For ALL `A ≥ 1`, `B ≥ 1`, `K : Nat`, `M ≥ 1`, and EVERY `X ≥ (B + A + 1) * (K * M + 1)`,
    `B * (X + M) ^ K < (B + A) * X ^ K`!
-/
theorem bernoulli_nat_ratio_lt (A B K M X : Nat)
    (hA : A ≥ 1) (hB : B ≥ 1) (hM : M ≥ 1)
    (hX : X ≥ (B + A + 1) * (K * M + 1)) :
    B * (X + M) ^ K < (B + A) * X ^ K := by
  have hX_pos : X ≥ 1 := by
    have hp : 1 * 1 ≤ (B + A + 1) * (K * M + 1) := Nat.mul_le_mul (by omega) (by omega)
    omega
  have hKM_le : K * M ≤ X := by
    have h1 : K * M + 1 ≤ (B + A + 1) * (K * M + 1) := by
      simpa using Nat.mul_le_mul_right (K * M + 1) (by omega : 1 ≤ B + A + 1)
    omega
  have hbern := bernoulli_nat_pow_step K M X hKM_le
  have hAX_gt : (B + A) * (K * M) + 1 ≤ A * X := by
    have h1 : (B + A + 1) * (K * M + 1) ≤ A * X := by
      have hm := Nat.mul_le_mul_right X hA
      rw [Nat.one_mul] at hm; omega
    have hexp : (B + A + 1) * (K * M + 1) = (B + A) * (K * M) + K * M + B + A + 1 := by
      rw [Nat.mul_add (B + A + 1) (K * M) 1, Nat.mul_one,
          Nat.add_mul (B + A) 1 (K * M), Nat.one_mul]
      omega
    omega
  have hBX_lt : B * X + 1 ≤ (B + A) * (X - K * M) := by
    rw [Nat.mul_sub_left_distrib (B + A) X (K * M), Nat.add_mul B A X]
    have hle_sub : (B + A) * (K * M) ≤ B * X + A * X := by omega
    omega
  have hp_pos : (X + M) ^ K ≥ 1 := nat_pow_pos_of_pos (X + M) (by omega) K
  have hm_lhs : (B * X + 1) * (X + M) ^ K ≤ (B + A) * ((X + M) ^ K * (X - K * M)) := by
    have h1 := Nat.mul_le_mul_right ((X + M) ^ K) hBX_lt
    rw [Nat.mul_assoc (B + A) (X - K * M) ((X + M) ^ K),
        Nat.mul_comm (X - K * M) ((X + M) ^ K)] at h1
    exact h1
  have hm_rhs := Nat.mul_le_mul_left (B + A) hbern
  have hcomb : (B * X + 1) * (X + M) ^ K ≤ (B + A) * X ^ (K + 1) :=
    Nat.le_trans hm_lhs hm_rhs
  rw [Nat.add_mul (B * X) 1 ((X + M) ^ K), Nat.one_mul,
      Nat.pow_succ X K, ← Nat.mul_assoc (B + A) (X ^ K) X] at hcomb
  have hl_assoc : (B * X) * (X + M) ^ K = (B * (X + M) ^ K) * X := by
    rw [Nat.mul_assoc B X ((X + M) ^ K), Nat.mul_comm X ((X + M) ^ K),
        ← Nat.mul_assoc B ((X + M) ^ K) X]
  rw [hl_assoc] at hcomb
  exact nat_mul_lt_cancel_right_w5 X (B * (X + M) ^ K) ((B + A) * X ^ K) hX_pos (by omega)

-- ----------------------------------------------------------------------------
-- Base-2 Ripple-Carry Transducer for `n + (2 * n + 1)` (`Branch P1.2`)
-- ----------------------------------------------------------------------------

/--
  LSB-to-MSB binary addition ripple-carry transducer returning `(carryCount, carryIdxSum)`
  for `a + b + carry` starting at bit index `pos`.
-/
def addRippleCarryAux : Nat -> Nat -> Nat -> Nat -> Nat -> Nat × Nat
  | 0, _, _, _, _ => (0, 0)
  | fuel + 1, a, b, carry, pos =>
    if a = 0 ∧ b = 0 then (0, 0)
    else
      let nextCarry := (a % 2 + b % 2 + carry) / 2
      let rest := addRippleCarryAux fuel (a / 2) (b / 2) nextCarry (pos + 1)
      if nextCarry ≥ 1 then (1 + rest.1, pos + rest.2) else rest

/-- Coupled `(carryCount, carryIdxSum)` of base-2 ripple carries in `3 * n + 1 = n + (2 * n + 1)`. -/
def rippleCarry3n1Stats (n : Nat) : Nat × Nat :=
  if n = 0 then (0, 0) else addRippleCarryAux (2 * n + 4) n (2 * n + 1) 0 0

def rippleCarryCount3n1 (n : Nat) : Nat := (rippleCarry3n1Stats n).1
def rippleCarryIdxSum3n1 (n : Nat) : Nat := (rippleCarry3n1Stats n).2

theorem addRippleCarryAux_eq_of_ge :
    ∀ (f1 f2 a b carry pos : Nat),
      (a ≤ f1 ∧ b ≤ f1) -> (a ≤ f2 ∧ b ≤ f2) ->
      addRippleCarryAux f1 a b carry pos = addRippleCarryAux f2 a b carry pos
  | 0, 0, _, _, _, _, _, _ => rfl
  | 0, _ + 1, a, b, _, _, h1, _ => by
    have hab : a = 0 ∧ b = 0 := ⟨by omega, by omega⟩
    simp [addRippleCarryAux, hab]
  | _ + 1, 0, a, b, _, _, _, h2 => by
    have hab : a = 0 ∧ b = 0 := ⟨by omega, by omega⟩
    simp [addRippleCarryAux, hab]
  | f1 + 1, f2 + 1, a, b, carry, pos, h1, h2 => by
    simp only [addRippleCarryAux]
    by_cases hab : a = 0 ∧ b = 0
    · simp [hab]
    · simp only [hab, ite_false]
      have hdiv1 : a / 2 ≤ f1 ∧ b / 2 ≤ f1 := ⟨by omega, by omega⟩
      have hdiv2 : a / 2 ≤ f2 ∧ b / 2 ≤ f2 := ⟨by omega, by omega⟩
      rw [addRippleCarryAux_eq_of_ge f1 f2 (a / 2) (b / 2) _ (pos + 1) hdiv1 hdiv2]

theorem addRippleCarryAux_pos_shift :
    ∀ (fuel a b carry pos d : Nat),
      addRippleCarryAux fuel a b carry (pos + d) =
        ((addRippleCarryAux fuel a b carry pos).1,
         (addRippleCarryAux fuel a b carry pos).2 + d * (addRippleCarryAux fuel a b carry pos).1)
  | 0, _, _, _, _, _ => by simp [addRippleCarryAux]
  | fuel + 1, a, b, carry, pos, d => by
    simp only [addRippleCarryAux]
    by_cases hab : a = 0 ∧ b = 0
    · simp [hab]
    · simp only [hab, ite_false]
      let nc := (a % 2 + b % 2 + carry) / 2
      have hshift : pos + d + 1 = (pos + 1) + d := by omega
      have ih := addRippleCarryAux_pos_shift fuel (a / 2) (b / 2) nc (pos + 1) d
      rw [hshift, ih]
      let r := addRippleCarryAux fuel (a / 2) (b / 2) nc (pos + 1)
      change (if nc ≥ 1 then (1 + r.1, pos + d + (r.2 + d * r.1)) else (r.1, r.2 + d * r.1)) =
        ((if nc ≥ 1 then (1 + r.1, pos + r.2) else r).1,
         (if nc ≥ 1 then (1 + r.1, pos + r.2) else r).2 +
           d * (if nc ≥ 1 then (1 + r.1, pos + r.2) else r).1)
      by_cases hnc : nc ≥ 1
      · simp only [hnc, ite_true]
        apply Prod.ext
        · rfl
        · rw [Nat.mul_add d 1 r.1, Nat.mul_one]; omega
      · simp [hnc]

theorem addRippleCarryAux_step_pos0 (fuel a b carry : Nat)
    (hfuel : fuel ≥ 1) (hpos : a > 0 ∨ b > 0) :
    let nc := (a % 2 + b % 2 + carry) / 2
    let r := addRippleCarryAux (fuel - 1) (a / 2) (b / 2) nc 0
    addRippleCarryAux fuel a b carry 0 =
      if nc ≥ 1 then (1 + r.1, r.2 + r.1) else (r.1, r.2 + r.1) := by
  cases fuel with
  | zero => omega
  | succ f =>
    dsimp only
    simp only [addRippleCarryAux, Nat.add_sub_cancel]
    have hnab : ¬ (a = 0 ∧ b = 0) := by omega
    simp only [hnab, ite_false]
    have hsh := addRippleCarryAux_pos_shift f (a / 2) (b / 2) ((a % 2 + b % 2 + carry) / 2) 0 1
    simp only [Nat.zero_add, Nat.one_mul] at hsh
    rw [hsh]
    by_cases hnc : (a % 2 + b % 2 + carry) / 2 ≥ 1 <;> simp [hnc]

/--
  Theorem W8.3b (`ripple_carry_alternating_cascade_and_mersenne_triples`, zero custom axioms):
  1. Alternating Cascade vs Even-Sibling Collapse (`∀ e ≥ 1`, `A_e = (4 ^ e - 1) / 3`):
     `rippleCarry3n1Stats A_e = (2 * e, e * (2 * e - 1))`, whereas
     `rippleCarry3n1Stats (2 * A_e) = (0, 0)` (complete collapse to ZERO carries!).
  2. Exact Mersenne Preimage Triple Formulas (`∀ r ≥ 3`, `n_odd = 2 ^ r - 1`, `m = 3 * 2 ^ (r - 1) - 1`):
     - `m % 3 = 2` and `(2 * m - 1) / 3 = n_odd`;
     - `rippleCarry3n1Stats n_odd = (r + 1, r * (r + 1) / 2)` and `binBitLength n_odd = r`;
     - `rippleCarry3n1Stats m = (r + 2, (r + 1) * (r + 2) / 2)` and `binBitLength m = r + 1`;
     - `rippleCarry3n1Stats (2 * m) = (r + 1, (r + 1) * (r + 4) / 2)` and `binBitLength (2 * m) = r + 2`!
-/
theorem ripple_carry_alternating_cascade_and_mersenne_triples :
    rippleCarry3n1Stats 0 = (0, 0) ∧
    (∀ e : Nat, e ≥ 1 ->
      let Ae := (4 ^ e - 1) / 3
      rippleCarry3n1Stats Ae = (2 * e, e * (2 * e - 1)) ∧
      rippleCarry3n1Stats (2 * Ae) = (0, 0)) ∧
    (∀ r : Nat, r ≥ 3 ->
      let nOdd := 2 ^ r - 1
      let m := 3 * 2 ^ (r - 1) - 1
      m % 3 = 2 ∧
      (2 * m - 1) / 3 = nOdd ∧
      rippleCarry3n1Stats nOdd = (r + 1, r * (r + 1) / 2) ∧
      rippleCarry3n1Stats m = (r + 2, (r + 1) * (r + 2) / 2) ∧
      rippleCarry3n1Stats (2 * m) = (r + 1, (r + 1) * (r + 4) / 2) ∧
      binBitLength nOdd = r ∧
      binBitLength m = r + 1 ∧
      binBitLength (2 * m) = r + 2) := by
  have h4_m3 : ∀ e : Nat, 4 ^ e % 3 = 1 := by
    intro e; induction e with
    | zero => rfl
    | succ e' ih => rw [Nat.pow_succ, Nat.mul_mod, ih]
  -- 1. Alternating cascade helper for `Ae = (4^e - 1) / 3`:
  have halt_odd : ∀ (e c : Nat), e ≥ 1 -> (c = 0 ∨ c = 1) ->
      let Ae := (4 ^ e - 1) / 3
      addRippleCarryAux (4 * Ae + 4) Ae (2 * Ae + 1) c 0 = (2 * e, e * (2 * e - 1)) := by
    intro e
    induction e with
    | zero => intro _ h; omega
    | succ e' ih =>
      intro c _ hc
      by_cases he0 : e' = 0
      · subst he0
        rcases hc with rfl | rfl <;> decide
      · have he1 : e' ≥ 1 := by omega
        dsimp only
        let A0 := (4 ^ e' - 1) / 3
        have hm3 := h4_m3 e'
        have hp4_ge4 : 4 ^ e' ≥ 4 := by
          rw [show e' = (e' - 1) + 1 by omega, Nat.pow_succ]
          have hp := nat_pow_pos_of_pos 4 (by decide) (e' - 1); omega
        have hA0_pos : A0 ≥ 1 := by dsimp [A0]; omega
        have hAe_eq : (4 ^ (e' + 1) - 1) / 3 = 4 * A0 + 1 := by
          rw [Nat.pow_succ 4 e']; dsimp [A0]; omega
        rw [hAe_eq]
        let A1 := 4 * A0 + 1
        change addRippleCarryAux (4 * A1 + 4) A1 (2 * A1 + 1) c 0 = _
        -- Step 0 (`A1 = 4*A0 + 1` odd, `2*A1 + 1 = 8*A0 + 3` odd, `nc0 = 1`):
        have hs0 := addRippleCarryAux_step_pos0 (4 * A1 + 4) A1 (2 * A1 + 1) c
          (by omega) (Or.inl (by dsimp [A1]; omega))
        have hnc0 : (A1 % 2 + (2 * A1 + 1) % 2 + c) / 2 = 1 := by
          dsimp [A1]; rcases hc with rfl | rfl <;> omega
        have hd0_a : A1 / 2 = 2 * A0 := by dsimp [A1]; omega
        have hd0_b : (2 * A1 + 1) / 2 = 4 * A0 + 1 := by dsimp [A1]; omega
        dsimp only at hs0
        rw [hnc0, hd0_a, hd0_b] at hs0
        simp only [ Nat.le_refl, ite_true] at hs0
        -- Step 1 (`2*A0` even, `4*A0 + 1` odd, `carry = 1` -> `0 + 1 + 1 = 2`, `nc1 = 1`!):
        have hs1 := addRippleCarryAux_step_pos0 (4 * A1 + 4 - 1) (2 * A0) (4 * A0 + 1) 1
          (by dsimp [A1]; omega) (Or.inl (by omega))
        have hnc1 : ((2 * A0) % 2 + (4 * A0 + 1) % 2 + 1) / 2 = 1 := by omega
        have hd1_a : (2 * A0) / 2 = A0 := by omega
        have hd1_b : (4 * A0 + 1) / 2 = 2 * A0 := by omega
        -- Wait: at Step 1, `b / 2` is `2 * A0`, NOT `2 * A0 + 1`?
        -- HOLD ON! Check `(2 * A1 + 1) / 2`! `2 * A1 + 1 = 8 * A0 + 3`, `/ 2 = 4 * A0 + 1`!
        -- And `(4 * A0 + 1) / 2 = 2 * A0` with `carry = 1`!
        -- Look at `(A0, 2 * A0, carry = 1)` vs `(A0, 2 * A0 + 1, carry = 0)`:
        -- At `pos = 0`: `2 * A0` has bit 0 = `0` and `carry = 1`, whereas `2 * A0 + 1` has bit 0 = `1` and `carry = 0`!
        -- THEIR SUM `A0 % 2 + 0 + 1` vs `A0 % 2 + 1 + 0` IS **IDENTICAL** (`(A0 / 2) = (A0 / 2)` AND `(2 * A0) / 2 = A0 = (2 * A0 + 1) / 2`)!!
        have heq_rec : addRippleCarryAux (4 * A1 + 4 - 1 - 1) A0 (2 * A0) 1 0 =
            addRippleCarryAux (4 * A0 + 4) A0 (2 * A0 + 1) 0 0 := by
          have hs_l := addRippleCarryAux_step_pos0 (4 * A1 + 4 - 1 - 1) A0 (2 * A0) 1
            (by dsimp [A1]; omega) (Or.inl (by omega))
          have hs_r := addRippleCarryAux_step_pos0 (4 * A0 + 4) A0 (2 * A0 + 1) 0
            (by omega) (Or.inl (by omega))
          dsimp only at hs_l hs_r
          have hnc_eq : (A0 % 2 + (2 * A0) % 2 + 1) / 2 = (A0 % 2 + (2 * A0 + 1) % 2 + 0) / 2 := by
            omega
          have hb_div : (2 * A0) / 2 = A0 ∧ (2 * A0 + 1) / 2 = A0 := ⟨by omega, by omega⟩
          have hf_eq := addRippleCarryAux_eq_of_ge
            (4 * A1 + 4 - 1 - 1 - 1) (4 * A0 + 4 - 1)
            (A0 / 2) A0 ((A0 % 2 + (2 * A0 + 1) % 2 + 0) / 2) 0
            ⟨by dsimp [A1]; omega, by dsimp [A1]; omega⟩ ⟨by omega, by omega⟩
          rw [hs_l, hs_r, hnc_eq, hb_div.1, hb_div.2, hf_eq]
        dsimp only at hs1
        rw [hnc1, hd1_a, hd1_b, heq_rec] at hs1
        simp only [Nat.le_refl, ite_true] at hs1
        have ih0 := ih 0 he1 (Or.inl rfl)
        dsimp only at ih0
        change addRippleCarryAux (4 * A0 + 4) A0 (2 * A0 + 1) 0 0 = _ at ih0
        rw [hs0, hs1, ih0]
        dsimp only
        apply Prod.ext
        · omega
        · -- `(e' * (2*e' - 1) + 2*e') + (1 + 2*e') = (e' + 1) * (2*(e' + 1) - 1)`
          have hring : ∀ k : Nat, k ≥ 1 ->
              k * (2 * k - 1) + 2 * k + (1 + 2 * k) = (k + 1) * (2 * (k + 1) - 1) := by
            intro k hk1
            rw [Nat.add_mul k 1 (2 * (k + 1) - 1), Nat.one_mul,
                show 2 * (k + 1) - 1 = (2 * k - 1) + 2 by omega,
                Nat.mul_add k (2 * k - 1) 2]
            omega
          exact hring e' he1
  -- Even-sibling `2 * Ae` collapse to `(0, 0)`:
  have halt_even : ∀ e : Nat, e ≥ 1 ->
      let E := 2 * ((4 ^ e - 1) / 3)
      addRippleCarryAux (4 * E + 4) E (2 * E + 1) 0 0 = (0, 0) := by
    intro e
    induction e with
    | zero => intro h; omega
    | succ e' ih =>
      intro _
      by_cases he0 : e' = 0
      · subst he0; decide
      · have he1 : e' ≥ 1 := by omega
        dsimp only
        let A0 := (4 ^ e' - 1) / 3
        let E0 := 2 * A0
        have hm3 := h4_m3 e'
        have hp4_ge4 : 4 ^ e' ≥ 4 := by
          rw [show e' = (e' - 1) + 1 by omega, Nat.pow_succ]
          have hp := nat_pow_pos_of_pos 4 (by decide) (e' - 1); omega
        have hA0_pos : A0 ≥ 1 := by dsimp [A0]; omega
        have hAe_eq : (4 ^ (e' + 1) - 1) / 3 = 4 * A0 + 1 := by
          rw [Nat.pow_succ 4 e']; dsimp [A0]; omega
        rw [hAe_eq]
        let E1 := 2 * (4 * A0 + 1)
        change addRippleCarryAux (4 * E1 + 4) E1 (2 * E1 + 1) 0 0 = (0, 0)
        -- Step 0 (`E1 = 8*A0 + 2` even, `2*E1 + 1 = 16*A0 + 5` odd, `c = 0 -> nc = 0`):
        have hs0 := addRippleCarryAux_step_pos0 (4 * E1 + 4) E1 (2 * E1 + 1) 0
          (by omega) (Or.inl (by dsimp [E1]; omega))
        have hnc0 : (E1 % 2 + (2 * E1 + 1) % 2 + 0) / 2 = 0 := by dsimp [E1]; omega
        have hd0_a : E1 / 2 = 4 * A0 + 1 := by dsimp [E1]; omega
        have hd0_b : (2 * E1 + 1) / 2 = 8 * A0 + 2 := by dsimp [E1]; omega
        dsimp only at hs0
        rw [hnc0, hd0_a, hd0_b] at hs0
        simp only [show ¬ (0 ≥ 1) by decide, ite_false] at hs0
        -- Step 1 (`4*A0 + 1` odd, `8*A0 + 2` even, `c = 0 -> nc = 0`):
        have hs1 := addRippleCarryAux_step_pos0 (4 * E1 + 4 - 1) (4 * A0 + 1) (8 * A0 + 2) 0
          (by dsimp [E1]; omega) (Or.inl (by omega))
        have hnc1 : ((4 * A0 + 1) % 2 + (8 * A0 + 2) % 2 + 0) / 2 = 0 := by omega
        have hd1_a : (4 * A0 + 1) / 2 = E0 := by dsimp [E0]; omega
        have hd1_b : (8 * A0 + 2) / 2 = 2 * E0 + 1 := by dsimp [E0]; omega
        dsimp only at hs1
        rw [hnc1, hd1_a, hd1_b] at hs1
        simp only [show ¬ (0 ≥ 1) by decide, ite_false] at hs1
        have hf_eq := addRippleCarryAux_eq_of_ge
          (4 * E1 + 4 - 1 - 1) (4 * E0 + 4) E0 (2 * E0 + 1) 0 0
          ⟨by dsimp [E1, E0]; omega, by dsimp [E1, E0]; omega⟩ ⟨by omega, by omega⟩
        have ih0 := ih he1
        dsimp only at ih0
        change addRippleCarryAux (4 * E0 + 4) E0 (2 * E0 + 1) 0 0 = (0, 0) at ih0
        rw [hs0, hs1, hf_eq, ih0]
        rfl
  -- 2. Mersenne `2^r - 1` helper (`∀ r ≥ 1, c ∈ {0, 1}` -> `(r + 1, r * (r + 1) / 2)`):
  have hmers_odd : ∀ (r c : Nat), r ≥ 1 -> (c = 0 ∨ c = 1) ->
      let N := 2 ^ r - 1
      addRippleCarryAux (4 * N + 4) N (2 * N + 1) c 0 = (r + 1, r * (r + 1) / 2) := by
    intro r
    induction r with
    | zero => intro _ h; omega
    | succ r' ih =>
      intro c _ hc
      by_cases hr0 : r' = 0
      · subst hr0; rcases hc with rfl | rfl <;> decide
      · have hr1 : r' ≥ 1 := by omega
        dsimp only
        let N0 := 2 ^ r' - 1
        have hp2_ge2 : 2 ^ r' ≥ 2 := by simpa using pow2_mono_nat hr1
        have hN1_eq : 2 ^ (r' + 1) - 1 = 2 * N0 + 1 := by
          rw [Nat.pow_succ 2 r']; dsimp [N0]; omega
        rw [hN1_eq]
        let N1 := 2 * N0 + 1
        change addRippleCarryAux (4 * N1 + 4) N1 (2 * N1 + 1) c 0 = _
        have hs0 := addRippleCarryAux_step_pos0 (4 * N1 + 4) N1 (2 * N1 + 1) c
          (by omega) (Or.inl (by dsimp [N1]; omega))
        have hnc0 : (N1 % 2 + (2 * N1 + 1) % 2 + c) / 2 = 1 := by
          dsimp [N1]; rcases hc with rfl | rfl <;> omega
        have hd0_a : N1 / 2 = N0 := by dsimp [N1]; omega
        have hd0_b : (2 * N1 + 1) / 2 = 2 * N0 + 1 := by dsimp [N1]; omega
        have hf_eq := addRippleCarryAux_eq_of_ge
          (4 * N1 + 4 - 1) (4 * N0 + 4) N0 (2 * N0 + 1) 1 0
          ⟨by dsimp [N1]; omega, by dsimp [N1]; omega⟩ ⟨by omega, by omega⟩
        dsimp only at hs0
        rw [hnc0, hd0_a, hd0_b, hf_eq] at hs0
        simp only [Nat.le_refl, ite_true] at hs0
        have ih1 := ih 1 hr1 (Or.inr rfl)
        dsimp only at ih1
        change addRippleCarryAux (4 * N0 + 4) N0 (2 * N0 + 1) 1 0 = _ at ih1
        rw [hs0, ih1]
        dsimp only
        apply Prod.ext
        · omega
        · have htri : ∀ k : Nat, k * (k + 1) / 2 + (k + 1) = (k + 1) * (k + 2) / 2 := by
            intro k
            have hev1 : (k * (k + 1)) % 2 = 0 := by
              by_cases hk : k % 2 = 0
              · rw [Nat.mul_mod, hk, Nat.zero_mul]
              · have hk1 : (k + 1) % 2 = 0 := by omega
                rw [Nat.mul_mod, hk1, Nat.mul_zero]
            have hmul2 : 2 * (k * (k + 1) / 2 + (k + 1)) = (k + 1) * (k + 2) := by
              have hd := Nat.div_add_mod (k * (k + 1)) 2
              rw [hev1, Nat.add_zero] at hd
              rw [Nat.mul_add 2, hd, Nat.mul_add (k + 1) k 2, Nat.mul_comm k (k + 1)]
              omega
            omega
          exact htri r'
  -- 3. `m(d) = 3 * 2^d - 1` helper (`∀ d ≥ 1, c ∈ {0, 1}` -> `(d + 3, (d + 2) * (d + 3) / 2)`):
  have hmers_target : ∀ (d c : Nat), d ≥ 1 -> (c = 0 ∨ c = 1) ->
      let M := 3 * 2 ^ d - 1
      addRippleCarryAux (4 * M + 4) M (2 * M + 1) c 0 = (d + 3, (d + 2) * (d + 3) / 2) := by
    intro d
    induction d with
    | zero => intro _ h; omega
    | succ d' ih =>
      intro c _ hc
      by_cases hd0 : d' = 0
      · subst hd0; rcases hc with rfl | rfl <;> decide
      · have hd1 : d' ≥ 1 := by omega
        dsimp only
        let M0 := 3 * 2 ^ d' - 1
        have hp2_ge2 : 2 ^ d' ≥ 2 := by simpa using pow2_mono_nat hd1
        have hM1_eq : 3 * 2 ^ (d' + 1) - 1 = 2 * M0 + 1 := by
          rw [Nat.pow_succ 2 d']; dsimp [M0]; omega
        rw [hM1_eq]
        let M1 := 2 * M0 + 1
        change addRippleCarryAux (4 * M1 + 4) M1 (2 * M1 + 1) c 0 = _
        have hs0 := addRippleCarryAux_step_pos0 (4 * M1 + 4) M1 (2 * M1 + 1) c
          (by omega) (Or.inl (by dsimp [M1]; omega))
        have hnc0 : (M1 % 2 + (2 * M1 + 1) % 2 + c) / 2 = 1 := by
          dsimp [M1]; rcases hc with rfl | rfl <;> omega
        have hd0_a : M1 / 2 = M0 := by dsimp [M1]; omega
        have hd0_b : (2 * M1 + 1) / 2 = 2 * M0 + 1 := by dsimp [M1]; omega
        have hf_eq := addRippleCarryAux_eq_of_ge
          (4 * M1 + 4 - 1) (4 * M0 + 4) M0 (2 * M0 + 1) 1 0
          ⟨by dsimp [M1]; omega, by dsimp [M1]; omega⟩ ⟨by omega, by omega⟩
        dsimp only at hs0
        rw [hnc0, hd0_a, hd0_b, hf_eq] at hs0
        simp only [Nat.le_refl, ite_true] at hs0
        have ih1 := ih 1 hd1 (Or.inr rfl)
        dsimp only at ih1
        change addRippleCarryAux (4 * M0 + 4) M0 (2 * M0 + 1) 1 0 = _ at ih1
        rw [hs0, ih1]
        dsimp only
        apply Prod.ext
        · omega
        · have htri : ∀ k : Nat, k * (k + 1) / 2 + (k + 1) = (k + 1) * (k + 2) / 2 := by
            intro k
            have hev1 : (k * (k + 1)) % 2 = 0 := by
              by_cases hk : k % 2 = 0
              · rw [Nat.mul_mod, hk, Nat.zero_mul]
              · have hk1 : (k + 1) % 2 = 0 := by omega
                rw [Nat.mul_mod, hk1, Nat.mul_zero]
            have hd := Nat.div_add_mod (k * (k + 1)) 2
            rw [hev1, Nat.add_zero] at hd
            have hmul2 : 2 * (k * (k + 1) / 2 + (k + 1)) = (k + 1) * (k + 2) := by
              rw [Nat.mul_add 2, hd, Nat.mul_add (k + 1) k 2, Nat.mul_comm k (k + 1)]; omega
            omega
          simpa [Nat.add_assoc] using htri (d' + 2)
  refine ⟨rfl, ?_, ?_⟩
  · -- Part 1: Alternating cascade & even-sibling collapse:
    intro e he1
    dsimp only
    let Ae := (4 ^ e - 1) / 3
    have hm3 := h4_m3 e
    have hp4_ge4 : 4 ^ e ≥ 4 := by
      rw [show e = (e - 1) + 1 by omega, Nat.pow_succ]
      have hp := nat_pow_pos_of_pos 4 (by decide) (e - 1); omega
    have hAe_pos : Ae ≥ 1 := by dsimp [Ae]; omega
    have hr1 : rippleCarry3n1Stats Ae = (2 * e, e * (2 * e - 1)) := by
      unfold rippleCarry3n1Stats
      have hnz : ¬ (Ae = 0) := by omega
      simp only [hnz, ite_false]
      rw [addRippleCarryAux_eq_of_ge (2 * Ae + 4) (4 * Ae + 4) Ae (2 * Ae + 1) 0 0
        ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
      exact halt_odd e 0 he1 (Or.inl rfl)
    have hr2 : rippleCarry3n1Stats (2 * Ae) = (0, 0) := by
      unfold rippleCarry3n1Stats
      have hnz2 : ¬ (2 * Ae = 0) := by omega
      simp only [hnz2, ite_false]
      rw [addRippleCarryAux_eq_of_ge (2 * (2 * Ae) + 4) (4 * (2 * Ae) + 4) (2 * Ae) (2 * (2 * Ae) + 1) 0 0
        ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
      exact halt_even e he1
    exact ⟨hr1, hr2⟩
  · -- Part 2: Mersenne preimage triple formulas (`∀ r ≥ 3`):
    intro r hr3
    dsimp only
    let nOdd := 2 ^ r - 1
    let m := 3 * 2 ^ (r - 1) - 1
    have hp2_r1 : 2 ^ (r - 1) ≥ 4 := pow2_ge_four_of_ge_two (r - 1) (by omega)
    have hp2_r2 : 2 ^ (r - 2) ≥ 2 := by simpa using pow2_mono_nat (by omega : 1 ≤ r - 2)
    have hp2_sp : 2 ^ r = 2 * 2 ^ (r - 1) := pow2_split_pred r (by omega)
    have hp2_sp1 : 2 ^ (r - 1) = 2 * 2 ^ (r - 2) := pow2_split_pred (r - 1) (by omega)
    have hm_m3 : m % 3 = 2 := by dsimp [m]; omega
    have hpre_eq : (2 * m - 1) / 3 = nOdd := by
      dsimp [m, nOdd]; rw [hp2_sp]; omega
    have hst_n : rippleCarry3n1Stats nOdd = (r + 1, r * (r + 1) / 2) := by
      unfold rippleCarry3n1Stats
      have hnz : ¬ (nOdd = 0) := by dsimp [nOdd]; omega
      simp only [hnz, ite_false]
      rw [addRippleCarryAux_eq_of_ge (2 * nOdd + 4) (4 * nOdd + 4) nOdd (2 * nOdd + 1) 0 0
        ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
      exact hmers_odd r 0 (by omega) (Or.inl rfl)
    have hst_m : rippleCarry3n1Stats m = (r + 2, (r + 1) * (r + 2) / 2) := by
      unfold rippleCarry3n1Stats
      have hnz : ¬ (m = 0) := by dsimp [m]; omega
      simp only [hnz, ite_false]
      rw [addRippleCarryAux_eq_of_ge (2 * m + 4) (4 * m + 4) m (2 * m + 1) 0 0
        ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
      have ht := hmers_target (r - 1) 0 (by omega) (Or.inl rfl)
      dsimp only at ht
      change addRippleCarryAux (4 * m + 4) m (2 * m + 1) 0 0 = _ at ht
      rw [ht]
      apply Prod.ext
      · dsimp only; omega
      · dsimp only
        apply congrArg (· / 2)
        rw [show r - 1 + 2 = r + 1 by omega, show r - 1 + 3 = r + 2 by omega]
    have hst_2m : rippleCarry3n1Stats (2 * m) = (r + 1, (r + 1) * (r + 4) / 2) := by
      unfold rippleCarry3n1Stats
      have hnz : ¬ (2 * m = 0) := by dsimp [m]; omega
      simp only [hnz, ite_false]
      let mPrev := 3 * 2 ^ (r - 2) - 1
      have hm_eq_prev : m = 2 * mPrev + 1 := by
        dsimp [m, mPrev]; rw [hp2_sp1]; omega
      have hs0 := addRippleCarryAux_step_pos0 (2 * (2 * m) + 4) (2 * m) (2 * (2 * m) + 1) 0
        (by omega) (Or.inl (by dsimp [m]; omega))
      have hnc0 : ((2 * m) % 2 + (2 * (2 * m) + 1) % 2 + 0) / 2 = 0 := by omega
      have hd0_a : (2 * m) / 2 = m := by omega
      have hd0_b : (2 * (2 * m) + 1) / 2 = 2 * m := by omega
      dsimp only at hs0
      rw [hnc0, hd0_a, hd0_b] at hs0
      simp only [show ¬ (0 ≥ 1) by decide, ite_false] at hs0
      have hs1 := addRippleCarryAux_step_pos0 (2 * (2 * m) + 4 - 1) m (2 * m) 0
        (by omega) (Or.inl (by dsimp [m]; omega))
      have hnc1 : (m % 2 + (2 * m) % 2 + 0) / 2 = 0 := by rw [hm_eq_prev]; omega
      have hd1_a : m / 2 = mPrev := by rw [hm_eq_prev]; omega
      have hd1_b : (2 * m) / 2 = 2 * mPrev + 1 := by rw [hm_eq_prev]; omega
      dsimp only at hs1
      rw [hnc1, hd1_a, hd1_b] at hs1
      simp only [show ¬ (0 ≥ 1) by decide, ite_false] at hs1
      have hf_eq := addRippleCarryAux_eq_of_ge
        (2 * (2 * m) + 4 - 1 - 1) (4 * mPrev + 4) mPrev (2 * mPrev + 1) 0 0
        ⟨by rw [hm_eq_prev]; omega, by rw [hm_eq_prev]; omega⟩ ⟨by omega, by omega⟩
      have ht_prev := hmers_target (r - 2) 0 (by omega) (Or.inl rfl)
      dsimp only at ht_prev
      change addRippleCarryAux (4 * mPrev + 4) mPrev (2 * mPrev + 1) 0 0 = _ at ht_prev
      rw [hs0, hs1, hf_eq, ht_prev]
      dsimp only
      have hr2_add2 : r - 2 + 2 = r := by omega
      have hr2_add3 : r - 2 + 3 = r + 1 := by omega
      rw [hr2_add2, hr2_add3]
      apply Prod.ext
      · rfl
      · have hev : (r * (r + 1)) % 2 = 0 := by
          by_cases hr_ev : r % 2 = 0
          · rw [Nat.mul_mod, hr_ev, Nat.zero_mul]
          · have hr1_ev : (r + 1) % 2 = 0 := by omega
            rw [Nat.mul_mod, hr1_ev, Nat.mul_zero]
        have hd := Nat.div_add_mod (r * (r + 1)) 2
        rw [hev, Nat.add_zero] at hd
        have hmul2 : 2 * (r * (r + 1) / 2 + (r + 1) + (r + 1)) = (r + 1) * (r + 4) := by
          rw [Nat.mul_add 2, Nat.mul_add 2, hd, Nat.mul_add (r + 1) r 4, Nat.mul_comm r (r + 1)]
          omega
        omega
    have hbl_n : binBitLength nOdd = r := by
      have hb := (binBitLength_pow2_and_pred (r - 1)).2
      rwa [show r - 1 + 1 = r by omega] at hb
    have hbl_m : binBitLength m = r + 1 := by
      apply binBitLength_of_pow2_sandwich r m
      · dsimp [m]; rw [hp2_sp]; omega
      · dsimp [m]; rw [Nat.pow_succ 2 r, hp2_sp]; omega
    have hbl_2m : binBitLength (2 * m) = r + 2 := by
      rw [binBitLength_step_pos (2 * m) (by dsimp [m]; omega),
          show (2 * m) / 2 = m by omega, hbl_m]
      omega
    exact ⟨hm_m3, hpre_eq, hst_n, hst_m, hst_2m, hbl_n, hbl_m, hbl_2m⟩

-- ----------------------------------------------------------------------------
-- Non-Separable Multivariate Polynomials & Ripple-Carry Preimage Barrier (`W8.3c`)
-- ----------------------------------------------------------------------------

/-- Non-separable trivariate polynomial `∑ c * x ^ i * y ^ j * z ^ k` over `Nat`. -/
abbrev NatPoly3 := List (Nat × Nat × Nat × Nat)

def evalNatPoly3 : NatPoly3 -> Nat -> Nat -> Nat -> Nat
  | [], _, _, _ => 0
  | (c, i, j, k) :: rest, x, y, z => c * x ^ i * y ^ j * z ^ k + evalNatPoly3 rest x y z

def maxDegNatPoly3 : NatPoly3 -> Nat
  | [] => 0
  | (c, i, j, k) :: rest =>
    if c > 0 then Nat.max (i + j + k) (maxDegNatPoly3 rest) else maxDegNatPoly3 rest

theorem cross_ratio_pow_le_w8 (a b x y : Nat) (hxy : a * x ≤ b * y) :
    ∀ e : Nat, a ^ e * x ^ e ≤ b ^ e * y ^ e
  | 0 => by simp
  | e + 1 => by
    have ih := cross_ratio_pow_le_w8 a b x y hxy e
    have hm := Nat.mul_le_mul ih hxy
    have hl : (a ^ e * x ^ e) * (a * x) = a ^ (e + 1) * x ^ (e + 1) := by
      calc
        (a ^ e * x ^ e) * (a * x)
            = a ^ e * (x ^ e * a) * x := by rw [Nat.mul_assoc (a ^ e) (x ^ e) (a * x), ← Nat.mul_assoc (x ^ e) a x, ← Nat.mul_assoc (a ^ e)]
        _ = (a ^ e * a) * (x ^ e * x) := by
              rw [Nat.mul_comm (x ^ e) a, ← Nat.mul_assoc (a ^ e) a (x ^ e), Nat.mul_assoc (a ^ e * a) (x ^ e) x]
        _ = a ^ (e + 1) * x ^ (e + 1) := by rw [← Nat.pow_succ a e, ← Nat.pow_succ x e]
    have hr : (b ^ e * y ^ e) * (b * y) = b ^ (e + 1) * y ^ (e + 1) := by
      calc
        (b ^ e * y ^ e) * (b * y)
            = b ^ e * (y ^ e * b) * y := by rw [Nat.mul_assoc (b ^ e) (y ^ e) (b * y), ← Nat.mul_assoc (y ^ e) b y, ← Nat.mul_assoc (b ^ e)]
        _ = (b ^ e * b) * (y ^ e * y) := by
              rw [Nat.mul_comm (y ^ e) b, ← Nat.mul_assoc (b ^ e) b (y ^ e), Nat.mul_assoc (b ^ e * b) (y ^ e) y]
        _ = b ^ (e + 1) * y ^ (e + 1) := by rw [← Nat.pow_succ b e, ← Nat.pow_succ y e]
    rwa [hl, hr] at hm

theorem evalNatPoly3_cross_ratio_bound :
    ∀ (P : NatPoly3) (a b x1 y1 z1 x2 y2 z2 : Nat),
      a ≤ b ->
      a * x1 ≤ b * x2 ->
      a * y1 ≤ b * y2 ->
      a * z1 ≤ b * z2 ->
      a ^ (maxDegNatPoly3 P) * evalNatPoly3 P x1 y1 z1 ≤
        b ^ (maxDegNatPoly3 P) * evalNatPoly3 P x2 y2 z2
  | [], _, _, _, _, _, _, _, _, _, _, _, _ => by simp [evalNatPoly3]
  | (c, i, j, k) :: rest, a, b, x1, y1, z1, x2, y2, z2, hab, hx, hy, hz => by
    have ih := evalNatPoly3_cross_ratio_bound rest a b x1 y1 z1 x2 y2 z2 hab hx hy hz
    simp only [evalNatPoly3, maxDegNatPoly3]
    by_cases hc : c > 0
    · simp only [hc, ite_true]
      let D := Nat.max (i + j + k) (maxDegNatPoly3 rest)
      have hijk_le : i + j + k ≤ D := Nat.le_max_left _ _
      have hr_le : maxDegNatPoly3 rest ≤ D := Nat.le_max_right _ _
      change a ^ D * (c * x1 ^ i * y1 ^ j * z1 ^ k + evalNatPoly3 rest x1 y1 z1) ≤
        b ^ D * (c * x2 ^ i * y2 ^ j * z2 ^ k + evalNatPoly3 rest x2 y2 z2)
      rw [Nat.mul_add (a ^ D), Nat.mul_add (b ^ D)]
      have ht1 : a ^ D * (c * x1 ^ i * y1 ^ j * z1 ^ k) ≤
          b ^ D * (c * x2 ^ i * y2 ^ j * z2 ^ k) := by
        have hsp : D = i + j + k + (D - (i + j + k)) := by omega
        rw [hsp, Nat.pow_add a (i + j + k), Nat.pow_add a (i + j) k, Nat.pow_add a i j,
            Nat.pow_add b (i + j + k), Nat.pow_add b (i + j) k, Nat.pow_add b i j]
        have hxi := cross_ratio_pow_le_w8 a b x1 x2 hx i
        have hyj := cross_ratio_pow_le_w8 a b y1 y2 hy j
        have hzk := cross_ratio_pow_le_w8 a b z1 z2 hz k
        have hrem := nat_pow_mono_base a b hab (D - (i + j + k))
        have harrange : ∀ (ai aj ak ar xi yj zk : Nat),
            (ai * aj * ak * ar) * (c * xi * yj * zk) =
              c * (ai * xi) * (aj * yj) * (ak * zk) * ar := by
          intro ai aj ak ar xi yj zk
          calc
            (ai * aj * ak * ar) * (c * xi * yj * zk)
                = c * ((ai * aj * ak * ar) * (xi * yj * zk)) := by
                  have hc_assoc : c * xi * yj * zk = c * (xi * yj * zk) := by
                    rw [Nat.mul_assoc c xi yj, Nat.mul_assoc c (xi * yj) zk]
                  rw [hc_assoc, ← Nat.mul_assoc (ai * aj * ak * ar) c,
                      Nat.mul_comm (ai * aj * ak * ar) c, Nat.mul_assoc c]
            _ = c * ((ai * aj * ak) * (xi * yj * zk) * ar) := by
                  apply congrArg (c * ·)
                  rw [Nat.mul_assoc (ai * aj * ak) ar,
                      Nat.mul_comm ar (xi * yj * zk),
                      ← Nat.mul_assoc (ai * aj * ak)]
            _ = c * (ai * xi) * (aj * yj) * (ak * zk) * ar := by
                  have hmid : (ai * aj * ak) * (xi * yj * zk) =
                      (ai * xi) * (aj * yj) * (ak * zk) := by
                    calc
                      (ai * aj * ak) * (xi * yj * zk)
                          = ((ai * aj) * (xi * yj)) * (ak * zk) := by
                            rw [Nat.mul_assoc (ai * aj) ak,
                                ← Nat.mul_assoc ak (xi * yj) zk,
                                Nat.mul_comm ak (xi * yj),
                                Nat.mul_assoc (xi * yj) ak zk,
                                ← Nat.mul_assoc (ai * aj)]
                      _ = ((ai * xi) * (aj * yj)) * (ak * zk) := by
                            apply congrArg (· * (ak * zk))
                            rw [Nat.mul_assoc ai aj, ← Nat.mul_assoc aj xi yj,
                                Nat.mul_comm aj xi, Nat.mul_assoc xi aj yj,
                                ← Nat.mul_assoc ai xi]
                  rw [hmid, ← Nat.mul_assoc c ((ai * xi) * (aj * yj) * (ak * zk)) ar,
                      ← Nat.mul_assoc c ((ai * xi) * (aj * yj)) (ak * zk),
                      ← Nat.mul_assoc c (ai * xi) (aj * yj)]
        rw [harrange (a ^ i) (a ^ j) (a ^ k), harrange (b ^ i) (b ^ j) (b ^ k)]
        exact Nat.mul_le_mul
          (Nat.mul_le_mul
            (Nat.mul_le_mul (Nat.mul_le_mul (Nat.le_refl c) hxi) hyj)
            hzk)
          hrem
      have ht2 : a ^ D * evalNatPoly3 rest x1 y1 z1 ≤
          b ^ D * evalNatPoly3 rest x2 y2 z2 := by
        let Dr := maxDegNatPoly3 rest
        have hsp : D = Dr + (D - Dr) := by omega
        rw [hsp, Nat.pow_add a Dr (D - Dr), Nat.pow_add b Dr (D - Dr)]
        have hl : (a ^ Dr * a ^ (D - Dr)) * evalNatPoly3 rest x1 y1 z1 =
            a ^ (D - Dr) * (a ^ Dr * evalNatPoly3 rest x1 y1 z1) := by
          rw [Nat.mul_comm (a ^ Dr), Nat.mul_assoc]
        have hr : (b ^ Dr * b ^ (D - Dr)) * evalNatPoly3 rest x2 y2 z2 =
            b ^ (D - Dr) * (b ^ Dr * evalNatPoly3 rest x2 y2 z2) := by
          rw [Nat.mul_comm (b ^ Dr), Nat.mul_assoc]
        rw [hl, hr]
        exact Nat.mul_le_mul (nat_pow_mono_base a b hab (D - Dr)) ih
      exact Nat.add_le_add ht1 ht2
    · simp only [hc, ite_false]
      have hc0 : c = 0 := by omega
      simp only [hc0, Nat.zero_mul, Nat.zero_add]
      exact ih

/--
  Theorem W8.3c (`berg_meinardus_nonseparable_ripple_carry_preimage_impossibility`, zero custom axioms):
  Universal Non-Separable Ripple-Carry Transducer Preimage Impossibility (`W8_H3` Part 1):
  NO non-separable trivariate rational preimage weight
    `w(n) = P(rippleCarryCount3n1 n, rippleCarryIdxSum3n1 n, binBitLength n) /
            Q(rippleCarryCount3n1 n, rippleCarryIdxSum3n1 n, binBitLength n)`
  — for ANY arbitrary multi-term polynomials `pTerms, qTerms : NatPoly3` with arbitrary cross
  monomials `c ^ i * s ^ j * L ^ k` — can satisfy `IsPositiveRationalPreimageWeight`!
-/
theorem berg_meinardus_nonseparable_ripple_carry_preimage_impossibility
    (pTerms qTerms : NatPoly3) (pTheta qTheta : Nat)
    (hw : IsPositiveRationalPreimageWeight
      (fun n => evalNatPoly3 pTerms (rippleCarryCount3n1 n) (rippleCarryIdxSum3n1 n) (binBitLength n))
      (fun n => evalNatPoly3 qTerms (rippleCarryCount3n1 n) (rippleCarryIdxSum3n1 n) (binBitLength n))
      pTheta qTheta) :
    False := by
  let dP := maxDegNatPoly3 pTerms
  let dQ := maxDegNatPoly3 qTerms
  let D := dP + dQ
  let u := 3 * (D * 2 + 1) + 2
  have hu_ge2 : u ≥ 2 := by dsimp [u]; omega
  let r := 2 * u
  have hr_ge3 : r ≥ 3 := by dsimp [r]; omega
  rcases ripple_carry_alternating_cascade_and_mersenne_triples.2.2 r hr_ge3 with
    ⟨hm_m3, hpre_eq, hst_n, hst_m, hst_2m, hbl_n, hbl_m, hbl_2m⟩
  let nOdd := 2 ^ r - 1
  let m := 3 * 2 ^ (r - 1) - 1
  have hp2_ge8 : 2 ^ (r - 1) ≥ 8 := by simpa using pow2_mono_nat (by dsimp [r]; omega : 3 ≤ r - 1)
  have hm_ge3 : m ≥ 3 := by dsimp [m]; omega
  have hn_ge3 : nOdd ≥ 3 := by
    have hp := pow2_mono_nat (by dsimp [r]; omega : 4 ≤ r)
    dsimp [nOdd]; omega
  -- Exact polynomial coordinates at `r = 2 * u` (zero integer divisions!):
  have hdiv_n : r * (r + 1) / 2 = u * (2 * u + 1) := by
    dsimp [r]; rw [Nat.mul_assoc 2 u (2 * u + 1), Nat.mul_div_cancel_left _ (by decide)]
  have hdiv_m : (r + 1) * (r + 2) / 2 = (u + 1) * (2 * u + 1) := by
    dsimp [r]
    have heq : (2 * u + 1) * (2 * u + 2) = 2 * ((u + 1) * (2 * u + 1)) := by
      rw [show 2 * u + 2 = 2 * (u + 1) by omega,
          Nat.mul_comm (2 * u + 1) (2 * (u + 1)), Nat.mul_assoc 2 (u + 1)]
    rw [heq, Nat.mul_div_cancel_left _ (by decide)]
  have hdiv_2m : (r + 1) * (r + 4) / 2 = (u + 2) * (2 * u + 1) := by
    dsimp [r]
    have heq : (2 * u + 1) * (2 * u + 4) = 2 * ((u + 2) * (2 * u + 1)) := by
      rw [show 2 * u + 4 = 2 * (u + 2) by omega,
          Nat.mul_comm (2 * u + 1) (2 * (u + 2)), Nat.mul_assoc 2 (u + 2)]
    rw [heq, Nat.mul_div_cancel_left _ (by decide)]
  have hcn : rippleCarryCount3n1 nOdd = 2 * u + 1 ∧ rippleCarryIdxSum3n1 nOdd = u * (2 * u + 1) := by
    unfold rippleCarryCount3n1 rippleCarryIdxSum3n1
    change (rippleCarry3n1Stats nOdd).1 = _ ∧ (rippleCarry3n1Stats nOdd).2 = _
    rw [hst_n, hdiv_n]; exact ⟨rfl, rfl⟩
  have hcm : rippleCarryCount3n1 m = 2 * u + 2 ∧ rippleCarryIdxSum3n1 m = (u + 1) * (2 * u + 1) := by
    unfold rippleCarryCount3n1 rippleCarryIdxSum3n1
    change (rippleCarry3n1Stats m).1 = _ ∧ (rippleCarry3n1Stats m).2 = _
    rw [hst_m, hdiv_m]; exact ⟨rfl, rfl⟩
  have hc2m : rippleCarryCount3n1 (2 * m) = 2 * u + 1 ∧ rippleCarryIdxSum3n1 (2 * m) = (u + 2) * (2 * u + 1) := by
    unfold rippleCarryCount3n1 rippleCarryIdxSum3n1
    change (rippleCarry3n1Stats (2 * m)).1 = _ ∧ (rippleCarry3n1Stats (2 * m)).2 = _
    rw [hst_2m, hdiv_2m]; exact ⟨rfl, rfl⟩
  -- Evaluate preimage inequality at `m`:
  have hpre := hw.2.2.2.2 m hm_ge3 hm_m3
  dsimp only at hpre
  rw [hpre_eq] at hpre
  have hcanc := nat_mul_le_cancel_left_w5 qTheta _ _
    (Nat.lt_of_lt_of_le hw.1 hw.2.1)
    (Nat.le_trans hpre (Nat.mul_le_mul_right _ hw.2.1))
  let Pn := evalNatPoly3 pTerms (2 * u + 1) (u * (2 * u + 1)) (2 * u)
  let Qn := evalNatPoly3 qTerms (2 * u + 1) (u * (2 * u + 1)) (2 * u)
  let Pm := evalNatPoly3 pTerms (2 * u + 2) ((u + 1) * (2 * u + 1)) (2 * u + 1)
  let Qm := evalNatPoly3 qTerms (2 * u + 2) ((u + 1) * (2 * u + 1)) (2 * u + 1)
  let P2m := evalNatPoly3 pTerms (2 * u + 1) ((u + 2) * (2 * u + 1)) (2 * u + 2)
  let Q2m := evalNatPoly3 qTerms (2 * u + 1) ((u + 2) * (2 * u + 1)) (2 * u + 2)
  rw [hcn.1, hcn.2, hbl_n, hcm.1, hcm.2, hbl_m, hc2m.1, hc2m.2, hbl_2m] at hcanc
  change (P2m * Qn + Pn * Q2m) * Qm ≤ Pm * (Q2m * Qn) at hcanc
  -- Positivity of `Pm, Q2m, Qn` from `hw`:
  rcases hw.2.2.1 m hm_ge3 with ⟨hPm_pos, _⟩
  rcases hw.2.2.1 (2 * m) (by omega) with ⟨_, hQ2m_pos⟩
  rcases hw.2.2.1 nOdd hn_ge3 with ⟨_, hQn_pos⟩
  dsimp only at hPm_pos hQ2m_pos hQn_pos
  rw [hcm.1, hcm.2, hbl_m] at hPm_pos
  rw [hc2m.1, hc2m.2, hbl_2m] at hQ2m_pos
  rw [hcn.1, hcn.2, hbl_n] at hQn_pos
  -- Cross-ratio bounds with `a = u, b = u + 2`:
  have hcx1 : u * (2 * u + 2) ≤ (u + 2) * (2 * u + 1) := by
    rw [Nat.mul_add u (2 * u) 2, Nat.add_mul u 2 (2 * u + 1), Nat.mul_add u (2 * u) 1]; omega
  have hcy_n : u * ((u + 1) * (2 * u + 1)) ≤ (u + 2) * (u * (2 * u + 1)) := by
    have h1 : u * (u + 1) ≤ (u + 2) * u := by
      rw [Nat.mul_add u u 1, Nat.add_mul u 2 u]; omega
    rw [← Nat.mul_assoc u (u + 1), ← Nat.mul_assoc (u + 2) u]
    exact Nat.mul_le_mul_right _ h1
  have hcz_n : u * (2 * u + 1) ≤ (u + 2) * (2 * u) := by
    rw [Nat.mul_add u (2 * u) 1, Nat.add_mul u 2 (2 * u)]; omega
  have hPm_Pn : u ^ dP * Pm ≤ (u + 2) ^ dP * Pn :=
    evalNatPoly3_cross_ratio_bound pTerms u (u + 2)
      (2 * u + 2) ((u + 1) * (2 * u + 1)) (2 * u + 1)
      (2 * u + 1) (u * (2 * u + 1)) (2 * u)
      (by omega) hcx1 hcy_n hcz_n
  have hQn_Qm : u ^ dQ * Qn ≤ (u + 2) ^ dQ * Qm :=
    evalNatPoly3_cross_ratio_bound qTerms u (u + 2)
      (2 * u + 1) (u * (2 * u + 1)) (2 * u)
      (2 * u + 2) ((u + 1) * (2 * u + 1)) (2 * u + 1)
      (by omega)
      (Nat.mul_le_mul (by omega) (by omega))
      (Nat.mul_le_mul (by omega) (Nat.mul_le_mul_right _ (by omega)))
      (Nat.mul_le_mul (by omega) (by omega))
  have hPm_P2m : u ^ dP * Pm ≤ (u + 2) ^ dP * P2m :=
    evalNatPoly3_cross_ratio_bound pTerms u (u + 2)
      (2 * u + 2) ((u + 1) * (2 * u + 1)) (2 * u + 1)
      (2 * u + 1) ((u + 2) * (2 * u + 1)) (2 * u + 2)
      (by omega) hcx1
      (Nat.mul_le_mul (by omega) (Nat.mul_le_mul_right _ (by omega)))
      (Nat.mul_le_mul (by omega) (by omega))
  have hQ2m_Qm : u ^ dQ * Q2m ≤ (u + 2) ^ dQ * Qm := by
    have hcy_2m : u * ((u + 2) * (2 * u + 1)) ≤ (u + 2) * ((u + 1) * (2 * u + 1)) := by
      have h1 : u * (u + 2) ≤ (u + 2) * (u + 1) := by
        rw [Nat.mul_comm u (u + 2)]
        exact Nat.mul_le_mul_left (u + 2) (by omega)
      rw [← Nat.mul_assoc u (u + 2), ← Nat.mul_assoc (u + 2) (u + 1)]
      exact Nat.mul_le_mul_right _ h1
    have hcz_2m : u * (2 * u + 2) ≤ (u + 2) * (2 * u + 1) := hcx1
    exact evalNatPoly3_cross_ratio_bound qTerms u (u + 2)
      (2 * u + 1) ((u + 2) * (2 * u + 1)) (2 * u + 2)
      (2 * u + 2) ((u + 1) * (2 * u + 1)) (2 * u + 1)
      (by omega)
      (Nat.mul_le_mul (by omega) (by omega))
      hcy_2m hcz_2m
  -- Combine both branches into `2 * u ^ D * (Pm * (Q2m * Qn)) ≤ (u + 2) ^ D * (Pm * (Q2m * Qn))`:
  let DenProd := Pm * (Q2m * Qn)
  have hDen_pos : DenProd ≥ 1 :=
    Nat.mul_le_mul hPm_pos (Nat.mul_le_mul hQ2m_pos hQn_pos)
  have hbr1 : u ^ D * DenProd ≤ (u + 2) ^ D * (P2m * Qn * Qm) := by
    have hm := Nat.mul_le_mul_right Qn (Nat.mul_le_mul hPm_P2m hQ2m_Qm)
    have hl : (u ^ dP * Pm * (u ^ dQ * Q2m)) * Qn = u ^ D * DenProd := by
      dsimp [D, DenProd]
      rw [Nat.pow_add u dP dQ]
      calc
        (u ^ dP * Pm * (u ^ dQ * Q2m)) * Qn
            = (u ^ dP * (Pm * u ^ dQ) * Q2m) * Qn := by
              rw [← Nat.mul_assoc (u ^ dP * Pm) (u ^ dQ) Q2m, Nat.mul_assoc (u ^ dP) Pm (u ^ dQ)]
        _ = (u ^ dP * u ^ dQ) * (Pm * (Q2m * Qn)) := by
              rw [Nat.mul_comm Pm (u ^ dQ), ← Nat.mul_assoc (u ^ dP) (u ^ dQ) Pm,
                  Nat.mul_assoc (u ^ dP * u ^ dQ) Pm Q2m,
                  Nat.mul_assoc (u ^ dP * u ^ dQ) (Pm * Q2m) Qn,
                  Nat.mul_assoc Pm Q2m Qn]
    have hr : ((u + 2) ^ dP * P2m * ((u + 2) ^ dQ * Qm)) * Qn =
        (u + 2) ^ D * (P2m * Qn * Qm) := by
      dsimp [D]
      rw [Nat.pow_add (u + 2) dP dQ]
      calc
        ((u + 2) ^ dP * P2m * ((u + 2) ^ dQ * Qm)) * Qn
            = ((u + 2) ^ dP * (P2m * (u + 2) ^ dQ) * Qm) * Qn := by
              rw [← Nat.mul_assoc ((u + 2) ^ dP * P2m), Nat.mul_assoc ((u + 2) ^ dP) P2m]
        _ = ((u + 2) ^ dP * (u + 2) ^ dQ) * (P2m * Qm * Qn) := by
              rw [Nat.mul_comm P2m ((u + 2) ^ dQ), ← Nat.mul_assoc ((u + 2) ^ dP) ((u + 2) ^ dQ) P2m,
                  Nat.mul_assoc ((u + 2) ^ dP * (u + 2) ^ dQ) P2m Qm,
                  Nat.mul_assoc ((u + 2) ^ dP * (u + 2) ^ dQ) (P2m * Qm) Qn]
        _ = ((u + 2) ^ dP * (u + 2) ^ dQ) * (P2m * Qn * Qm) := by
              rw [Nat.mul_assoc P2m Qm Qn, Nat.mul_comm Qm Qn, ← Nat.mul_assoc P2m Qn Qm]
    rwa [hl, hr] at hm
  have hbr2 : u ^ D * DenProd ≤ (u + 2) ^ D * (Pn * Q2m * Qm) := by
    have hm := Nat.mul_le_mul_right Q2m (Nat.mul_le_mul hPm_Pn hQn_Qm)
    have hl : (u ^ dP * Pm * (u ^ dQ * Qn)) * Q2m = u ^ D * DenProd := by
      dsimp [D, DenProd]
      rw [Nat.pow_add u dP dQ]
      calc
        (u ^ dP * Pm * (u ^ dQ * Qn)) * Q2m
            = (u ^ dP * (Pm * u ^ dQ) * Qn) * Q2m := by
              rw [← Nat.mul_assoc (u ^ dP * Pm) (u ^ dQ) Qn, Nat.mul_assoc (u ^ dP) Pm (u ^ dQ)]
        _ = (u ^ dP * u ^ dQ) * (Pm * Qn * Q2m) := by
              rw [Nat.mul_comm Pm (u ^ dQ), ← Nat.mul_assoc (u ^ dP) (u ^ dQ) Pm,
                  Nat.mul_assoc (u ^ dP * u ^ dQ) Pm Qn,
                  Nat.mul_assoc (u ^ dP * u ^ dQ) (Pm * Qn) Q2m]
        _ = (u ^ dP * u ^ dQ) * (Pm * (Q2m * Qn)) := by
              rw [Nat.mul_assoc Pm Qn Q2m, Nat.mul_comm Qn Q2m]
    have hr : ((u + 2) ^ dP * Pn * ((u + 2) ^ dQ * Qm)) * Q2m =
        (u + 2) ^ D * (Pn * Q2m * Qm) := by
      dsimp [D]
      rw [Nat.pow_add (u + 2) dP dQ]
      calc
        ((u + 2) ^ dP * Pn * ((u + 2) ^ dQ * Qm)) * Q2m
            = ((u + 2) ^ dP * (Pn * (u + 2) ^ dQ) * Qm) * Q2m := by
              rw [← Nat.mul_assoc ((u + 2) ^ dP * Pn), Nat.mul_assoc ((u + 2) ^ dP) Pn]
        _ = ((u + 2) ^ dP * (u + 2) ^ dQ) * (Pn * Qm * Q2m) := by
              rw [Nat.mul_comm Pn ((u + 2) ^ dQ), ← Nat.mul_assoc ((u + 2) ^ dP) ((u + 2) ^ dQ) Pn,
                  Nat.mul_assoc ((u + 2) ^ dP * (u + 2) ^ dQ) Pn Qm,
                  Nat.mul_assoc ((u + 2) ^ dP * (u + 2) ^ dQ) (Pn * Qm) Q2m]
        _ = ((u + 2) ^ dP * (u + 2) ^ dQ) * (Pn * Q2m * Qm) := by
              rw [Nat.mul_assoc Pn Qm Q2m, Nat.mul_comm Qm Q2m, ← Nat.mul_assoc Pn Q2m Qm]
    rwa [hl, hr] at hm
  have hsum_br : 2 * u ^ D * DenProd ≤ (u + 2) ^ D * ((P2m * Qn + Pn * Q2m) * Qm) := by
    have hadd := Nat.add_le_add hbr1 hbr2
    rw [← Nat.two_mul (u ^ D * DenProd), ← Nat.mul_assoc 2 (u ^ D) DenProd] at hadd
    rw [← Nat.mul_add ((u + 2) ^ D), ← Nat.add_mul (P2m * Qn) (Pn * Q2m) Qm] at hadd
    exact hadd
  have htot : (2 * u ^ D) * DenProd ≤ ((u + 2) ^ D) * DenProd :=
    Nat.le_trans hsum_br (Nat.mul_le_mul_left ((u + 2) ^ D) hcanc)
  have h2u_le := nat_mul_le_cancel_right_w5 DenProd (2 * u ^ D) ((u + 2) ^ D) hDen_pos htot
  have hbern_lt := bernoulli_nat_ratio_lt 1 1 D 2 u (by decide) (by decide) (by decide)
    (by dsimp [u]; omega)
  rw [Nat.one_mul, show 1 + 1 = 2 from rfl] at hbern_lt
  omega

-- ----------------------------------------------------------------------------
-- Universal `∀ W_win ≥ 1` Sliding-Window `k`-Gram Transducer Barrier (`W8.3d`)
-- ----------------------------------------------------------------------------

def nonZeroWindowAux (W : Nat) : Nat -> Nat -> List Nat
  | 0, _ => []
  | fuel + 1, n =>
    if n = 0 then []
    else
      let w := n % (2 ^ W)
      let rest := nonZeroWindowAux W fuel (n / 2)
      if w = 0 then rest else w :: rest

def zeroWindowCountAux (W : Nat) : Nat -> Nat -> Nat
  | 0, _ => 0
  | fuel + 1, n =>
    if n = 0 then 0
    else
      (if n % (2 ^ W) = 0 then 1 else 0) + zeroWindowCountAux W fuel (n / 2)

/-- LSB-to-MSB list of non-zero `W`-bit sliding windows `(n / 2^i) % (2^W)` across `0 ≤ i < binBitLength n`. -/
def nonZeroWindowList (W n : Nat) : List Nat :=
  nonZeroWindowAux W n n

/-- Count of `0`-valued `W`-bit sliding windows `(n / 2^i) % (2^W) = 0` across `0 ≤ i < binBitLength n`. -/
def zeroWindowCount (W n : Nat) : Nat :=
  zeroWindowCountAux W n n

/-- Non-separable bivariate polynomial `∑ c * z ^ i * L ^ j` in `(zeroWindowCount W n, binBitLength n)`. -/
abbrev NatPoly2 := List (Nat × Nat × Nat)

def evalNatPoly2 : NatPoly2 -> Nat -> Nat -> Nat
  | [], _, _ => 0
  | (c, i, j) :: rest, z, L => c * z ^ i * L ^ j + evalNatPoly2 rest z L

def maxDegNatPoly2 : NatPoly2 -> Nat
  | [] => 0
  | (c, i, j) :: rest =>
    if c > 0 then Nat.max (i + j) (maxDegNatPoly2 rest) else maxDegNatPoly2 rest

theorem evalNatPoly2_to_3_eq :
    ∀ (P : NatPoly2) (z L : Nat),
      evalNatPoly2 P z L =
        evalNatPoly3 (P.map (fun t => (t.1, t.2.1, t.2.2, 0))) z L 1 ∧
      maxDegNatPoly2 P = maxDegNatPoly3 (P.map (fun t => (t.1, t.2.1, t.2.2, 0)))
  | [], _, _ => ⟨rfl, rfl⟩
  | (c, i, j) :: rest, z, L => by
    rcases evalNatPoly2_to_3_eq rest z L with ⟨ih_e, ih_d⟩
    simp only [List.map_cons, evalNatPoly2, evalNatPoly3, maxDegNatPoly2, maxDegNatPoly3,
      Nat.pow_zero, Nat.mul_one, Nat.add_zero]
    rw [ih_e, ih_d]
    exact ⟨rfl, rfl⟩

theorem nonZeroWindowAux_eq_of_ge (W : Nat) :
    ∀ (f1 f2 n : Nat), n ≤ f1 -> n ≤ f2 ->
      nonZeroWindowAux W f1 n = nonZeroWindowAux W f2 n
  | 0, 0, _, _, _ => rfl
  | 0, _ + 1, n, h1, _ => by rw [show n = 0 by omega]; simp [nonZeroWindowAux]
  | _ + 1, 0, n, _, h2 => by rw [show n = 0 by omega]; simp [nonZeroWindowAux]
  | f1 + 1, f2 + 1, n, h1, h2 => by
    simp only [nonZeroWindowAux]
    by_cases hn0 : n = 0
    · simp [hn0]
    · simp only [hn0, ite_false]
      rw [nonZeroWindowAux_eq_of_ge W f1 f2 (n / 2) (by omega) (by omega)]

theorem zeroWindowCountAux_eq_of_ge (W : Nat) :
    ∀ (f1 f2 n : Nat), n ≤ f1 -> n ≤ f2 ->
      zeroWindowCountAux W f1 n = zeroWindowCountAux W f2 n
  | 0, 0, _, _, _ => rfl
  | 0, _ + 1, n, h1, _ => by rw [show n = 0 by omega]; simp [zeroWindowCountAux]
  | _ + 1, 0, n, _, h2 => by rw [show n = 0 by omega]; simp [zeroWindowCountAux]
  | f1 + 1, f2 + 1, n, h1, h2 => by
    simp only [zeroWindowCountAux]
    by_cases hn0 : n = 0
    · simp [hn0]
    · simp only [hn0, ite_false]
      rw [zeroWindowCountAux_eq_of_ge W f1 f2 (n / 2) (by omega) (by omega)]

theorem window_step_pos (W n : Nat) (hn : n ≥ 1) :
    nonZeroWindowList W n =
      (if n % (2 ^ W) = 0 then nonZeroWindowList W (n / 2)
       else (n % (2 ^ W)) :: nonZeroWindowList W (n / 2)) ∧
    zeroWindowCount W n =
      (if n % (2 ^ W) = 0 then 1 else 0) + zeroWindowCount W (n / 2) := by
  unfold nonZeroWindowList zeroWindowCount
  cases n with
  | zero => omega
  | succ m =>
    simp only [nonZeroWindowAux, zeroWindowCountAux, Nat.succ_ne_zero, ite_false]
    rw [nonZeroWindowAux_eq_of_ge W m ((m + 1) / 2) ((m + 1) / 2) (by omega) (Nat.le_refl _),
        zeroWindowCountAux_eq_of_ge W m ((m + 1) / 2) ((m + 1) / 2) (by omega) (Nat.le_refl _)]
    exact ⟨rfl, rfl⟩

theorem window_pow2_shift_invariance (W H : Nat) (hH : H ≥ 1) :
    ∀ g : Nat,
      nonZeroWindowList W (2 ^ (W + g) * H) = nonZeroWindowList W (2 ^ W * H) ∧
      zeroWindowCount W (2 ^ (W + g) * H) = g + zeroWindowCount W (2 ^ W * H)
  | 0 => ⟨rfl, by simp⟩
  | g + 1 => by
    rcases window_pow2_shift_invariance W H hH g with ⟨ih_nz, ih_z⟩
    have hexp : 2 ^ (W + (g + 1)) * H = 2 * (2 ^ (W + g) * H) := by
      rw [show W + (g + 1) = (W + g) + 1 by omega, Nat.pow_succ, Nat.mul_comm (2 ^ (W + g)) 2, Nat.mul_assoc]
    have hpos : 2 ^ (W + g) * H ≥ 1 := Nat.mul_le_mul (pow2_pos_nat _) hH
    have hm_zero : (2 * (2 ^ (W + g) * H)) % (2 ^ W) = 0 := by
      have hsp : 2 * (2 ^ (W + g) * H) = 2 ^ W * (2 ^ (g + 1) * H) := by
        rw [← hexp, show W + (g + 1) = W + (g + 1) from rfl, Nat.pow_add 2 W (g + 1), Nat.mul_assoc]
      rw [hsp, Nat.mul_mod_right]
    have hdiv : (2 * (2 ^ (W + g) * H)) / 2 = 2 ^ (W + g) * H := by omega
    rcases window_step_pos W (2 * (2 ^ (W + g) * H)) (by omega) with ⟨hs_nz, hs_z⟩
    rw [hexp, hs_nz, hs_z, hm_zero, hdiv]
    simp only [ite_true]
    rw [ih_nz, ih_z]
    exact ⟨rfl, by omega⟩

theorem window_low_pad_peel (W H g : Nat) (hH : H ≥ 1) :
    ∀ (s R : Nat), R < 2 ^ s ->
      nonZeroWindowList W (2 ^ (W + g + s) * H + R) =
        nonZeroWindowList W (2 ^ (W + s) * H + R) ∧
      zeroWindowCount W (2 ^ (W + g + s) * H + R) =
        g + zeroWindowCount W (2 ^ (W + s) * H + R)
  | 0, R, hR => by
    have hR0 : R = 0 := by simp at hR; exact hR
    subst hR0
    simp only [Nat.add_zero]
    exact window_pow2_shift_invariance W H hH g
  | s + 1, R, hR => by
    have hR2 : R / 2 < 2 ^ s := by
      rw [Nat.pow_succ] at hR; omega
    rcases window_low_pad_peel W H g hH s (R / 2) hR2 with ⟨ih_nz, ih_z⟩
    let N1 := 2 ^ (W + g + (s + 1)) * H + R
    let N0 := 2 ^ (W + (s + 1)) * H + R
    have hN1_pos : N1 ≥ 1 := by
      dsimp [N1]; have hp := Nat.mul_le_mul (pow2_pos_nat (W + g + (s + 1))) hH; omega
    have hN0_pos : N0 ≥ 1 := by
      dsimp [N0]; have hp := Nat.mul_le_mul (pow2_pos_nat (W + (s + 1))) hH; omega
    have hmod_eq : N1 % (2 ^ W) = N0 % (2 ^ W) := by
      have hm1 : N1 = R + 2 ^ W * (2 ^ (g + (s + 1)) * H) := by
        dsimp [N1]; rw [show W + g + (s + 1) = W + (g + (s + 1)) by omega,
          Nat.pow_add 2 W, Nat.mul_assoc, Nat.add_comm]
      have hm0 : N0 = R + 2 ^ W * (2 ^ (s + 1) * H) := by
        dsimp [N0]; rw [Nat.pow_add 2 W (s + 1), Nat.mul_assoc, Nat.add_comm]
      rw [hm1, hm0, Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left]
    have hdiv1 : N1 / 2 = 2 ^ (W + g + s) * H + R / 2 := by
      dsimp [N1]
      rw [show W + g + (s + 1) = (W + g + s) + 1 by omega, Nat.pow_succ,
          Nat.mul_comm (2 ^ (W + g + s)) 2, Nat.mul_assoc 2]
      omega
    have hdiv0 : N0 / 2 = 2 ^ (W + s) * H + R / 2 := by
      dsimp [N0]
      rw [show W + (s + 1) = (W + s) + 1 by omega, Nat.pow_succ,
          Nat.mul_comm (2 ^ (W + s)) 2, Nat.mul_assoc 2]
      omega
    rcases window_step_pos W N1 hN1_pos with ⟨hs1_nz, hs1_z⟩
    rcases window_step_pos W N0 hN0_pos with ⟨hs0_nz, hs0_z⟩
    change nonZeroWindowList W N1 = nonZeroWindowList W N0 ∧
      zeroWindowCount W N1 = g + zeroWindowCount W N0
    rw [hs1_nz, hs0_nz, hs1_z, hs0_z, hmod_eq, hdiv1, hdiv0, ih_nz, ih_z]
    refine ⟨rfl, ?_⟩
    by_cases hw0 : N0 % 2 ^ W = 0 <;> simp [hw0] <;> omega

/--
  Theorem W8.3d (`berg_meinardus_sliding_window_kgram_impossibility`, zero custom axioms):
  Universal All-Width (`∀ W_win ≥ 1`) Sliding-Window `k`-Gram Transducer Preimage Impossibility:
  1. Infinite Exact Collision & Affine Zero-Window Family (`∀ W_win ≥ 1, ∀ t : Nat`):
     Along `m(W_win, t) = 3 * 4 ^ (2 * W_win + t) + 2 ^ (2 * W_win + 1)`:
     - `m % 3 = 2`, `nonZeroWindowList W_win m` is **CONSTANT** in `t` and **IDENTICAL** to
       `nonZeroWindowList W_win (2 * m)`, and `nonZeroWindowList W_win ((2 * m - 1) / 3)` is
       **CONSTANT** in `t`!
     - `zeroWindowCount W_win` and `binBitLength` grow with exact affine slope `+ 2 * t`!
  2. Universal Barrier: For EVERY window width `W_win ≥ 1`, ANY arbitrary functions
     `fNum, fDen : List Nat -> Nat` of the ordered `W_win`-bit non-zero window sequence
     `nonZeroWindowList W_win n`, and ANY non-separable bivariate polynomials `pTerms, qTerms : NatPoly2`
     in `(zeroWindowCount W_win n, binBitLength n)`, NO weight
       `w(n) = (fNum (nonZeroWindowList W_win n) * evalNatPoly2 pTerms (zeroWindowCount W_win n) (binBitLength n)) /
               (fDen (nonZeroWindowList W_win n) * evalNatPoly2 qTerms (zeroWindowCount W_win n) (binBitLength n))`
     can satisfy `IsPositiveRationalPreimageWeight`!
-/
theorem berg_meinardus_sliding_window_kgram_impossibility :
    (∀ (W t : Nat), W ≥ 1 ->
      let m0 := 3 * 4 ^ (2 * W) + 2 ^ (2 * W + 1)
      let n0 := (2 * m0 - 1) / 3
      let mt := 3 * 4 ^ (2 * W + t) + 2 ^ (2 * W + 1)
      let nt := (2 * mt - 1) / 3
      mt % 3 = 2 ∧
      nonZeroWindowList W mt = nonZeroWindowList W m0 ∧
      nonZeroWindowList W (2 * mt) = nonZeroWindowList W m0 ∧
      nonZeroWindowList W nt = nonZeroWindowList W n0 ∧
      zeroWindowCount W mt = 2 * t + zeroWindowCount W m0 ∧
      zeroWindowCount W (2 * mt) = 2 * t + zeroWindowCount W m0 + 1 ∧
      zeroWindowCount W nt = 2 * t + zeroWindowCount W n0 ∧
      binBitLength mt = 2 * t + binBitLength m0 ∧
      binBitLength (2 * mt) = 2 * t + binBitLength m0 + 1 ∧
      binBitLength nt = 2 * t + binBitLength n0) ∧
    (∀ (W : Nat) (_hW : W ≥ 1)
       (fNum fDen : List Nat -> Nat)
       (pTerms qTerms : NatPoly2)
       (pTheta qTheta : Nat),
      ¬ IsPositiveRationalPreimageWeight
        (fun n => fNum (nonZeroWindowList W n) * evalNatPoly2 pTerms (zeroWindowCount W n) (binBitLength n))
        (fun n => fDen (nonZeroWindowList W n) * evalNatPoly2 qTerms (zeroWindowCount W n) (binBitLength n))
        pTheta qTheta) := by
  have hfam : ∀ (W t : Nat), W ≥ 1 ->
      let m0 := 3 * 4 ^ (2 * W) + 2 ^ (2 * W + 1)
      let n0 := (2 * m0 - 1) / 3
      let mt := 3 * 4 ^ (2 * W + t) + 2 ^ (2 * W + t - t + 1) -- wait: `2 ^ (2 * W + 1)`!
      True := fun _ _ _ => trivial
  clear hfam
  have hfamily : ∀ (W t : Nat), W ≥ 1 ->
      let m0 := 3 * 4 ^ (2 * W) + 2 ^ (2 * W + 1)
      let n0 := (2 * m0 - 1) / 3
      let mt := 3 * 4 ^ (2 * W + t) + 2 ^ (2 * W + 1)
      let nt := (2 * mt - 1) / 3
      mt % 3 = 2 ∧
      nonZeroWindowList W mt = nonZeroWindowList W m0 ∧
      nonZeroWindowList W (2 * mt) = nonZeroWindowList W m0 ∧
      nonZeroWindowList W nt = nonZeroWindowList W n0 ∧
      zeroWindowCount W mt = 2 * t + zeroWindowCount W m0 ∧
      zeroWindowCount W (2 * mt) = 2 * t + zeroWindowCount W m0 + 1 ∧
      zeroWindowCount W nt = 2 * t + zeroWindowCount W n0 ∧
      binBitLength mt = 2 * t + binBitLength m0 ∧
      binBitLength (2 * mt) = 2 * t + binBitLength m0 + 1 ∧
      binBitLength nt = 2 * t + binBitLength n0 := by
    intro W t hW
    dsimp only
    let R_m := 2 ^ (2 * W + 1)
    let R_n := (4 ^ (W + 1) - 1) / 3
    have h4_m3 : 4 ^ W % 3 = 1 := by
      have hm := (pow4_ge_four_and_mod3_w5 (W - 1)).2
      rwa [show W - 1 + 1 = W by omega] at hm
    have hRm_m3 : R_m % 3 = 2 := by
      dsimp [R_m]
      rw [Nat.pow_succ 2 (2 * W), ← pow4_eq_pow2_even W, Nat.mul_mod, h4_m3]
    let m0 := 3 * 4 ^ (2 * W) + R_m
    let mt := 3 * 4 ^ (2 * W + t) + R_m
    have hmt_m3 : mt % 3 = 2 := by dsimp [mt]; omega
    -- Express `4 ^ (2 * W + t) = 2 ^ (W + 2 * t + (3 * W))` with `s := 2 * W + 2`?
    -- Wait: `4 ^ (2 * W) = 2 ^ (4 * W) = 2 ^ (W + (3 * W))`!
    -- Since `W ≥ 1`, `3 * W ≥ 2 * W + 1`, wait: is `R_m = 2 ^ (2 * W + 1) < 2 ^ (3 * W)`?
    -- Check `W = 1`: `2 * W + 1 = 3`, `3 * W = 3` (`R_m = 8` is NOT `< 8`, at `W = 1` `m0 = 3*16 + 8 = 56 = 2^3 * 7`!).
    -- For ALL `W ≥ 1`, `4 * W = W + (3 * W)` has `3 * W = 2 * W + W`:
    -- Wait: at `W = 1`, `4 ^ (2 * W) = 16 = 2 ^ 4` while `R_m = 2 ^ 3 = 8` — there is NO `W`-bit zero gap inside `m0` at `t = 0` when `W = 1`?
    -- WAIT A SECOND! Check `cs_cegar_redteam.py` line 8320 (`W = 1..7, t = 0..5`)! It PASSED for `W = 1, t = 0`! WHY?!
    -- Because `s := 3 * W`! At `W = 1`, `3 * W = 3`, and `4 ^ (2 * W) = 2 ^ (4 * W) = 2 ^ (W + 3 * W)`!
    -- Wait: at `W = 1`, `R_m = 2 ^ (2 * W + 1) = 2 ^ 3 = 8` has `R_m = 2 ^ (3 * W)`, NOT `< 2 ^ (3 * W)` — why did `W = 1` STILL work at `t = 0`?!
    -- Let's check `W = 1, t = 0` (`56 = 0b111000`) vs `W = 1, t = 1` (`200 = 0b11001000`)!!
    -- For `W = 1`: `2 ^ W = 2`, so `nonZeroWindowList 1 n` is `[1, 1, 1]` (three `1`-bits!) on BOTH `56` AND `200`!!
    -- Whereas for `W ≥ 2`: `2 * W + 1 < 3 * W` (`W ≥ 2 => 2 * W + 1 ≤ 3 * W - 1 < 3 * W`), so **`R_m = 2 ^ (2 * W + 1) < 2 ^ (3 * W)` FOR ALL `W ≥ 2`**!!
    -- AND for `W = 1`: `m0 = 56 = 2 ^ 3 * 7` (`pop1 = 3 -> [1, 1, 1]`, `zeros = 3`, `L = 6`), while for `t ≥ 1`, `mt = 3 * 4 ^ (2 + t) + 8 = 2 ^ (1 + (2 * t - 2) + 4) * 3 + 8` (`8 < 16 = 2^4`!), which has `[1, 1, 1]` and `zeros = 3 + 2 * t = 2 * t + 3`, `L = 6 + 2 * t`!!
    -- WHAT A CATCH!! Checking `W = 1` vs `W ≥ 2` BEFORE compiling saved an impossible inequality `2 ^ 3 < 2 ^ 3` at `W = 1`!
    have hRn_eq : (2 * R_m - 1) / 3 = R_n := by
      dsimp [R_m, R_n]
      rw [show 2 * 2 ^ (2 * W + 1) = 4 ^ (W + 1) by
        rw [Nat.pow_succ 4 W, pow4_eq_pow2_even W, Nat.pow_succ 2 (2 * W)]; omega]
    have h2R_div3 : 3 * R_n = 2 * R_m - 1 := by
      dsimp [R_n, R_m]
      have h4_1 : 4 ^ (W + 1) % 3 = 1 := by
        rw [Nat.pow_succ, Nat.mul_mod, h4_m3]
      have h4_eq : 4 ^ (W + 1) = 2 * 2 ^ (2 * W + 1) := by
        rw [Nat.pow_succ 4 W, pow4_eq_pow2_even W, Nat.pow_succ 2 (2 * W)]; omega
      omega
    have hnt_eq : ∀ u : Nat, (2 * (3 * 4 ^ u + R_m) - 1) / 3 = 2 * 4 ^ u + R_n := by
      intro u; omega
    let n0 := 2 * 4 ^ (2 * W) + R_n
    let nt := 2 * 4 ^ (2 * W + t) + R_n
    rw [hnt_eq (2 * W), hnt_eq (2 * W + t)]
    change mt % 3 = 2 ∧
      nonZeroWindowList W mt = nonZeroWindowList W m0 ∧
      nonZeroWindowList W (2 * mt) = nonZeroWindowList W m0 ∧
      nonZeroWindowList W nt = nonZeroWindowList W n0 ∧
      zeroWindowCount W mt = 2 * t + zeroWindowCount W m0 ∧
      zeroWindowCount W (2 * mt) = 2 * t + zeroWindowCount W m0 + 1 ∧
      zeroWindowCount W nt = 2 * t + zeroWindowCount W n0 ∧
      binBitLength mt = 2 * t + binBitLength m0 ∧
      binBitLength (2 * mt) = 2 * t + binBitLength m0 + 1 ∧
      binBitLength nt = 2 * t + binBitLength n0
    -- Helper for `2 * mt` from `mt` (since `2 ^ W ∣ (2 * mt)` for ALL `W ≥ 1`):
    have h2mt_step : nonZeroWindowList W (2 * mt) = nonZeroWindowList W mt ∧
        zeroWindowCount W (2 * mt) = 1 + zeroWindowCount W mt ∧
        binBitLength (2 * mt) = 1 + binBitLength mt := by
      have hmt_pos : mt ≥ 1 := by
        dsimp [mt, R_m]; have hp := pow2_pos_nat (2 * W + 1); omega
      have h2mt_mod : (2 * mt) % (2 ^ W) = 0 := by
        have hdvd_m : 2 ^ W ∣ mt := by
          dsimp [mt, R_m]
          have h1 : 2 ^ W ∣ 3 * 4 ^ (2 * W + t) := by
            rw [pow4_eq_pow2_even (2 * W + t),
                show 2 * (2 * W + t) = W + (3 * W + 2 * t) by omega,
                Nat.pow_add 2 W]
            exact ⟨3 * 2 ^ (3 * W + 2 * t),
              by rw [← Nat.mul_assoc 3 (2 ^ W), Nat.mul_comm 3 (2 ^ W), Nat.mul_assoc]⟩
          have h2 : 2 ^ W ∣ 2 ^ (2 * W + 1) := by
            rw [show 2 * W + 1 = W + (W + 1) by omega, Nat.pow_add 2 W]
            exact ⟨2 ^ (W + 1), rfl⟩
          exact Nat.dvd_add h1 h2
        rcases hdvd_m with ⟨qm, hqm⟩
        have hmul : 2 * mt = 2 ^ W * (2 * qm) := by
          rw [hqm, ← Nat.mul_assoc 2 (2 ^ W), Nat.mul_comm 2 (2 ^ W), Nat.mul_assoc]
        rw [hmul, Nat.mul_mod_right]
      rcases window_step_pos W (2 * mt) (by omega) with ⟨h_nz, h_z⟩
      rw [h2mt_mod, show (2 * mt) / 2 = mt by omega] at h_nz h_z
      simp only [ite_true] at h_nz h_z
      have hbl2 : binBitLength (2 * mt) = 1 + binBitLength mt := by
        rw [binBitLength_step_pos (2 * mt) (by omega), show (2 * mt) / 2 = mt by omega]
      exact ⟨h_nz, h_z, hbl2⟩
    -- Bit-lengths of `m0, mt, n0, nt` via `binBitLength_of_pow2_sandwich`:
    have hRn_lt : R_n < R_m := by
      have hp := pow2_pos_nat (2 * W + 1)
      dsimp [R_m] at h2R_div3 ⊢
      omega
    have h4_eq_pow2 : ∀ u : Nat, 4 ^ u = 2 ^ (2 * u) := pow4_eq_pow2_even
    have hbl_m_gen : ∀ u : Nat, u ≥ 2 * W ->
        binBitLength (3 * 4 ^ u + R_m) = 2 * u + 2 := by
      intro u hu
      have hRm_le : R_m < 4 ^ u := by
        dsimp [R_m]; rw [h4_eq_pow2 u]
        have hm := pow2_mono_nat (by omega : 2 * W + 2 ≤ 2 * u)
        rw [show 2 * W + 2 = (2 * W + 1) + 1 by omega, Nat.pow_succ] at hm
        have hp := pow2_pos_nat (2 * W + 1); omega
      apply binBitLength_of_pow2_sandwich (2 * u + 1)
      · rw [Nat.pow_succ 2 (2 * u), ← h4_eq_pow2 u]; omega
      · rw [show 2 * u + 1 + 1 = 2 * (u + 1) by omega, ← h4_eq_pow2 (u + 1), Nat.pow_succ 4 u]; omega
    have hbl_n_gen : ∀ u : Nat, u ≥ 2 * W ->
        binBitLength (2 * 4 ^ u + R_n) = 2 * u + 2 := by
      intro u hu
      have hRn_le : R_n < 2 * 4 ^ u := by
        have hRm_le : R_m ≤ 2 * 4 ^ u := by
          dsimp [R_m]
          rw [h4_eq_pow2 u, show 2 * 2 ^ (2 * u) = 2 ^ (2 * u + 1) by rw [Nat.pow_succ, Nat.mul_comm]]
          exact pow2_mono_nat (by omega)
        omega
      apply binBitLength_of_pow2_sandwich (2 * u + 1)
      · rw [Nat.pow_succ 2 (2 * u), ← h4_eq_pow2 u, Nat.mul_comm]; omega
      · rw [show 2 * u + 1 + 1 = 2 * (u + 1) by omega, ← h4_eq_pow2 (u + 1), Nat.pow_succ 4 u]; omega
    have hbl_m0 : binBitLength m0 = 4 * W + 2 := by
      rw [hbl_m_gen (2 * W) (Nat.le_refl _)]; omega
    have hbl_mt : binBitLength mt = 2 * t + (4 * W + 2) := by
      rw [hbl_m_gen (2 * W + t) (by omega)]; omega
    have hbl_n0 : binBitLength n0 = 4 * W + 2 := by
      rw [hbl_n_gen (2 * W) (Nat.le_refl _)]; omega
    have hbl_nt : binBitLength nt = 2 * t + (4 * W + 2) := by
      rw [hbl_n_gen (2 * W + t) (by omega)]; omega
    by_cases hW1 : W = 1
    · -- Case `W = 1`: `t = 0` is trivial; for `t = t' + 1`, peel from `t = 1` (`200` and `133`) and check `t = 1` vs `t = 0` (`56` and `37`) by `decide`!
      subst hW1
      cases t with
      | zero =>
        have hmt0 : mt = m0 := rfl
        have hnt0 : nt = n0 := rfl
        rw [hmt0] at hmt_m3 h2mt_step ⊢
        rw [hnt0]
        refine ⟨hmt_m3, rfl, h2mt_step.1, rfl,
          by simp, by rw [h2mt_step.2.1]; omega, by simp,
          by simp, by rw [h2mt_step.2.2]; omega, by simp⟩
      | succ t' =>
        have hm_pad5 : mt = 2 ^ (1 + 2 * t' + 5) * 3 + 8 := by
          dsimp [mt, R_m]
          rw [show 2 * 1 + (t' + 1) = t' + 3 by omega, h4_eq_pow2 (t' + 3),
              show 2 * (t' + 3) = 1 + 2 * t' + 5 by omega, Nat.mul_comm 3]
        have hn_pad5 : nt = 2 ^ (1 + 2 * t' + 5) * 2 + 5 := by
          dsimp [nt, R_n]
          rw [show 2 * 1 + (t' + 1) = t' + 3 by omega, h4_eq_pow2 (t' + 3),
              show 2 * (t' + 3) = 1 + 2 * t' + 5 by omega, Nat.mul_comm 2]
        rcases window_low_pad_peel 1 3 (2 * t') (by decide) 5 8 (by decide) with ⟨h_nzm, h_zm⟩
        rcases window_low_pad_peel 1 2 (2 * t') (by decide) 5 5 (by decide) with ⟨h_nzn, h_zn⟩
        rw [← hm_pad5, show 2 ^ (1 + 5) * 3 + 8 = 200 from rfl] at h_nzm h_zm
        rw [← hn_pad5, show 2 ^ (1 + 5) * 2 + 5 = 133 from rfl] at h_nzn h_zn
        have hm0_val : m0 = 56 := rfl
        have hn0_val : n0 = 37 := rfl
        have hb_200_56 : nonZeroWindowList 1 200 = nonZeroWindowList 1 56 ∧
            zeroWindowCount 1 200 = 2 + zeroWindowCount 1 56 := by decide
        have hb_133_37 : nonZeroWindowList 1 133 = nonZeroWindowList 1 37 ∧
            zeroWindowCount 1 133 = 2 + zeroWindowCount 1 37 := by decide
        exact ⟨hmt_m3,
               h_nzm.trans (hb_200_56.1.trans (by rw [hm0_val])),
               h2mt_step.1.trans (h_nzm.trans (hb_200_56.1.trans (by rw [hm0_val]))),
               h_nzn.trans (hb_133_37.1.trans (by rw [hn0_val])),
               by rw [h_zm, hb_200_56.2, hm0_val]; omega,
               by rw [h2mt_step.2.1, h_zm, hb_200_56.2, hm0_val]; omega,
               by rw [h_zn, hb_133_37.2, hn0_val]; omega,
               by rw [hbl_mt, hbl_m0],
               by rw [h2mt_step.2.2, hbl_mt, hbl_m0]; omega,
               by rw [hbl_nt, hbl_n0]⟩
    · -- Case `W ≥ 2`: `2 * W + 1 < 3 * W`, so peel `g = 2 * t` directly with `s = 3 * W`!
      have hW2 : W ≥ 2 := by omega
      have hRm_lt_s : R_m < 2 ^ (3 * W) := by
        dsimp [R_m]
        have hm := pow2_mono_nat (by omega : 2 * W + 2 ≤ 3 * W)
        rw [show 2 * W + 2 = (2 * W + 1) + 1 by omega, Nat.pow_succ] at hm
        have hp := pow2_pos_nat (2 * W + 1); omega
      have hRn_lt_s : R_n < 2 ^ (3 * W) := Nat.lt_trans hRn_lt hRm_lt_s
      have hm_pad : mt = 2 ^ (W + 2 * t + 3 * W) * 3 + R_m := by
        dsimp [mt]
        rw [h4_eq_pow2 (2 * W + t), show 2 * (2 * W + t) = W + 2 * t + 3 * W by omega, Nat.mul_comm 3]
      have hm0_pad : m0 = 2 ^ (W + 3 * W) * 3 + R_m := by
        dsimp [m0]
        rw [h4_eq_pow2 (2 * W), show 2 * (2 * W) = W + 3 * W by omega, Nat.mul_comm 3]
      have hn_pad : nt = 2 ^ (W + 2 * t + 3 * W) * 2 + R_n := by
        dsimp [nt]
        rw [h4_eq_pow2 (2 * W + t), show 2 * (2 * W + t) = W + 2 * t + 3 * W by omega, Nat.mul_comm 2]
      have hn0_pad : n0 = 2 ^ (W + 3 * W) * 2 + R_n := by
        dsimp [n0]
        rw [h4_eq_pow2 (2 * W), show 2 * (2 * W) = W + 3 * W by omega, Nat.mul_comm 2]
      rcases window_low_pad_peel W 3 (2 * t) (by decide) (3 * W) R_m hRm_lt_s with ⟨h_nzm, h_zm⟩
      rcases window_low_pad_peel W 2 (2 * t) (by decide) (3 * W) R_n hRn_lt_s with ⟨h_nzn, h_zn⟩
      rw [← hm_pad, ← hm0_pad] at h_nzm h_zm
      rw [← hn_pad, ← hn0_pad] at h_nzn h_zn
      exact ⟨hmt_m3, h_nzm, h2mt_step.1.trans h_nzm, h_nzn,
             h_zm, by rw [h2mt_step.2.1, h_zm]; omega, h_zn,
             by rw [hbl_mt, hbl_m0],
             by rw [h2mt_step.2.2, hbl_mt, hbl_m0]; omega,
             by rw [hbl_nt, hbl_n0]⟩
  refine ⟨hfamily, ?_⟩
  -- Part 2: Universal `∀ W_win ≥ 1` non-separable sliding-window preimage impossibility:
  intro W hW fNum fDen pTerms qTerms pTheta qTheta hw
  let m0 := 3 * 4 ^ (2 * W) + 2 ^ (2 * W + 1)
  let n0 := (2 * m0 - 1) / 3
  let aE := fNum (nonZeroWindowList W m0)
  let bE := fDen (nonZeroWindowList W m0)
  let aO := fNum (nonZeroWindowList W n0)
  let bO := fDen (nonZeroWindowList W n0)
  -- Establish `aE, bE, aO, bO ≥ 1` from `t = 0`:
  have hp2_2W1 : 2 ^ (2 * W + 1) ≥ 1 := pow2_pos_nat (2 * W + 1)
  have hm0_ge3 : m0 ≥ 3 := by
    have h4 := nat_pow_pos_of_pos 4 (by decide) (2 * W)
    dsimp [m0]; omega
  have hn0_ge3 : n0 ≥ 3 := by
    have h4 : 4 ^ (2 * W) ≥ 16 := by
      have hm := nat_pow_mono_exp_pos 4 2 (2 * W) (by decide) (by omega); simpa using hm
    dsimp [n0, m0]; omega
  rcases hw.2.2.1 m0 hm0_ge3 with ⟨hnum_m0, hden_m0⟩
  rcases hw.2.2.1 n0 hn0_ge3 with ⟨hnum_n0, hden_n0⟩
  dsimp only at hnum_m0 hden_m0 hnum_n0 hden_n0
  have haE_pos : aE ≥ 1 := (pos_factors_of_mul_pos _ _ hnum_m0).1
  have hbE_pos : bE ≥ 1 := (pos_factors_of_mul_pos _ _ hden_m0).1
  have haO_pos : aO ≥ 1 := (pos_factors_of_mul_pos _ _ hnum_n0).1
  have hbO_pos : bO ≥ 1 := (pos_factors_of_mul_pos _ _ hden_n0).1
  let dP := maxDegNatPoly2 pTerms
  let dQ := maxDegNatPoly2 qTerms
  let D := dP + dQ
  let Zm0 := zeroWindowCount W m0
  let Zn0 := zeroWindowCount W n0
  let Lm0 := binBitLength m0
  let Ln0 := binBitLength n0
  let C := Zm0 + Zn0 + Lm0 + Ln0 + 2
  have hC_pos : C ≥ 1 := by dsimp [C]; omega
  let A_b := aO * bE
  let B_b := aE * bO
  have hAb_pos : A_b ≥ 1 := Nat.mul_le_mul haO_pos hbE_pos
  have hBb_pos : B_b ≥ 1 := Nat.mul_le_mul haE_pos hbO_pos
  let t := (B_b + A_b + 1) * (D * C + 1) + 1
  let X := 2 * t
  have hX_ge : X ≥ (B_b + A_b + 1) * (D * C + 1) := by dsimp [X, t]; omega
  rcases hfamily W t hW with
    ⟨hmt_m3, hnz_mt, hnz_2mt, hnz_nt, hz_mt, hz_2mt, hz_nt, hbl_mt, hbl_2mt, hbl_nt⟩
  let mt := 3 * 4 ^ (2 * W + t) + 2 ^ (2 * W + 1)
  let nt := (2 * mt - 1) / 3
  have hmt_ge3 : mt ≥ 3 := by
    have h4 := nat_pow_pos_of_pos 4 (by decide) (2 * W + t)
    dsimp [mt]; omega
  have hnt_ge3 : nt ≥ 3 := by
    have h4 : 4 ^ (2 * W + t) ≥ 16 := by
      have hm := nat_pow_mono_exp_pos 4 2 (2 * W + t) (by decide) (by omega); simpa using hm
    dsimp [nt, mt]; omega
  have hpre := hw.2.2.2.2 mt hmt_ge3 hmt_m3
  dsimp only at hpre
  change qTheta *
    ((fNum (nonZeroWindowList W (2 * mt)) * evalNatPoly2 pTerms (zeroWindowCount W (2 * mt)) (binBitLength (2 * mt)) *
        (fDen (nonZeroWindowList W nt) * evalNatPoly2 qTerms (zeroWindowCount W nt) (binBitLength nt)) +
      fNum (nonZeroWindowList W nt) * evalNatPoly2 pTerms (zeroWindowCount W nt) (binBitLength nt) *
        (fDen (nonZeroWindowList W (2 * mt)) * evalNatPoly2 qTerms (zeroWindowCount W (2 * mt)) (binBitLength (2 * mt)))) *
      (fDen (nonZeroWindowList W mt) * evalNatPoly2 qTerms (zeroWindowCount W mt) (binBitLength mt))) ≤
    pTheta *
      (fNum (nonZeroWindowList W mt) * evalNatPoly2 pTerms (zeroWindowCount W mt) (binBitLength mt) *
        (fDen (nonZeroWindowList W (2 * mt)) * evalNatPoly2 qTerms (zeroWindowCount W (2 * mt)) (binBitLength (2 * mt)) *
          (fDen (nonZeroWindowList W nt) * evalNatPoly2 qTerms (zeroWindowCount W nt) (binBitLength nt)))) at hpre
  rw [hnz_mt, hnz_2mt, hnz_nt] at hpre
  have hcanc := nat_mul_le_cancel_left_w5 qTheta _ _
    (Nat.lt_of_lt_of_le hw.1 hw.2.1)
    (Nat.le_trans hpre (Nat.mul_le_mul_right _ hw.2.1))
  let P_m := evalNatPoly2 pTerms (zeroWindowCount W mt) (binBitLength mt)
  let Q_m := evalNatPoly2 qTerms (zeroWindowCount W mt) (binBitLength mt)
  let P_2m := evalNatPoly2 pTerms (zeroWindowCount W (2 * mt)) (binBitLength (2 * mt))
  let Q_2m := evalNatPoly2 qTerms (zeroWindowCount W (2 * mt)) (binBitLength (2 * mt))
  let P_n := evalNatPoly2 pTerms (zeroWindowCount W nt) (binBitLength nt)
  let Q_n := evalNatPoly2 qTerms (zeroWindowCount W nt) (binBitLength nt)
  change ((aE * P_2m) * (bO * Q_n) + (aO * P_n) * (bE * Q_2m)) * (bE * Q_m) ≤
    (aE * P_m) * ((bE * Q_2m) * (bO * Q_n)) at hcanc
  -- Positivity of `P_m, Q_2m, Q_n`:
  rcases hw.2.2.1 mt hmt_ge3 with ⟨hnum_mt, _⟩
  rcases hw.2.2.1 (2 * mt) (by omega) with ⟨_, hden_2mt⟩
  rcases hw.2.2.1 nt hnt_ge3 with ⟨_, hden_nt⟩
  dsimp only at hnum_mt hden_2mt hden_nt
  have hPm_pos : P_m ≥ 1 := (pos_factors_of_mul_pos _ _ hnum_mt).2
  have hQ2m_pos : Q_2m ≥ 1 := (pos_factors_of_mul_pos _ _ hden_2mt).2
  have hQn_pos : Q_n ≥ 1 := (pos_factors_of_mul_pos _ _ hden_nt).2
  -- Universal `[X, X + C]` sandwich for `evalNatPoly2`:
  have hpoly2_sand : ∀ (F : NatPoly2) (z1 L1 z2 L2 : Nat),
      X ≤ z1 -> z1 ≤ X + C -> X ≤ L1 -> L1 ≤ X + C ->
      X ≤ z2 -> z2 ≤ X + C -> X ≤ L2 -> L2 ≤ X + C ->
      X ^ (maxDegNatPoly2 F) * evalNatPoly2 F z1 L1 ≤
        (X + C) ^ (maxDegNatPoly2 F) * evalNatPoly2 F z2 L2 := by
    intro F z1 L1 z2 L2 hz1_lo hz1_hi hL1_lo hL1_hi hz2_lo _ hL2_lo _
    rcases evalNatPoly2_to_3_eq F z1 L1 with ⟨he1, hd1⟩
    rcases evalNatPoly2_to_3_eq F z2 L2 with ⟨he2, _⟩
    rw [he1, he2, hd1]
    apply evalNatPoly3_cross_ratio_bound _ X (X + C) z1 L1 1 z2 L2 1 (by omega)
    · exact Nat.le_trans (Nat.mul_le_mul_left X hz1_hi)
        (by rw [Nat.mul_comm X (X + C)]; exact Nat.mul_le_mul_left (X + C) hz2_lo)
    · exact Nat.le_trans (Nat.mul_le_mul_left X hL1_hi)
        (by rw [Nat.mul_comm X (X + C)]; exact Nat.mul_le_mul_left (X + C) hL2_lo)
    · omega
  have hb_mt : X ≤ zeroWindowCount W mt ∧ zeroWindowCount W mt ≤ X + C ∧
      X ≤ binBitLength mt ∧ binBitLength mt ≤ X + C := by
    rw [hz_mt, hbl_mt]; dsimp [X, C, Zm0, Zn0, Lm0, Ln0, m0, n0]; exact ⟨by omega, by omega, by omega, by omega⟩
  have hb_2mt : X ≤ zeroWindowCount W (2 * mt) ∧ zeroWindowCount W (2 * mt) ≤ X + C ∧
      X ≤ binBitLength (2 * mt) ∧ binBitLength (2 * mt) ≤ X + C := by
    rw [hz_2mt, hbl_2mt]; dsimp [X, C, Zm0, Zn0, Lm0, Ln0, m0, n0]; exact ⟨by omega, by omega, by omega, by omega⟩
  have hb_nt : X ≤ zeroWindowCount W nt ∧ zeroWindowCount W nt ≤ X + C ∧
      X ≤ binBitLength nt ∧ binBitLength nt ≤ X + C := by
    rw [hz_nt, hbl_nt]; dsimp [X, C, Zm0, Zn0, Lm0, Ln0, m0, n0]; exact ⟨by omega, by omega, by omega, by omega⟩
  have hPm_P2m : X ^ dP * P_m ≤ (X + C) ^ dP * P_2m :=
    hpoly2_sand pTerms _ _ _ _ hb_mt.1 hb_mt.2.1 hb_mt.2.2.1 hb_mt.2.2.2
      hb_2mt.1 hb_2mt.2.1 hb_2mt.2.2.1 hb_2mt.2.2.2
  have hQ2m_Qm : X ^ dQ * Q_2m ≤ (X + C) ^ dQ * Q_m :=
    hpoly2_sand qTerms _ _ _ _ hb_2mt.1 hb_2mt.2.1 hb_2mt.2.2.1 hb_2mt.2.2.2
      hb_mt.1 hb_mt.2.1 hb_mt.2.2.1 hb_mt.2.2.2
  have hPm_Pn : X ^ dP * P_m ≤ (X + C) ^ dP * P_n :=
    hpoly2_sand pTerms _ _ _ _ hb_mt.1 hb_mt.2.1 hb_mt.2.2.1 hb_mt.2.2.2
      hb_nt.1 hb_nt.2.1 hb_nt.2.2.1 hb_nt.2.2.2
  have hQn_Qm : X ^ dQ * Q_n ≤ (X + C) ^ dQ * Q_m :=
    hpoly2_sand qTerms _ _ _ _ hb_nt.1 hb_nt.2.1 hb_nt.2.2.1 hb_nt.2.2.2
      hb_mt.1 hb_mt.2.1 hb_mt.2.2.1 hb_mt.2.2.2
  let K_den := bE * (P_m * (Q_2m * Q_n))
  have hK_pos : K_den ≥ 1 :=
    Nat.mul_le_mul hbE_pos (Nat.mul_le_mul hPm_pos (Nat.mul_le_mul hQ2m_pos hQn_pos))
  -- Factor `hcanc` rhs as `B_b * K_den`:
  have hrhs_f : (aE * P_m) * ((bE * Q_2m) * (bO * Q_n)) = B_b * K_den := by
    dsimp [B_b, K_den]
    calc
      (aE * P_m) * ((bE * Q_2m) * (bO * Q_n))
          = aE * (P_m * ((bE * bO) * (Q_2m * Q_n))) := by
            have hmid : (bE * Q_2m) * (bO * Q_n) = (bE * bO) * (Q_2m * Q_n) := by
              rw [Nat.mul_assoc bE Q_2m, ← Nat.mul_assoc Q_2m bO Q_n,
                  Nat.mul_comm Q_2m bO, Nat.mul_assoc bO Q_2m Q_n, ← Nat.mul_assoc bE bO]
            rw [hmid, Nat.mul_assoc aE P_m]
      _ = (aE * bO) * (bE * (P_m * (Q_2m * Q_n))) := by
            have hinner : P_m * ((bE * bO) * (Q_2m * Q_n)) = bO * (bE * (P_m * (Q_2m * Q_n))) := by
              rw [Nat.mul_comm bE bO, Nat.mul_assoc bO bE (Q_2m * Q_n),
                  ← Nat.mul_assoc P_m bO (bE * (Q_2m * Q_n)),
                  Nat.mul_comm P_m bO, Nat.mul_assoc bO P_m (bE * (Q_2m * Q_n)),
                  ← Nat.mul_assoc P_m bE (Q_2m * Q_n), Nat.mul_comm P_m bE,
                  Nat.mul_assoc bE P_m (Q_2m * Q_n)]
            rw [hinner, ← Nat.mul_assoc aE bO]
  have hbr1 : B_b * X ^ D * K_den ≤ (X + C) ^ D * (((aE * P_2m) * (bO * Q_n)) * (bE * Q_m)) := by
    have hm := Nat.mul_le_mul_left B_b
      (Nat.mul_le_mul_right (bE * Q_n) (Nat.mul_le_mul hPm_P2m hQ2m_Qm))
    have hl : B_b * ((X ^ dP * P_m * (X ^ dQ * Q_2m)) * (bE * Q_n)) = B_b * X ^ D * K_den := by
      dsimp [D, K_den]
      rw [Nat.pow_add X dP dQ, Nat.mul_assoc B_b]
      apply congrArg (B_b * ·)
      calc
        (X ^ dP * P_m * (X ^ dQ * Q_2m)) * (bE * Q_n)
            = (X ^ dP * X ^ dQ) * (P_m * Q_2m) * (bE * Q_n) := by
              rw [← Nat.mul_assoc (X ^ dP * P_m), Nat.mul_assoc (X ^ dP) P_m (X ^ dQ),
                  Nat.mul_comm P_m (X ^ dQ), ← Nat.mul_assoc (X ^ dP) (X ^ dQ) P_m,
                  Nat.mul_assoc (X ^ dP * X ^ dQ) P_m Q_2m]
        _ = (X ^ dP * X ^ dQ) * (bE * (P_m * (Q_2m * Q_n))) := by
              rw [Nat.mul_assoc (X ^ dP * X ^ dQ)]
              apply congrArg ((X ^ dP * X ^ dQ) * ·)
              rw [← Nat.mul_assoc (P_m * Q_2m) bE Q_n, Nat.mul_comm (P_m * Q_2m) bE,
                  Nat.mul_assoc bE (P_m * Q_2m) Q_n, Nat.mul_assoc P_m Q_2m Q_n]
    have hr : B_b * (((X + C) ^ dP * P_2m * ((X + C) ^ dQ * Q_m)) * (bE * Q_n)) =
        (X + C) ^ D * (((aE * P_2m) * (bO * Q_n)) * (bE * Q_m)) := by
      dsimp [D, B_b]
      rw [Nat.pow_add (X + C) dP dQ]
      calc
        (aE * bO) * (((X + C) ^ dP * P_2m * ((X + C) ^ dQ * Q_m)) * (bE * Q_n))
            = (aE * bO) * (((X + C) ^ dP * (X + C) ^ dQ) * (P_2m * Q_m * (bE * Q_n))) := by
              apply congrArg ((aE * bO) * ·)
              rw [← Nat.mul_assoc ((X + C) ^ dP * P_2m),
                  Nat.mul_assoc ((X + C) ^ dP) P_2m ((X + C) ^ dQ),
                  Nat.mul_comm P_2m ((X + C) ^ dQ),
                  ← Nat.mul_assoc ((X + C) ^ dP) ((X + C) ^ dQ) P_2m,
                  Nat.mul_assoc ((X + C) ^ dP * (X + C) ^ dQ) P_2m Q_m,
                  Nat.mul_assoc ((X + C) ^ dP * (X + C) ^ dQ)]
        _ = ((X + C) ^ dP * (X + C) ^ dQ) * ((aE * bO) * (P_2m * Q_m * (bE * Q_n))) := by
              rw [← Nat.mul_assoc (aE * bO), Nat.mul_comm (aE * bO) ((X + C) ^ dP * (X + C) ^ dQ),
                  Nat.mul_assoc]
        _ = ((X + C) ^ dP * (X + C) ^ dQ) * (((aE * P_2m) * (bO * Q_n)) * (bE * Q_m)) := by
              apply congrArg (((X + C) ^ dP * (X + C) ^ dQ) * ·)
              have h1 : P_2m * Q_m * (bE * Q_n) = P_2m * Q_n * (bE * Q_m) := by
                rw [Nat.mul_assoc P_2m Q_m, ← Nat.mul_assoc Q_m bE Q_n,
                    Nat.mul_comm (Q_m * bE) Q_n, Nat.mul_comm Q_m bE,
                    ← Nat.mul_assoc P_2m Q_n]
              have h2 : (aE * bO) * (P_2m * Q_n) = (aE * P_2m) * (bO * Q_n) := by
                rw [Nat.mul_assoc aE bO, ← Nat.mul_assoc bO P_2m Q_n,
                    Nat.mul_comm bO P_2m, Nat.mul_assoc P_2m bO Q_n, ← Nat.mul_assoc aE P_2m]
              rw [h1, ← Nat.mul_assoc (aE * bO) (P_2m * Q_n), h2]
    rwa [hl, hr] at hm
  have hbr2 : A_b * X ^ D * K_den ≤ (X + C) ^ D * (((aO * P_n) * (bE * Q_2m)) * (bE * Q_m)) := by
    have hm := Nat.mul_le_mul_left A_b
      (Nat.mul_le_mul_right (bE * Q_2m) (Nat.mul_le_mul hPm_Pn hQn_Qm))
    have hl : A_b * ((X ^ dP * P_m * (X ^ dQ * Q_n)) * (bE * Q_2m)) = A_b * X ^ D * K_den := by
      dsimp [D, K_den]
      rw [Nat.pow_add X dP dQ, Nat.mul_assoc A_b]
      apply congrArg (A_b * ·)
      calc
        (X ^ dP * P_m * (X ^ dQ * Q_n)) * (bE * Q_2m)
            = (X ^ dP * X ^ dQ) * (P_m * Q_n) * (bE * Q_2m) := by
              rw [← Nat.mul_assoc (X ^ dP * P_m), Nat.mul_assoc (X ^ dP) P_m (X ^ dQ),
                  Nat.mul_comm P_m (X ^ dQ), ← Nat.mul_assoc (X ^ dP) (X ^ dQ) P_m,
                  Nat.mul_assoc (X ^ dP * X ^ dQ) P_m Q_n]
        _ = (X ^ dP * X ^ dQ) * (bE * (P_m * (Q_2m * Q_n))) := by
              rw [Nat.mul_assoc (X ^ dP * X ^ dQ)]
              apply congrArg ((X ^ dP * X ^ dQ) * ·)
              rw [← Nat.mul_assoc (P_m * Q_n) bE Q_2m, Nat.mul_comm (P_m * Q_n) bE,
                  Nat.mul_assoc bE (P_m * Q_n) Q_2m, Nat.mul_assoc P_m Q_n Q_2m,
                  Nat.mul_comm Q_n Q_2m]
    have hr : A_b * (((X + C) ^ dP * P_n * ((X + C) ^ dQ * Q_m)) * (bE * Q_2m)) =
        (X + C) ^ D * (((aO * P_n) * (bE * Q_2m)) * (bE * Q_m)) := by
      dsimp [D, A_b]
      rw [Nat.pow_add (X + C) dP dQ]
      calc
        (aO * bE) * (((X + C) ^ dP * P_n * ((X + C) ^ dQ * Q_m)) * (bE * Q_2m))
            = (aO * bE) * (((X + C) ^ dP * (X + C) ^ dQ) * (P_n * Q_m * (bE * Q_2m))) := by
              apply congrArg ((aO * bE) * ·)
              rw [← Nat.mul_assoc ((X + C) ^ dP * P_n),
                  Nat.mul_assoc ((X + C) ^ dP) P_n ((X + C) ^ dQ),
                  Nat.mul_comm P_n ((X + C) ^ dQ),
                  ← Nat.mul_assoc ((X + C) ^ dP) ((X + C) ^ dQ) P_n,
                  Nat.mul_assoc ((X + C) ^ dP * (X + C) ^ dQ) P_n Q_m,
                  Nat.mul_assoc ((X + C) ^ dP * (X + C) ^ dQ)]
        _ = ((X + C) ^ dP * (X + C) ^ dQ) * ((aO * bE) * (P_n * Q_m * (bE * Q_2m))) := by
              rw [← Nat.mul_assoc (aO * bE), Nat.mul_comm (aO * bE) ((X + C) ^ dP * (X + C) ^ dQ),
                  Nat.mul_assoc]
        _ = ((X + C) ^ dP * (X + C) ^ dQ) * (((aO * P_n) * (bE * Q_2m)) * (bE * Q_m)) := by
              apply congrArg (((X + C) ^ dP * (X + C) ^ dQ) * ·)
              have h1 : P_n * Q_m * (bE * Q_2m) = P_n * (bE * Q_2m) * Q_m := by
                rw [Nat.mul_assoc P_n Q_m, Nat.mul_comm Q_m (bE * Q_2m), ← Nat.mul_assoc P_n]
              have ha : aO * bE * P_n = aO * P_n * bE := by
                rw [Nat.mul_assoc aO bE P_n, Nat.mul_comm bE P_n, ← Nat.mul_assoc aO P_n bE]
              have hb : bE * (bE * Q_2m) * Q_m = (bE * Q_2m) * (bE * Q_m) := by
                rw [Nat.mul_comm bE (bE * Q_2m), Nat.mul_assoc (bE * Q_2m) bE Q_m]
              rw [h1, ← Nat.mul_assoc (aO * bE) (P_n * (bE * Q_2m)) Q_m,
                  ← Nat.mul_assoc (aO * bE) P_n (bE * Q_2m), ha,
                  Nat.mul_assoc (aO * P_n) bE (bE * Q_2m),
                  Nat.mul_assoc (aO * P_n) (bE * (bE * Q_2m)) Q_m,
                  hb, ← Nat.mul_assoc (aO * P_n) (bE * Q_2m) (bE * Q_m)]
    rwa [hl, hr] at hm
  have hsum := Nat.add_le_add hbr1 hbr2
  rw [← Nat.add_mul (B_b * X ^ D) (A_b * X ^ D) K_den,
      ← Nat.add_mul B_b A_b (X ^ D),
      ← Nat.mul_add ((X + C) ^ D),
      ← Nat.add_mul ((aE * P_2m) * (bO * Q_n)) ((aO * P_n) * (bE * Q_2m)) (bE * Q_m)] at hsum
  have htot : ((B_b + A_b) * X ^ D) * K_den ≤ (B_b * (X + C) ^ D) * K_den := by
    have hm := Nat.mul_le_mul_left ((X + C) ^ D) hcanc
    rw [hrhs_f, ← Nat.mul_assoc ((X + C) ^ D) B_b K_den,
        Nat.mul_comm ((X + C) ^ D) B_b] at hm
    exact Nat.le_trans hsum hm
  have hle_b := nat_mul_le_cancel_right_w5 K_den _ _ hK_pos htot
  have hlt_b := bernoulli_nat_ratio_lt A_b B_b D C X hAb_pos hBb_pos hC_pos hX_ge
  omega

-- ============================================================================
-- SECTION 3C: Front C (Branch P5) — 5th Solvable Mixed-(2,3) Cousin `T_diamond5`:
--             Genuine `v_2(3x + 1) = 3` (`/ 8`) Jump Into `Cone 5` Spiral Climb,
--             3-Tier `ω^3` Global Convergence, & `M1 / M2 / M3` Separation
-- ============================================================================

/-- Cone 6 of `T_diamond5`: `x + 19 = 2 ^ e * 3 ^ f` with `e ≥ 8, f ≥ 2` (starting at `x = 2285`). -/
def isDiamond5Cone6 (x : Nat) : Prop :=
  x ≥ 2285 ∧ x % 256 = 237 ∧ x % 9 = 8 ∧ coprime23Core (x + 19) = 1

instance (x : Nat) : Decidable (isDiamond5Cone6 x) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/--
  5th solvable mixed-(2,3) Collatz cousin `T_diamond5` on `Nat`:
  Extends `T_diamond4` by adding Cone 6 (`isDiamond5Cone6 x -> (3 * x + 1) / 8`, a genuine
  `v_2(3x + 1) = 3` Syracuse jump that steps `2 ^ e * 3 ^ f - 19 -> 2 ^ (e - 3) * 3 ^ (f + 1) - 7`
  upward in `Φ_diamond2` directly into Cone 5's unbounded `r`-block spiral climb, e.g.
  `2285 -> 857` and `73709 -> 27641 -> 1019 ...`, while converging globally to `1`)!
-/
def cousinDiamond5Step (x : Nat) : Nat :=
  if isDiamond5Cone6 x then (3 * x + 1) / 8 else cousinDiamond4Step x

def cousinDiamond5Iter : Nat -> Nat -> Nat
  | 0, x => x
  | k + 1, x => cousinDiamond5Iter k (cousinDiamond5Step x)

theorem cousinDiamond5Iter_add : ∀ (a b x : Nat),
    cousinDiamond5Iter (a + b) x = cousinDiamond5Iter b (cousinDiamond5Iter a x)
  | 0, _, _ => by simp [cousinDiamond5Iter]
  | a + 1, b, x => by
    rw [Nat.succ_add]
    exact cousinDiamond5Iter_add a b (cousinDiamond5Step x)

/-- Signed extension of `T_diamond5` (`q = 3`) to `Int` for `M2 = Z^-` separation. -/
def cousinDiamond5StepInt (x : Int) : Int :=
  if x ≥ 2285 ∧ x % 256 = 237 ∧ x % 9 = 8 ∧ coprime23Core (x.toNat + 19) = 1
  then (3 * x + 1) / 8
  else cousinDiamond4StepInt x

def cousinDiamond5IterInt : Nat -> Int -> Int
  | 0, x => x
  | k + 1, x => cousinDiamond5IterInt k (cousinDiamond5StepInt x)

/-- Hensel lift of `invMod64Odd` to `mod 256` (`(d * invMod256Odd d) % 256 = 1` for odd `d`). -/
def invMod256Odd (d : Nat) : Nat :=
  let i64 := invMod64Odd d
  (i64 * (258 - ((d % 256) * i64) % 256)) % 256

/-- Canonical reduced-pair extension of `T_diamond5` (`q = 3`) to positive `Q_(6)^+`. -/
def cousinDiamond5StepQ6 (p : Nat × Nat) : Nat × Nat :=
  let num := p.1
  let den := p.2
  let r256 := (num * invMod256Odd den) % 256
  let r9 := (num * ((den % 9) ^ 5 % 9)) % 9
  if num ≥ 2285 * den ∧ r256 = 237 ∧ r9 = 8 ∧ core3 (core2 (num + 19 * den)) = den
  then reduceRatPair (3 * num + den) (8 * den)
  else cousinDiamond4StepQ6 p

def cousinDiamond5IterQ6 : Nat -> (Nat × Nat) -> (Nat × Nat)
  | 0, p => p
  | k + 1, p => cousinDiamond5IterQ6 k (cousinDiamond5StepQ6 p)

/-- Generalized odd-multiplier `q` step of `T_diamond5` on `Nat` for `M3` (`q = 7`) separation. -/
def cousinDiamond5StepParam (q x : Nat) : Nat :=
  if isDiamond5Cone6 x then (q * x + 1) / 8 else cousinDiamond4StepParam q x

def cousinDiamond5IterParam (q : Nat) : Nat -> Nat -> Nat
  | 0, x => x
  | k + 1, x => cousinDiamond5IterParam q k (cousinDiamond5StepParam q x)

/-- Exact `Nat`/`Int` step agreement for `T_diamond5` (zero custom axioms). -/
theorem cousinDiamond5StepInt_ofNat_eq (x : Nat) :
    cousinDiamond5StepInt (x : Int) = (cousinDiamond5Step x : Int) := by
  unfold cousinDiamond5StepInt cousinDiamond5Step isDiamond5Cone6
  have htoNat : (x : Int).toNat = x := rfl
  rw [htoNat]
  by_cases hc6 : x ≥ 2285 ∧ x % 256 = 237 ∧ x % 9 = 8 ∧ coprime23Core (x + 19) = 1
  · have hc6_i : (x : Int) ≥ 2285 ∧ (x : Int) % 256 = 237 ∧ (x : Int) % 9 = 8 ∧
        coprime23Core (x + 19) = 1 :=
      ⟨by omega, by omega, by omega, hc6.2.2.2⟩
    simp only [hc6_i, hc6, and_self, ite_true]
    omega
  · have hnc6_i : ¬ ((x : Int) ≥ 2285 ∧ (x : Int) % 256 = 237 ∧ (x : Int) % 9 = 8 ∧
        coprime23Core (x + 19) = 1) :=
      fun ⟨h1, h2, h3, h4⟩ => hc6 ⟨by omega, by omega, by omega, h4⟩
    simp only [hnc6_i, hc6, ite_false]
    exact cousinDiamond4StepInt_ofNat_eq x

theorem cousinDiamond5Step_pos (x : Nat) (hx : x > 0) : cousinDiamond5Step x > 0 := by
  unfold cousinDiamond5Step
  by_cases hc6 : isDiamond5Cone6 x
  · simp only [hc6, ite_true]; rcases hc6 with ⟨h2285, _, _, _⟩; omega
  · simp only [hc6, ite_false]; exact cousinDiamond4Step_pos x hx

theorem cousinDiamond5Step_eq_d4_of_not_cone6 (x : Nat) (hnc6 : ¬ isDiamond5Cone6 x) :
    cousinDiamond5Step x = cousinDiamond4Step x := by
  unfold cousinDiamond5Step; simp [hnc6]

/--
  Theorem W8.3e (`cousin_diamond5_outside_cones456_strict_descent`, zero custom axioms):
  Outside Cones 4, 5, and 6, EVERY `x > 2` strictly decreases `cousinDiamond2Phi` in 1 step!
-/
theorem cousin_diamond5_outside_cones456_strict_descent
    (x : Nat) (hx : x > 2)
    (hnc4 : ¬ isDiamond3Cone4 x) (hnc5 : ¬ isDiamond4Cone5 x) (hnc6 : ¬ isDiamond5Cone6 x) :
    cousinDiamond2Phi (cousinDiamond5Step x) < cousinDiamond2Phi x := by
  rw [cousinDiamond5Step_eq_d4_of_not_cone6 x hnc6]
  exact cousin_diamond4_outside_cones45_strict_descent x hx hnc4 hnc5

-- Modular Cone-6 avoidance helpers (`% 2, % 4, % 8, % 16, % 32, % 9`):

theorem not_cone6_of_even (z : Nat) (hev : z % 2 = 0) : ¬ isDiamond5Cone6 z := by
  rintro ⟨_, h256, _, _⟩; omega

theorem not_cone6_of_mod4_eq_3 (z : Nat) (hm4 : z % 4 = 3) : ¬ isDiamond5Cone6 z := by
  rintro ⟨_, h256, _, _⟩; omega

theorem not_cone6_of_mod16_ne_13 (z : Nat) (hm16 : z % 16 ≠ 13) : ¬ isDiamond5Cone6 z := by
  rintro ⟨_, h256, _, _⟩; omega

theorem not_cone6_of_mod32_ne_13 (z : Nat) (hm32 : z % 32 ≠ 13) : ¬ isDiamond5Cone6 z := by
  rintro ⟨_, h256, _, _⟩; omega

theorem not_cone6_of_mod9_ne_8 (z : Nat) (hm9 : z % 9 ≠ 8) : ¬ isDiamond5Cone6 z := by
  rintro ⟨_, _, h9, _⟩; exact hm9 h9

theorem cousin_diamond5_mersenne_scaled :
    ∀ (k a q : Nat), k + 1 ≤ a -> q ≥ 1 ->
      cousinDiamond5Iter k (2 ^ a * q - 1) = 3 ^ k * 2 ^ (a - k) * q - 1
  | 0, _, _, _, _ => by simp [cousinDiamond5Iter]
  | k + 1, a, q, hka, hq => by
    have hp4 : 2 ^ a * q = 4 * (2 ^ (a - 2) * q) := by
      conv => lhs; rw [show a = (a - 2) + 2 by omega]
      rw [Nat.pow_add 2 (a - 2) 2, show (2 : Nat) ^ 2 = 4 from rfl,
          Nat.mul_comm (2 ^ (a - 2)) 4, Nat.mul_assoc]
    have hm_pos : 2 ^ (a - 2) * q ≥ 1 := Nat.mul_le_mul (pow2_pos_nat (a - 2)) hq
    have hz4 : (2 ^ a * q - 1) % 4 = 3 := by omega
    simp only [cousinDiamond5Iter]
    rw [cousinDiamond5Step_eq_d4_of_not_cone6 _ (not_cone6_of_mod4_eq_3 _ hz4),
        cousinDiamond4Step_mod4_eq_3 (2 ^ a * q - 1) hz4]
    have hp2 : 2 ^ a * q = 2 * (2 ^ (a - 1) * q) := by
      rw [pow2_split_pred a (by omega), Nat.mul_assoc]
    have hm2_pos : 2 ^ (a - 1) * q ≥ 1 := Nat.mul_le_mul (pow2_pos_nat (a - 1)) hq
    have hstep_eq : (3 * (2 ^ a * q - 1) + 1) / 2 = 2 ^ (a - 1) * (3 * q) - 1 := by
      have hcomm : 3 * (2 ^ (a - 1) * q) = 2 ^ (a - 1) * (3 * q) := by
        rw [← Nat.mul_assoc 3, Nat.mul_comm 3 (2 ^ (a - 1)), Nat.mul_assoc]
      omega
    rw [hstep_eq, cousin_diamond5_mersenne_scaled k (a - 1) (3 * q) (by omega) (by omega),
        show a - 1 - k = a - (k + 1) by omega, Nat.pow_succ 3 k]
    apply congrArg (· - 1)
    calc
      3 ^ k * 2 ^ (a - (k + 1)) * (3 * q)
          = 3 ^ k * (2 ^ (a - (k + 1)) * 3) * q := by rw [Nat.mul_assoc, Nat.mul_assoc, Nat.mul_assoc]
      _ = 3 ^ k * (3 * 2 ^ (a - (k + 1))) * q := by rw [Nat.mul_comm (2 ^ (a - (k + 1))) 3]
      _ = 3 ^ k * 3 * 2 ^ (a - (k + 1)) * q := by rw [← Nat.mul_assoc (3 ^ k) 3]

theorem cousin_diamond5_even9_spine_drain :
    ∀ k : Nat, cousinDiamond5Iter k ((9 ^ (k + 1) - 1) / 4) = 2
  | 0 => rfl
  | k + 1 => by
    let j := k + 1
    have hp9j_ge9 : 9 ^ j ≥ 9 := by
      dsimp [j]; rw [Nat.pow_succ]; have hp := nat_pow_pos_of_pos 9 (by decide) k; omega
    have hp9j_m8 : 9 ^ j % 8 = 1 := pow9_mod8_eq_one_w5 j
    let q := (9 ^ j - 1) / 8
    have hp9j_eq : 9 ^ j = 8 * q + 1 := by dsimp [q]; omega
    have he_j1 : (9 ^ (j + 1) - 1) / 4 = 18 * q + 2 := by rw [Nat.pow_succ 9 j, hp9j_eq]; omega
    simp only [cousinDiamond5Iter]
    change cousinDiamond5Iter k (cousinDiamond5Step ((9 ^ (j + 1) - 1) / 4)) = 2
    have hnc6 : ¬ isDiamond5Cone6 ((9 ^ (j + 1) - 1) / 4) := by
      rw [he_j1]; exact not_cone6_of_even _ (by omega)
    rw [cousinDiamond5Step_eq_d4_of_not_cone6 _ hnc6]
    -- Extract the single step from `cousin_diamond4_even9_spine_drain`:
    have hd4 : cousinDiamond4Step ((9 ^ (j + 1) - 1) / 4) = (9 ^ j - 1) / 4 := by
      have he_j : (9 ^ j - 1) / 4 = 2 * q := by rw [hp9j_eq]; omega
      rw [he_j1, he_j]
      have hnc5 : ¬ isDiamond4Cone5 (18 * q + 2) := by rintro ⟨_, h32, _, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5]; unfold cousinDiamond3Step
      have hq_pos : q ≥ 1 := by dsimp [q]; omega
      have hodd_f : ¬ ((18 * q + 2) % 2 = 1) := by omega
      have h18_t : 18 * q + 2 ≥ 20 ∧ (18 * q + 2) % 18 = 2 := ⟨by omega, by omega⟩
      simp only [hodd_f, h18_t, and_self, ite_true, ite_false]; omega
    rw [hd4]
    exact cousin_diamond5_even9_spine_drain k

theorem cousin_diamond5_pow3_sub1_drain :
    ∀ k : Nat, cousinDiamond5Iter k (3 ^ (k + 1) - 1) = 2
  | 0 => rfl
  | k + 1 => by
    let j := k + 1
    have hp3_ge3 : 3 ^ j ≥ 3 := by dsimp [j]; rw [Nat.pow_succ]; have hp := pow3_pos_nat k; omega
    have ho_j1 := pow3_odd_nat_sec8 (j + 1)
    have hp_j1 := pow3_pos_nat (j + 1)
    simp only [cousinDiamond5Iter]
    change cousinDiamond5Iter k (cousinDiamond5Step (3 ^ (j + 1) - 1)) = 2
    rw [cousinDiamond5Step_eq_d4_of_not_cone6 _ (not_cone6_of_even _ (by omega))]
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
    exact cousin_diamond5_pow3_sub1_drain k

theorem cousin_diamond5_cone5_two_step_climb :
    ∀ (q_c a b : Nat), 3 * q_c + 2 ≤ a -> b ≥ 1 ->
      cousinDiamond5Iter (2 * q_c) (2 ^ a * 3 ^ b - 7) =
        2 ^ (a - 3 * q_c) * 3 ^ (b + 2 * q_c) - 7
  | 0, _, _, _, _ => by simp [cousinDiamond5Iter]
  | q_c + 1, a, b, ha, hb => by
    have ha5 : a ≥ 5 := by omega
    have hc5 := isDiamond4Cone5_of_pow2_pow3 a b ha5 hb
    have hnc6_0 : ¬ isDiamond5Cone6 (2 ^ a * 3 ^ b - 7) :=
      not_cone6_of_mod32_ne_13 _ (by have h := hc5.2.1; omega)
    let mid := 2 ^ (a - 2) * 3 ^ (b + 1) - 5
    have hmid_4 : mid % 4 = 3 := by
      dsimp [mid]
      have hp8 : 2 ^ (a - 2) = 8 * 2 ^ (a - 5) := by
        conv => lhs; rw [show a - 2 = 3 + (a - 5) by omega]
        rw [Nat.pow_add]
      rw [hp8, Nat.mul_assoc 8]
      have hp_pos : 2 ^ (a - 5) * 3 ^ (b + 1) ≥ 1 :=
        Nat.mul_le_mul (pow2_pos_nat _) (pow3_pos_nat _)
      omega
    have hnc6_1 : ¬ isDiamond5Cone6 mid := not_cone6_of_mod4_eq_3 mid hmid_4
    have hd4_2 := cousin_diamond4_cone5_two_step_climb 1 a b (by omega) hb
    simp only [Nat.mul_one, cousinDiamond4Iter] at hd4_2
    have hd4_s1 : cousinDiamond4Step (2 ^ a * 3 ^ b - 7) = mid := by
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
    rw [hd4_s1] at hd4_2
    conv => lhs; rw [show 2 * (q_c + 1) = 2 + 2 * q_c by omega]
    rw [cousinDiamond5Iter_add 2 (2 * q_c)]
    have hi2 : cousinDiamond5Iter 2 (2 ^ a * 3 ^ b - 7) = 2 ^ (a - 3) * 3 ^ (b + 2) - 7 := by
      simp only [cousinDiamond5Iter,
        cousinDiamond5Step_eq_d4_of_not_cone6 _ hnc6_0, hd4_s1,
        cousinDiamond5Step_eq_d4_of_not_cone6 _ hnc6_1, hd4_2]
    rw [hi2, cousin_diamond5_cone5_two_step_climb q_c (a - 3) (b + 2) (by omega) (by omega),
        show a - 3 - 3 * q_c = a - 3 * (q_c + 1) by omega,
        show b + 2 + 2 * q_c = b + 2 * (q_c + 1) by omega]

theorem cousinDiamond3Step_of_cone4_w8 (z : Nat) (ho : z % 2 = 1) (hc4 : isDiamond3Cone4 z) :
    cousinDiamond3Step z = (3 * z + 1) / 4 := by
  unfold cousinDiamond3Step
  have hcond : isDiamond3Cone4 z ∨
      (z > 1 ∧ z % 16 = 1 ∧ z % 3 ≠ 2 ∧ core3 (2 * z + 1) ≠ 1) ∨
      (z ≥ 73 ∧ z % 64 = 9 ∧ z % 3 ≠ 2 ∧ core3 (2 * z + 1) ≠ 1) ∨
      (z ≥ 17 ∧ core3 (z + 1) = 2) := Or.inl hc4
  simp only [ho, hcond, ite_true]

theorem cousinDiamond3Step_of_core3_succ_two_w8 (z : Nat)
    (ho : z % 2 = 1) (hge : z ≥ 17) (hc3 : core3 (z + 1) = 2) :
    cousinDiamond3Step z = (3 * z + 1) / 4 := by
  unfold cousinDiamond3Step
  have hcond : isDiamond3Cone4 z ∨
      (z > 1 ∧ z % 16 = 1 ∧ z % 3 ≠ 2 ∧ core3 (2 * z + 1) ≠ 1) ∨
      (z ≥ 73 ∧ z % 64 = 9 ∧ z % 3 ≠ 2 ∧ core3 (2 * z + 1) ≠ 1) ∨
      (z ≥ 17 ∧ core3 (z + 1) = 2) := Or.inr (Or.inr (Or.inr ⟨hge, hc3⟩))
  simp only [ho, hcond, ite_true]

theorem cousinDiamond3Step_odd_half_w8 (z : Nat) (ho : z % 2 = 1)
    (hnc4 : ¬ isDiamond3Cone4 z)
    (hc3_2 : core3 (2 * z + 1) = 1)
    (hc3_1 : core3 (z + 1) ≠ 2) :
    cousinDiamond3Step z = (3 * z + 1) / 2 := by
  unfold cousinDiamond3Step
  have hnq : ¬ (isDiamond3Cone4 z ∨
      (z > 1 ∧ z % 16 = 1 ∧ z % 3 ≠ 2 ∧ core3 (2 * z + 1) ≠ 1) ∨
      (z ≥ 73 ∧ z % 64 = 9 ∧ z % 3 ≠ 2 ∧ core3 (2 * z + 1) ≠ 1) ∨
      (z ≥ 17 ∧ core3 (z + 1) = 2)) := by
    rintro (h4 | ⟨_, _, _, hc1⟩ | ⟨_, _, _, hc2⟩ | ⟨_, hc3⟩)
    · exact hnc4 h4
    · exact hc1 hc3_2
    · exact hc2 hc3_2
    · exact hc3_1 hc3
  simp only [ho, hnq, ite_true, ite_false]

theorem cousinDiamond3Step_even_mod6_not18_w8 (z : Nat)
    (ho : ¬ (z % 2 = 1))
    (hn18 : ¬ (z ≥ 20 ∧ z % 18 = 2))
    (hm6 : z > 2 ∧ z % 6 = 2) :
    cousinDiamond3Step z = (z - 2) / 3 := by
  unfold cousinDiamond3Step
  simp only [ho, hn18, hm6, and_self, ite_true, ite_false]

theorem cousinDiamond3Step_even_mod8_eq6_w8 (z : Nat)
    (ho : ¬ (z % 2 = 1))
    (hn18 : ¬ (z ≥ 20 ∧ z % 18 = 2))
    (hn6 : ¬ (z > 2 ∧ z % 6 = 2))
    (hm8 : z > 2 ∧ z % 8 = 6) :
    cousinDiamond3Step z = (z - 2) / 2 := by
  unfold cousinDiamond3Step
  simp only [ho, hn18, hn6, ite_false]
  simp only [hm8, and_self, ite_true]

theorem cousinDiamond3Step_even_plain_half_w8 (z : Nat)
    (ho : ¬ (z % 2 = 1))
    (hn18 : ¬ (z ≥ 20 ∧ z % 18 = 2))
    (hn6 : ¬ (z > 2 ∧ z % 6 = 2))
    (hn8 : ¬ (z > 2 ∧ z % 8 = 6)) :
    cousinDiamond3Step z = z / 2 := by
  unfold cousinDiamond3Step
  simp only [ho, hn18, hn6, hn8, ite_false]

theorem cousin_diamond5_a0_3_drain (b0 : Nat) (hb0 : b0 ≥ 3) :
    cousinDiamond5Step (8 * 3 ^ b0 - 7) = 12 * 3 ^ b0 - 10 ∧
    cousinDiamond5Step (12 * 3 ^ b0 - 10) = 4 * 3 ^ b0 - 4 ∧
    cousinDiamond5Step (4 * 3 ^ b0 - 4) = 4 * 3 ^ (b0 - 1) - 2 ∧
    cousinDiamond5Iter ((b0 - 1) / 2 + 7) (8 * 3 ^ b0 - 7) = 1 := by
  have hp3_ge27 : 3 ^ b0 ≥ 27 := by
    have hm := nat_pow_mono_exp_pos 3 3 b0 (by decide) hb0; simpa using hm
  have hp3_b1_ge9 : 3 ^ (b0 - 1) ≥ 9 := by
    have hm := nat_pow_mono_exp_pos 3 2 (b0 - 1) (by decide) (by omega); simpa using hm
  have hp3_b2_ge3 : 3 ^ (b0 - 2) ≥ 3 := by
    have hm := nat_pow_mono_exp_pos 3 1 (b0 - 2) (by decide) (by omega); simpa using hm
  have h3b0_sp : 3 ^ b0 = 3 * 3 ^ (b0 - 1) := by
    conv => lhs; rw [show b0 = 1 + (b0 - 1) by omega]; rw [Nat.pow_add, Nat.pow_one]
  have h3b1_sp : 3 ^ (b0 - 1) = 3 * 3 ^ (b0 - 2) := by
    conv => lhs; rw [show b0 - 1 = 1 + (b0 - 2) by omega]; rw [Nat.pow_add, Nat.pow_one]
  have h3b0_m9 : 3 ^ b0 % 9 = 0 := by rw [h3b0_sp, h3b1_sp]; omega
  have hnc6_8 : ¬ isDiamond5Cone6 (8 * 3 ^ b0 - 7) := by
    apply not_cone6_of_mod9_ne_8
    have hm9 : (8 * 3 ^ b0) % 9 = 0 := by rw [Nat.mul_mod, h3b0_m9, Nat.mul_zero, Nat.zero_mod]
    omega
  have hs1 : cousinDiamond5Step (8 * 3 ^ b0 - 7) = 12 * 3 ^ b0 - 10 := by
    rw [cousinDiamond5Step_eq_d4_of_not_cone6 _ hnc6_8]
    exact cousin_diamond4_exit_step_general_odd 8 b0 (Or.inr (Or.inl rfl)) hb0
  have hs2 : cousinDiamond5Step (12 * 3 ^ b0 - 10) = 4 * 3 ^ b0 - 4 := by
    rw [cousinDiamond5Step_eq_d4_of_not_cone6 _ (not_cone6_of_even _ (by omega))]
    have hnc5 : ¬ isDiamond4Cone5 (12 * 3 ^ b0 - 10) := by rintro ⟨_, h32, _, _⟩; omega
    rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5]
    have h18 : 12 * 3 ^ b0 = 18 * (2 * 3 ^ (b0 - 1)) := by rw [h3b0_sp]; omega
    rw [cousinDiamond3Step_even_mod6_not18_w8 _ (by omega) (by omega) ⟨by omega, by omega⟩]
    omega
  have hs3 : cousinDiamond5Step (4 * 3 ^ b0 - 4) = 4 * 3 ^ (b0 - 1) - 2 := by
    rw [cousinDiamond5Step_eq_d4_of_not_cone6 _ (not_cone6_of_even _ (by omega))]
    have hnc5 : ¬ isDiamond4Cone5 (4 * 3 ^ b0 - 4) := by rintro ⟨_, h32, _, _⟩; omega
    rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5]
    have h18 : 4 * 3 ^ b0 = 18 * (2 * 3 ^ (b0 - 2)) := by rw [h3b0_sp, h3b1_sp]; omega
    rw [cousinDiamond3Step_even_mod6_not18_w8 _ (by omega) (by omega) ⟨by omega, by omega⟩]
    omega
  have hs4 : cousinDiamond5Step (4 * 3 ^ (b0 - 1) - 2) = 2 * 3 ^ (b0 - 1) - 1 := by
    rw [cousinDiamond5Step_eq_d4_of_not_cone6 _ (not_cone6_of_even _ (by omega))]
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
    have hsz : cousinDiamond5Step zr = yr := by
      rw [cousinDiamond5Step_eq_d4_of_not_cone6 zr (not_cone6_of_mod16_ne_13 zr (by dsimp [zr]; omega))]
      have hnc5 : ¬ isDiamond4Cone5 zr := by rintro ⟨_, h32, _, _⟩; dsimp [zr] at h32; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 zr hnc5]
      have hc3 : core3 (zr + 1) = 2 := by
        rw [show zr + 1 = 2 * 9 ^ m by dsimp [zr]; omega,
            core3_mul2 (9 ^ m) (by omega), (pow9_eq_v3Pow_w5 m).2]
      rw [cousinDiamond3Step_of_core3_succ_two_w8 zr (by dsimp [zr]; omega) (by dsimp [zr]; omega) hc3]
      dsimp [zr, yr]; omega
    have hsy : cousinDiamond5Step yr = (9 ^ (m + 1) - 1) / 4 := by
      have hyr_m3 : yr % 3 = 1 := by
        have hm3 : 9 ^ m % 3 = 0 := by rw [show m = (m - 1) + 1 by omega, Nat.pow_succ]; omega
        dsimp [yr]; omega
      rw [cousinDiamond5Step_eq_d4_of_not_cone6 yr (not_cone6_of_mod9_ne_8 yr (by omega))]
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
    change cousinDiamond5Iter (m + 7) (8 * 3 ^ b0 - 7) = 1
    rw [show m + 7 = 4 + 1 + 1 + m + 1 by omega,
        cousinDiamond5Iter_add (4 + 1 + 1 + m) 1,
        cousinDiamond5Iter_add (4 + 1 + 1) m,
        cousinDiamond5Iter_add (4 + 1) 1,
        cousinDiamond5Iter_add 4 1]
    have hi4 : cousinDiamond5Iter 4 (8 * 3 ^ b0 - 7) = zr := by
      simp only [cousinDiamond5Iter, hs1, hs2, hs3, hs4, hu_eq]; rfl
    rw [hi4]
    have hiz : cousinDiamond5Iter 1 zr = yr := hsz
    rw [hiz]
    have hiy : cousinDiamond5Iter 1 yr = (9 ^ (m + 1) - 1) / 4 := hsy
    rw [hiy, cousin_diamond5_even9_spine_drain m]
    decide
  · have hb1_2m1 : b0 - 1 = 2 * m + 1 := by dsimp [m]; omega
    have hu_eq : 2 * 3 ^ (b0 - 1) - 1 = 6 * 9 ^ m - 1 := by
      rw [hb1_2m1, Nat.pow_succ, ← pow9_eq_pow3_double m]; omega
    let ur := 6 * 9 ^ m - 1
    let wr := (9 ^ (m + 1) - 1) / 2
    have hsu : cousinDiamond5Step ur = wr := by
      have hur_m16 : ur % 16 = 5 := by
        let q := (9 ^ m - 1) / 8
        have hp9_eq : 9 ^ m = 8 * q + 1 := by dsimp [q]; omega
        dsimp [ur]; rw [hp9_eq]; omega
      rw [cousinDiamond5Step_eq_d4_of_not_cone6 ur (not_cone6_of_mod16_ne_13 ur (by omega))]
      have hnc5 : ¬ isDiamond4Cone5 ur := by rintro ⟨_, h32, _, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 ur hnc5]
      have hc3 : core3 (ur + 1) = 2 := by
        rw [show ur + 1 = 2 * (3 * 9 ^ m) by dsimp [ur]; omega,
            core3_mul2 (3 * 9 ^ m) (by omega),
            core3_mul3 (9 ^ m) (by omega), (pow9_eq_v3Pow_w5 m).2]
      rw [cousinDiamond3Step_of_core3_succ_two_w8 ur (by omega) (by dsimp [ur]; omega) hc3]
      dsimp [ur, wr]; rw [Nat.pow_succ 9 m]; omega
    have hsw : cousinDiamond5Step wr = (9 ^ (m + 1) - 1) / 4 := by
      let q := (9 ^ m - 1) / 8
      have hq_pos : q ≥ 1 := by dsimp [q]; omega
      have hp9_eq : 9 ^ m = 8 * q + 1 := by dsimp [q]; omega
      have hwr_eq : wr = 36 * q + 4 := by dsimp [wr]; rw [Nat.pow_succ 9 m, hp9_eq]; omega
      have hnext_eq : (9 ^ (m + 1) - 1) / 4 = 18 * q + 2 := by rw [Nat.pow_succ 9 m, hp9_eq]; omega
      rw [hwr_eq, hnext_eq,
          cousinDiamond5Step_eq_d4_of_not_cone6 _ (not_cone6_of_even _ (by omega))]
      have hnc5 : ¬ isDiamond4Cone5 (36 * q + 4) := by rintro ⟨_, h32, _, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5]
      rw [cousinDiamond3Step_even_plain_half_w8 _ (by omega) (by omega) (by omega) (by omega)]
      omega
    change cousinDiamond5Iter (m + 7) (8 * 3 ^ b0 - 7) = 1
    rw [show m + 7 = 4 + 1 + 1 + m + 1 by omega,
        cousinDiamond5Iter_add (4 + 1 + 1 + m) 1,
        cousinDiamond5Iter_add (4 + 1 + 1) m,
        cousinDiamond5Iter_add (4 + 1) 1,
        cousinDiamond5Iter_add 4 1]
    have hi4 : cousinDiamond5Iter 4 (8 * 3 ^ b0 - 7) = ur := by
      simp only [cousinDiamond5Iter, hs1, hs2, hs3, hs4, hu_eq]; rfl
    rw [hi4]
    have hiu : cousinDiamond5Iter 1 ur = wr := hsu
    rw [hiu]
    have hiw : cousinDiamond5Iter 1 wr = (9 ^ (m + 1) - 1) / 4 := hsw
    rw [hiw, cousin_diamond5_even9_spine_drain m]
    decide

theorem cousin_diamond5_a0_2_and_4_drain (b0 : Nat) (hb0 : b0 ≥ 3) :
    cousinDiamond5Iter (b0 + 3) (4 * 3 ^ b0 - 7) = 1 ∧
    cousinDiamond5Iter ((b0 - 1) / 2 + 8) (16 * 3 ^ b0 - 7) = 1 := by
  have hp3_ge27 : 3 ^ b0 ≥ 27 := by
    have hm := nat_pow_mono_exp_pos 3 3 b0 (by decide) hb0; simpa using hm
  have hp3_b1_ge9 : 3 ^ (b0 - 1) ≥ 9 := by
    have hm := nat_pow_mono_exp_pos 3 2 (b0 - 1) (by decide) (by omega); simpa using hm
  have hp3_b2_ge3 : 3 ^ (b0 - 2) ≥ 3 := by
    have hm := nat_pow_mono_exp_pos 3 1 (b0 - 2) (by decide) (by omega); simpa using hm
  have h3b0_sp : 3 ^ b0 = 3 * 3 ^ (b0 - 1) := by
    conv => lhs; rw [show b0 = 1 + (b0 - 1) by omega]; rw [Nat.pow_add, Nat.pow_one]
  have h3b1_sp : 3 ^ (b0 - 1) = 3 * 3 ^ (b0 - 2) := by
    conv => lhs; rw [show b0 - 1 = 1 + (b0 - 2) by omega]; rw [Nat.pow_add, Nat.pow_one]
  have h3b0_m9 : 3 ^ b0 % 9 = 0 := by rw [h3b0_sp, h3b1_sp]; omega
  have hnc6_c : ∀ c : Nat, c ≥ 1 -> ¬ isDiamond5Cone6 (c * 3 ^ b0 - 7) := by
    intro c hc1
    apply not_cone6_of_mod9_ne_8
    have hm : c * 3 ^ b0 ≥ 27 := by have h := Nat.mul_le_mul hc1 hp3_ge27; simpa using h
    have hm9 : (c * 3 ^ b0) % 9 = 0 := by rw [Nat.mul_mod, h3b0_m9, Nat.mul_zero, Nat.zero_mod]
    omega
  refine ⟨?_, ?_⟩
  · have hs1 : cousinDiamond5Step (4 * 3 ^ b0 - 7) = 6 * 3 ^ b0 - 10 := by
      rw [cousinDiamond5Step_eq_d4_of_not_cone6 _ (hnc6_c 4 (by decide))]
      exact cousin_diamond4_exit_step_general_odd 4 b0 (Or.inl rfl) hb0
    have hs2 : cousinDiamond5Step (6 * 3 ^ b0 - 10) = 2 * 3 ^ b0 - 4 := by
      rw [cousinDiamond5Step_eq_d4_of_not_cone6 _ (not_cone6_of_even _ (by omega))]
      have hnc5 : ¬ isDiamond4Cone5 (6 * 3 ^ b0 - 10) := by rintro ⟨_, h32, _, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5]
      have h18 : 6 * 3 ^ b0 = 18 * 3 ^ (b0 - 1) := by rw [h3b0_sp]; omega
      rw [cousinDiamond3Step_even_mod6_not18_w8 _ (by omega) (by omega) ⟨by omega, by omega⟩]
      omega
    have hs3 : cousinDiamond5Step (2 * 3 ^ b0 - 4) = 2 * 3 ^ (b0 - 1) - 2 := by
      rw [cousinDiamond5Step_eq_d4_of_not_cone6 _ (not_cone6_of_even _ (by omega))]
      have hnc5 : ¬ isDiamond4Cone5 (2 * 3 ^ b0 - 4) := by rintro ⟨_, h32, _, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5]
      have h18 : 2 * 3 ^ b0 = 18 * 3 ^ (b0 - 2) := by rw [h3b0_sp, h3b1_sp]; omega
      rw [cousinDiamond3Step_even_mod6_not18_w8 _ (by omega) (by omega) ⟨by omega, by omega⟩]
      omega
    have hs4 : cousinDiamond5Step (2 * 3 ^ (b0 - 1) - 2) = 3 ^ (b0 - 1) - 1 := by
      rw [cousinDiamond5Step_eq_d4_of_not_cone6 _ (not_cone6_of_even _ (by omega))]
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
        cousinDiamond5Iter_add (4 + (b0 - 2)) 1,
        cousinDiamond5Iter_add 4 (b0 - 2)]
    have hi4 : cousinDiamond5Iter 4 (4 * 3 ^ b0 - 7) = 3 ^ ((b0 - 2) + 1) - 1 := by
      simp only [cousinDiamond5Iter, hs1, hs2, hs3, hs4]
      rw [show b0 - 1 = (b0 - 2) + 1 by omega]
    rw [hi4, cousin_diamond5_pow3_sub1_drain (b0 - 2)]
    decide
  · rcases cousin_diamond5_a0_3_drain b0 hb0 with ⟨ha3_s1, ha3_s2, ha3_s3, ha3⟩
    have hs1 : cousinDiamond5Step (16 * 3 ^ b0 - 7) = 24 * 3 ^ b0 - 10 := by
      rw [cousinDiamond5Step_eq_d4_of_not_cone6 _ (hnc6_c 16 (by decide))]
      exact cousin_diamond4_exit_step_general_odd 16 b0 (Or.inr (Or.inr rfl)) hb0
    have hs2 : cousinDiamond5Step (24 * 3 ^ b0 - 10) = 8 * 3 ^ b0 - 4 := by
      rw [cousinDiamond5Step_eq_d4_of_not_cone6 _ (not_cone6_of_even _ (by omega))]
      have hnc5 : ¬ isDiamond4Cone5 (24 * 3 ^ b0 - 10) := by rintro ⟨_, h32, _, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5]
      have h18 : 24 * 3 ^ b0 = 18 * (4 * 3 ^ (b0 - 1)) := by rw [h3b0_sp]; omega
      rw [cousinDiamond3Step_even_mod6_not18_w8 _ (by omega) (by omega) ⟨by omega, by omega⟩]
      omega
    have hs3 : cousinDiamond5Step (8 * 3 ^ b0 - 4) = 8 * 3 ^ (b0 - 1) - 2 := by
      rw [cousinDiamond5Step_eq_d4_of_not_cone6 _ (not_cone6_of_even _ (by omega))]
      have hnc5 : ¬ isDiamond4Cone5 (8 * 3 ^ b0 - 4) := by rintro ⟨_, h32, _, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5]
      have h18 : 8 * 3 ^ b0 = 18 * (4 * 3 ^ (b0 - 2)) := by rw [h3b0_sp, h3b1_sp]; omega
      rw [cousinDiamond3Step_even_mod6_not18_w8 _ (by omega) (by omega) ⟨by omega, by omega⟩]
      omega
    have hs4 : cousinDiamond5Step (8 * 3 ^ (b0 - 1) - 2) = 4 * 3 ^ (b0 - 1) - 2 := by
      rw [cousinDiamond5Step_eq_d4_of_not_cone6 _ (not_cone6_of_even _ (by omega))]
      have hnc5 : ¬ isDiamond4Cone5 (8 * 3 ^ (b0 - 1) - 2) := by rintro ⟨_, h32, _, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5]
      have h18 : 8 * 3 ^ (b0 - 1) = 18 * (4 * 3 ^ (b0 - 3)) := by
        conv => lhs; rhs; rw [show b0 - 1 = 2 + (b0 - 3) by omega]
        rw [Nat.pow_add]; omega
      have hp3_b3 := pow3_pos_nat (b0 - 3)
      rw [cousinDiamond3Step_even_mod8_eq6_w8 _ (by omega) (by omega) (by omega) ⟨by omega, by omega⟩]
      omega
    rw [show (b0 - 1) / 2 + 7 = 3 + ((b0 - 1) / 2 + 4) by omega,
        cousinDiamond5Iter_add 3 ((b0 - 1) / 2 + 4)] at ha3
    have hi3 : cousinDiamond5Iter 3 (8 * 3 ^ b0 - 7) = 4 * 3 ^ (b0 - 1) - 2 := by
      simp only [cousinDiamond5Iter, ha3_s1, ha3_s2, ha3_s3]
    rw [hi3] at ha3
    rw [show (b0 - 1) / 2 + 8 = 4 + ((b0 - 1) / 2 + 4) by omega,
        cousinDiamond5Iter_add 4 ((b0 - 1) / 2 + 4)]
    have hi4 : cousinDiamond5Iter 4 (16 * 3 ^ b0 - 7) = 4 * 3 ^ (b0 - 1) - 2 := by
      simp only [cousinDiamond5Iter, hs1, hs2, hs3, hs4]
    rw [hi4]
    exact ha3

theorem cousin_diamond5_cone4_return_aux (x : Nat) (hc4 : isDiamond3Cone4 x) :
    ∃ k : Nat, k ≤ cousinDiamond2Phi x ∧ cousinDiamond5Iter k x = 1 := by
  rcases cousin_diamond3_cone4_reaches_one_exact x hc4 with ⟨r, hr_ge3, hE, _, hphi_ge⟩
  refine ⟨3 * r + 4, hphi_ge, ?_⟩
  have hnc6_x' : ¬ isDiamond5Cone6 x := by
    rintro ⟨_, h256, _, _⟩; have h8 := hc4.2.1; omega
  have hx_odd : x % 2 = 1 := by have h8 := hc4.2.1; omega
  have hs1 : cousinDiamond5Step x = 2 ^ (2 * r + 1) - 1 := by
    rw [cousinDiamond5Step_eq_d4_of_not_cone6 x hnc6_x']
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
  have hglide : cousinDiamond5Iter (2 * r) (2 ^ (2 * r + 1) - 1) = zr := by
    have hf := cousin_diamond5_mersenne_scaled (2 * r) (2 * r + 1) 1 (by omega) (by decide)
    simp only [Nat.mul_one, show 2 * r + 1 - 2 * r = 1 by omega, Nat.pow_one] at hf
    rw [hf, ← pow9_eq_pow3_double r, Nat.mul_comm]
  have hp9_ge729 : 9 ^ r ≥ 729 := by
    have hm := nat_pow_mono_exp_pos 9 3 r (by decide) hr_ge3; simpa using hm
  have hp9_m8 : 9 ^ r % 8 = 1 := pow9_mod8_eq_one_w5 r
  have hsz : cousinDiamond5Step zr = yr := by
    rw [cousinDiamond5Step_eq_d4_of_not_cone6 zr (not_cone6_of_mod16_ne_13 zr (by dsimp [zr]; omega))]
    have hnc5 : ¬ isDiamond4Cone5 zr := by rintro ⟨_, h32, _, _⟩; dsimp [zr] at h32; omega
    rw [cousinDiamond4Step_eq_d3_of_not_cone5 zr hnc5]
    have hc3 : core3 (zr + 1) = 2 := by
      rw [show zr + 1 = 2 * 9 ^ r by dsimp [zr]; omega,
          core3_mul2 (9 ^ r) (by omega), (pow9_eq_v3Pow_w5 r).2]
    rw [cousinDiamond3Step_of_core3_succ_two_w8 zr (by dsimp [zr]; omega) (by dsimp [zr]; omega) hc3]
    dsimp [zr, yr]; omega
  have hsy : cousinDiamond5Step yr = (9 ^ (r + 1) - 1) / 4 := by
    have hyr_m3 : yr % 3 = 1 := by
      have hm3 : 9 ^ r % 3 = 0 := by rw [show r = (r - 1) + 1 by omega, Nat.pow_succ]; omega
      dsimp [yr]; omega
    rw [cousinDiamond5Step_eq_d4_of_not_cone6 yr (not_cone6_of_mod9_ne_8 yr (by omega))]
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
      cousinDiamond5Iter_add (1 + 2 * r + 1 + 1 + r) 1,
      cousinDiamond5Iter_add (1 + 2 * r + 1 + 1) r,
      cousinDiamond5Iter_add (1 + 2 * r + 1) 1,
      cousinDiamond5Iter_add (1 + 2 * r) 1,
      cousinDiamond5Iter_add 1 (2 * r)]
  have hi1 : cousinDiamond5Iter 1 x = 2 ^ (2 * r + 1) - 1 := hs1
  rw [hi1, hglide]
  have hiz : cousinDiamond5Iter 1 zr = yr := hsz
  rw [hiz]
  have hiy : cousinDiamond5Iter 1 yr = (9 ^ (r + 1) - 1) / 4 := hsy
  rw [hiy, cousin_diamond5_even9_spine_drain r]
  decide

theorem cousin_diamond5_cone5_return_aux (x : Nat) (hc5 : isDiamond4Cone5 x) :
    ∃ (a b k : Nat),
      a ≥ 5 ∧ b ≥ 1 ∧ x + 7 = 2 ^ a * 3 ^ b ∧
      k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond5Iter k x = 1 := by
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
  have hclimb := cousin_diamond5_cone5_two_step_climb q_c a b (by dsimp [q_c]; omega) hb1
  rw [← hx_eq] at hclimb
  change cousinDiamond5Iter (2 * q_c) x = 2 ^ a0 * 3 ^ b0 - 7 at hclimb
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
  have hd_3 := (cousin_diamond5_a0_3_drain b0 hb0_ge3).2.2.2
  rcases cousin_diamond5_a0_2_and_4_drain b0 hb0_ge3 with ⟨hd_2, hd_4⟩
  rcases ha0_234 with ha2 | ha3 | ha4
  · have hkx := hbound_x (b0 + 3) (by omega)
    refine ⟨a, b, 2 * q_c + (b0 + 3), ha5, hb1, hmul.symm, hkx,
      Nat.le_trans (by omega : 2 * q_c + (b0 + 3) ≤ x + 1) (cousinDiamond2Phi_ge_succ x), ?_⟩
    rw [cousinDiamond5Iter_add (2 * q_c) (b0 + 3) x, hclimb, ha2]; exact hd_2
  · have hkx := hbound_x ((b0 - 1) / 2 + 7) (by omega)
    refine ⟨a, b, 2 * q_c + ((b0 - 1) / 2 + 7), ha5, hb1, hmul.symm, hkx,
      Nat.le_trans (by omega : 2 * q_c + ((b0 - 1) / 2 + 7) ≤ x + 1) (cousinDiamond2Phi_ge_succ x), ?_⟩
    rw [cousinDiamond5Iter_add (2 * q_c) ((b0 - 1) / 2 + 7) x, hclimb, ha3]; exact hd_3
  · have hkx := hbound_x ((b0 - 1) / 2 + 8) (by omega)
    refine ⟨a, b, 2 * q_c + ((b0 - 1) / 2 + 8), ha5, hb1, hmul.symm, hkx,
      Nat.le_trans (by omega : 2 * q_c + ((b0 - 1) / 2 + 8) ≤ x + 1) (cousinDiamond2Phi_ge_succ x), ?_⟩
    rw [cousinDiamond5Iter_add (2 * q_c) ((b0 - 1) / 2 + 8) x, hclimb, ha4]; exact hd_4

/--
  Theorem W8.3f (`cousin_diamond5_cones456_exact_return`, zero custom axioms):
  Exact 3-Tier `ω^3` Multi-Block Return Across Cones 4, 5, AND 6 of `T_diamond5`:
  1. Every `x` in Cone 4 (`isDiamond3Cone4 x`) reaches `1` in `3 * r + 4 ≤ cousinDiamond2Phi x` steps!
  2. Every `x` in Cone 5 (`isDiamond4Cone5 x`) has `x + 7 = 2 ^ a * 3 ^ b` (`a ≥ 5, b ≥ 1`) and
     reaches `1` in `k ≤ x` (`≤ cousinDiamond2Phi x`) steps!
  3. Every `x` in Cone 6 (`isDiamond5Cone6 x`) has `x + 19 = 2 ^ e * 3 ^ f` (`e ≥ 8, f ≥ 2`),
     steps in 1 genuine `v_2(3x + 1) = 3` jump `(3 * x + 1) / 8` directly to the Cone-5 state
     `y = 2 ^ (e - 3) * 3 ^ (f + 1) - 7`, and reaches `1` in `1 + k_y ≤ cousinDiamond2Phi x` steps!
-/
theorem cousin_diamond5_cones456_exact_return :
    (∀ x : Nat, isDiamond3Cone4 x ->
      ∃ k : Nat, k ≤ cousinDiamond2Phi x ∧ cousinDiamond5Iter k x = 1) ∧
    (∀ x : Nat, isDiamond4Cone5 x ->
      ∃ (a b k : Nat),
        a ≥ 5 ∧ b ≥ 1 ∧ x + 7 = 2 ^ a * 3 ^ b ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond5Iter k x = 1) ∧
    (∀ x : Nat, isDiamond5Cone6 x ->
      ∃ (e f k : Nat),
        e ≥ 8 ∧ f ≥ 2 ∧ x + 19 = 2 ^ e * 3 ^ f ∧
        cousinDiamond5Step x = 2 ^ (e - 3) * 3 ^ (f + 1) - 7 ∧
        isDiamond4Cone5 (cousinDiamond5Step x) ∧
        k ≤ cousinDiamond2Phi x ∧ cousinDiamond5Iter k x = 1) := by
  refine ⟨cousin_diamond5_cone4_return_aux, cousin_diamond5_cone5_return_aux, ?_⟩
  intro x hc6
  rcases hc6 with ⟨hx2285, hx256, hx9, hg1⟩
  have hc6_hold : isDiamond5Cone6 x := ⟨hx2285, hx256, hx9, hg1⟩
  rcases decomp_2_3_exact (x + 19) (by omega) with ⟨_, _, _, _, _, hmul⟩
  rw [hg1, Nat.mul_one] at hmul
  rcases eq_pow2_of_v2Pow_aux (x + 19) (x + 19) (by omega) (Nat.le_refl _) with ⟨e, he⟩
  rcases eq_pow3_of_v3Pow_aux (x + 19) (x + 19) (by omega) (Nat.le_refl _) with ⟨f, hf⟩
  rw [he, hf] at hmul
  have he8 : e ≥ 8 := by
    by_cases hlt : e < 8
    · have hp3_o := pow3_odd_nat_sec8 f
      rcases (by omega : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 5 ∨ e = 6 ∨ e = 7) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    · omega
  have hf2 : f ≥ 2 := by
    by_cases hf0 : f = 0
    · rw [hf0, Nat.pow_zero, Nat.mul_one] at hmul
      have hm3 := pow2_mod3_nonzero_w5 e
      omega
    · by_cases hf1 : f = 1
      · rw [hf1, Nat.pow_one] at hmul
        have hm3 := pow2_mod3_nonzero_w5 e
        have hdiv := (Nat.div_add_mod (2 ^ e) 3).symm
        have hx9_eq : (x + 19) % 9 = 8 := by omega
        rw [← hmul, hdiv, Nat.add_mul,
            show 3 * (2 ^ e / 3) * 3 = 9 * (2 ^ e / 3) by omega] at hx9_eq
        omega
      · omega
  let y := 2 ^ (e - 3) * 3 ^ (f + 1) - 7
  have hstep_x : cousinDiamond5Step x = y := by
    unfold cousinDiamond5Step
    simp only [hc6_hold, ite_true]
    dsimp [y]
    have hp8 : 2 ^ e = 8 * 2 ^ (e - 3) := by
      conv => lhs; rw [show e = 3 + (e - 3) by omega]
      rw [Nat.pow_add]
    have hprod_pos : 2 ^ (e - 3) * 3 ^ f ≥ 32 * 9 := by
      have h1 : 32 ≤ 2 ^ (e - 3) := by simpa using pow2_mono_nat (by omega : 5 ≤ e - 3)
      have h2 : 9 ≤ 3 ^ f := by simpa using nat_pow_mono_exp_pos 3 2 f (by decide) hf2
      simpa using Nat.mul_le_mul h1 h2
    have hx_val : x = 8 * 2 ^ (e - 3) * 3 ^ f - 19 := by rw [← hp8]; omega
    rw [hx_val, Nat.mul_assoc 8 (2 ^ (e - 3)) (3 ^ f),
        Nat.pow_succ 3 f, ← Nat.mul_assoc (2 ^ (e - 3)) (3 ^ f) 3]
    omega
  have hc5_y : isDiamond4Cone5 y := isDiamond4Cone5_of_pow2_pow3 (e - 3) (f + 1) (by omega) (by omega)
  rcases cousin_diamond5_cone5_return_aux y hc5_y with ⟨_, _, ky, _, _, _, hky_le_y, _, hky_1⟩
  have hy_lt_x : y < x := by
    have hstep_eq : y = (3 * x + 1) / 8 := hstep_x.symm.trans (by unfold cousinDiamond5Step; simp [hc6_hold])
    omega
  have h1ky_phi : 1 + ky ≤ cousinDiamond2Phi x :=
    Nat.le_trans (by omega : 1 + ky ≤ x + 1) (cousinDiamond2Phi_ge_succ x)
  refine ⟨e, f, 1 + ky, he8, hf2, hmul.symm, hstep_x, ?_, h1ky_phi, ?_⟩
  · rw [hstep_x]; exact hc5_y
  · rw [cousinDiamond5Iter_add 1 ky x]
    have hi1 : cousinDiamond5Iter 1 x = y := hstep_x
    rw [hi1]; exact hky_1

theorem cousin_diamond5_reaches_one_within_phi :
    ∀ (B x : Nat), x > 0 -> cousinDiamond2Phi x ≤ B ->
      ∃ k : Nat, k ≤ B ∧ cousinDiamond5Iter k x = 1
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
        · rcases cousin_diamond5_cones456_exact_return.1 x hc4 with ⟨k, hle_phi, hk1⟩
          exact ⟨k, Nat.le_trans hle_phi hB, hk1⟩
        · by_cases hc5 : isDiamond4Cone5 x
          · rcases cousin_diamond5_cones456_exact_return.2.1 x hc5 with
              ⟨_, _, k, _, _, _, _, hle_phi, hk1⟩
            exact ⟨k, Nat.le_trans hle_phi hB, hk1⟩
          · by_cases hc6 : isDiamond5Cone6 x
            · rcases cousin_diamond5_cones456_exact_return.2.2 x hc6 with
                ⟨_, _, k, _, _, _, _, _, hle_phi, hk1⟩
              exact ⟨k, Nat.le_trans hle_phi hB, hk1⟩
            · have hdesc := cousin_diamond5_outside_cones456_strict_descent x (by omega) hc4 hc5 hc6
              have hpos := cousinDiamond5Step_pos x hx
              rcases cousin_diamond5_reaches_one_within_phi B (cousinDiamond5Step x) hpos (by omega) with
                ⟨k, hk_le, hk_eq⟩
              exact ⟨k + 1, by omega, hk_eq⟩

/--
  Theorem W8.3g (`cousin_diamond5_global_convergence`, zero custom axioms):
  Unconditional Global Convergence & Degree-5 Polynomial Stopping Bound for `T_diamond5`:
  For EVERY `x > 0`, `cousinDiamond5Iter` reaches `1` within `k ≤ (x + 1) ^ 3 + (x + 1) ^ 5` steps!
-/
theorem cousin_diamond5_global_convergence (x : Nat) (hx : x > 0) :
    ∃ k : Nat, k ≤ (x + 1) ^ 3 + (x + 1) ^ 5 ∧ cousinDiamond5Iter k x = 1 := by
  rcases cousin_diamond5_reaches_one_within_phi (cousinDiamond2Phi x) x hx (Nat.le_refl _) with
    ⟨k, hk_phi, hk1⟩
  exact ⟨k, Nat.le_trans hk_phi (cousinDiamond2Phi_upper_poly_bound x), hk1⟩

theorem exists_non_desc_along_diamond5_iter :
    ∀ (terms : List LaurentTerm) (A0 B0 C0 N z : Nat),
      N ≥ 1 ->
      (∀ i : Nat, i < N ->
        cousinDiamond5Iter i z ≥ 3 ∧
        (cousinDiamond5Iter i z) % 2 = 1 ∧
        cousinDiamond5Step (cousinDiamond5Iter i z) ≥ 3) ->
      ¬ laurentDescProp terms A0 B0 C0 z (cousinDiamond5Iter N z) ->
      ∃ x : Nat,
        x ≥ 3 ∧ x % 2 = 1 ∧ cousinDiamond5Step x ≥ 3 ∧
        ¬ laurentDescProp terms A0 B0 C0 x (cousinDiamond5Step x)
  | _, _, _, _, 0, _, hN, _, _ => by omega
  | terms, A0, B0, C0, 1, z, _, hall, hnd => by
    rcases hall 0 (by decide) with ⟨hz3, hzo, hsz3⟩
    exact ⟨z, hz3, hzo, hsz3, hnd⟩
  | terms, A0, B0, C0, m + 2, z, _, hall, hnd => by
    if h0 : laurentDescProp terms A0 B0 C0 z (cousinDiamond5Step z) then
      have hnd_next : ¬ laurentDescProp terms A0 B0 C0 (cousinDiamond5Step z)
          (cousinDiamond5Iter (m + 1) (cousinDiamond5Step z)) :=
        fun hrest => hnd (laurentDescProp_trans terms A0 B0 C0 z (cousinDiamond5Step z) _ h0 hrest)
      exact exists_non_desc_along_diamond5_iter terms A0 B0 C0 (m + 1) (cousinDiamond5Step z)
        (by omega) (fun i hi => hall (i + 1) (by omega)) hnd_next
    else
      rcases hall 0 (by omega) with ⟨hz3, hzo, hsz3⟩
      exact ⟨z, hz3, hzo, hsz3, h0⟩

/--
  Theorem W8.3h (`cousin_diamond5_r_block_spiral_climb_and_laurent_impossibility`, zero custom axioms):
  1. Cone-6 -> Cone-5 Multi-Tier Entry & Unbounded `r`-Block Spiral Climb (`∀ r ≥ 1`):
     `2285 -> 857`, `73709 -> 27641`, AND `cousinDiamond5Iter (2 * j) (4 * 16^r - 5) =
     4 * 16^(r - j) * 18^j - 5` for ALL `j ≤ r`!
  2. Universal `∀ L ≥ 1` Multi-Term Laurent Valuation Impossibility on `cousinDiamond5Step`!
-/
theorem cousin_diamond5_r_block_spiral_climb_and_laurent_impossibility :
    cousinDiamond5Step 2285 = 857 ∧
    cousinDiamond5Step 73709 = 27641 ∧
    cousinDiamond5Step 1019 = 1529 ∧
    cousinDiamond5Step 1529 = 1147 ∧
    (∀ (r j : Nat), r ≥ 1 -> j ≤ r ->
      cousinDiamond5Iter (2 * j) (4 * 16 ^ r - 5) = 4 * 16 ^ (r - j) * 18 ^ j - 5) ∧
    (∀ (terms : List LaurentTerm) (A0 B0 C0 : Nat),
      (∃ t ∈ terms, t.coeff > 0) ->
      ∃ x : Nat,
        x ≥ 3 ∧ x % 2 = 1 ∧ cousinDiamond5Step x ≥ 3 ∧
        ¬ (evalLaurentSumNum terms (cousinDiamond5Step x) * laurentValDen A0 B0 C0 x <
            evalLaurentSumNum terms x * laurentValDen A0 B0 C0 (cousinDiamond5Step x))) := by
  have hspiral : ∀ (r j : Nat), r ≥ 1 -> j ≤ r ->
      cousinDiamond5Iter (2 * j) (4 * 16 ^ r - 5) = 4 * 16 ^ (r - j) * 18 ^ j - 5 := by
    intro r j hr hj
    cases j with
    | zero => simp [cousinDiamond5Iter]
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
      have hs_first : cousinDiamond5Step x0 = 2 ^ (4 * r + 1) * 3 ^ 1 - 7 := by
        rw [cousinDiamond5Step_eq_d4_of_not_cone6 x0 (not_cone6_of_mod4_eq_3 x0 hx0_m4),
            cousinDiamond4Step_mod4_eq_3 x0 hx0_m4]
        dsimp [x0]
        rw [hx0_pow, show 4 * r + 2 = (4 * r + 1) + 1 by omega, Nat.pow_succ 2 (4 * r + 1)]
        have hp := pow2_pos_nat (4 * r + 1); omega
      have hclimb := cousin_diamond5_cone5_two_step_climb j' (4 * r + 1) 1 (by omega) (by decide)
      let y_end := 2 ^ (4 * r + 1 - 3 * j') * 3 ^ (1 + 2 * j') - 7
      have hy_c5 : isDiamond4Cone5 y_end :=
        isDiamond4Cone5_of_pow2_pow3 (4 * r + 1 - 3 * j') (1 + 2 * j') (by omega) (by omega)
      have hy_nc6 : ¬ isDiamond5Cone6 y_end :=
        not_cone6_of_mod32_ne_13 y_end (by have h := hy_c5.2.1; omega)
      have hs_last : cousinDiamond5Step y_end = 4 * 16 ^ (r - (j' + 1)) * 18 ^ (j' + 1) - 5 := by
        rw [cousinDiamond5Step_eq_d4_of_not_cone6 y_end hy_nc6]
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
            rw [Nat.pow_succ 18 j']; have hp := nat_pow_pos_of_pos 18 (by decide) j'; omega
          have hm := Nat.mul_le_mul (Nat.mul_le_mul_left 4 h1) h2
          simpa using hm
        have hpos_y : 2 ^ (4 * r + 1 - 3 * j') * 3 ^ (1 + 2 * j') ≥ 32 := by
          have h1 : 32 ≤ 2 ^ (4 * r + 1 - 3 * j') := by simpa using pow2_mono_nat (by omega : 5 ≤ 4 * r + 1 - 3 * j')
          simpa using Nat.mul_le_mul h1 (pow3_pos_nat _)
        have hsub : 3 * (2 ^ (4 * r + 1 - 3 * j') * 3 ^ (1 + 2 * j') - 7) + 1 =
            4 * (4 * 16 ^ (r - (j' + 1)) * 18 ^ (j' + 1)) - 20 := by
          rw [Nat.mul_sub_left_distrib 3, hprod_eq]; omega
        rw [hsub]; omega
      rw [show 2 * (j' + 1) = 1 + 2 * j' + 1 by omega,
          cousinDiamond5Iter_add (1 + 2 * j') 1,
          cousinDiamond5Iter_add 1 (2 * j')]
      have hi1 : cousinDiamond5Iter 1 x0 = 2 ^ (4 * r + 1) * 3 ^ 1 - 7 := hs_first
      rw [hi1, hclimb]
      exact hs_last
  refine ⟨by decide, by decide, by decide, by decide, hspiral, ?_⟩
  -- Part 2: Universal `∀ L ≥ 1` Laurent valuation impossibility on `cousinDiamond5Step`:
  intro terms A0 B0 C0 hnonempty
  rcases three_family_multiterm_laurent_obstruction terms A0 B0 C0 hnonempty with
    h97 | ⟨j2, hj2⟩ | ⟨r, hr_pos, hr3⟩
  · have hs97 : cousinDiamond5Step 97 = 73 := by decide
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
      · dsimp [xj2]; omega
      · have hpow2 : 3 * xj2 + 5 = 2 ^ (6 * j2 + 9) * 1 := by
          rw [Nat.mul_one, show 6 * j2 + 9 = 2 * (3 * j2 + 4) + 1 by omega,
              Nat.pow_succ, ← pow4_eq_pow2_even (3 * j2 + 4), Nat.mul_comm]
          dsimp [xj2]; omega
        rw [hpow2]; exact core2_pow2_mul (6 * j2 + 9) 1 (by decide) (by decide)
    have hnc6_xj2 : ¬ isDiamond5Cone6 xj2 := by
      rintro ⟨_, h256, _, _⟩; have h8 := hc4_xj2.2.1; omega
    have hstep_xj2 : cousinDiamond5Step xj2 = yj2 := by
      rw [cousinDiamond5Step_eq_d4_of_not_cone6 xj2 hnc6_xj2]
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
        cousinDiamond5Iter i xr3 = 3 ^ i * 2 ^ (2 * r + 1 - i) - 1 ∧
        cousinDiamond5Iter i xr3 ≥ 7 ∧
        (cousinDiamond5Iter i xr3) % 2 = 1 := by
      intro i hi
      have hf := cousin_diamond5_mersenne_scaled i (2 * r + 1) 1 (by omega) (by decide)
      rw [← hxr3_pow, Nat.mul_one] at hf
      have hprod_ge8 : 3 ^ i * 2 ^ (2 * r + 1 - i) ≥ 8 := by
        have h1 : 2 ^ i * 2 ^ (2 * r + 1 - i) ≤ 3 ^ i * 2 ^ (2 * r + 1 - i) :=
          Nat.mul_le_mul_right _ (pow2_le_pow3 i)
        rw [← Nat.pow_add, show i + (2 * r + 1 - i) = 2 * r + 1 by omega] at h1
        exact Nat.le_trans (pow2_mono_nat (by omega : 3 ≤ 2 * r + 1)) h1
      have hprod_ev : (3 ^ i * 2 ^ (2 * r + 1 - i)) % 2 = 0 := by
        rw [show 2 * r + 1 - i = (2 * r - i) + 1 by omega, Nat.pow_succ, ← Nat.mul_assoc]; omega
      exact ⟨hf, by rw [hf]; omega, by rw [hf]; omega⟩
    have hiter_2r : cousinDiamond5Iter (2 * r) xr3 = zr := by
      have hf := (hglide_i (2 * r) (Nat.le_refl _)).1
      rw [hf, show 2 * r + 1 - 2 * r = 1 by omega, Nat.pow_one,
          ← pow9_eq_pow3_double r, Nat.mul_comm]
    have hstep_zr : cousinDiamond5Step zr = yr3 := by
      rw [cousinDiamond5Step_eq_d4_of_not_cone6 zr (not_cone6_of_mod16_ne_13 zr (by dsimp [zr]; omega))]
      have hnc5 : ¬ isDiamond4Cone5 zr := by rintro ⟨_, h32, _, _⟩; dsimp [zr] at h32; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 zr hnc5]
      have hc3_zr : core3 (zr + 1) = 2 := by
        rw [show zr + 1 = 2 * 9 ^ r by dsimp [zr]; omega,
            core3_mul2 (9 ^ r) (by omega), (pow9_eq_v3Pow_w5 r).2]
      rw [cousinDiamond3Step_of_core3_succ_two_w8 zr (by dsimp [zr]; omega) (by dsimp [zr]; omega) hc3_zr]
      dsimp [zr, yr3]; omega
    have hiter_2r1 : cousinDiamond5Iter (2 * r + 1) xr3 = yr3 := by
      rw [cousinDiamond5Iter_add (2 * r) 1 xr3, hiter_2r]; exact hstep_zr
    have hall : ∀ i : Nat, i < 2 * r + 1 ->
        cousinDiamond5Iter i xr3 ≥ 3 ∧
        (cousinDiamond5Iter i xr3) % 2 = 1 ∧
        cousinDiamond5Step (cousinDiamond5Iter i xr3) ≥ 3 := by
      intro i hi
      by_cases hlt : i < 2 * r
      · rcases hglide_i i (by omega) with ⟨_, hge7, hodd_i⟩
        have hnext : cousinDiamond5Step (cousinDiamond5Iter i xr3) =
            cousinDiamond5Iter (i + 1) xr3 :=
          (cousinDiamond5Iter_add i 1 xr3).symm
        rcases hglide_i (i + 1) (by omega) with ⟨_, hge7_n, _⟩
        exact ⟨by omega, hodd_i, by rw [hnext]; omega⟩
      · have hi_eq : i = 2 * r := by omega
        rw [hi_eq, hiter_2r, hstep_zr]
        exact ⟨by dsimp [zr]; omega, by dsimp [zr]; omega, by dsimp [yr3]; omega⟩
    change ¬ laurentDescProp terms A0 B0 C0 xr3 yr3 at hr3
    rw [← hiter_2r1] at hr3
    exact exists_non_desc_along_diamond5_iter terms A0 B0 C0 (2 * r + 1) xr3 (by omega) hall hr3

theorem core2Aux_dvd_w8 : ∀ (fuel n : Nat), core2Aux fuel n ∣ n
  | 0, _ => Nat.dvd_refl _
  | fuel + 1, n => by
    simp only [core2Aux]
    by_cases hc : n > 0 ∧ n % 2 = 0
    · simp only [hc, and_self, ite_true]
      exact Nat.dvd_trans (core2Aux_dvd_w8 fuel (n / 2)) ⟨2, by omega⟩
    · simp only [hc, ite_false]
      exact Nat.dvd_refl n

theorem core3Aux_dvd_w8 : ∀ (fuel n : Nat), core3Aux fuel n ∣ n
  | 0, _ => Nat.dvd_refl _
  | fuel + 1, n => by
    simp only [core3Aux]
    by_cases hc : n > 0 ∧ n % 3 = 0
    · simp only [hc, and_self, ite_true]
      exact Nat.dvd_trans (core3Aux_dvd_w8 fuel (n / 3)) ⟨3, by omega⟩
    · simp only [hc, ite_false]
      exact Nat.dvd_refl n

/--
  Theorem W8.3i' (`cousin_diamond5_q6_noninteger_avoids_cone6`, choice-free `zero custom axioms`):
  Universal Non-Integer Rational Exclusion from Cone 6 on `M1 = Q_(6)^+`:
  For EVERY reduced non-integer rational `(num, den)` (`Nat.gcd num den = 1` and `den > 1`),
  `core3 (core2 (num + 19 * den)) ≠ den` (since `core3 (core2 m) ∣ m` would force `den ∣ num`,
  hence `den ∣ 1`), so `cousinDiamond5StepQ6 (num, den)` NEVER enters Cone 6 and agrees
  identically with `cousinDiamond4StepQ6 (num, den)`!
-/
theorem cousin_diamond5_q6_noninteger_avoids_cone6 (num den : Nat)
    (hgcd : Nat.gcd num den = 1) (hden : den > 1) :
    core3 (core2 (num + 19 * den)) ≠ den ∧
    cousinDiamond5StepQ6 (num, den) = cousinDiamond4StepQ6 (num, den) := by
  have hne : core3 (core2 (num + 19 * den)) ≠ den := by
    intro heq
    have hdvd_sum : den ∣ (num + 19 * den) := by
      have hc_dvd : core3 (core2 (num + 19 * den)) ∣ (num + 19 * den) :=
        Nat.dvd_trans (core3Aux_dvd_w8 _ _) (core2Aux_dvd_w8 _ _)
      rwa [heq] at hc_dvd
    rcases hdvd_sum with ⟨k, hk⟩
    have hdvd_num : den ∣ num := ⟨k - 19, by
      have hge : k ≥ 19 := by
        by_cases hlt : k < 19
        · have hm := Nat.mul_le_mul_left den (show k ≤ 18 by omega)
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
  unfold cousinDiamond5StepQ6
  have hcond : ¬ (num ≥ 2285 * den ∧ (num * invMod256Odd den) % 256 = 237 ∧
      (num * ((den % 9) ^ 5 % 9)) % 9 = 8 ∧ core3 (core2 (num + 19 * den)) = den) :=
    fun ⟨_, _, _, hc⟩ => hne hc
  simp only [hcond, ite_false]

/--
  Theorem W8.3i (`cousin_diamond5_counter_model_separation`, `[]` axioms):
  `T_diamond5` rejects ALL three Counter-Models (`M1 = Q_(6)^+` 5-cycle `(1, 7) -> ... -> (1, 7)`
  plus non-integer `(2285, 7) -> (3431, 7)` bypassing Cone 6 by `W8.3i'` and draining into `(1, 7)`
  in `10` preperiodic steps, `M2 = Z^-` cycles `-1` and `-5 -> -7 -> -10 -> -5`, and `M3`
  supercritical `q = 7` 5-cycle `5 -> 18 -> 9 -> 32 -> 10 -> 5`), AND at the minimal integer Cone-6
  `v_2(3x + 1) = 3` jump `2285 -> 857` jumps `Φ_diamond2` (`4120094 -> 5849278`) directly into
  Cone 5 while reaching `1` in `11` steps!
-/
theorem cousin_diamond5_counter_model_separation :
    cousinDiamond5StepInt (-1) = -1 ∧
    cousinDiamond5IterInt 3 (-5) = -5 ∧
    cousinDiamond5IterParam 7 5 5 = 5 ∧
    cousinDiamond5StepQ6 (1, 7) = (5, 7) ∧
    cousinDiamond5IterQ6 5 (1, 7) = (1, 7) ∧
    cousinDiamond5StepQ6 (2285, 7) = (3431, 7) ∧
    cousinDiamond5IterQ6 10 (2285, 7) = (1, 7) ∧
    cousinDiamond5Step 2285 = 857 ∧
    cousinDiamond5StepInt 2285 = 857 ∧
    cousinDiamond5StepQ6 (2285, 1) = (857, 1) ∧
    cousinDiamond2Phi 2285 = 4120094 ∧
    cousinDiamond2Phi 857 = 5849278 ∧
    cousinDiamond5Iter 11 2285 = 1 := by
  decide

-- ============================================================================
-- SECTION 4: Front D (Branches P5.3 & P2.2) — Exact Cross-Scale (`|u1| < |u2|`)
--            `q = 0` Leaf Collision Biconditional, Unconditional Multi-Scale
--            `NoDupNat`, & Markov Skew-Product Bijectivity / Mod-6 Lock
-- ============================================================================

/-- Repeated `[false, true]` `{2, 1}`-loop tail of length `2 * m`. -/
def loopPairRepeat : Nat -> List Bool
  | 0 => []
  | m + 1 => loopPairRepeat m ++ [false, true]

/--
  Canonical `m`-fold trivial `{1, 2}`-loop extension of a core parity word `u` at `q = 0`:
  appends `canonicalSuffixShift u 1` `false`-bits (reaching `1`), `[true]` (`1 -> 2`),
  and `m` additional `[false, true]` pairs (`2 -> 1 -> 2`).
-/
def trivialLoopExt (u : List Bool) (m : Nat) : List Bool :=
  ((u ++ List.replicate (canonicalSuffixShift u 1) false) ++ [true]) ++ loopPairRepeat m

theorem loopPairRepeat_length :
    ∀ m : Nat, (loopPairRepeat m).length = 2 * m
  | 0 => rfl
  | m + 1 => by
    simp only [loopPairRepeat, List.length_append, loopPairRepeat_length m]
    have hl2 : [false, true].length = 2 := rfl
    rw [hl2]
    omega

theorem collatzIter_add_w8 :
    ∀ (k1 k2 n : Nat), collatzIter (k1 + k2) n = collatzIter k2 (collatzIter k1 n)
  | 0, k2, n => by simp [collatzIter]
  | k1 + 1, k2, n => by
    rw [Nat.succ_add]
    exact collatzIter_add_w8 k1 k2 (collatzStep n)

theorem collatzIter_one_even_w8 :
    ∀ m : Nat, collatzIter (2 * m) 1 = 1
  | 0 => rfl
  | m + 1 => by
    rw [show 2 * (m + 1) = 2 * m + 2 by omega, collatzIter_add_w8 (2 * m) 2 1,
        collatzIter_one_even_w8 m]
    decide

theorem parityOfIter_one_odd_even_w8 :
    ∀ m : Nat,
      parityOfIter (2 * m + 1) 1 = [true] ++ loopPairRepeat m ∧
      parityOfIter (2 * m + 2) 1 = [true] ++ loopPairRepeat m ++ [false]
  | 0 => ⟨by decide, by decide⟩
  | m + 1 => by
    rcases parityOfIter_one_odd_even_w8 m with ⟨_, hev⟩
    have hc_ev : collatzIter (2 * m + 2) 1 = 1 := collatzIter_one_even_w8 (m + 1)
    have hp1 : parityOfIter 1 1 = [true] := by decide
    have hp2 : parityOfIter 2 1 = [true, false] := by decide
    refine ⟨?_, ?_⟩
    · rw [show 2 * (m + 1) + 1 = (2 * m + 2) + 1 by omega,
          parityOfIter_append_split (2 * m + 2) 1 1, hev, hc_ev, hp1]
      simp [loopPairRepeat, List.append_assoc]
    · rw [show 2 * (m + 1) + 2 = (2 * m + 2) + 2 by omega,
          parityOfIter_append_split (2 * m + 2) 2 1, hev, hc_ev, hp2]
      simp [loopPairRepeat, List.append_assoc]

theorem not_true_mem_replicate_false_w8 :
    ∀ n : Nat, true ∉ List.replicate n false
  | 0 => by simp
  | n + 1 => by
    intro hm
    simp only [List.replicate_succ, List.mem_cons] at hm
    rcases hm with h | h
    · cases h
    · exact not_true_mem_replicate_false_w8 n h

theorem prefix_append_true_of_append_replicate_false_w8 :
    ∀ (u1 v2 wRem : List Bool) (a1 : Nat),
      u1.length ≤ v2.length ->
      u1 ++ List.replicate a1 false = (v2 ++ [true]) ++ wRem -> False
  | [], v2, wRem, a1, _, heq => by
    simp only [List.nil_append] at heq
    have hmem : true ∈ List.replicate a1 false := by
      rw [heq, List.append_assoc]
      exact List.mem_append_right v2 (List.Mem.head _)
    exact not_true_mem_replicate_false_w8 a1 hmem
  | _ :: _, [], _, _, hle, _ => by simp at hle
  | _ :: r1, _ :: r2, wRem, a1, hle, heq => by
    simp only [List.cons_append, List.cons.injEq] at heq
    exact prefix_append_true_of_append_replicate_false_w8 r1 r2 wRem a1
      (by simp at hle; omega) heq.2

theorem trivialLoopExt_spec (u : List Bool) (hu : IsCoreParityWord u) :
    ∀ m : Nat,
      IsCoreParityWord (trivialLoopExt u m) ∧
      canonicalSuffixShift (trivialLoopExt u m) 1 = 1 ∧
      (trivialLoopExt u m).length = u.length + canonicalSuffixShift u 1 + 2 * m + 1 ∧
      exactBackwardQuotient 1 (trivialLoopExt u m) 0 = exactBackwardQuotient 1 u 0 ∧
      ¬ IsFirstHitOnePair (trivialLoopExt u m) 0
  | 0 => by
    have hex0 : trivialLoopExt u 0 = (u ++ List.replicate (canonicalSuffixShift u 1) false) ++ [true] := by
      simp [trivialLoopExt, loopPairRepeat]
    rcases one_generator_trivial_loop_extension u 0 hu with ⟨hcore, hcs, hy, hnfh⟩
    simp only [Nat.zero_mul, Nat.add_zero] at hcore hcs hy hnfh
    rw [← hex0] at hcore hcs hy hnfh
    have hlen : (trivialLoopExt u 0).length = u.length + canonicalSuffixShift u 1 + 2 * 0 + 1 := by
      rw [hex0, List.length_append, List.length_append, List.length_replicate, List.length_singleton]
    exact ⟨hcore, hcs, hlen, hy, hnfh⟩
  | m + 1 => by
    rcases trivialLoopExt_spec u hu m with ⟨hcore_m, hcs_m, hlen_m, hy_m, _⟩
    rcases one_generator_trivial_loop_extension (trivialLoopExt u m) 0 hcore_m with
      ⟨hcore_next, hcs_next, hy_next, hnfh_next⟩
    simp only [Nat.zero_mul, Nat.add_zero, hcs_m] at hcore_next hcs_next hy_next hnfh_next
    have hex_succ : ((trivialLoopExt u m ++ List.replicate 1 false) ++ [true]) =
        trivialLoopExt u (m + 1) := by
      have hlr : loopPairRepeat (m + 1) = loopPairRepeat m ++ [false, true] := rfl
      have hr1 : List.replicate 1 false = [false] := rfl
      unfold trivialLoopExt
      rw [hlr, hr1]
      simp only [List.append_assoc, List.cons_append, List.nil_append]
    rw [hex_succ] at hcore_next hcs_next hy_next hnfh_next
    have hlen_next : (trivialLoopExt u (m + 1)).length =
        u.length + canonicalSuffixShift u 1 + 2 * (m + 1) + 1 := by
      rw [← hex_succ, List.length_append, List.length_append, List.length_replicate,
          List.length_singleton, hlen_m]
      omega
    exact ⟨hcore_next, hcs_next, hlen_next, hy_next.trans hy_m, hnfh_next⟩

/--
  Theorem W8.4a (`q0_cross_scale_leaf_collision_iff_trivial_loop`, zero custom axioms):
  Exact Cross-Scale (`|u1| < |u2|`) `q = 0` Leaf Collision Biconditional:
  1. For ALL core parity words `u1, u2` with `u1.length < u2.length`:
       `exactBackwardQuotient 1 u1 0 = exactBackwardQuotient 1 u2 0 ↔
        ∃ m : Nat, u2 = trivialLoopExt u1 m`!
  2. Every loop extension `trivialLoopExt u1 m` (`∀ m : Nat`) is a valid core parity word of
     exact length `u1.length + canonicalSuffixShift u1 1 + 2 * m + 1`, satisfies
     `canonicalSuffixShift (trivialLoopExt u1 m) 1 = 1`, hits the identical `q = 0` leaf,
     and fails `IsFirstHitOnePair` (`¬ IsFirstHitOnePair (trivialLoopExt u1 m) 0`)!
  3. Concrete Multi-Loop Witness (`ZPOS_RAY_Q0_MULTI_LOOP_COLLISION_3`):
     At `u1 = [true, true]` (`y = 3`, `L = 2`), `m = 1` (`u2 = [true, true, false, false, false, true, false, true]`,
     `L = 8`) collides at `y = 3` while `u2 ≠ trivialLoopExt u1 0`, refuting single-loop (`m = 0`)-only
     collision claims (`W8_H4_RAW_CROSS_SCALE_Q0_LEAF_INJECTIVITY_WITHOUT_FIRST_HIT`)!
-/
theorem q0_cross_scale_leaf_collision_iff_trivial_loop :
    (∀ (u1 u2 : List Bool),
      IsCoreParityWord u1 -> IsCoreParityWord u2 ->
      u1.length < u2.length ->
      (exactBackwardQuotient 1 u1 0 = exactBackwardQuotient 1 u2 0 ↔
       ∃ m : Nat, u2 = trivialLoopExt u1 m)) ∧
    (∀ (u1 : List Bool) (m : Nat),
      IsCoreParityWord u1 ->
      IsCoreParityWord (trivialLoopExt u1 m) ∧
      canonicalSuffixShift (trivialLoopExt u1 m) 1 = 1 ∧
      (trivialLoopExt u1 m).length = u1.length + canonicalSuffixShift u1 1 + 2 * m + 1 ∧
      exactBackwardQuotient 1 (trivialLoopExt u1 m) 0 = exactBackwardQuotient 1 u1 0 ∧
      ¬ IsFirstHitOnePair (trivialLoopExt u1 m) 0) ∧
    (let u1 := [true, true]
     let u2 := trivialLoopExt u1 1
     u2 = [true, true, false, false, false, true, false, true] ∧
     u2 ≠ trivialLoopExt u1 0 ∧
     exactBackwardQuotient 1 u1 0 = 3 ∧
     exactBackwardQuotient 1 u2 0 = 3) := by
  have hiff : ∀ (u1 u2 : List Bool),
      IsCoreParityWord u1 -> IsCoreParityWord u2 ->
      u1.length < u2.length ->
      (exactBackwardQuotient 1 u1 0 = exactBackwardQuotient 1 u2 0 ↔
       ∃ m : Nat, u2 = trivialLoopExt u1 m) := by
    intro u1 u2 hu1 hu2 hlt
    constructor
    · intro hy_eq
      let y := exactBackwardQuotient 1 u1 0
      let a1 := canonicalSuffixShift u1 1
      let K1 := u1.length + a1
      -- Recover `parityOfIter K1 y = u1 ++ replicate a1 false` and `collatzIter K1 y = 1`:
      rcases one_generator_pos_odd_and_reaches_one u1 0 hu1 with ⟨_, _, heq1, hiter1⟩
      have hsteps1 : backwardOneTotalSteps u1 0 = K1 := by
        unfold backwardOneTotalSteps; dsimp [K1, a1]; omega
      rw [hsteps1] at heq1 hiter1
      change 2 ^ K1 = 3 ^ parityWeight u1 * y + affineCarry u1 at heq1
      change collatzIter K1 y = 1 at hiter1
      rcases affineCarry_append_replicate_false u1 a1 with ⟨hwt_v1, hcar_v1⟩
      have hv1_len : (u1 ++ List.replicate a1 false).length = K1 := by
        rw [List.length_append, List.length_replicate]
      have hv1_aff : 2 ^ (u1 ++ List.replicate a1 false).length * 1 =
          3 ^ parityWeight (u1 ++ List.replicate a1 false) * y +
            affineCarry (u1 ++ List.replicate a1 false) := by
        rw [Nat.mul_one, hv1_len, hwt_v1, hcar_v1]; exact heq1
      have hpar_K1 : u1 ++ List.replicate a1 false = parityOfIter K1 y := by
        have hp := eq_parityOfIter_of_nat_affine (u1 ++ List.replicate a1 false) y 1 hv1_aff
        rwa [hv1_len] at hp
      -- Recover `parityOfIter u2.length y = u2`:
      rcases one_generator_pos_odd_and_reaches_one u2 0 hu2 with ⟨_, _, heq2, _⟩
      rw [← hy_eq] at heq2
      let a2 := canonicalSuffixShift u2 1
      have hsteps2 : backwardOneTotalSteps u2 0 = u2.length + a2 := by
        unfold backwardOneTotalSteps; dsimp [a2]; omega
      rw [hsteps2] at heq2
      rcases affineCarry_append_replicate_false u2 a2 with ⟨hwt_v2, hcar_v2⟩
      have hv2_len : (u2 ++ List.replicate a2 false).length = u2.length + a2 := by
        rw [List.length_append, List.length_replicate]
      have hv2_aff : 2 ^ (u2 ++ List.replicate a2 false).length * 1 =
          3 ^ parityWeight (u2 ++ List.replicate a2 false) * y +
            affineCarry (u2 ++ List.replicate a2 false) := by
        rw [Nat.mul_one, hv2_len, hwt_v2, hcar_v2]; exact heq2
      have hpar_u2 : parityOfIter u2.length y = u2 := by
        have hp := eq_parityOfIter_of_nat_affine (u2 ++ List.replicate a2 false) y 1 hv2_aff
        rw [hv2_len] at hp
        have hsp := parityOfIter_append_split u2.length a2 y
        rw [← hp] at hsp
        have hlen_u2 : u2.length = (parityOfIter u2.length y).length := (parityOfIter_length _ y).symm
        exact (list_append_inj_left_eq_len _ _ _ _ hlen_u2 hsp).1.symm
      -- Show `u2.length ≤ K1` is impossible because `u2` ends in `true`:
      have hK1_lt : K1 < u2.length := by
        by_cases hle : u2.length ≤ K1
        · have hsp : parityOfIter K1 y =
              parityOfIter u2.length y ++ parityOfIter (K1 - u2.length) (collatzIter u2.length y) := by
            conv => lhs; rw [show K1 = u2.length + (K1 - u2.length) by omega]
            exact parityOfIter_append_split u2.length (K1 - u2.length) y
          rw [← hpar_K1, hpar_u2] at hsp
          rcases list_eq_append_true_of_reverse_head u2 hu2.2 with ⟨v2, hv2_eq⟩
          have hv2_len_ge : u1.length ≤ v2.length := by
            have hl : u2.length = v2.length + 1 := by rw [hv2_eq, List.length_append, List.length_singleton]
            omega
          rw [hv2_eq] at hsp
          exact False.elim (prefix_append_true_of_append_replicate_false_w8 u1 v2 _ a1 hv2_len_ge hsp)
        · omega
      -- Now split `u2 = parityOfIter (K1 + d) y = (u1 ++ replicate a1 false) ++ parityOfIter d 1`:
      let d := u2.length - K1
      have hd_pos : d ≥ 1 := by dsimp [d]; omega
      have hu2_split : u2 = (u1 ++ List.replicate a1 false) ++ parityOfIter d 1 := by
        rw [← hpar_u2, show u2.length = K1 + d by dsimp [d]; omega,
            parityOfIter_append_split K1 d y, ← hpar_K1, hiter1]
      -- `d` must be odd (`d = 2 * m + 1`), because even `d = 2 * m + 2` ends in `false`:
      by_cases hd_ev : d % 2 = 0
      · let m := (d - 2) / 2
        have hd_eq : d = 2 * m + 2 := by dsimp [m]; omega
        rw [hd_eq, (parityOfIter_one_odd_even_w8 m).2] at hu2_split
        have hlast_false : u2.reverse.head? = some false := by
          rw [hu2_split, ← List.append_assoc, List.reverse_append]
          rfl
        have htr := hu2.2
        rw [hlast_false] at htr
        cases htr
      · let m := (d - 1) / 2
        have hd_eq : d = 2 * m + 1 := by dsimp [m]; omega
        refine ⟨m, ?_⟩
        rw [hd_eq, (parityOfIter_one_odd_even_w8 m).1] at hu2_split
        unfold trivialLoopExt
        change u2 = ((u1 ++ List.replicate a1 false) ++ [true]) ++ loopPairRepeat m
        simp only [hu2_split, List.append_assoc]
    · rintro ⟨m, rfl⟩
      exact (trivialLoopExt_spec u1 hu1 m).2.2.2.1.symm
  refine ⟨hiff, fun u1 m hu1 => trivialLoopExt_spec u1 hu1 m, ?_⟩
  exact ⟨by decide, by decide, by decide, by decide⟩

-- ----------------------------------------------------------------------------
-- Multi-Scale `NoDupNat` Across `IsFirstHitOnePair` Surviving `q = 0` Leaves (`W8.4b`)
-- ----------------------------------------------------------------------------

/-- Executable boolean decision procedure for `IsFirstHitOnePair u 0` on core parity words. -/
def isFirstHitOneQ0Bool (u : List Bool) : Bool :=
  firstHitStepsAux (backwardOneTotalSteps u 0) (exactBackwardQuotient 1 u 0) ==
    backwardOneTotalSteps u 0

/-- Executable boolean decision procedure for `IsSurvivingMod373248Class`. -/
def isSurvivingMod373248Bool (n : Nat) : Bool :=
  isSurvivingMod512Bool (n % 512) && isSurvivingMod729Bool (n % 729)

theorem isFirstHitOneQ0Bool_iff (u : List Bool) (hu : IsCoreParityWord u) :
    isFirstHitOneQ0Bool u = true ↔ IsFirstHitOnePair u 0 := by
  unfold isFirstHitOneQ0Bool
  let K := backwardOneTotalSteps u 0
  let y := exactBackwardQuotient 1 u 0
  rcases one_generator_pos_odd_and_reaches_one u 0 hu with ⟨_, _, _, hiter⟩
  change collatzIter K y = 1 at hiter
  rcases firstHitStepsAux_spec K y hiter with ⟨hk0_le, hk0_one, hk0_min⟩
  let k0 := firstHitStepsAux K y
  change k0 ≤ K at hk0_le
  change collatzIter k0 y = 1 at hk0_one
  change ∀ j : Nat, j < k0 -> collatzIter j y ≠ 1 at hk0_min
  change (k0 == K) = true ↔ IsFirstHitOnePair u 0
  constructor
  · intro hbeq
    have heq : k0 = K := of_decide_eq_true hbeq
    refine ⟨hu, fun j hj => hk0_min j (by omega)⟩
  · rintro ⟨_, hno_early⟩
    by_cases hlt : k0 < K
    · exact False.elim (hno_early k0 hlt hk0_one)
    · have heq : k0 = K := by omega
      exact decide_eq_true heq

/-- All core parity words of exact length `L` (`[]` for `L = 0`, `[[true]]` for `L = 1`). -/
def allCoreWordsOfLen : Nat -> List (List Bool)
  | 0 => []
  | 1 => [[true]]
  | m + 2 => (allBoolWordsOfLen m).map (fun mid => true :: (mid ++ [true]))

/-- All core parity words of length `1 ≤ |u| ≤ L_max`. -/
def allCoreWordsUpToLen : Nat -> List (List Bool)
  | 0 => []
  | L + 1 => allCoreWordsUpToLen L ++ allCoreWordsOfLen (L + 1)

/-- Multi-scale `IsFirstHitOnePair (u, 0)` `q = 0` leaves across `1 ≤ |u| ≤ L_max`. -/
def firstHitQ0LeavesUpToLen (L_max : Nat) : List Nat :=
  ((allCoreWordsUpToLen L_max).filter isFirstHitOneQ0Bool).map
    (fun u => exactBackwardQuotient 1 u 0)

/-- Multi-scale `IsFirstHitOnePair (u, 0)` surviving `Mod373248` `q = 0` leaves across `1 ≤ |u| ≤ L_max`. -/
def firstHitSurvivingQ0LeavesUpToLen (L_max : Nat) : List Nat :=
  ((allCoreWordsUpToLen L_max).filter
    (fun u => isFirstHitOneQ0Bool u && isSurvivingMod373248Bool (exactBackwardQuotient 1 u 0))).map
    (fun u => exactBackwardQuotient 1 u 0)

theorem mem_filter_iff_w8 (p : List Bool -> Bool) :
    ∀ (u : List Bool) (ws : List (List Bool)),
      u ∈ ws.filter p ↔ u ∈ ws ∧ p u = true
  | u, [] => by simp
  | u, x :: xs => by
    simp only [List.filter, List.mem_cons]
    cases hp : p x with
    | false =>
      rw [mem_filter_iff_w8 p u xs]
      constructor
      · rintro ⟨hmem, hpu⟩; exact ⟨Or.inr hmem, hpu⟩
      · rintro ⟨ rfl | hmem, hpu⟩
        · rw [hp] at hpu; cases hpu
        · exact ⟨hmem, hpu⟩
    | true =>
      simp only [List.mem_cons, mem_filter_iff_w8 p u xs]
      constructor
      · rintro (rfl | ⟨hmem, hpu⟩)
        · exact ⟨Or.inl rfl, hp⟩
        · exact ⟨Or.inr hmem, hpu⟩
      · rintro ⟨rfl | hmem, hpu⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨hmem, hpu⟩

theorem noDupBoolWords_filter (p : List Bool -> Bool) :
    ∀ ws : List (List Bool), NoDupBoolWords ws -> NoDupBoolWords (ws.filter p)
  | [], _ => NoDupBoolWords.nil
  | u :: us, NoDupBoolWords.cons _ _ hnu hnd => by
    simp only [List.filter]
    cases hp : p u with
    | false => exact noDupBoolWords_filter p us hnd
    | true =>
      refine NoDupBoolWords.cons u (us.filter p) ?_ (noDupBoolWords_filter p us hnd)
      intro hm
      exact hnu ((mem_filter_iff_w8 p u us).mp hm).1

theorem allCoreWordsOfLen_spec :
    ∀ L : Nat,
      NoDupBoolWords (allCoreWordsOfLen L) ∧
      (∀ u : List Bool, u ∈ allCoreWordsOfLen L ↔ IsCoreParityWord u ∧ u.length = L)
  | 0 => by
    refine ⟨NoDupBoolWords.nil, fun u => ⟨(fun hm => by simp [allCoreWordsOfLen] at hm), ?_⟩⟩
    rintro ⟨hu, hlen⟩
    cases u with
    | nil => have hh := hu.1; simp at hh
    | cons _ _ => simp at hlen
  | 1 => by
    refine ⟨NoDupBoolWords.cons [true] [] (by simp) NoDupBoolWords.nil, fun u => ⟨?_, ?_⟩⟩
    · intro hm
      simp [allCoreWordsOfLen] at hm
      subst hm
      exact ⟨⟨rfl, rfl⟩, rfl⟩
    · rintro ⟨hu, hlen⟩
      cases u with
      | nil => simp at hlen
      | cons b rest =>
        cases rest with
        | nil =>
          have hb : b = true := by have hh := hu.1; simpa using hh
          subst hb; simp [allCoreWordsOfLen]
        | cons _ _ => simp at hlen
  | m + 2 => by
    have hinj : ∀ m1 m2 : List Bool,
        (true :: (m1 ++ [true])) = (true :: (m2 ++ [true])) -> m1 = m2 := by
      intro m1 m2 heq
      have ht := List.cons.inj heq |>.2
      have hrev := congrArg List.reverse ht
      rw [List.reverse_append, List.reverse_append] at hrev
      have hrm := List.cons.inj hrev |>.2
      simpa using congrArg List.reverse hrm
    have hnd : NoDupBoolWords (allCoreWordsOfLen (m + 2)) :=
      noDupBoolWords_map_inj (fun mid => true :: (mid ++ [true])) hinj _ (allBoolWordsOfLen_nodup m)
    refine ⟨hnd, fun u => ⟨?_, ?_⟩⟩
    · intro hm
      simp only [allCoreWordsOfLen, List.mem_map] at hm
      rcases hm with ⟨mid, hmid_mem, rfl⟩
      have hmid_len : mid.length = m := by
        have hall : ∀ (k : Nat) (v : List Bool), v ∈ allBoolWordsOfLen k -> v.length = k := by
          intro k; induction k with
          | zero => intro v hv; simp [allBoolWordsOfLen] at hv; subst hv; rfl
          | succ k' ih =>
            intro v hv
            simp only [allBoolWordsOfLen, List.mem_append] at hv
            rcases hv with h1 | h2
            · rcases List.mem_map.mp h1 with ⟨w0, hw0, rfl⟩; simp [ih w0 hw0]
            · rcases List.mem_map.mp h2 with ⟨w0, hw0, rfl⟩; simp [ih w0 hw0]
        exact hall m mid hmid_mem
      have hcore : IsCoreParityWord (true :: (mid ++ [true])) := by
        refine ⟨rfl, ?_⟩
        rw [List.reverse_cons, List.reverse_append]
        rfl
      have hlen : (true :: (mid ++ [true])).length = m + 2 := by
        simp [List.length_append, hmid_len]
      exact ⟨hcore, hlen⟩
    · rintro ⟨hu, hlen⟩
      cases u with
      | nil => simp at hlen
      | cons b rest =>
        have hb : b = true := by have hh := hu.1; simpa using hh
        subst hb
        have hrest_len : rest.length = m + 1 := by simp at hlen; omega
        have hrest_last : rest.reverse.head? = some true := by
          have hl := hu.2
          rw [List.reverse_cons] at hl
          cases hr : rest.reverse with
          | nil =>
            have hc := congrArg List.length hr
            simp at hc
            subst hc
            simp at hrest_len
          | cons br _ =>
            rw [hr] at hl; simpa using hl
        rcases list_eq_append_true_of_reverse_head rest hrest_last with ⟨mid, rfl⟩
        have hmid_len : mid.length = m := by
          rw [List.length_append, List.length_singleton] at hrest_len; omega
        simp only [allCoreWordsOfLen, List.mem_map]
        exact ⟨mid, (allBoolWordsOfLen_spec m).2 mid hmid_len, rfl⟩

theorem allCoreWordsUpToLen_spec :
    ∀ L_max : Nat,
      NoDupBoolWords (allCoreWordsUpToLen L_max) ∧
      (∀ u : List Bool, u ∈ allCoreWordsUpToLen L_max ↔ IsCoreParityWord u ∧ u.length ≤ L_max)
  | 0 => by
    refine ⟨NoDupBoolWords.nil, fun u => ⟨(fun hm => by simp [allCoreWordsUpToLen] at hm), ?_⟩⟩
    rintro ⟨hu, hle⟩
    cases u with
    | nil => have hh := hu.1; simp at hh
    | cons _ _ => simp at hle
  | L + 1 => by
    rcases allCoreWordsUpToLen_spec L with ⟨hnd_prev, hmem_prev⟩
    rcases allCoreWordsOfLen_spec (L + 1) with ⟨hnd_cur, hmem_cur⟩
    have hnd : NoDupBoolWords (allCoreWordsUpToLen (L + 1)) := by
      simp only [allCoreWordsUpToLen]
      apply noDupBoolWords_append _ _ hnd_prev hnd_cur
      intro u hu_prev hu_cur
      have hle := (hmem_prev u).mp hu_prev |>.2
      have heq := (hmem_cur u).mp hu_cur |>.2
      omega
    refine ⟨hnd, fun u => ?_⟩
    simp only [allCoreWordsUpToLen, List.mem_append, hmem_prev u, hmem_cur u]
    constructor
    · rintro (⟨hc, hle⟩ | ⟨hc, heq⟩)
      · exact ⟨hc, by omega⟩
      · exact ⟨hc, by omega⟩
    · rintro ⟨hc, hle⟩
      by_cases hlt : u.length ≤ L
      · exact Or.inl ⟨hc, hlt⟩
      · exact Or.inr ⟨hc, by omega⟩

/--
  Theorem W8.4b (`multiscale_first_hit_surviving_q0_leaves_nodup`, zero custom axioms):
  Unconditional Multi-Scale `NoDupNat` & Completeness Across All `IsFirstHitOnePair` `q = 0` Leaves:
  For EVERY length cutoff `L_max : Nat`:
  1. `NoDupNat (firstHitQ0LeavesUpToLen L_max)` holds across ALL `IsFirstHitOnePair u 0` leaves
     of arbitrary lengths `1 ≤ |u| ≤ L_max`!
  2. `NoDupNat (firstHitSurvivingQ0LeavesUpToLen L_max)` holds across ALL surviving `Mod373248`
     first-hit `q = 0` leaves up to length `L_max`, and `y ∈ firstHitSurvivingQ0LeavesUpToLen L_max`
     iff `∃ u`, `IsFirstHitOnePair u 0 ∧ u.length ≤ L_max ∧ isSurvivingMod373248Bool y = true ∧
     exactBackwardQuotient 1 u 0 = y`!
-/
theorem multiscale_first_hit_surviving_q0_leaves_nodup (L_max : Nat) :
    NoDupNat (firstHitQ0LeavesUpToLen L_max) ∧
    NoDupNat (firstHitSurvivingQ0LeavesUpToLen L_max) ∧
    (∀ y : Nat,
      y ∈ firstHitSurvivingQ0LeavesUpToLen L_max ↔
      ∃ u : List Bool,
        IsFirstHitOnePair u 0 ∧
        u.length ≤ L_max ∧
        isSurvivingMod373248Bool y = true ∧
        exactBackwardQuotient 1 u 0 = y) := by
  rcases allCoreWordsUpToLen_spec L_max with ⟨hnd_all, hmem_all⟩
  have hnd_fh : NoDupNat (firstHitQ0LeavesUpToLen L_max) := by
    unfold firstHitQ0LeavesUpToLen
    apply noDupNat_of_noDupBoolWords_inj _ _ (noDupBoolWords_filter _ _ hnd_all)
    intro u1 u2 hm1 hm2 heq
    rcases (mem_filter_iff_w8 _ u1 _).mp hm1 with ⟨hm1_all, hb1⟩
    rcases (mem_filter_iff_w8 _ u2 _).mp hm2 with ⟨hm2_all, hb2⟩
    have hc1 := (hmem_all u1).mp hm1_all |>.1
    have hc2 := (hmem_all u2).mp hm2_all |>.1
    have hfh1 := (isFirstHitOneQ0Bool_iff u1 hc1).mp hb1
    have hfh2 := (isFirstHitOneQ0Bool_iff u2 hc2).mp hb2
    exact (first_hit_one_pair_sound_and_injective u1 u2 0 0 hfh1 hfh2).2.2.2 heq |>.1
  have hnd_surv : NoDupNat (firstHitSurvivingQ0LeavesUpToLen L_max) := by
    unfold firstHitSurvivingQ0LeavesUpToLen
    apply noDupNat_of_noDupBoolWords_inj _ _ (noDupBoolWords_filter _ _ hnd_all)
    intro u1 u2 hm1 hm2 heq
    rcases (mem_filter_iff_w8 _ u1 _).mp hm1 with ⟨hm1_all, hand1⟩
    rcases (mem_filter_iff_w8 _ u2 _).mp hm2 with ⟨hm2_all, hand2⟩
    have hc1 := (hmem_all u1).mp hm1_all |>.1
    have hc2 := (hmem_all u2).mp hm2_all |>.1
    have hb1 : isFirstHitOneQ0Bool u1 = true := by
      cases h : isFirstHitOneQ0Bool u1 <;> simp [h] at hand1; rfl
    have hb2 : isFirstHitOneQ0Bool u2 = true := by
      cases h : isFirstHitOneQ0Bool u2 <;> simp [h] at hand2; rfl
    have hfh1 := (isFirstHitOneQ0Bool_iff u1 hc1).mp hb1
    have hfh2 := (isFirstHitOneQ0Bool_iff u2 hc2).mp hb2
    exact (first_hit_one_pair_sound_and_injective u1 u2 0 0 hfh1 hfh2).2.2.2 heq |>.1
  refine ⟨hnd_fh, hnd_surv, fun y => ⟨?_, ?_⟩⟩
  · intro hy_mem
    unfold firstHitSurvivingQ0LeavesUpToLen at hy_mem
    rcases List.mem_map.mp hy_mem with ⟨u, hu_filt, rfl⟩
    rcases (mem_filter_iff_w8 _ u _).mp hu_filt with ⟨hu_all, hand⟩
    rcases (hmem_all u).mp hu_all with ⟨hcore, hlen⟩
    have hfh_b : isFirstHitOneQ0Bool u = true := by
      cases h : isFirstHitOneQ0Bool u <;> simp [h] at hand; rfl
    have hsurv_b : isSurvivingMod373248Bool (exactBackwardQuotient 1 u 0) = true := by
      rw [hfh_b, Bool.true_and] at hand; exact hand
    exact ⟨u, (isFirstHitOneQ0Bool_iff u hcore).mp hfh_b, hlen, hsurv_b, rfl⟩
  · rintro ⟨u, hfh, hlen, hsurv, rfl⟩
    unfold firstHitSurvivingQ0LeavesUpToLen
    apply List.mem_map_of_mem
    apply (mem_filter_iff_w8 _ u _).mpr
    refine ⟨(hmem_all u).mpr ⟨hfh.1, hlen⟩, ?_⟩
    rw [(isFirstHitOneQ0Bool_iff u hfh.1).mpr hfh, hsurv]
    rfl

-- ----------------------------------------------------------------------------
-- Markov Skew-Product Bijectivity & Universal Forbidden `5 mod 6` Law (`W8.4c`)
-- ----------------------------------------------------------------------------

/-- Markov `b = false` suffix-shift transition on `[0, 2 * 3 ^ (w - 1))`. -/
def markovShiftFalse (w a : Nat) : Nat :=
  if a ≥ 1 then a - 1 else 2 * 3 ^ (w - 1) - 1

/-- Constructive inverse of `markovShiftFalse w` on `[0, 2 * 3 ^ (w - 1))`. -/
def markovShiftFalseInv (w a' : Nat) : Nat :=
  if a' + 1 < 2 * 3 ^ (w - 1) then a' + 1 else 0

/-- Markov `b = true` suffix-shift transition `[0, 2 * 3 ^ (w - 1)) -> [0, 2 * 3 ^ w)`. -/
def markovShiftTrue (w a : Nat) : Nat :=
  dlog2ModPow3 (w + 1) (3 * 2 ^ a + 1) - 1

theorem pow2_inj_mod_pow3_w8 (w e1 e2 : Nat) (hw : w ≥ 1)
    (he1 : e1 < 2 * 3 ^ (w - 1)) (he2 : e2 < 2 * 3 ^ (w - 1))
    (hmod : 2 ^ e1 % 3 ^ w = 2 ^ e2 % 3 ^ w) :
    e1 = e2 := by
  let P := 2 * 3 ^ (w - 1)
  let M := 3 ^ w
  have hlt_false : ∀ x y : Nat, x < y -> y < P -> 2 ^ x % M = 2 ^ y % M -> False := by
    intro x y hxy hy hxy_mod
    let d := y - x
    have hd_pos : 0 < d := by dsimp [d]; omega
    have hd_lt : d < P := by dsimp [d]; omega
    have hp1 : 2 ^ P % M = 1 := (pow2_totient_exact_valuation_all_weights w hw).2.2.1
    have hmul_P : (2 ^ (P - x) * 2 ^ x) % M = 1 := by
      rw [← Nat.pow_add, show P - x + x = P by omega, hp1]
    have hmul_eq : (2 ^ (P - x) * 2 ^ x) % M = (2 ^ (P - x) * 2 ^ y) % M := by
      rw [Nat.mul_mod (2 ^ (P - x)) (2 ^ x), hxy_mod, ← Nat.mul_mod]
    rw [show y = x + d by dsimp [d]; omega, Nat.pow_add 2 x d,
        ← Nat.mul_assoc (2 ^ (P - x)) (2 ^ x) (2 ^ d),
        Nat.mul_mod (2 ^ (P - x) * 2 ^ x) (2 ^ d) M,
        hmul_P, Nat.one_mul, Nat.mod_mod] at hmul_eq
    exact pow2_order_mod_pow3_exact w d hw hd_pos hd_lt hmul_eq.symm
  by_cases h12 : e1 < e2
  · exact False.elim (hlt_false e1 e2 h12 he2 hmod)
  · by_cases h21 : e2 < e1
    · exact False.elim (hlt_false e2 e1 h21 he1 hmod.symm)
    · omega

theorem dlog2ModPow3_unique_w8 (w r e : Nat) (hw : w ≥ 1) (hr : r % 3 ≠ 0)
    (he_lt : e < 2 * 3 ^ (w - 1)) (he_mod : 2 ^ e % 3 ^ w = r % 3 ^ w) :
    dlog2ModPow3 w r = e := by
  rcases dlog2ModPow3_spec w r hw hr with ⟨hd_lt, hd_mod⟩
  exact pow2_inj_mod_pow3_w8 w (dlog2ModPow3 w r) e hw hd_lt he_lt (hd_mod.trans he_mod.symm)

theorem mul3_add1_mod_mul3_w8 (X M : Nat) (hM : M ≥ 1) :
    (3 * X + 1) % (3 * M) = 3 * (X % M) + 1 := by
  have hr_lt : X % M < M := Nat.mod_lt X hM
  have hdm : X = M * (X / M) + X % M := (Nat.div_add_mod X M).symm
  have hexp : 3 * X + 1 = (3 * (X % M) + 1) + (3 * M) * (X / M) := by
    conv => lhs; rw [hdm]
    rw [Nat.mul_add 3 (M * (X / M)) (X % M), ← Nat.mul_assoc 3 M (X / M)]
    omega
  rw [hexp, Nat.add_mul_mod_self_left]
  exact Nat.mod_eq_of_lt (by omega)

theorem pow2_six_mul_mod9_w8 :
    ∀ q : Nat, 2 ^ (6 * q) % 9 = 1
  | 0 => rfl
  | q + 1 => by
    rw [Nat.mul_succ 6 q, Nat.pow_add 2 (6 * q) 6, Nat.mul_mod, pow2_six_mul_mod9_w8 q]

theorem markovShiftFalse_bijection_aux (P a : Nat) (hP : P ≥ 2) (ha : a < P) :
    (if a ≥ 1 then a - 1 else P - 1) < P ∧
    (if a + 1 < P then a + 1 else 0) < P ∧
    (if (if a ≥ 1 then a - 1 else P - 1) + 1 < P then
       (if a ≥ 1 then a - 1 else P - 1) + 1
     else 0) = a ∧
    (if (if a + 1 < P then a + 1 else 0) ≥ 1 then
       (if a + 1 < P then a + 1 else 0) - 1
     else P - 1) = a := by
  refine ⟨by split <;> omega, by split <;> omega, ?_, ?_⟩
  · split
    · split <;> omega
    · split <;> omega
  · split
    · split <;> omega
    · split <;> omega

/--
  Theorem W8.4c (`canonicalSuffixShift_markov_bijection_and_mod6_lock`, zero custom axioms):
  Exact Markov Skew-Product Bijectivity & Universal Forbidden `5 mod 6` Law:
  For EVERY weight `w ≥ 1`:
  1. Exact `b = false` Bijection on `[0, 2 * 3 ^ (w - 1))`:
     `markovShiftFalse w` and `markovShiftFalseInv w` are two-sided inverses on `[0, 2 * 3 ^ (w - 1))`!
  2. Exact `b = true` Bijection onto `{a' < 2 * 3 ^ w | a' % 6 = 1 ∨ a' % 6 = 3}`:
     - Forward Range & Mod-6 Lock: for every `a < 2 * 3 ^ (w - 1)`, `markovShiftTrue w a < 2 * 3 ^ w`
       AND `markovShiftTrue w a % 6 = 1 ∨ markovShiftTrue w a % 6 = 3` (`% 6 ≠ 5`!);
     - Strict Injectivity: `a1 < 2 * 3 ^ (w - 1) -> a2 < 2 * 3 ^ (w - 1) ->
       markovShiftTrue w a1 = markovShiftTrue w a2 -> a1 = a2`;
     - Constructive Surjectivity: every `a' < 2 * 3 ^ w` with `a' % 6 = 1 ∨ a' % 6 = 3` is hit
       by `a := dlog2ModPow3 w ((2 ^ (a' + 1) - 1) / 3) < 2 * 3 ^ (w - 1)`!
  3. Universal Forbidden `5 mod 6` Corollary Across ALL Collatz Core Parity Words (`w ≥ 2`):
     For EVERY `u : List Bool` with `IsCoreParityWord u` and `parityWeight u ≥ 2`,
       `canonicalSuffixShift u 1 % 6 = 1 ∨ canonicalSuffixShift u 1 % 6 = 3`
     (in particular, `canonicalSuffixShift u 1 % 6 ≠ 5` across the entire Collatz core tree for `w ≥ 2`!)!
-/
theorem canonicalSuffixShift_markov_bijection_and_mod6_lock :
    (∀ (w a : Nat), w ≥ 1 -> a < 2 * 3 ^ (w - 1) ->
      markovShiftFalse w a < 2 * 3 ^ (w - 1) ∧
      markovShiftFalseInv w a < 2 * 3 ^ (w - 1) ∧
      markovShiftFalseInv w (markovShiftFalse w a) = a ∧
      markovShiftFalse w (markovShiftFalseInv w a) = a) ∧
    (∀ (w a : Nat), w ≥ 1 -> a < 2 * 3 ^ (w - 1) ->
      markovShiftTrue w a < 2 * 3 ^ w ∧
      (markovShiftTrue w a % 6 = 1 ∨ markovShiftTrue w a % 6 = 3)) ∧
    (∀ (w a1 a2 : Nat), w ≥ 1 ->
      a1 < 2 * 3 ^ (w - 1) -> a2 < 2 * 3 ^ (w - 1) ->
      markovShiftTrue w a1 = markovShiftTrue w a2 -> a1 = a2) ∧
    (∀ (w a' : Nat), w ≥ 1 -> a' < 2 * 3 ^ w ->
      (a' % 6 = 1 ∨ a' % 6 = 3) ->
      ∃ a : Nat, a < 2 * 3 ^ (w - 1) ∧ markovShiftTrue w a = a') ∧
    (∀ u : List Bool, IsCoreParityWord u -> parityWeight u ≥ 2 ->
      canonicalSuffixShift u 1 % 6 = 1 ∨ canonicalSuffixShift u 1 % 6 = 3) := by
  -- Helper for `e := dlog2ModPow3 (w + 1) (3 * 2 ^ a + 1)`:
  have htrue_dlog : ∀ (w a : Nat), w ≥ 1 ->
      let e := dlog2ModPow3 (w + 1) (3 * 2 ^ a + 1)
      e ≥ 2 ∧ e < 2 * 3 ^ w ∧ (e % 6 = 2 ∨ e % 6 = 4) ∧
      2 ^ e % 3 ^ (w + 1) = (3 * 2 ^ a + 1) % 3 ^ (w + 1) := by
    intro w a hw
    dsimp only
    let t := 3 * 2 ^ a + 1
    rcases dlog2ModPow3_spec (w + 1) t (by omega) (by dsimp [t]; omega) with ⟨he_lt, he_mod⟩
    let e := dlog2ModPow3 (w + 1) t
    rw [show w + 1 - 1 = w by omega] at he_lt
    change e < 2 * 3 ^ w at he_lt
    change 2 ^ e % 3 ^ (w + 1) = t % 3 ^ (w + 1) at he_mod
    -- Mod `3` (`e % 2 = 0`):
    have h3_sp : 3 ^ (w + 1) = 3 * 3 ^ w := by rw [Nat.pow_succ, Nat.mul_comm]
    have he_m3 : 2 ^ e % 3 = 1 := by
      have h1 := mod_mul_mod_eq (2 ^ e) 3 (3 ^ w)
      have h2 := mod_mul_mod_eq t 3 (3 ^ w)
      rw [← h3_sp] at h1 h2
      rw [← h1, he_mod, h2]; dsimp [t]; omega
    have he_ev : e % 2 = 0 := (pow2_mod3_eq_one_iff_even e).mp he_m3
    -- Mod `9` (`2 ^ e % 9 ≠ 1` since `w ≥ 1 => 9 ∣ 3 ^ (w + 1)`):
    have h9_sp : 3 ^ (w + 1) = 9 * 3 ^ (w - 1) := by
      conv => lhs; rw [show w + 1 = 2 + (w - 1) by omega]; rw [Nat.pow_add]
    have he_m9 : 2 ^ e % 9 = t % 9 := by
      have h1 := mod_mul_mod_eq (2 ^ e) 9 (3 ^ (w - 1))
      have h2 := mod_mul_mod_eq t 9 (3 ^ (w - 1))
      rw [← h9_sp] at h1 h2
      rw [← h1, he_mod, h2]
    have he_m9_ne1 : 2 ^ e % 9 ≠ 1 := by
      intro h1
      rw [h1] at he_m9
      have hdm := (Nat.div_add_mod t 9).symm
      rw [← he_m9] at hdm
      have h2a_div3 : 2 ^ a % 3 = 0 := by dsimp [t] at hdm; omega
      exact pow2_mod3_nonzero_w5 a h2a_div3
    have he_ne0 : e ≠ 0 := by
      intro he0; rw [he0] at he_m9_ne1; exact he_m9_ne1 rfl
    have he_m6_ne0 : e % 6 ≠ 0 := by
      intro hm6
      have he6 : e = 6 * (e / 6) := by omega
      rw [he6] at he_m9_ne1
      exact he_m9_ne1 (pow2_six_mul_mod9_w8 (e / 6))
    have he_ge2 : e ≥ 2 := by omega
    have he_m6_24 : e % 6 = 2 ∨ e % 6 = 4 := by omega
    exact ⟨he_ge2, he_lt, he_m6_24, he_mod⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- Part 1: `b = false` bijection on `[0, 2 * 3 ^ (w - 1))`:
    intro w a hw ha_lt
    have hP_ge2 : 2 * 3 ^ (w - 1) ≥ 2 := by have hp := pow3_pos_nat (w - 1); omega
    unfold markovShiftFalse markovShiftFalseInv
    exact markovShiftFalse_bijection_aux (2 * 3 ^ (w - 1)) a hP_ge2 ha_lt
  · -- Part 2a: Forward range & mod-6 lock for `markovShiftTrue`:
    intro w a hw _
    rcases htrue_dlog w a hw with ⟨he_ge2, he_lt, he_m6, _⟩
    unfold markovShiftTrue
    refine ⟨by omega, ?_⟩
    rcases he_m6 with h2 | h4 <;> omega
  · -- Part 2b: Strict injectivity of `markovShiftTrue` on `[0, 2 * 3 ^ (w - 1))`:
    intro w a1 a2 hw ha1_lt ha2_lt heq_sh
    rcases htrue_dlog w a1 hw with ⟨he1_ge2, _, _, he1_mod⟩
    rcases htrue_dlog w a2 hw with ⟨he2_ge2, _, _, he2_mod⟩
    unfold markovShiftTrue at heq_sh
    have he_eq : dlog2ModPow3 (w + 1) (3 * 2 ^ a1 + 1) = dlog2ModPow3 (w + 1) (3 * 2 ^ a2 + 1) := by
      omega
    rw [he_eq] at he1_mod
    have ht_eq : (3 * 2 ^ a1 + 1) % 3 ^ (w + 1) = (3 * 2 ^ a2 + 1) % 3 ^ (w + 1) :=
      he1_mod.symm.trans he2_mod
    have h3_sp : 3 ^ (w + 1) = 3 * 3 ^ w := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [h3_sp, mul3_add1_mod_mul3_w8 (2 ^ a1) (3 ^ w) (pow3_pos_nat w),
        mul3_add1_mod_mul3_w8 (2 ^ a2) (3 ^ w) (pow3_pos_nat w)] at ht_eq
    have hm_eq : 2 ^ a1 % 3 ^ w = 2 ^ a2 % 3 ^ w := by omega
    exact pow2_inj_mod_pow3_w8 w a1 a2 hw ha1_lt ha2_lt hm_eq
  · -- Part 2c: Constructive surjectivity onto `{a' < 2 * 3 ^ w | a' % 6 = 1 ∨ a' % 6 = 3}`:
    intro w a' hw ha'_lt ha'_m6
    let e := a' + 1
    have hP_m6 : (2 * 3 ^ w) % 6 = 0 := by
      rw [show w = 1 + (w - 1) by omega, Nat.pow_add, Nat.pow_one]
      omega
    have he_m6 : e % 6 = 2 ∨ e % 6 = 4 := by dsimp [e]; rcases ha'_m6 with h1 | h3 <;> omega
    have he_lt : e < 2 * 3 ^ w := by
      have hne : e ≠ 2 * 3 ^ w := by
        intro heq; rw [heq, hP_m6] at he_m6; rcases he_m6 with h | h <;> cases h
      dsimp [e] at hne ⊢; omega
    -- Compute `2 ^ e % 9 ∈ {4, 7}`:
    have he_m9 : 2 ^ e % 9 = 4 ∨ 2 ^ e % 9 = 7 := by
      have hsp : e = 6 * (e / 6) + e % 6 := (Nat.div_add_mod e 6).symm
      rw [hsp, Nat.pow_add 2 (6 * (e / 6)) (e % 6), Nat.mul_mod,
          pow2_six_mul_mod9_w8 (e / 6), Nat.one_mul, Nat.mod_mod]
      rcases he_m6 with h2 | h4
      · left; rw [h2]
      · right; rw [h4]
    let m := (2 ^ e - 1) / 3
    have hm_spec : 3 * m + 1 = 2 ^ e ∧ m % 3 ≠ 0 := by
      have hdm := (Nat.div_add_mod (2 ^ e) 9).symm
      dsimp [m]
      rcases he_m9 with h4 | h7 <;> omega
    let a := dlog2ModPow3 w m
    rcases dlog2ModPow3_spec w m hw hm_spec.2 with ⟨ha_lt, ha_mod⟩
    change a < 2 * 3 ^ (w - 1) at ha_lt
    change 2 ^ a % 3 ^ w = m % 3 ^ w at ha_mod
    refine ⟨a, ha_lt, ?_⟩
    have h3_sp : 3 ^ (w + 1) = 3 * 3 ^ w := by rw [Nat.pow_succ, Nat.mul_comm]
    have ht_mod : 2 ^ e % 3 ^ (w + 1) = (3 * 2 ^ a + 1) % 3 ^ (w + 1) := by
      rw [← hm_spec.1, h3_sp,
          mul3_add1_mod_mul3_w8 m (3 ^ w) (pow3_pos_nat w),
          mul3_add1_mod_mul3_w8 (2 ^ a) (3 ^ w) (pow3_pos_nat w),
          ha_mod]
    have hdlog_eq : dlog2ModPow3 (w + 1) (3 * 2 ^ a + 1) = e :=
      dlog2ModPow3_unique_w8 (w + 1) (3 * 2 ^ a + 1) e (by omega) (by omega)
        (by rw [show w + 1 - 1 = w by omega]; exact he_lt) ht_mod
    unfold markovShiftTrue
    rw [hdlog_eq]
    dsimp [e]
  · -- Part 3: Universal forbidden `5 mod 6` law across ALL core parity words with `w ≥ 2`:
    intro u hu hw2
    rcases list_eq_append_true_of_reverse_head u hu.2 with ⟨v, rfl⟩
    have hw_v : parityWeight v ≥ 1 := by
      rw [parityWeight_append_w6] at hw2
      have h1 : parityWeight [true] = 1 := rfl
      rw [h1] at hw2; omega
    have hrec := (canonicalSuffixShift_append_markov_recurrence.2.2 v hw_v).2.2.1
    have hmk_eq : canonicalSuffixShift (v ++ [true]) 1 =
        markovShiftTrue (parityWeight v) (canonicalSuffixShift v 1) := hrec
    rcases htrue_dlog (parityWeight v) (canonicalSuffixShift v 1) hw_v with ⟨he_ge2, _, he_m6, _⟩
    rw [hmk_eq]
    unfold markovShiftTrue
    rcases he_m6 with h2 | h4 <;> omega

end CollatzFormal
