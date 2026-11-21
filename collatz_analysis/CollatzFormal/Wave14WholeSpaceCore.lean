/-
  CollatzFormal/Wave14WholeSpaceCore.lean
  Wave 14 Whole-Space Mathematical & CS Proof Loop (Core — Fronts A & B):
  1. Front A — `M1 = 19/5` Coset `4919 -> 4151` 42-Step `c39`/`c78` SRS Witness & Mixed Zero-Diagonal
     Non-Triangular `d = 2` Weak Matrix Orientation vs Integral Farkas Zero-Strict-Drop Lock (`W14_H1`),
     All-Dimension (`∀ d ≥ 1`, Including Full-Rank `d = 2` `[[2, 1], [1, 2]]` with `(M_s)_{1,1} ≥ 2,
     (M_s)_{1,0} ≥ 1` & Full-Rank `d = 3` `[[3, 1, 0], [1, 2, 1], [0, 1, 3]]`) Perron–Frobenius
     Column-Eigenweight & `.R`/`.L`-Boundary-Growth `ω^k` Matrix-Tower Collapse on `c39` & `c78`,
     All-Dimension (`∀ d ≥ 1`) 4-Rule Pure-Interior Block-Coupled Trace Syzygy, & Exact `∀ r ≥ 1`
     Iterated `leftAnchoredDP2Step` Affine-Carry Homomorphism, `1..5`-Cycle Freedom, `M1` Carry
     Separation, & Exponential `2^r` 1-Block Steiner `DP2` Cycle Lock (Branch P4.3)
  2. Front B — Universal Third-Order Four-Block `(U = 4)` `(4T) × (4T)` Cyclotomic Confluent
     Divisibility `2^((3*T*(T-1) + 4*T^2)*u) * (2^u - 1)^(6*T^2) * (2^u + 1)^(2*T^2) *
     (4^u + 2^u + 1)^(T^2) ∣ intDet (4*T) M0`, Strict Reduced Majorant Bound, & Unit-Grid Exactness,
     Rectangular `6 × 6` `(T = 2, U = 3)` Joint Row+Column `Nat.lcm` Divisibility & Odd-`W` Coprime
     Reduced Quotient Bound vs `(4, 7, 1)` Overlap Obstruction (`W14_H2`), Rank-3 Two-Base `9 × 9`
     `(T = 3, U = 3)` Exact 4-Variable Grassmann Identity, All-`u` (`∀ u ≥ 1`) Collatz-Cone Strict
     Positivity, Global `u = 1..4` Non-Vanishing (`P^1(F_61), P^1(F_43), P^1(F_41), P^1(F_53)`), &
     `(12, 19)` Upper-Convergent Sign-Flip, & Universal Two-Pivot Cross-Block Brox Telescoping +
     `5 × d_mult` 2-Adic Quotient Boost Eliminating Balanced `m = 3` `[(17, 2), (17, 2), (17, 26)]`
     (Branches P3.3 & P3.4)

  Zero `sorry`, zero `native_decide`, zero custom axioms.
-/

import CollatzFormal.Wave13WholeSpace

namespace CollatzFormal

-- ============================================================================
-- SECTION 1: Front A (Branch P4.3) — `4919 -> 4151` `c39`/`c78` Witness & Weak
--            `d = 2` Farkas Lock, All-Dimension Perron–Frobenius & Boundary-Growth
--            Matrix Collapse, 4-Rule Pure-Interior Trace Syzygy, & `∀ r ≥ 1`
--            Iterated `leftAnchoredDP2Step` Affine-Carry / Cycle / Steiner Laws
-- ============================================================================

-- ----------------------------------------------------------------------------
-- Section 1A: `4919 -> 4151` 42-Step `c39`/`c78` Derivation & Mixed Zero-Diagonal
--             Non-Triangular `d = 2` Weak Matrix Farkas Lock (`W14_H1`)
-- ----------------------------------------------------------------------------

private theorem natMatVec_two_expand_w14 (M : Fin 2 -> Fin 2 -> Nat) (r : Fin 2 -> Nat) (i : Fin 2) :
    natMatVec 2 M r i =
      M i ⟨0, by decide⟩ * r ⟨0, by decide⟩ + M i ⟨1, by decide⟩ * r ⟨1, by decide⟩ := by
  change (0 + M i ⟨0, by decide⟩ * r ⟨0, by decide⟩) +
    M i ⟨1, by decide⟩ * r ⟨1, by decide⟩ = _
  rw [Nat.zero_add]

private theorem bool_or_split_w14 {a b : Bool} (h : (a || b) = true) : a = true ∨ b = true := by
  cases a with
  | true => exact Or.inl rfl
  | false => exact Or.inr h

private theorem natSumPrefix_zero_w14 (d : Nat) (f : Fin d -> Nat)
    (hz : ∀ i : Fin d, f i = 0) : ∀ m : Nat, natSumPrefix d f m = 0
  | 0 => rfl
  | m + 1 => by
    simp only [natSumPrefix]
    by_cases hm : m < d
    · simp only [hm, dite_true, natSumPrefix_zero_w14 d f hz m, hz ⟨m, hm⟩]
    · simp only [hm, dite_false, natSumPrefix_zero_w14 d f hz m]

/-- Explicit mixed zero-diagonal non-triangular `d = 2` matrix assignment on `Fin 42` with
    `weakMat2DC39 s 0 0 = 1`, `weakMat2DC39 28 1 1 = 5 ≥ 2`, `weakMat2DC39 28 1 0 = 1 ≥ 1`,
    and `weakMat2DC39 37 0 1 = 1 ≥ 1`. Weakly orients all 39 rules of `c39` with strict matrix
    inequality on 20 rules, yet admits zero strict `v_0` drops by integral Farkas duality! -/
def weakMat2DC39 (s : Fin 42) (i j : Fin 2) : Nat :=
  match i.val, j.val with
  | 0, 0 => 1
  | 0, 1 =>
    match s.val with
    | 20 => 6 | 22 => 5 | 23 => 5 | 37 => 1 | _ => 0
  | 1, 0 =>
    match s.val with
    | 28 => 1 | 31 => 7 | _ => 0
  | _, _ =>
    match s.val with
    | 6 => 5 | 7 => 3 | 14 => 3 | 17 => 1 | 23 => 1 | 28 => 5 | 31 => 1 | 32 => 1 | _ => 0

/-- Order-independent positive integral Farkas row-0 multipliers `μ_0(r) ≥ 1` on `c39`. -/
def farkasMu0C39 : List (Fin 42) -> Nat
  | a :: b :: _ =>
    match a.val, b.val with
    | 1, 14 => 1  | 1, 18 => 12 | 2, 13 => 13 | 2, 20 => 11
    | 4, 14 => 1  | 4, 18 => 1  | 5, 13 => 2  | 5, 20 => 1
    | 28, 6 => 4  | 28, 7 => 2  | 28, 8 => 2  | 28, 18 => 8
    | 29, 20 => 9 | 31, 6 => 7  | 31, 7 => 1  | 31, 8 => 1
    | 31, 14 => 9 | 31, 18 => 1 | 32, 13 => 13 | 32, 20 => 1
    | 33, 22 => 8 | 35, 16 => 3 | 35, 23 => 6 | 36, 22 => 14
    | 37, 9 => 3  | 37, 10 => 1 | 37, 11 => 1 | 37, 17 => 1
    | 37, 21 => 2 | 38, 16 => 18 | 38, 23 => 1 | 39, 22 => 3
    | 40, 9 => 1  | 40, 10 => 1 | 40, 11 => 1 | 40, 17 => 13
    | 40, 21 => 1 | 41, 16 => 1 | 41, 23 => 1 | _, _ => 1
  | _ => 1

/-- Order-independent non-negative integral Farkas row-1 multipliers `μ_1(r) ≥ 0` on `c39`
    (non-zero on only two rules: `(33, 22) -> (17, 37)` and `(35, 16) -> (21, 28)`). -/
def farkasMu1C39 : List (Fin 42) -> Nat
  | a :: b :: _ =>
    if a.val == 33 && b.val == 22 then 1
    else if a.val == 35 && b.val == 16 then 2
    else 0
  | _ => 0

/-- 42-step `(prefix_len, rule_idx_in_all11OmitR3List)` trace of `4919 -> 4151`. -/
def trace4919To4151 : List (Nat × Nat) :=
  [(0, 1), (1, 6), (2, 6), (3, 5), (4, 4), (5, 6), (6, 5), (7, 3), (8, 2), (9, 4),
   (10, 5), (11, 3), (12, 7), (0, 1), (1, 6), (2, 5), (3, 3), (4, 2), (5, 3), (6, 2),
   (7, 4), (8, 5), (9, 3), (10, 2), (11, 4), (12, 9), (0, 1), (1, 5), (0, 0), (1, 4),
   (0, 0), (1, 6), (2, 6), (3, 6), (4, 5), (5, 3), (6, 2), (7, 4), (8, 5), (9, 4),
   (10, 5), (11, 8)]

private def rulePairAt (rs : List (List MixedSRSSym × List MixedSRSSym)) :
    Nat -> Option (List MixedSRSSym × List MixedSRSSym)
  | 0 => rs.head?
  | k + 1 =>
    match rs with
    | [] => none
    | _ :: tl => rulePairAt tl k

private theorem rulePairAt_mem :
    ∀ (rs : List (List MixedSRSSym × List MixedSRSSym)) (idx : Nat)
      (p : List MixedSRSSym × List MixedSRSSym),
      rulePairAt rs idx = some p -> p ∈ rs
  | [], 0, _, h => by simp [rulePairAt] at h
  | r0 :: _, 0, p, h => by
    simp only [rulePairAt, List.head?_cons, Option.some.injEq] at h
    subst h; exact List.Mem.head _
  | [], _ + 1, _, h => by simp [rulePairAt] at h
  | r0 :: tl, k + 1, p, h =>
    List.mem_cons_of_mem r0 (rulePairAt_mem tl k p h)

private def isPrefixBool (pat w : List MixedSRSSym) : Bool :=
  decide (w.take pat.length = pat)

private theorem split_of_isPrefixBool_eq_true :
    ∀ (pat w : List MixedSRSSym),
      w.take pat.length = pat -> w = pat ++ w.drop pat.length
  | [], _, _ => rfl
  | _ :: _, [], h => by simp at h
  | p0 :: ptl, w0 :: wtl, h => by
    simp only [List.length_cons, List.take_succ_cons, List.cons.injEq] at h
    rcases h with ⟨h0, htl⟩
    subst h0
    simp only [List.length_cons, List.drop_succ_cons, List.cons_append, List.cons.injEq, true_and]
    exact split_of_isPrefixBool_eq_true ptl wtl htl

private def finWordPairMemBool {N : Nat} (p : List (Fin N) × List (Fin N))
    (rules : List (List (Fin N) × List (Fin N))) : Bool :=
  rules.any (fun r => decide (r = p))

/-- Replay `steps` from `cur`, verifying each rewrite uses `all11OmitR3List` AND its exact
    `TwoSided(2 × 3)` and `TwoSided(2 × 6)` contextual labellings belong to `c39` and `c78`! -/
def replayTraceInC39C78Bool
    (c39 : List (List (Fin 42) × List (Fin 42)))
    (c78 : List (List (Fin 84) × List (Fin 84))) :
    List MixedSRSSym -> List (Nat × Nat) -> List MixedSRSSym -> Bool
  | cur, [], target => decide (cur = target)
  | cur, (pLen, rIdx) :: rest, target =>
    match rulePairAt all11OmitR3List rIdx with
    | none => false
    | some (lhs, rhs) =>
      let pre := cur.take pLen
      let rem := cur.drop pLen
      if decide (pre.length = pLen) && isPrefixBool lhs rem then
        let sfx := rem.drop lhs.length
        let q := evalCollatzSemL2 pre 0
        let hq : q < 2 := evalCollatzSemL2_lt pre 0
        let a3 := evalCollatzSemWord 3 sfx 0
        let ha3 : a3 < 3 := evalCollatzSemWord_lt 3 (by decide) sfx 0 (by decide)
        let a6 := evalCollatzSemWord 6 sfx 0
        let ha6 : a6 < 6 := evalCollatzSemWord_lt 6 (by decide) sfx 0 (by decide)
        let r3 := (labelCollatzWordTwoSided 3 (by decide) lhs q hq a3 ha3,
                   labelCollatzWordTwoSided 3 (by decide) rhs q hq a3 ha3)
        let r6 := (labelCollatzWordTwoSided 6 (by decide) lhs q hq a6 ha6,
                   labelCollatzWordTwoSided 6 (by decide) rhs q hq a6 ha6)
        finWordPairMemBool r3 c39 &&
        finWordPairMemBool r6 c78 &&
        replayTraceInC39C78Bool c39 c78 (pre ++ rhs ++ sfx) rest target
      else false

private theorem take_append_drop_eq_w14 :
    ∀ (k : Nat) (xs : List MixedSRSSym), xs.take k ++ xs.drop k = xs
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | k + 1, x :: xs => by
    simp only [List.take_succ_cons, List.drop_succ_cons, List.cons_append,
               take_append_drop_eq_w14 k xs]

private theorem replayTraceInC39C78Bool_sound
    (c39 : List (List (Fin 42) × List (Fin 42)))
    (c78 : List (List (Fin 84) × List (Fin 84))) :
    ∀ (steps : List (Nat × Nat)) (cur target : List MixedSRSSym),
      replayTraceInC39C78Bool c39 c78 cur steps target = true ->
      srsReachesFromList all11OmitR3List cur target
  | [], cur, target, hb => by
    have heq : cur = target := of_decide_eq_true hb
    subst heq; exact .refl _
  | (pLen, rIdx) :: rest, cur, target, hb => by
    unfold replayTraceInC39C78Bool at hb
    cases hr_opt : rulePairAt all11OmitR3List rIdx with
    | none => rw [hr_opt] at hb; cases hb
    | some pair =>
      rcases pair with ⟨lhs, rhs⟩
      rw [hr_opt] at hb; dsimp only at hb
      split at hb
      · next hcond =>
        rcases bool_and_split hcond with ⟨_, hpref_b⟩
        rcases bool_and_split hb with ⟨_, hrest_b⟩
        have hmem_r : (lhs, rhs) ∈ all11OmitR3List := rulePairAt_mem all11OmitR3List rIdx _ hr_opt
        have hrem_eq : cur.drop pLen = lhs ++ (cur.drop pLen).drop lhs.length :=
          split_of_isPrefixBool_eq_true lhs (cur.drop pLen) (of_decide_eq_true hpref_b)
        have hcur_eq : cur = cur.take pLen ++ lhs ++ (cur.drop pLen).drop lhs.length := by
          have ht := (take_append_drop_eq_w14 pLen cur).symm
          rw [hrem_eq, ← List.append_assoc] at ht
          exact ht
        have hstep : srsStepFromList all11OmitR3List cur
            (cur.take pLen ++ rhs ++ (cur.drop pLen).drop lhs.length) :=
          ⟨cur.take pLen, lhs, rhs, (cur.drop pLen).drop lhs.length, hmem_r, hcur_eq, rfl⟩
        exact .step hstep (replayTraceInC39C78Bool_sound c39 c78 rest _ target hrest_b)
      · cases hb

def checkWeakMat2DRuleBool (N : Nat) (M : Fin N -> Fin 2 -> Fin 2 -> Nat)
    (l r : List (Fin N)) : Bool :=
  let ml := evalFinWordMat N 2 M l
  let mr := evalFinWordMat N 2 M r
  let z0 : Fin 2 := ⟨0, by decide⟩
  let z1 : Fin 2 := ⟨1, by decide⟩
  decide (ml z0 z0 ≥ mr z0 z0) && decide (ml z0 z1 ≥ mr z0 z1) &&
  decide (ml z1 z0 ≥ mr z1 z0) && decide (ml z1 z1 ≥ mr z1 z1)

def checkAllWeakMat2DBool (N : Nat) (M : Fin N -> Fin 2 -> Fin 2 -> Nat) :
    List (List (Fin N) × List (Fin N)) -> Bool
  | [] => true
  | (l, r) :: rs => checkWeakMat2DRuleBool N M l r && checkAllWeakMat2DBool N M rs

def countStrictMat2DRules (N : Nat) (M : Fin N -> Fin 2 -> Fin 2 -> Nat) :
    List (List (Fin N) × List (Fin N)) -> Nat
  | [] => 0
  | (l, r) :: rs =>
    let ml := evalFinWordMat N 2 M l
    let mr := evalFinWordMat N 2 M r
    let z0 : Fin 2 := ⟨0, by decide⟩
    let z1 : Fin 2 := ⟨1, by decide⟩
    let s := if ml z0 z0 > mr z0 z0 || ml z0 z1 > mr z0 z1 ||
                ml z1 z0 > mr z1 z0 || ml z1 z1 > mr z1 z1 then 1 else 0
    s + countStrictMat2DRules N M rs

private theorem checkAllWeakMat2DBool_sound (N : Nat) (M : Fin N -> Fin 2 -> Fin 2 -> Nat) :
    ∀ rules : List (List (Fin N) × List (Fin N)),
      checkAllWeakMat2DBool N M rules = true ->
      ∀ r ∈ rules, ∀ i j : Fin 2, evalFinWordMat N 2 M r.1 i j ≥ evalFinWordMat N 2 M r.2 i j
  | [], _, _, hr => by cases hr
  | (l0, r0) :: rs, hb, r, hr => by
    unfold checkAllWeakMat2DBool at hb
    rcases bool_and_split hb with ⟨hw0, hrs⟩
    cases hr with
    | head =>
      unfold checkWeakMat2DRuleBool at hw0
      rcases bool_and_split hw0 with ⟨h3, h11⟩
      rcases bool_and_split h3 with ⟨h2, h10⟩
      rcases bool_and_split h2 with ⟨h00, h01⟩
      intro i j
      rcases (by have := i.isLt; omega : i.val = 0 ∨ i.val = 1) with hi | hi <;>
      rcases (by have := j.isLt; omega : j.val = 0 ∨ j.val = 1) with hj | hj
      · rw [show i = ⟨0, by decide⟩ from Fin.ext hi, show j = ⟨0, by decide⟩ from Fin.ext hj]
        exact of_decide_eq_true h00
      · rw [show i = ⟨0, by decide⟩ from Fin.ext hi, show j = ⟨1, by decide⟩ from Fin.ext hj]
        exact of_decide_eq_true h01
      · rw [show i = ⟨1, by decide⟩ from Fin.ext hi, show j = ⟨0, by decide⟩ from Fin.ext hj]
        exact of_decide_eq_true h10
      · rw [show i = ⟨1, by decide⟩ from Fin.ext hi, show j = ⟨1, by decide⟩ from Fin.ext hj]
        exact of_decide_eq_true h11
    | tail _ htl =>
      exact checkAllWeakMat2DBool_sound N M rs hrs r htl

/-- Basis vector `e_{s0, j0} : Fin N -> Fin 2 -> Nat` (`1` at `(s0, j0)`, `0` elsewhere). -/
def basisVec2D (N : Nat) (s0 : Fin N) (j0 : Fin 2) (s : Fin N) (j : Fin 2) : Nat :=
  if s.val == s0.val && j.val == j0.val then 1 else 0

private theorem evalFinWordVec_linear_2d (N : Nat) (M : Fin N -> Fin 2 -> Fin 2 -> Nat)
    (v : Fin N -> Fin 2 -> Nat) :
    ∀ (w : List (Fin N)) (i : Fin 2),
      evalFinWordVec N 2 M v w i =
        natSumPrefix N (fun s0 =>
          v s0 ⟨0, by decide⟩ * evalFinWordVec N 2 M (basisVec2D N s0 ⟨0, by decide⟩) w i +
          v s0 ⟨1, by decide⟩ * evalFinWordVec N 2 M (basisVec2D N s0 ⟨1, by decide⟩) w i) N := by
  have hsum_add : ∀ (f g : Fin N -> Nat) (m : Nat),
      natSumPrefix N (fun s => f s + g s) m = natSumPrefix N f m + natSumPrefix N g m := by
    intro f g m; induction m with
    | zero => rfl
    | succ m' ih =>
      simp only [natSumPrefix]
      by_cases hm : m' < N
      · simp only [hm, dite_true, ih]; omega
      · simp [hm, ih]
  have hsum_mul : ∀ (c : Nat) (f : Fin N -> Nat) (m : Nat),
      c * natSumPrefix N f m = natSumPrefix N (fun s => c * f s) m := by
    intro c f m; induction m with
    | zero => simp [natSumPrefix]
    | succ m' ih =>
      simp only [natSumPrefix]
      by_cases hm : m' < N
      · simp only [hm, dite_true, Nat.mul_add, ih]
      · simp [hm, ih]
  have hdelta : ∀ (s : Fin N) (j : Fin 2),
      v s j = natSumPrefix N (fun s0 =>
        v s0 ⟨0, by decide⟩ * basisVec2D N s0 ⟨0, by decide⟩ s j +
        v s0 ⟨1, by decide⟩ * basisVec2D N s0 ⟨1, by decide⟩ s j) N := by
    intro s j
    have hst : ∀ m : Nat, m ≤ N ->
        natSumPrefix N (fun s0 =>
          v s0 ⟨0, by decide⟩ * basisVec2D N s0 ⟨0, by decide⟩ s j +
          v s0 ⟨1, by decide⟩ * basisVec2D N s0 ⟨1, by decide⟩ s j) m =
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
          · rw [show j = ⟨0, by decide⟩ from Fin.ext hj]; simp [basisVec2D]
          · rw [show j = ⟨1, by decide⟩ from Fin.ext hj]; simp [basisVec2D]
        · have hne_b : (s.val == m') = false := beq_false_of_ne heq
          have h0 : basisVec2D N ⟨m', hm_lt⟩ ⟨0, by decide⟩ s j = 0 := by simp [basisVec2D, hne_b]
          have h1 : basisVec2D N ⟨m', hm_lt⟩ ⟨1, by decide⟩ s j = 0 := by simp [basisVec2D, hne_b]
          rw [h0, h1, Nat.mul_zero, Nat.mul_zero, Nat.add_zero, Nat.add_zero]
          by_cases hlt : s.val < m'
          · rw [ite_true_of_w10 hlt, ite_true_of_w10 (by omega)]
          · rw [ite_false_of_w10 hlt, ite_false_of_w10 (by omega)]
    rw [hst N (Nat.le_refl N), ite_true_of_w10 s.isLt]
  intro w; induction w with
  | nil =>
    intro i
    exact (natSumPrefix_zero_w14 N _ (fun _ => by simp [evalFinWordVec]) N).symm
  | cons s rest ih =>
    intro i
    change v s i + natMatVec 2 (M s) (evalFinWordVec N 2 M v rest) i = _
    rw [natMatVec_two_expand_w14, ih ⟨0, by decide⟩, ih ⟨1, by decide⟩]
    conv => lhs; lhs; rw [hdelta s i]
    rw [hsum_mul (M s i ⟨0, by decide⟩), hsum_mul (M s i ⟨1, by decide⟩),
        ← hsum_add, ← hsum_add]
    have hcongr : ∀ m : Nat, m ≤ N ->
        natSumPrefix N (fun s0 =>
          (v s0 ⟨0, by decide⟩ * basisVec2D N s0 ⟨0, by decide⟩ s i +
            v s0 ⟨1, by decide⟩ * basisVec2D N s0 ⟨1, by decide⟩ s i) +
          (M s i ⟨0, by decide⟩ *
             (v s0 ⟨0, by decide⟩ * evalFinWordVec N 2 M (basisVec2D N s0 ⟨0, by decide⟩) rest ⟨0, by decide⟩ +
              v s0 ⟨1, by decide⟩ * evalFinWordVec N 2 M (basisVec2D N s0 ⟨1, by decide⟩) rest ⟨0, by decide⟩) +
           M s i ⟨1, by decide⟩ *
             (v s0 ⟨0, by decide⟩ * evalFinWordVec N 2 M (basisVec2D N s0 ⟨0, by decide⟩) rest ⟨1, by decide⟩ +
              v s0 ⟨1, by decide⟩ * evalFinWordVec N 2 M (basisVec2D N s0 ⟨1, by decide⟩) rest ⟨1, by decide⟩))) m =
        natSumPrefix N (fun s0 =>
          v s0 ⟨0, by decide⟩ * evalFinWordVec N 2 M (basisVec2D N s0 ⟨0, by decide⟩) (s :: rest) i +
          v s0 ⟨1, by decide⟩ * evalFinWordVec N 2 M (basisVec2D N s0 ⟨1, by decide⟩) (s :: rest) i) m := by
      intro m hm; induction m with
      | zero => rfl
      | succ m' ihm =>
        have hm_lt : m' < N := hm
        simp only [natSumPrefix, hm_lt, dite_true, ihm (Nat.le_of_lt hm)]
        congr 1
        simp only [evalFinWordVec, natMatVec_two_expand_w14, Nat.mul_add]
        ac_rfl
    exact hcongr N (Nat.le_refl N)

/-- Weighted Farkas LHS vs RHS sum over `rules` in `Fin 42` using `farkasMu0C39` and `farkasMu1C39`. -/
def farkasWeightedVecSum42 (v : Fin 42 -> Fin 2 -> Nat) :
    List (List (Fin 42) × List (Fin 42)) -> (Nat × Nat)
  | [] => (0, 0)
  | (l, r) :: rs =>
    let rest := farkasWeightedVecSum42 v rs
    let m0 := farkasMu0C39 l
    let m1 := farkasMu1C39 l
    (m0 * evalFinWordVec 42 2 weakMat2DC39 v l ⟨0, by decide⟩ +
       m1 * evalFinWordVec 42 2 weakMat2DC39 v l ⟨1, by decide⟩ + rest.1,
     m0 * evalFinWordVec 42 2 weakMat2DC39 v r ⟨0, by decide⟩ +
       m1 * evalFinWordVec 42 2 weakMat2DC39 v r ⟨1, by decide⟩ + rest.2)

def checkFarkasBasisLeC39Bool (rules : List (List (Fin 42) × List (Fin 42))) : Bool :=
  let rec loop : Nat -> Bool
    | 0 => true
    | k + 1 =>
      if h : k < 42 then
        let p0 := farkasWeightedVecSum42 (basisVec2D 42 ⟨k, h⟩ ⟨0, by decide⟩) rules
        let p1 := farkasWeightedVecSum42 (basisVec2D 42 ⟨k, h⟩ ⟨1, by decide⟩) rules
        decide (p0.1 ≤ p0.2 ∧ p1.1 ≤ p1.2) && loop k
      else loop k
  rules.all (fun r => decide (farkasMu0C39 r.1 ≥ 1)) && loop 42

set_option maxRecDepth 131072 in
/--
  Theorem W14.1a (`m1_4919_to_4151_c39_c78_and_weak_d2_farkas_cert`,
  choice-free `zero custom axioms`):
  Explicit Choice-Free Certificate for `4919 -> 4151` (`M1 = 19/5` Coset) Inside `c39` & `c78`,
  20-Rule Strict Matrix Drop of `weakMat2DC39` (`(M_28)_{1,1} = 5 ≥ 2, (M_28)_{1,0} = 1 ≥ 1`), &
  All-84-Basis Integral Farkas Inequality (`Branch P4.3`, `W14_H1`).
-/
theorem m1_4919_to_4151_c39_c78_and_weak_d2_farkas_cert :
    let c39 := filterFinParikhUnoriented 42 wtTwoSidedMod3OmitR3
      (twoSidedLabelledCollatzRules 3 (by decide) all11OmitR3List)
    let c78 := filterFinParikhUnoriented 84 wtTwoSidedMod6OmitR3
      (twoSidedLabelledCollatzRules 6 (by decide) all11OmitR3List)
    5 * 4919 - 19 = 3 * 2 ^ 13 ∧
    collatzIter 5 4919 = 4151 ∧
    trace4919To4151.length = 42 ∧
    replayTraceInC39C78Bool c39 c78
      (.L :: encodePosBinAux 14 4919 ++ [.R])
      trace4919To4151
      (.L :: encodePosBinAux 14 4151 ++ [.R]) = true ∧
    weakMat2DC39 ⟨28, by decide⟩ ⟨1, by decide⟩ ⟨1, by decide⟩ = 5 ∧
    weakMat2DC39 ⟨28, by decide⟩ ⟨1, by decide⟩ ⟨0, by decide⟩ = 1 ∧
    weakMat2DC39 ⟨37, by decide⟩ ⟨0, by decide⟩ ⟨1, by decide⟩ = 1 ∧
    checkAllWeakMat2DBool 42 weakMat2DC39 c39 = true ∧
    countStrictMat2DRules 42 weakMat2DC39 c39 = 20 ∧
    checkFarkasBasisLeC39Bool c39 = true := by decide

private theorem farkasLockGen42 (rules : List (List (Fin 42) × List (Fin 42)))
    (hfark_b : checkFarkasBasisLeC39Bool rules = true)
    (v : Fin 42 -> Fin 2 -> Nat)
    (hv_weak : ∀ r ∈ rules, ∀ i : Fin 2,
      evalFinWordVec 42 2 weakMat2DC39 v r.1 i ≥ evalFinWordVec 42 2 weakMat2DC39 v r.2 i) :
    ∀ r ∈ rules,
      evalFinWordVec 42 2 weakMat2DC39 v r.1 ⟨0, by decide⟩ =
        evalFinWordVec 42 2 weakMat2DC39 v r.2 ⟨0, by decide⟩ := by
  unfold checkFarkasBasisLeC39Bool at hfark_b
  rcases bool_and_split hfark_b with ⟨hmu0_all, hloop42⟩
  have hmu0_pos : ∀ r ∈ rules, farkasMu0C39 r.1 ≥ 1 :=
    fun r hr => of_decide_eq_true (List.all_eq_true.mp hmu0_all r hr)
  have hbasis_le : ∀ s0 : Fin 42,
      let p0 := farkasWeightedVecSum42 (basisVec2D 42 s0 ⟨0, by decide⟩) rules
      let p1 := farkasWeightedVecSum42 (basisVec2D 42 s0 ⟨1, by decide⟩) rules
      p0.1 ≤ p0.2 ∧ p1.1 ≤ p1.2 := by
    have hlp : ∀ n : Nat, n ≤ 42 -> checkFarkasBasisLeC39Bool.loop rules n = true ->
        ∀ k : Nat, k < n -> (hk : k < 42) ->
          let p0 := farkasWeightedVecSum42 (basisVec2D 42 ⟨k, hk⟩ ⟨0, by decide⟩) rules
          let p1 := farkasWeightedVecSum42 (basisVec2D 42 ⟨k, hk⟩ ⟨1, by decide⟩) rules
          p0.1 ≤ p0.2 ∧ p1.1 ≤ p1.2 := by
      intro n; induction n with
      | zero => intros _ _ _ hlt; omega
      | succ n' ih =>
        intro hn_le hn k hkn hk42
        have hn42 : n' < 42 := hn_le
        unfold checkFarkasBasisLeC39Bool.loop at hn
        simp only [hn42, dite_true] at hn
        rcases bool_and_split hn with ⟨hcur, hprev⟩
        by_cases hkeq : k = n'
        · subst hkeq; exact of_decide_eq_true hcur
        · exact ih (Nat.le_of_lt hn_le) hprev k (by omega) hk42
    intro s0; exact hlp 42 (Nat.le_refl 42) hloop42 s0.val s0.isLt s0.isLt
  have hsum_add42 : ∀ (f g : Fin 42 -> Nat) (m : Nat),
      natSumPrefix 42 (fun s => f s + g s) m = natSumPrefix 42 f m + natSumPrefix 42 g m := by
    intro f g m; induction m with
    | zero => rfl
    | succ m' ih =>
      simp only [natSumPrefix]
      by_cases hm : m' < 42
      · simp only [hm, dite_true, ih]; omega
      · simp [hm, ih]
  have hsum_mul42 : ∀ (c : Nat) (f : Fin 42 -> Nat) (m : Nat),
      c * natSumPrefix 42 f m = natSumPrefix 42 (fun s => c * f s) m := by
    intro c f m; induction m with
    | zero => simp [natSumPrefix]
    | succ m' ih =>
      simp only [natSumPrefix]
      by_cases hm : m' < 42
      · simp only [hm, dite_true, Nat.mul_add, ih]
      · simp [hm, ih]
  have hfark_lin : ∀ rs : List (List (Fin 42) × List (Fin 42)),
      (farkasWeightedVecSum42 v rs).1 =
        natSumPrefix 42 (fun s0 =>
          v s0 ⟨0, by decide⟩ * (farkasWeightedVecSum42 (basisVec2D 42 s0 ⟨0, by decide⟩) rs).1 +
          v s0 ⟨1, by decide⟩ * (farkasWeightedVecSum42 (basisVec2D 42 s0 ⟨1, by decide⟩) rs).1) 42 ∧
      (farkasWeightedVecSum42 v rs).2 =
        natSumPrefix 42 (fun s0 =>
          v s0 ⟨0, by decide⟩ * (farkasWeightedVecSum42 (basisVec2D 42 s0 ⟨0, by decide⟩) rs).2 +
          v s0 ⟨1, by decide⟩ * (farkasWeightedVecSum42 (basisVec2D 42 s0 ⟨1, by decide⟩) rs).2) 42 := by
    intro rs; induction rs with
    | nil =>
      exact ⟨(natSumPrefix_zero_w14 42 _ (fun _ => by simp [farkasWeightedVecSum42]) 42).symm,
             (natSumPrefix_zero_w14 42 _ (fun _ => by simp [farkasWeightedVecSum42]) 42).symm⟩
    | cons r0 tl ih =>
      rcases r0 with ⟨l0, r0_w⟩
      simp only [farkasWeightedVecSum42]
      rw [evalFinWordVec_linear_2d 42 weakMat2DC39 v l0 ⟨0, by decide⟩,
          evalFinWordVec_linear_2d 42 weakMat2DC39 v l0 ⟨1, by decide⟩,
          evalFinWordVec_linear_2d 42 weakMat2DC39 v r0_w ⟨0, by decide⟩,
          evalFinWordVec_linear_2d 42 weakMat2DC39 v r0_w ⟨1, by decide⟩,
          ih.1, ih.2,
          hsum_mul42 (farkasMu0C39 l0), hsum_mul42 (farkasMu1C39 l0),
          hsum_mul42 (farkasMu0C39 l0), hsum_mul42 (farkasMu1C39 l0),
          ← hsum_add42, ← hsum_add42, ← hsum_add42, ← hsum_add42]
      have hcg : ∀ (f1 f2 : Fin 42 -> Nat), (∀ s, f1 s = f2 s) ->
          ∀ m : Nat, natSumPrefix 42 f1 m = natSumPrefix 42 f2 m := by
        intro f1 f2 hf m; induction m with
        | zero => rfl
        | succ m' ihm =>
          simp only [natSumPrefix]
          by_cases hm : m' < 42
          · simp [hm, ihm, hf ⟨m', hm⟩]
          · simp [hm, ihm]
      refine ⟨hcg _ _ (fun s => by simp only [Nat.mul_add]; ac_rfl) 42,
              hcg _ _ (fun s => by simp only [Nat.mul_add]; ac_rfl) 42⟩
  have hsum_le_v : (farkasWeightedVecSum42 v rules).1 ≤ (farkasWeightedVecSum42 v rules).2 := by
    rcases hfark_lin rules with ⟨h1, h2⟩
    rw [h1, h2]
    exact natSumPrefix_mono_w5 42 _ _ (fun s0 => by
      rcases hbasis_le s0 with ⟨hb0, hb1⟩
      have hm0 := Nat.mul_le_mul_left (v s0 ⟨0, by decide⟩) hb0
      have hm1 := Nat.mul_le_mul_left (v s0 ⟨1, by decide⟩) hb1
      omega) 42
  have hsqueeze : ∀ rs : List (List (Fin 42) × List (Fin 42)),
      (∀ r ∈ rs, farkasMu0C39 r.1 ≥ 1) ->
      (∀ r ∈ rs, ∀ i : Fin 2,
        evalFinWordVec 42 2 weakMat2DC39 v r.1 i ≥ evalFinWordVec 42 2 weakMat2DC39 v r.2 i) ->
      (farkasWeightedVecSum42 v rs).1 ≥ (farkasWeightedVecSum42 v rs).2 ∧
      ((farkasWeightedVecSum42 v rs).1 = (farkasWeightedVecSum42 v rs).2 ->
        ∀ r ∈ rs,
          evalFinWordVec 42 2 weakMat2DC39 v r.1 ⟨0, by decide⟩ =
            evalFinWordVec 42 2 weakMat2DC39 v r.2 ⟨0, by decide⟩) := by
    intro rs; induction rs with
    | nil => intros _ _; exact ⟨Nat.le_refl 0, fun _ _ hr => by cases hr⟩
    | cons r0 tl ih =>
      rcases r0 with ⟨l0, r0_w⟩
      intro hm_pos hw_rs
      rcases ih (fun r hr => hm_pos r (List.mem_cons_of_mem _ hr))
                (fun r hr => hw_rs r (List.mem_cons_of_mem _ hr)) with ⟨htl_ge, htl_eq⟩
      have hm0_ge1 : farkasMu0C39 l0 ≥ 1 := hm_pos (l0, r0_w) List.mem_cons_self
      have hw0 : evalFinWordVec 42 2 weakMat2DC39 v l0 ⟨0, by decide⟩ ≥
          evalFinWordVec 42 2 weakMat2DC39 v r0_w ⟨0, by decide⟩ :=
        hw_rs (l0, r0_w) List.mem_cons_self ⟨0, by decide⟩
      have hw1 : evalFinWordVec 42 2 weakMat2DC39 v l0 ⟨1, by decide⟩ ≥
          evalFinWordVec 42 2 weakMat2DC39 v r0_w ⟨1, by decide⟩ :=
        hw_rs (l0, r0_w) List.mem_cons_self ⟨1, by decide⟩
      have hm0_le := Nat.mul_le_mul_left (farkasMu0C39 l0) hw0
      have hm1_le := Nat.mul_le_mul_left (farkasMu1C39 l0) hw1
      simp only [farkasWeightedVecSum42]
      refine ⟨by omega, ?_⟩
      intro heq_tot r hr_m
      have heq_m0 : farkasMu0C39 l0 * evalFinWordVec 42 2 weakMat2DC39 v l0 ⟨0, by decide⟩ =
          farkasMu0C39 l0 * evalFinWordVec 42 2 weakMat2DC39 v r0_w ⟨0, by decide⟩ := by omega
      have heq_tl : (farkasWeightedVecSum42 v tl).1 = (farkasWeightedVecSum42 v tl).2 := by omega
      cases hr_m with
      | head => exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < farkasMu0C39 l0) heq_m0
      | tail _ htl => exact htl_eq heq_tl r htl
  rcases hsqueeze rules hmu0_pos hv_weak with ⟨hsum_ge_v, himp_eq⟩
  exact himp_eq (Nat.le_antisymm hsum_le_v hsum_ge_v)

/--
  Theorem W14.1b (`m1_4919_to_4151_reach_and_weak_d2_farkas_lock`,
  `zero custom axioms`):
  Universal `4919 -> 4151` SRS Reachability & Integral Farkas Zero-Strict-Drop Lock on `weakMat2DC39`
  Across ALL `v : Fin 42 -> Fin 2 -> Nat` (`Branch P4.3`, `W14_H1`).
-/
theorem m1_4919_to_4151_reach_and_weak_d2_farkas_lock :
    let c39 := filterFinParikhUnoriented 42 wtTwoSidedMod3OmitR3
      (twoSidedLabelledCollatzRules 3 (by decide) all11OmitR3List)
    srsReachesFromList all11OmitR3List
      (.L :: encodePosBin 4919 ++ [.R])
      (.L :: encodePosBin 4151 ++ [.R]) ∧
    (∀ r ∈ c39, ∀ i j : Fin 2,
      evalFinWordMat 42 2 weakMat2DC39 r.1 i j ≥ evalFinWordMat 42 2 weakMat2DC39 r.2 i j) ∧
    (∀ v : Fin 42 -> Fin 2 -> Nat,
      (∀ r ∈ c39, ∀ i : Fin 2,
        evalFinWordVec 42 2 weakMat2DC39 v r.1 i ≥ evalFinWordVec 42 2 weakMat2DC39 v r.2 i) ->
      ∀ r ∈ c39,
        evalFinWordVec 42 2 weakMat2DC39 v r.1 ⟨0, by decide⟩ =
          evalFinWordVec 42 2 weakMat2DC39 v r.2 ⟨0, by decide⟩) := by
  let c39 := filterFinParikhUnoriented 42 wtTwoSidedMod3OmitR3
    (twoSidedLabelledCollatzRules 3 (by decide) all11OmitR3List)
  let c78 := filterFinParikhUnoriented 84 wtTwoSidedMod6OmitR3
    (twoSidedLabelledCollatzRules 6 (by decide) all11OmitR3List)
  rcases m1_4919_to_4151_c39_c78_and_weak_d2_farkas_cert with
    ⟨_, _, _, hrep, _, _, _, hweak_b, _, hfark_b⟩
  have henc_fuel : ∀ (f2 f1 n : Nat), n < 2 ^ f2 -> f2 ≤ f1 ->
      encodePosBinAux f2 n = encodePosBinAux f1 n := by
    intro f2; induction f2 with
    | zero =>
      intro f1 n hn2 _
      have hn0 : n = 0 := by simp at hn2; exact hn2
      subst hn0; cases f1 <;> rfl
    | succ k2 ih =>
      intro f1 n hn2 hle
      cases f1 with
      | zero => omega
      | succ k1 =>
        simp only [encodePosBinAux]
        by_cases hle1 : n ≤ 1
        · simp [hle1]
        · simp only [hle1, ite_false]
          apply congrArg ((if n % 2 == 1 then MixedSRSSym.B1 else MixedSRSSym.B0) :: ·)
          exact ih k1 (n / 2) (by rw [Nat.pow_succ] at hn2; omega) (by omega)
  have henc4919 : encodePosBin 4919 = encodePosBinAux 14 4919 :=
    (henc_fuel 14 4919 4919 (by decide) (by decide)).symm
  have henc4151 : encodePosBin 4151 = encodePosBinAux 14 4151 :=
    (henc_fuel 14 4151 4151 (by decide) (by decide)).symm
  have hreach := replayTraceInC39C78Bool_sound c39 c78 trace4919To4151 _ _ hrep
  rw [← henc4919, ← henc4151] at hreach
  exact ⟨hreach,
         checkAllWeakMat2DBool_sound 42 weakMat2DC39 c39 hweak_b,
         farkasLockGen42 c39 hfark_b⟩

-- ----------------------------------------------------------------------------
-- Section 1B: All-Dimension (`∀ d ≥ 1`, Including Full-Rank `d = 2` `(M_s)_{1,1} ≥ 2`
--             & Full-Rank `d = 3`) Perron–Frobenius Column-Eigenweight &
--             `.R`/`.L`-Boundary-Growth Matrix-Tower Collapse on `c39` & `c78`
-- ----------------------------------------------------------------------------

private def prodFinWordW14 (N : Nat) (m : Fin N -> Nat) : List (Fin N) -> Nat
  | [] => 1
  | s :: rest => m s * prodFinWordW14 N m rest

private theorem evalFinAffine1D_fst_w14 (N : Nat) (m c : Fin N -> Nat) :
    ∀ u : List (Fin N), (evalFinAffine1D N m c u).1 = prodFinWordW14 N m u
  | [] => rfl
  | s :: rest => by simp only [evalFinAffine1D, prodFinWordW14, evalFinAffine1D_fst_w14 N m c rest]

private theorem mem_of_mem_filterRulesByPosMults_w14 {α : Type} :
    ∀ (rs : List α) (ms : List Nat) (r : α),
      r ∈ filterRulesByPosMults rs ms -> r ∈ rs
  | [], _, _, hr => by cases hr
  | _ :: _, [], _, hr => by cases hr
  | r0 :: rs, 0 :: ms, r, hr =>
    List.mem_cons_of_mem r0 (mem_of_mem_filterRulesByPosMults_w14 rs ms r hr)
  | r0 :: rs, (_ + 1) :: ms, r, hr => by
    cases hr with
    | head => exact List.Mem.head _
    | tail _ htl => exact List.mem_cons_of_mem r0 (mem_of_mem_filterRulesByPosMults_w14 rs ms r htl)

private theorem syzygy_forces_parikh_eq_w14
    (N : Nat) (rules : List (List (Fin N) × List (Fin N))) (mults : List Nat)
    (hsyz : checkPositiveParikhSyzygyFastBool N rules mults = true) :
    ∀ wt : Fin N -> Nat,
      (∀ r ∈ rules, evalFinParikh N wt r.1 ≥ evalFinParikh N wt r.2) ->
      ∀ r ∈ rules, evalFinParikh N wt r.1 = evalFinParikh N wt r.2 := by
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
  intro wt hweak
  rcases weightedParikh_eq_sum_sym N wt rules mults with ⟨hl_sum, hr_sum⟩
  have htot_le : weightedParikhLhs N wt rules mults ≤ weightedParikhRhs N wt rules mults := by
    rw [hl_sum, hr_sum]
    exact natSumPrefix_mono_w5 N _ _ (fun s => Nat.mul_le_mul_left (wt s) (hsym_le s)) N
  exact weightedParikh_strict_of_mem N wt rules mults hlen hpos_m hweak htot_le

private theorem checkNoL1RulesBool_sound_w14 (M : Nat) :
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
    | tail _ htl => exact checkNoL1RulesBool_sound_w14 M rs hrs r htl

private theorem checkNoL0RulesBool_sound_w14 (M : Nat) :
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
    | tail _ htl => exact checkNoL0RulesBool_sound_w14 M rs hrs r htl

private theorem hasTwoToTwoRuleBool_sound_w14 (N : Nat) (a b c d : Fin N) :
    ∀ rs : List (List (Fin N) × List (Fin N)),
      hasTwoToTwoRuleBool N a.val b.val c.val d.val rs = true -> ([a, b], [c, d]) ∈ rs
  | [], h => by cases h
  | (l, r) :: rs, h => by
    unfold hasTwoToTwoRuleBool at h
    rcases bool_or_split_w14 h with h0 | htl
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
    · exact List.mem_cons_of_mem _ (hasTwoToTwoRuleBool_sound_w14 N a b c d rs htl)

private theorem checkSumPosListsBool_sound_w14 :
    ∀ (m0 m1 : List Nat),
      checkSumPosListsBool m0 m1 = true ->
      m0.length = m1.length ∧ ∀ i : Nat, i < m0.length -> natAt m0 i + natAt m1 i ≥ 1
  | [], [], _ => ⟨rfl, fun _ hi => by simp at hi⟩
  | [], _ :: _, hb => by cases hb
  | _ :: _, [], hb => by cases hb
  | u0 :: us0, u1 :: us1, hb => by
    unfold checkSumPosListsBool at hb
    rcases bool_and_split hb with ⟨hu, hrest⟩
    rcases checkSumPosListsBool_sound_w14 us0 us1 hrest with ⟨hlen, hall⟩
    refine ⟨by simp [hlen], ?_⟩
    intro i hi
    cases i with
    | zero => exact of_decide_eq_true hu
    | succ j => exact hall j (by simp at hi; omega)

private theorem coverByPosMults_w14 {α : Type} :
    ∀ (rs : List α) (m0 m1 : List Nat),
      rs.length = m0.length -> rs.length = m1.length ->
      (∀ i : Nat, i < m0.length -> natAt m0 i + natAt m1 i ≥ 1) ->
      ∀ r ∈ rs, r ∈ filterRulesByPosMults rs m0 ∨ r ∈ filterRulesByPosMults rs m1
  | [], _, _, _, _, _, _, hr => by cases hr
  | _ :: _, [], _, hl0, _, _, _, _ => by simp at hl0
  | _ :: _, _ :: _, [], _, hl1, _, _, _ => by simp at hl1
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
      have ih := coverByPosMults_w14 rt ut0 ut1
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

set_option maxRecDepth 65536 in
private theorem c39_c78_w14_sub_certs :
    let c39 := filterFinParikhUnoriented 42 wtTwoSidedMod3OmitR3
      (twoSidedLabelledCollatzRules 3 (by decide) all11OmitR3List)
    let c78 := filterFinParikhUnoriented 84 wtTwoSidedMod6OmitR3
      (twoSidedLabelledCollatzRules 6 (by decide) all11OmitR3List)
    (checkAllRulesShapeBool 3 c39 = true ∧
     c39 ≠ [] ∧
     checkPositiveParikhSyzygyFastBool 42
       (filterRulesByPosMults c39 syzC39L0Only) (filterPosMults syzC39L0Only) = true ∧
     checkNoL1RulesBool 3 (filterRulesByPosMults c39 syzC39L0Only) = true ∧
     checkPositiveParikhSyzygyFastBool 42
       (filterRulesByPosMults c39 syzC39L1Only) (filterPosMults syzC39L1Only) = true ∧
     checkNoL0RulesBool 3 (filterRulesByPosMults c39 syzC39L1Only) = true ∧
     c39.length = syzC39L0Only.length ∧
     checkSumPosListsBool syzC39L0Only syzC39L1Only = true) ∧
    (checkAllRulesShapeBool 6 c78 = true ∧
     c78 ≠ [] ∧
     checkPositiveParikhSyzygyFastBool 84
       (filterRulesByPosMults c78 syzC78L0Only) (filterPosMults syzC78L0Only) = true ∧
     checkNoL1RulesBool 6 (filterRulesByPosMults c78 syzC78L0Only) = true ∧
     checkPositiveParikhSyzygyFastBool 84
       (filterRulesByPosMults c78 syzC78L1Only) (filterPosMults syzC78L1Only) = true ∧
     checkNoL0RulesBool 6 (filterRulesByPosMults c78 syzC78L1Only) = true ∧
     c78.length = syzC78L0Only.length ∧
     checkSumPosListsBool syzC78L0Only syzC78L1Only = true) := by decide

/-- `k`-level `ω^k` Hofbauer–Waldmann natural matrix tower over `Fin N` of dimension `d ≥ 1`
    where every stage `M` has positive diagonal (`M s i i ≥ 1`) and admits a positive column
    Perron–Frobenius eigenweight `w : Fin d -> Nat` (`w i ≥ 1`, `m s ≥ 1`) satisfying
    `∑_i w_i * M s i j = m s * w_j`. Includes full-rank `d = 2` `[[2, 1], [1, 2]]` (`M 1 1 = 2 ≥ 2,
    M 1 0 = 1 ≥ 1, det = 3 ≠ 0`) and full-rank `d = 3` `[[3, 1, 0], [1, 2, 1], [0, 1, 3]]` (`det = 12 ≠ 0`)! -/
def GenOmegaPosDiagColPropMatTower (N d : Nat) (hd : d ≥ 1) :
    Nat -> List (List (Fin N) × List (Fin N)) -> Prop
  | 0, rules => rules = []
  | k + 1, rules =>
    rules = [] ∨
    ∃ (rem : List (List (Fin N) × List (Fin N)))
      (M : Fin N -> Fin d -> Fin d -> Nat)
      (v : Fin N -> Fin d -> Nat)
      (w : Fin d -> Nat) (m : Fin N -> Nat),
      (∀ s : Fin N, ∀ i : Fin d, M s i i ≥ 1) ∧
      (∀ i : Fin d, w i ≥ 1) ∧
      (∀ s : Fin N, m s ≥ 1) ∧
      (∀ s : Fin N, ∀ j : Fin d,
        natSumPrefix d (fun i => w i * M s i j) d = m s * w j) ∧
      (∀ r ∈ rules,
        (∀ i j : Fin d, evalFinWordMat N d M r.1 i j ≥ evalFinWordMat N d M r.2 i j) ∧
        (∀ i : Fin d, evalFinWordVec N d M v r.1 i ≥ evalFinWordVec N d M v r.2 i)) ∧
      (∀ r ∈ rules,
        ¬ (evalFinWordVec N d M v r.1 ⟨0, hd⟩ > evalFinWordVec N d M v r.2 ⟨0, hd⟩) ->
        r ∈ rem) ∧
      GenOmegaPosDiagColPropMatTower N d hd k rem

/-- `k`-level `ω^k` Hofbauer–Waldmann natural matrix tower over `Fin (14 * M)` of dimension `d ≥ 1`
    where active interior symbols (`s ≥ 4 * M`) have `M s = I_d`, active `.L_q` symbols have
    `M s 0 0 = 1` and carrier-uniform top row `M s 0 j = B_q j`, while ALL `.R` matrices (`2 * M ≤ s < 4 * M`)
    AND ALL bottom `d - 1` rows (`i ≥ 1`) of `.L` matrices are COMPLETELY ARBITRARY! -/
def GenOmegaBoundaryGrowthIntIdMatTower (M d : Nat) (hd : d ≥ 1) :
    Nat -> List (List (Fin (14 * M)) × List (Fin (14 * M))) -> Prop
  | 0, rules => rules = []
  | k + 1, rules =>
    rules = [] ∨
    ∃ (rem : List (List (Fin (14 * M)) × List (Fin (14 * M))))
      (mat : Fin (14 * M) -> Fin d -> Fin d -> Nat)
      (v : Fin (14 * M) -> Fin d -> Nat)
      (B0 B1 : Fin d -> Nat),
      (∀ s : Fin (14 * M), s.val < 2 * M -> mat s ⟨0, hd⟩ ⟨0, hd⟩ = 1) ∧
      (∀ s : Fin (14 * M), s.val < M -> ∀ j : Fin d, j.val ≥ 1 -> mat s ⟨0, hd⟩ j = B0 j) ∧
      (∀ s : Fin (14 * M), M ≤ s.val -> s.val < 2 * M ->
        ∀ j : Fin d, j.val ≥ 1 -> mat s ⟨0, hd⟩ j = B1 j) ∧
      (∀ s : Fin (14 * M), s.val ≥ 4 * M ->
        symAppearsInRulesBool (14 * M) s.val rules = true ->
        ∀ i j : Fin d, mat s i j = natMatId d i j) ∧
      (∀ r ∈ rules,
        (∀ i j : Fin d, evalFinWordMat (14 * M) d mat r.1 i j ≥ evalFinWordMat (14 * M) d mat r.2 i j) ∧
        (∀ i : Fin d, evalFinWordVec (14 * M) d mat v r.1 i ≥ evalFinWordVec (14 * M) d mat v r.2 i)) ∧
      (∀ r ∈ rules,
        ¬ (evalFinWordVec (14 * M) d mat v r.1 ⟨0, hd⟩ >
           evalFinWordVec (14 * M) d mat v r.2 ⟨0, hd⟩) ->
        r ∈ rem) ∧
      GenOmegaBoundaryGrowthIntIdMatTower M d hd k rem

private theorem natSumPrefix_add_w14 (d : Nat) (f g : Fin d -> Nat) :
    ∀ m : Nat, natSumPrefix d (fun i => f i + g i) m = natSumPrefix d f m + natSumPrefix d g m
  | 0 => rfl
  | m + 1 => by
    simp only [natSumPrefix]
    by_cases hm : m < d
    · simp only [hm, dite_true, natSumPrefix_add_w14 d f g m]; omega
    · simp [hm, natSumPrefix_add_w14 d f g m]

private theorem natSumPrefix_mul_right_w14 (d c : Nat) (f : Fin d -> Nat) :
    ∀ m : Nat, natSumPrefix d f m * c = natSumPrefix d (fun i => f i * c) m
  | 0 => Nat.zero_mul c
  | m + 1 => by
    simp only [natSumPrefix]
    by_cases hm : m < d
    · simp only [hm, dite_true, Nat.add_mul, natSumPrefix_mul_right_w14 d c f m]
    · simp [hm, natSumPrefix_mul_right_w14 d c f m]

private theorem natSumPrefix_mul_left_w14 (d c : Nat) (f : Fin d -> Nat) :
    ∀ m : Nat, c * natSumPrefix d f m = natSumPrefix d (fun i => c * f i) m
  | 0 => Nat.mul_zero c
  | m + 1 => by
    simp only [natSumPrefix]
    by_cases hm : m < d
    · simp only [hm, dite_true, Nat.mul_add, natSumPrefix_mul_left_w14 d c f m]
    · simp [hm, natSumPrefix_mul_left_w14 d c f m]

private theorem natSumPrefix_swap_w14 (d1 d2 : Nat) (H : Fin d1 -> Fin d2 -> Nat) :
    ∀ m1 : Nat,
      natSumPrefix d1 (fun i => natSumPrefix d2 (fun k => H i k) d2) m1 =
        natSumPrefix d2 (fun k => natSumPrefix d1 (fun i => H i k) m1) d2
  | 0 => (natSumPrefix_zero_w14 d2 _ (fun _ => rfl) d2).symm
  | m1 + 1 => by
    simp only [natSumPrefix]
    by_cases hm1 : m1 < d1
    · simp only [hm1, dite_true, natSumPrefix_swap_w14 d1 d2 H m1,
                 ← natSumPrefix_add_w14 d2]
    · simp only [hm1, dite_false, natSumPrefix_swap_w14 d1 d2 H m1, Nat.add_zero]

private theorem perron_col_word_invariants (N d : Nat)
    (M : Fin N -> Fin d -> Fin d -> Nat)
    (v : Fin N -> Fin d -> Nat)
    (w : Fin d -> Nat) (m : Fin N -> Nat)
    (hcol : ∀ s : Fin N, ∀ j : Fin d,
      natSumPrefix d (fun i => w i * M s i j) d = m s * w j) :
    let wt_v : Fin N -> Nat := fun s => natSumPrefix d (fun i => w i * v s i) d
    (∀ (u : List (Fin N)) (j : Fin d),
      natSumPrefix d (fun i => w i * evalFinWordMat N d M u i j) d =
        prodFinWordW14 N m u * w j) ∧
    (∀ u : List (Fin N),
      natSumPrefix d (fun i => w i * evalFinWordVec N d M v u i) d =
        (evalFinAffine1D N m wt_v u).2) := by
  let wt_v : Fin N -> Nat := fun s => natSumPrefix d (fun i => w i * v s i) d
  have hdelta_id : ∀ j : Fin d,
      natSumPrefix d (fun i => w i * natMatId d i j) d = w j := by
    intro j
    have hst : ∀ n : Nat, n ≤ d ->
        natSumPrefix d (fun i => w i * natMatId d i j) n =
          if j.val < n then w j else 0 := by
      intro n hn; induction n with
      | zero => simp [natSumPrefix]
      | succ n' ih =>
        have hn_lt : n' < d := hn
        simp only [natSumPrefix, hn_lt, dite_true, ih (Nat.le_of_lt hn)]
        by_cases heq : j.val = n'
        · have hjf : (⟨n', hn_lt⟩ : Fin d) = j := Fin.ext heq.symm
          rw [hjf, ite_false_of_w10 (by omega : ¬ (j.val < n')),
              ite_true_of_w10 (by omega : j.val < n' + 1)]
          simp [natMatId]
        · have hne : n' ≠ j.val := fun h => heq h.symm
          simp only [natMatId, hne, ite_false, Nat.mul_zero, Nat.add_zero]
          by_cases hlt : j.val < n'
          · rw [ite_true_of_w10 hlt, ite_true_of_w10 (by omega)]
          · rw [ite_false_of_w10 hlt, ite_false_of_w10 (by omega)]
    rw [hst d (Nat.le_refl d), ite_true_of_w10 j.isLt]
  have hmat_step : ∀ (s : Fin N) (vec : Fin d -> Nat),
      natSumPrefix d (fun i => w i * natMatVec d (M s) vec i) d =
        m s * natSumPrefix d (fun k => w k * vec k) d := by
    intro s vec
    have hcg1 : ∀ n : Nat,
        natSumPrefix d (fun i => w i * natMatVec d (M s) vec i) n =
          natSumPrefix d (fun i => natSumPrefix d (fun k => (w i * M s i k) * vec k) d) n := by
      intro n; induction n with
      | zero => rfl
      | succ n' ih =>
        simp only [natSumPrefix]
        by_cases hn : n' < d
        · simp only [hn, dite_true, ih]
          congr 1
          change w ⟨n', hn⟩ * natSumPrefix d (fun k => M s ⟨n', hn⟩ k * vec k) d = _
          rw [natSumPrefix_mul_left_w14 d (w ⟨n', hn⟩)]
          have hc2 : ∀ p : Nat,
              natSumPrefix d (fun k => w ⟨n', hn⟩ * (M s ⟨n', hn⟩ k * vec k)) p =
                natSumPrefix d (fun k => (w ⟨n', hn⟩ * M s ⟨n', hn⟩ k) * vec k) p := by
            intro p; induction p with
            | zero => rfl
            | succ p' ihp =>
              simp only [natSumPrefix]
              by_cases hp : p' < d <;> simp [hp, ihp, Nat.mul_assoc]
          exact hc2 d
        · simp [hn, ih]
    rw [hcg1 d, natSumPrefix_swap_w14 d d (fun i k => (w i * M s i k) * vec k) d]
    have hcg2 : ∀ p : Nat,
        natSumPrefix d (fun k => natSumPrefix d (fun i => (w i * M s i k) * vec k) d) p =
          natSumPrefix d (fun k => m s * (w k * vec k)) p := by
      intro p; induction p with
      | zero => rfl
      | succ p' ihp =>
        simp only [natSumPrefix]
        by_cases hp : p' < d
        · simp only [hp, dite_true, ihp]
          congr 1
          rw [← natSumPrefix_mul_right_w14 d (vec ⟨p', hp⟩) (fun i => w i * M s i ⟨p', hp⟩) d,
              hcol s ⟨p', hp⟩, Nat.mul_assoc]
        · simp [hp, ihp]
    rw [hcg2 d, ← natSumPrefix_mul_left_w14 d (m s)]
  refine ⟨?_, ?_⟩
  · intro u; induction u with
    | nil =>
      intro j; simp [evalFinWordMat, prodFinWordW14, hdelta_id j]
    | cons s rest ih =>
      intro j
      change natSumPrefix d (fun i => w i * natMatVec d (M s) (fun k => evalFinWordMat N d M rest k j) i) d =
        (m s * prodFinWordW14 N m rest) * w j
      rw [hmat_step s (fun k => evalFinWordMat N d M rest k j), ih j, Nat.mul_assoc]
  · intro u; induction u with
    | nil =>
      exact natSumPrefix_zero_w14 d _ (fun _ => Nat.mul_zero _) d
    | cons s rest ih =>
      change natSumPrefix d (fun i => w i * (v s i + natMatVec d (M s) (evalFinWordVec N d M v rest) i)) d =
        wt_v s + m s * (evalFinAffine1D N m wt_v rest).2
      have hdist : ∀ p : Nat,
          natSumPrefix d (fun i => w i * (v s i + natMatVec d (M s) (evalFinWordVec N d M v rest) i)) p =
            natSumPrefix d (fun i => w i * v s i + w i * natMatVec d (M s) (evalFinWordVec N d M v rest) i) p := by
        intro p; induction p with
        | zero => rfl
        | succ p' ihp =>
          simp only [natSumPrefix]
          by_cases hp : p' < d
          · simp only [hp, dite_true, Nat.mul_add]
          · simp only [hp, dite_false, ihp]
      rw [hdist d, natSumPrefix_add_w14 d, hmat_step s (evalFinWordVec N d M v rest), ih]

private theorem natMatVec_id_eq_w14 (d : Nat) (mat_s : Fin d -> Fin d -> Nat)
    (vec : Fin d -> Nat) (hid : ∀ i j : Fin d, mat_s i j = natMatId d i j) :
    ∀ i : Fin d, natMatVec d mat_s vec i = vec i := by
  intro i
  change natSumPrefix d (fun k => mat_s i k * vec k) d = vec i
  have hst : ∀ m : Nat, m ≤ d ->
      natSumPrefix d (fun k => mat_s i k * vec k) m =
        if i.val < m then vec i else 0 := by
    intro m hm; induction m with
    | zero => simp [natSumPrefix]
    | succ m' ih =>
      have hm_lt : m' < d := hm
      simp only [natSumPrefix, hm_lt, dite_true, ih (Nat.le_of_lt hm)]
      rw [hid i ⟨m', hm_lt⟩]
      by_cases heq : i.val = m'
      · have hif : (⟨m', hm_lt⟩ : Fin d) = i := Fin.ext heq.symm
        rw [hif, ite_false_of_w10 (by omega : ¬ (i.val < m')),
            ite_true_of_w10 (by omega : i.val < m' + 1)]
        simp [natMatId]
      · simp only [natMatId, heq, ite_false, Nat.zero_mul, Nat.add_zero]
        by_cases hlt : i.val < m'
        · rw [ite_true_of_w10 hlt, ite_true_of_w10 (by omega)]
        · rw [ite_false_of_w10 hlt, ite_false_of_w10 (by omega)]
  rw [hst d (Nat.le_refl d), ite_true_of_w10 i.isLt]

private theorem idIntDim_vec_eval_w14 (M_mod d : Nat)
    (mat : Fin (14 * M_mod) -> Fin d -> Fin d -> Nat)
    (v : Fin (14 * M_mod) -> Fin d -> Nat) :
    (∀ w : List (Fin (14 * M_mod)),
      (∀ s ∈ w, ∀ i j : Fin d, mat s i j = natMatId d i j) ->
      ∀ i : Fin d, evalFinWordVec (14 * M_mod) d mat v w i =
        evalFinParikh (14 * M_mod) (fun s => v s i) w) ∧
    (∀ w : List (Fin (14 * M_mod)),
      checkWordRightOrIntBool M_mod w = true ->
      (∀ s ∈ w, s.val ≥ 4 * M_mod -> ∀ i j : Fin d, mat s i j = natMatId d i j) ->
      ∀ i : Fin d, evalFinWordVec (14 * M_mod) d mat v w i =
        evalFinParikh (14 * M_mod) (fun s => v s i) w) := by
  have h1 : ∀ w : List (Fin (14 * M_mod)),
      (∀ s ∈ w, ∀ i j : Fin d, mat s i j = natMatId d i j) ->
      ∀ i : Fin d, evalFinWordVec (14 * M_mod) d mat v w i =
        evalFinParikh (14 * M_mod) (fun s => v s i) w := by
    intro w; induction w with
    | nil => intros; rfl
    | cons s rest ih =>
      intro hall i
      have hs_id := hall s List.mem_cons_self
      have ih_r := ih (fun x hx => hall x (List.mem_cons_of_mem s hx))
      change v s i + natMatVec d (mat s) (evalFinWordVec (14 * M_mod) d mat v rest) i =
        v s i + evalFinParikh (14 * M_mod) (fun x => v x i) rest
      rw [natMatVec_id_eq_w14 d (mat s) _ hs_id i, ih_r i]
  refine ⟨h1, ?_⟩
  intro w; induction w with
  | nil => intros; rfl
  | cons s rest ih =>
    cases rest with
    | nil =>
      intros _ _ i
      change v s i + natSumPrefix d (fun k => mat s i k * (0 : Nat)) d = v s i + 0
      rw [natSumPrefix_zero_w14 d _ (fun _ => Nat.mul_zero _) d]
    | cons s2 tl =>
      intro hb hint i
      rcases bool_and_split hb with ⟨hs4_b, hrest⟩
      have hs_id := hint s List.mem_cons_self (of_decide_eq_true hs4_b)
      have ih_r := ih hrest (fun x hx => hint x (List.mem_cons_of_mem s hx))
      change v s i + natMatVec d (mat s) (evalFinWordVec (14 * M_mod) d mat v (s2 :: tl)) i =
        v s i + evalFinParikh (14 * M_mod) (fun x => v x i) (s2 :: tl)
      rw [natMatVec_id_eq_w14 d (mat s) _ hs_id i, ih_r i]

def fullRankPerron2DWitness (i j : Fin 2) : Nat :=
  if i.val = j.val then 2 else 1

def fullRankPerron3DWitness (i j : Fin 3) : Nat :=
  match i.val, j.val with
  | 0, 0 => 3 | 0, 1 => 1 | 0, 2 => 0
  | 1, 0 => 1 | 1, 1 => 2 | 1, 2 => 1
  | _, 0 => 0 | _, 1 => 1 | _, _ => 3

/--
  Theorem W14.1c (`twosided_c39_c78_all_dim_perron_and_r_nontri_impossibility`,
  `zero custom axioms`):
  All-Dimension (`∀ d ≥ 1`, Including Full-Rank `d = 2` `(M_s)_{1,1} ≥ 2, (M_s)_{1,0} ≥ 1` &
  Full-Rank `d = 3`) Perron–Frobenius Column-Eigenweight & `.R`/`.L`-Boundary-Growth Matrix-Tower
  Collapse on `TwoSided(2 × 3)` `c39` & `TwoSided(2 × 6)` `c78` (`Branch P4.3`).
-/
theorem twosided_c39_c78_all_dim_perron_and_r_nontri_impossibility :
    let c39 := filterFinParikhUnoriented 42 wtTwoSidedMod3OmitR3
      (twoSidedLabelledCollatzRules 3 (by decide) all11OmitR3List)
    let c78 := filterFinParikhUnoriented 84 wtTwoSidedMod6OmitR3
      (twoSidedLabelledCollatzRules 6 (by decide) all11OmitR3List)
    (fullRankPerron2DWitness ⟨1, by decide⟩ ⟨1, by decide⟩ = 2 ∧
     fullRankPerron2DWitness ⟨1, by decide⟩ ⟨0, by decide⟩ = 1 ∧
     intDet 2 (fun i j => (fullRankPerron2DWitness i j : Int)) = 3 ∧
     (∀ j : Fin 2, natSumPrefix 2 (fun i => 1 * fullRankPerron2DWitness i j) 2 = 3 * 1) ∧
     intDet 3 (fun i j => (fullRankPerron3DWitness i j : Int)) = 12 ∧
     (∀ j : Fin 3, natSumPrefix 3 (fun i => 1 * fullRankPerron3DWitness i j) 3 = 4 * 1)) ∧
    (∀ (d : Nat) (hd : d ≥ 1) (k : Nat),
      ¬ GenOmegaPosDiagColPropMatTower 42 d hd k c39 ∧
      ¬ GenOmegaPosDiagColPropMatTower 84 d hd k c78) ∧
    (∀ (d : Nat) (hd : d ≥ 1) (k : Nat),
      ¬ GenOmegaBoundaryGrowthIntIdMatTower 3 d hd k c39 ∧
      ¬ GenOmegaBoundaryGrowthIntIdMatTower 6 d hd k c78) := by
  let c39 := filterFinParikhUnoriented 42 wtTwoSidedMod3OmitR3
    (twoSidedLabelledCollatzRules 3 (by decide) all11OmitR3List)
  let c78 := filterFinParikhUnoriented 84 wtTwoSidedMod6OmitR3
    (twoSidedLabelledCollatzRules 6 (by decide) all11OmitR3List)
  have hperron_to_aff : ∀ (N d : Nat) (hd : d ≥ 1) (k : Nat)
      (rules : List (List (Fin N) × List (Fin N))),
      GenOmegaPosDiagColPropMatTower N d hd k rules -> GenOmegaAffine1DFinTower N k rules := by
    have hsum_mono : ∀ (d : Nat) (hd : d ≥ 1) (w f g : Fin d -> Nat),
        (∀ i : Fin d, w i ≥ 1) ->
        (∀ i : Fin d, f i ≥ g i) ->
        natSumPrefix d (fun i => w i * f i) d ≥ natSumPrefix d (fun i => w i * g i) d ∧
        (f ⟨0, hd⟩ > g ⟨0, hd⟩ ->
          natSumPrefix d (fun i => w i * f i) d > natSumPrefix d (fun i => w i * g i) d) := by
      intro d hd w f g hw_pos hfg
      have hst : ∀ m : Nat, m ≤ d ->
          natSumPrefix d (fun i => w i * f i) m ≥ natSumPrefix d (fun i => w i * g i) m ∧
          (0 < m -> f ⟨0, hd⟩ > g ⟨0, hd⟩ ->
            natSumPrefix d (fun i => w i * f i) m > natSumPrefix d (fun i => w i * g i) m) := by
        intro m hm; induction m with
        | zero => exact ⟨Nat.le_refl 0, fun h0 => by omega⟩
        | succ m' ih =>
          have hm_lt : m' < d := hm
          rcases ih (Nat.le_of_lt hm) with ⟨hle_m, hgt_m⟩
          simp only [natSumPrefix, hm_lt, dite_true]
          have hcur_le := Nat.mul_le_mul_left (w ⟨m', hm_lt⟩) (hfg ⟨m', hm_lt⟩)
          refine ⟨by omega, ?_⟩
          intro _ hf0_gt
          cases m' with
          | zero =>
            have h0f : (⟨0, hm_lt⟩ : Fin d) = ⟨0, hd⟩ := rfl
            rw [h0f]
            have hcur_gt := Nat.mul_lt_mul_of_pos_left hf0_gt (hw_pos ⟨0, hd⟩)
            omega
          | succ m'' =>
            have hp_gt := hgt_m (by omega) hf0_gt
            omega
      rcases hst d (Nat.le_refl d) with ⟨hle, hgt⟩
      exact ⟨hle, hgt hd⟩
    intro N d hd k; induction k with
    | zero => intro _ h0; exact h0
    | succ k' ih =>
      intro rules hsucc
      rcases hsucc with rfl | ⟨rem, M, v, w, m, _, hw_pos, hm_pos, hcol, hweak, hkeep, hrem⟩
      · exact Or.inl rfl
      · right
        let wt_v : Fin N -> Nat := fun s => natSumPrefix d (fun i => w i * v s i) d
        rcases perron_col_word_invariants N d M v w m hcol with ⟨hmat_inv, hvec_inv⟩
        refine ⟨rem, m, wt_v, hm_pos, ?_, ?_, ih rem hrem⟩
        · intro r hr
          rcases hweak r hr with ⟨hm_ge, hv_ge⟩
          have h1 := (hsum_mono d hd w
            (fun i => evalFinWordMat N d M r.1 i ⟨0, hd⟩)
            (fun i => evalFinWordMat N d M r.2 i ⟨0, hd⟩)
            hw_pos (fun i => hm_ge i ⟨0, hd⟩)).1
          rw [hmat_inv r.1 ⟨0, hd⟩, hmat_inv r.2 ⟨0, hd⟩] at h1
          have hm_prod_ge : (evalFinAffine1D N m wt_v r.1).1 ≥ (evalFinAffine1D N m wt_v r.2).1 := by
            rw [evalFinAffine1D_fst_w14 N m wt_v r.1, evalFinAffine1D_fst_w14 N m wt_v r.2]
            have hw0 := hw_pos ⟨0, hd⟩
            by_cases hlt : prodFinWordW14 N m r.1 < prodFinWordW14 N m r.2
            · exfalso
              have hc := Nat.mul_lt_mul_of_pos_right hlt hw0
              omega
            · omega
          have h2 := (hsum_mono d hd w
            (fun i => evalFinWordVec N d M v r.1 i)
            (fun i => evalFinWordVec N d M v r.2 i)
            hw_pos hv_ge).1
          rw [hvec_inv r.1, hvec_inv r.2] at h2
          exact ⟨hm_prod_ge, h2⟩
        · intro r hr hnot_aff_gt
          apply hkeep r hr
          intro hv0_gt
          apply hnot_aff_gt
          have h2 := (hsum_mono d hd w
            (fun i => evalFinWordVec N d M v r.1 i)
            (fun i => evalFinWordVec N d M v r.2 i)
            hw_pos (hweak r hr).2).2 hv0_gt
          rwa [hvec_inv r.1, hvec_inv r.2] at h2
  have haff_imp := twosided_c39_c78_affine1d_and_coord_monotone_impossibility.1
  have hbnd_master : ∀ (M : Nat) (core : List (List (Fin (14 * M)) × List (Fin (14 * M))))
      (syzL0 syzL1 : List Nat),
      checkAllRulesShapeBool M core = true ->
      core ≠ [] ->
      checkPositiveParikhSyzygyFastBool (14 * M)
        (filterRulesByPosMults core syzL0) (filterPosMults syzL0) = true ->
      checkNoL1RulesBool M (filterRulesByPosMults core syzL0) = true ->
      checkPositiveParikhSyzygyFastBool (14 * M)
        (filterRulesByPosMults core syzL1) (filterPosMults syzL1) = true ->
      checkNoL0RulesBool M (filterRulesByPosMults core syzL1) = true ->
      (∀ r ∈ core, r ∈ filterRulesByPosMults core syzL0 ∨ r ∈ filterRulesByPosMults core syzL1) ->
      ∀ (d : Nat) (hd : d ≥ 1) (k : Nat),
        ¬ GenOmegaBoundaryGrowthIntIdMatTower M d hd k core := by
    intro M core syzL0 syzL1 hsh_b hne_c hsyz0 hno1 hsyz1 hno0 hcov d hd
    let N := 14 * M
    let z0 : Fin d := ⟨0, hd⟩
    have hshape_all := checkAllRulesShapeBool_sound M core hsh_b
    have hpar0_eq := syzygy_forces_parikh_eq_w14 N
      (filterRulesByPosMults core syzL0) (filterPosMults syzL0) hsyz0
    have hpar1_eq := syzygy_forces_parikh_eq_w14 N
      (filterRulesByPosMults core syzL1) (filterPosMults syzL1) hsyz1
    have hno1_s := checkNoL1RulesBool_sound_w14 M (filterRulesByPosMults core syzL0) hno1
    have hno0_s := checkNoL0RulesBool_sound_w14 M (filterRulesByPosMults core syzL1) hno0
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
    have hno_strict : ∀ (mat : Fin N -> Fin d -> Fin d -> Nat)
        (v : Fin N -> Fin d -> Nat) (B0 B1 : Fin d -> Nat),
        (∀ s : Fin N, s.val < 2 * M -> mat s z0 z0 = 1) ->
        (∀ s : Fin N, s.val < M -> ∀ j : Fin d, j.val ≥ 1 -> mat s z0 j = B0 j) ->
        (∀ s : Fin N, M ≤ s.val -> s.val < 2 * M -> ∀ j : Fin d, j.val ≥ 1 -> mat s z0 j = B1 j) ->
        (∀ s : Fin N, s.val ≥ 4 * M -> symAppearsInRulesBool N s.val core = true ->
          ∀ i j : Fin d, mat s i j = natMatId d i j) ->
        (∀ r ∈ core, ∀ i : Fin d, evalFinWordVec N d mat v r.1 i ≥ evalFinWordVec N d mat v r.2 i) ->
        ∀ r ∈ core, evalFinWordVec N d mat v r.1 z0 = evalFinWordVec N d mat v r.2 z0 := by
      intro mat v B0 B1 h00 hB0 hB1 hint_id hv_weak
      rcases idIntDim_vec_eval_w14 M d mat v with ⟨hvec_int, hvec_r⟩
      let tailDot (B : Fin d -> Nat) (s : Fin N) : Nat :=
        natSumPrefix d (fun j => if j.val = 0 then v s z0 else B j * v s j) d
      have hpar_dot : ∀ (B : Fin d -> Nat) (wt : Fin N -> Nat),
          (∀ s : Fin N, s.val ≥ 2 * M -> wt s = tailDot B s) ->
          ∀ w : List (Fin N), (∀ s ∈ w, s.val ≥ 2 * M) ->
            evalFinParikh N wt w =
              natSumPrefix d (fun j =>
                if j.val = 0 then evalFinParikh N (fun s => v s z0) w
                else B j * evalFinParikh N (fun s => v s j) w) d := by
        intro B wt hwt w; induction w with
        | nil =>
          intro _
          change 0 = natSumPrefix d _ d
          exact (natSumPrefix_zero_w14 d _ (fun j => by
            by_cases hz : j.val = 0 <;> simp [hz, evalFinParikh]) d).symm
        | cons s rest ih =>
          intro hall
          simp only [evalFinParikh, hwt s (hall s List.mem_cons_self),
                     ih (fun x hx => hall x (List.mem_cons_of_mem s hx))]
          dsimp only [tailDot]
          rw [← natSumPrefix_add_w14 d]
          have hcg : ∀ m : Nat,
              natSumPrefix d (fun j =>
                (if j.val = 0 then v s z0 else B j * v s j) +
                (if j.val = 0 then evalFinParikh N (fun x => v x z0) rest
                 else B j * evalFinParikh N (fun x => v x j) rest)) m =
              natSumPrefix d (fun j =>
                if j.val = 0 then v s z0 + evalFinParikh N (fun x => v x z0) rest
                else B j * (v s j + evalFinParikh N (fun x => v x j) rest)) m := by
            intro m; induction m with
            | zero => rfl
            | succ m' ihm =>
              simp only [natSumPrefix]
              by_cases hm : m' < d
              · simp only [hm, dite_true, ihm]
                by_cases hz0 : m' = 0 <;> simp [hz0, Nat.mul_add]
              · simp [hm, ihm]
          exact hcg d
      have hl_row0 : ∀ (B : Fin d -> Nat) (l0 : Fin N) (u : List (Fin N)),
          mat l0 z0 z0 = 1 ->
          (∀ j : Fin d, j.val ≥ 1 -> mat l0 z0 j = B j) ->
          (∀ j : Fin d, evalFinWordVec N d mat v u j = evalFinParikh N (fun s => v s j) u) ->
          evalFinWordVec N d mat v (l0 :: u) z0 =
            v l0 z0 + natSumPrefix d (fun j =>
              if j.val = 0 then evalFinParikh N (fun s => v s z0) u
              else B j * evalFinParikh N (fun s => v s j) u) d := by
        intro B l0 u hl00 hlB hu_vec
        change v l0 z0 + natSumPrefix d (fun j => mat l0 z0 j * evalFinWordVec N d mat v u j) d = _
        congr 1
        have hcg : ∀ m : Nat, m ≤ d ->
            natSumPrefix d (fun j => mat l0 z0 j * evalFinWordVec N d mat v u j) m =
              natSumPrefix d (fun j =>
                if j.val = 0 then evalFinParikh N (fun s => v s z0) u
                else B j * evalFinParikh N (fun s => v s j) u) m := by
          intro m hm; induction m with
          | zero => rfl
          | succ m' ihm =>
            have hm_lt : m' < d := hm
            simp only [natSumPrefix, hm_lt, dite_true, ihm (Nat.le_of_lt hm)]
            congr 1
            rw [hu_vec ⟨m', hm_lt⟩]
            by_cases hz : m' = 0
            · have hj0 : (⟨m', hm_lt⟩ : Fin d) = z0 := Fin.ext hz
              change mat l0 z0 ⟨m', hm_lt⟩ * _ =
                if m' = 0 then _ else _
              rw [ite_true_of_w10 hz, hj0, hl00, Nat.one_mul]
            · change mat l0 z0 ⟨m', hm_lt⟩ * _ =
                if m' = 0 then _ else _
              rw [ite_false_of_w10 hz, hlB ⟨m', hm_lt⟩ (show (⟨m', hm_lt⟩ : Fin d).val ≥ 1 by dsimp; omega)]
        exact hcg d (Nat.le_refl d)
      have hr_ge_dot : ∀ (B : Fin d -> Nat) (r : List (Fin N) × List (Fin N)),
          r ∈ core ->
          (∀ j : Fin d, evalFinWordVec N d mat v r.1 j = evalFinParikh N (fun s => v s j) r.1) ->
          (∀ j : Fin d, evalFinWordVec N d mat v r.2 j = evalFinParikh N (fun s => v s j) r.2) ->
          natSumPrefix d (fun j =>
            if j.val = 0 then evalFinParikh N (fun s => v s z0) r.1
            else B j * evalFinParikh N (fun s => v s j) r.1) d ≥
          natSumPrefix d (fun j =>
            if j.val = 0 then evalFinParikh N (fun s => v s z0) r.2
            else B j * evalFinParikh N (fun s => v s j) r.2) d ∧
          (natSumPrefix d (fun j =>
             if j.val = 0 then evalFinParikh N (fun s => v s z0) r.1
             else B j * evalFinParikh N (fun s => v s j) r.1) d =
           natSumPrefix d (fun j =>
             if j.val = 0 then evalFinParikh N (fun s => v s z0) r.2
             else B j * evalFinParikh N (fun s => v s j) r.2) d ->
           evalFinWordVec N d mat v r.1 z0 = evalFinWordVec N d mat v r.2 z0) := by
        intro B r hr h1_eq h2_eq
        have hst : ∀ m : Nat, m ≤ d ->
            natSumPrefix d (fun j =>
              if j.val = 0 then evalFinParikh N (fun s => v s z0) r.1
              else B j * evalFinParikh N (fun s => v s j) r.1) m ≥
            natSumPrefix d (fun j =>
              if j.val = 0 then evalFinParikh N (fun s => v s z0) r.2
              else B j * evalFinParikh N (fun s => v s j) r.2) m ∧
            (0 < m ->
              natSumPrefix d (fun j =>
                if j.val = 0 then evalFinParikh N (fun s => v s z0) r.1
                else B j * evalFinParikh N (fun s => v s j) r.1) m =
              natSumPrefix d (fun j =>
                if j.val = 0 then evalFinParikh N (fun s => v s z0) r.2
                else B j * evalFinParikh N (fun s => v s j) r.2) m ->
              evalFinWordVec N d mat v r.1 z0 = evalFinWordVec N d mat v r.2 z0) := by
          intro m hm; induction m with
          | zero => exact ⟨Nat.le_refl 0, fun h0 => by omega⟩
          | succ m' ihm =>
            have hm_lt : m' < d := hm
            rcases ihm (Nat.le_of_lt hm) with ⟨hle_p, heq_p⟩
            simp only [natSumPrefix, hm_lt, dite_true]
            have hwj := hv_weak r hr ⟨m', hm_lt⟩
            rw [h1_eq ⟨m', hm_lt⟩, h2_eq ⟨m', hm_lt⟩] at hwj
            cases m' with
            | zero =>
              have hj0 : (⟨0, hm_lt⟩ : Fin d) = z0 := rfl
              rw [hj0] at hwj
              change _ + (if (0 : Nat) = 0 then _ else _) ≥
                  _ + (if (0 : Nat) = 0 then _ else _) ∧ _
              simp only [ite_true]
              refine ⟨by omega, fun _ heq0 => ?_⟩
              rw [h1_eq z0, h2_eq z0]; omega
            | succ m'' =>
              change _ + (if m'' + 1 = 0 then _ else _) ≥
                  _ + (if m'' + 1 = 0 then _ else _) ∧ _
              simp only [Nat.succ_ne_zero, ite_false]
              have hmul_j := Nat.mul_le_mul_left (B ⟨m'' + 1, hm_lt⟩) hwj
              exact ⟨by omega, fun _ heq_s => heq_p (by omega) (by omega)⟩
        rcases hst d (Nat.le_refl d) with ⟨hle_d, heq_d⟩
        exact ⟨hle_d, heq_d hd⟩
      let wt0 : Fin N -> Nat := fun s => if s.val < 2 * M then v s z0 else tailDot B0 s
      let wt1 : Fin N -> Nat := fun s => if s.val < 2 * M then v s z0 else tailDot B1 s
      let subL0 := filterRulesByPosMults core syzL0
      have hrel0 : ∀ r ∈ subL0,
          evalFinParikh N wt0 r.1 ≥ evalFinParikh N wt0 r.2 ∧
          (evalFinParikh N wt0 r.1 = evalFinParikh N wt0 r.2 ->
            evalFinWordVec N d mat v r.1 z0 = evalFinWordVec N d mat v r.2 z0) := by
        intro r hr_sub
        have hr : r ∈ core := mem_of_mem_filterRulesByPosMults_w14 core syzL0 r hr_sub
        have hsh := hshape_all r hr; unfold checkRuleTwoSidedShapeBool at hsh
        rcases bool_or_split_w14 hsh with hL_c | hR_c
        · cases hl1 : r.1 with
          | nil => rw [hl1] at hL_c; simp at hL_c
          | cons l0 lint =>
            cases hr1 : r.2 with
            | nil => rw [hl1, hr1] at hL_c; simp at hL_c
            | cons r0 rint =>
              rw [hl1, hr1] at hL_c; dsimp only at hL_c
              rcases bool_or_split_w14 hL_c with hq0 | hq1
              · rcases bool_and_split hq0 with ⟨hb0, hrint_b⟩
                rcases bool_and_split hb0 with ⟨hlr_b, hlint_b⟩
                rcases of_decide_eq_true hlr_b with ⟨hl0_lt, hr0_lt⟩
                have hli_v := hvec_int lint (fun x hx => hint_id x (allGe4MBool_sound M lint hlint_b x hx)
                  (symAppearsInRulesBool_of_mem_lhs N x core r hr (hl1 ▸ List.mem_cons_of_mem l0 hx)))
                have hri_v := hvec_int rint (fun x hx => hint_id x (allGe4MBool_sound M rint hrint_b x hx)
                  (symAppearsInRulesBool_of_mem_rhs N x core r hr (hr1 ▸ List.mem_cons_of_mem r0 hx)))
                have hvl := hl_row0 B0 l0 lint (h00 l0 (by omega)) (hB0 l0 hl0_lt) hli_v
                have hvr := hl_row0 B0 r0 rint (h00 r0 (by omega)) (hB0 r0 hr0_lt) hri_v
                have hwli := hpar_dot B0 wt0 (fun s hs => by dsimp [wt0]; rw [ite_false_of_w10 (by omega)])
                  lint (fun x hx => by have := allGe4MBool_sound M lint hlint_b x hx; omega)
                have hwri := hpar_dot B0 wt0 (fun s hs => by dsimp [wt0]; rw [ite_false_of_w10 (by omega)])
                  rint (fun x hx => by have := allGe4MBool_sound M rint hrint_b x hx; omega)
                have hpl0 : evalFinParikh N wt0 (l0 :: lint) = evalFinWordVec N d mat v (l0 :: lint) z0 := by
                  simp only [evalFinParikh]; rw [hvl, ← hwli]
                  have : wt0 l0 = v l0 z0 := by dsimp [wt0]; rw [ite_true_of_w10 (by omega)]
                  rw [this]
                have hpr0 : evalFinParikh N wt0 (r0 :: rint) = evalFinWordVec N d mat v (r0 :: rint) z0 := by
                  simp only [evalFinParikh]; rw [hvr, ← hwri]
                  have : wt0 r0 = v r0 z0 := by dsimp [wt0]; rw [ite_true_of_w10 (by omega)]
                  rw [this]
                have hw0 := hv_weak r hr z0
                rw [hl1, hr1, ← hpl0, ← hpr0] at hw0
                exact ⟨hw0, fun h => by rw [← hpl0, ← hpr0, h]⟩
              · rcases bool_and_split hq1 with ⟨hb1, _⟩
                rcases bool_and_split hb1 with ⟨hlr_b, _⟩
                rcases of_decide_eq_true hlr_b with ⟨hl0_ge, hl0_lt, _, _⟩
                exact False.elim (hno1_s r hr_sub l0 (Or.inl (hl1 ▸ List.Mem.head _)) ⟨hl0_ge, hl0_lt⟩)
        · rcases bool_and_split hR_c with ⟨hl_r, hr_r⟩
          have hvl := hvec_r r.1 hl_r (fun x hx hx4 => hint_id x hx4 (symAppearsInRulesBool_of_mem_lhs N x core r hr hx))
          have hvr := hvec_r r.2 hr_r (fun x hx hx4 => hint_id x hx4 (symAppearsInRulesBool_of_mem_rhs N x core r hr hx))
          have hpl := hpar_dot B0 wt0 (fun s hs => by dsimp [wt0]; rw [ite_false_of_w10 (by omega)])
            r.1 (hge2M_w r.1 hl_r)
          have hpr := hpar_dot B0 wt0 (fun s hs => by dsimp [wt0]; rw [ite_false_of_w10 (by omega)])
            r.2 (hge2M_w r.2 hr_r)
          rcases hr_ge_dot B0 r hr hvl hvr with ⟨hge_d, heq_d⟩
          rw [← hpl, ← hpr] at hge_d heq_d
          exact ⟨hge_d, heq_d⟩
      let subL1 := filterRulesByPosMults core syzL1
      have hrel1 : ∀ r ∈ subL1,
          evalFinParikh N wt1 r.1 ≥ evalFinParikh N wt1 r.2 ∧
          (evalFinParikh N wt1 r.1 = evalFinParikh N wt1 r.2 ->
            evalFinWordVec N d mat v r.1 z0 = evalFinWordVec N d mat v r.2 z0) := by
        intro r hr_sub
        have hr : r ∈ core := mem_of_mem_filterRulesByPosMults_w14 core syzL1 r hr_sub
        have hsh := hshape_all r hr; unfold checkRuleTwoSidedShapeBool at hsh
        rcases bool_or_split_w14 hsh with hL_c | hR_c
        · cases hl1 : r.1 with
          | nil => rw [hl1] at hL_c; simp at hL_c
          | cons l0 lint =>
            cases hr1 : r.2 with
            | nil => rw [hl1, hr1] at hL_c; simp at hL_c
            | cons r0 rint =>
              rw [hl1, hr1] at hL_c; dsimp only at hL_c
              rcases bool_or_split_w14 hL_c with hq0 | hq1
              · rcases bool_and_split hq0 with ⟨hb0, _⟩
                rcases bool_and_split hb0 with ⟨hlr_b, _⟩
                rcases of_decide_eq_true hlr_b with ⟨hl0_lt, _⟩
                exact False.elim (hno0_s r hr_sub l0 (Or.inl (hl1 ▸ List.Mem.head _)) hl0_lt)
              · rcases bool_and_split hq1 with ⟨hb1, hrint_b⟩
                rcases bool_and_split hb1 with ⟨hlr_b, hlint_b⟩
                rcases of_decide_eq_true hlr_b with ⟨hl0_ge, hl0_lt, hr0_ge, hr0_lt⟩
                have hli_v := hvec_int lint (fun x hx => hint_id x (allGe4MBool_sound M lint hlint_b x hx)
                  (symAppearsInRulesBool_of_mem_lhs N x core r hr (hl1 ▸ List.mem_cons_of_mem l0 hx)))
                have hri_v := hvec_int rint (fun x hx => hint_id x (allGe4MBool_sound M rint hrint_b x hx)
                  (symAppearsInRulesBool_of_mem_rhs N x core r hr (hr1 ▸ List.mem_cons_of_mem r0 hx)))
                have hvl := hl_row0 B1 l0 lint (h00 l0 hl0_lt) (hB1 l0 hl0_ge hl0_lt) hli_v
                have hvr := hl_row0 B1 r0 rint (h00 r0 hr0_lt) (hB1 r0 hr0_ge hr0_lt) hri_v
                have hwli := hpar_dot B1 wt1 (fun s hs => by dsimp [wt1]; rw [ite_false_of_w10 (by omega)])
                  lint (fun x hx => by have := allGe4MBool_sound M lint hlint_b x hx; omega)
                have hwri := hpar_dot B1 wt1 (fun s hs => by dsimp [wt1]; rw [ite_false_of_w10 (by omega)])
                  rint (fun x hx => by have := allGe4MBool_sound M rint hrint_b x hx; omega)
                have hpl1 : evalFinParikh N wt1 (l0 :: lint) = evalFinWordVec N d mat v (l0 :: lint) z0 := by
                  simp only [evalFinParikh]; rw [hvl, ← hwli]
                  have : wt1 l0 = v l0 z0 := by dsimp [wt1]; rw [ite_true_of_w10 hl0_lt]
                  rw [this]
                have hpr1 : evalFinParikh N wt1 (r0 :: rint) = evalFinWordVec N d mat v (r0 :: rint) z0 := by
                  simp only [evalFinParikh]; rw [hvr, ← hwri]
                  have : wt1 r0 = v r0 z0 := by dsimp [wt1]; rw [ite_true_of_w10 hr0_lt]
                  rw [this]
                have hw0 := hv_weak r hr z0
                rw [hl1, hr1, ← hpl1, ← hpr1] at hw0
                exact ⟨hw0, fun h => by rw [← hpl1, ← hpr1, h]⟩
        · rcases bool_and_split hR_c with ⟨hl_r, hr_r⟩
          have hvl := hvec_r r.1 hl_r (fun x hx hx4 => hint_id x hx4 (symAppearsInRulesBool_of_mem_lhs N x core r hr hx))
          have hvr := hvec_r r.2 hr_r (fun x hx hx4 => hint_id x hx4 (symAppearsInRulesBool_of_mem_rhs N x core r hr hx))
          have hpl := hpar_dot B1 wt1 (fun s hs => by dsimp [wt1]; rw [ite_false_of_w10 (by omega)])
            r.1 (hge2M_w r.1 hl_r)
          have hpr := hpar_dot B1 wt1 (fun s hs => by dsimp [wt1]; rw [ite_false_of_w10 (by omega)])
            r.2 (hge2M_w r.2 hr_r)
          rcases hr_ge_dot B1 r hr hvl hvr with ⟨hge_d, heq_d⟩
          rw [← hpl, ← hpr] at hge_d heq_d
          exact ⟨hge_d, heq_d⟩
      have heq0 := hpar0_eq wt0 (fun r hr => (hrel0 r hr).1)
      have heq1 := hpar1_eq wt1 (fun r hr => (hrel1 r hr).1)
      intro r hr
      rcases hcov r hr with hr0 | hr1
      · exact (hrel0 r hr0).2 (heq0 r hr0)
      · exact (hrel1 r hr1).2 (heq1 r hr1)
    cases hc_eq : core with
    | nil => exact False.elim (hne_c hc_eq)
    | cons r0 rs =>
      rw [← hc_eq]
      have hm0 : r0 ∈ core := hc_eq ▸ List.Mem.head _
      have himp : ∀ (k : Nat) (cur : List (List (Fin N) × List (Fin N))),
          (∀ r ∈ core, r ∈ cur) -> ¬ GenOmegaBoundaryGrowthIntIdMatTower M d hd k cur := by
        intro k; induction k with
        | zero =>
          intro cur hsub h0; rw [GenOmegaBoundaryGrowthIntIdMatTower] at h0; subst h0
          exact List.not_mem_nil (hsub r0 hm0)
        | succ k' ih =>
          intro cur hsub hsucc
          rcases hsucc with rfl | ⟨rem, mat, v, B0, B1, h00, hB0, hB1, hint, hweak, hkeep, hrem⟩
          · exact List.not_mem_nil (hsub r0 hm0)
          · have hint_core : ∀ s : Fin N, s.val ≥ 4 * M ->
                symAppearsInRulesBool N s.val core = true ->
                ∀ i j : Fin d, mat s i j = natMatId d i j := by
              intro s hs4 hsa
              have hsa_cur : symAppearsInRulesBool N s.val cur = true := by
                have hmem_ex : ∀ xs : List (List (Fin N) × List (Fin N)),
                    symAppearsInRulesBool N s.val xs = true ->
                    ∃ r ∈ xs, s ∈ r.1 ∨ s ∈ r.2 := by
                  intro xs; induction xs with
                  | nil => intro h; cases h
                  | cons x xtl ihx =>
                    intro h; unfold symAppearsInRulesBool at h
                    rcases bool_or_split_w14 h with h1 | h2
                    · have hcnt := of_decide_eq_true h1
                      have hcnt_mem : ∀ w : List (Fin N),
                          countNatOccW11 s.val (w.map Fin.val) ≥ 1 -> s ∈ w := by
                        intro w; induction w with
                        | nil => intro hc; simp [countNatOccW11] at hc
                        | cons y ytl ihy =>
                          intro hc; simp only [List.map_cons, countNatOccW11] at hc
                          by_cases heq : y.val = s.val
                          · exact Fin.ext heq ▸ List.Mem.head _
                          · rw [ite_false_of_w10 heq, Nat.zero_add] at hc
                            exact List.mem_cons_of_mem y (ihy hc)
                      rcases (by omega :
                        countNatOccW11 s.val (x.1.map Fin.val) ≥ 1 ∨
                        countNatOccW11 s.val (x.2.map Fin.val) ≥ 1) with hc1 | hc2
                      · exact ⟨x, List.Mem.head _, Or.inl (hcnt_mem x.1 hc1)⟩
                      · exact ⟨x, List.Mem.head _, Or.inr (hcnt_mem x.2 hc2)⟩
                    · rcases ihx h2 with ⟨r, hrm, hsm⟩
                      exact ⟨r, List.mem_cons_of_mem x hrm, hsm⟩
                rcases hmem_ex core hsa with ⟨r, hrc, hsm⟩
                rcases hsm with hml | hmr
                · exact symAppearsInRulesBool_of_mem_lhs N s cur r (hsub r hrc) hml
                · exact symAppearsInRulesBool_of_mem_rhs N s cur r (hsub r hrc) hmr
              exact hint s hs4 hsa_cur
            have heq := hno_strict mat v B0 B1 h00 hB0 hB1 hint_core
              (fun r hr => (hweak r (hsub r hr)).2)
            exact ih rem (fun r hr => hkeep r (hsub r hr)
              (by rw [heq r hr]; exact Nat.lt_irrefl _)) hrem
      exact fun k => himp k core (fun _ hr => hr)
  rcases c39_c78_w14_sub_certs with
    ⟨⟨hsh3, hne3, hsyzL0_3, hnoL1_3, hsyzL1_3, hnoL0_3, hcl3, hsum3⟩,
     ⟨hsh6, hne6, hsyzL0_6, hnoL1_6, hsyzL1_6, hnoL0_6, hcl6, hsum6⟩⟩
  rcases checkSumPosListsBool_sound_w14 syzC39L0Only syzC39L1Only hsum3 with ⟨hl01_3, hpos3⟩
  have hcov3 := coverByPosMults_w14 c39 syzC39L0Only syzC39L1Only hcl3 (hcl3.trans hl01_3) hpos3
  rcases checkSumPosListsBool_sound_w14 syzC78L0Only syzC78L1Only hsum6 with ⟨hl01_6, hpos6⟩
  have hcov6 := coverByPosMults_w14 c78 syzC78L0Only syzC78L1Only hcl6 (hcl6.trans hl01_6) hpos6
  exact ⟨by decide,
         fun d hd k =>
           ⟨fun h => (haff_imp k).1 (hperron_to_aff 42 d hd k c39 h),
            fun h => (haff_imp k).2 (hperron_to_aff 84 d hd k c78 h)⟩,
         fun d hd k =>
           ⟨hbnd_master 3 c39 syzC39L0Only syzC39L1Only hsh3 hne3
              hsyzL0_3 hnoL1_3 hsyzL1_3 hnoL0_3 hcov3 d hd k,
            hbnd_master 6 c78 syzC78L0Only syzC78L1Only hsh6 hne6
              hsyzL0_6 hnoL1_6 hsyzL1_6 hnoL0_6 hcov6 d hd k⟩⟩

-- ----------------------------------------------------------------------------
-- Section 1C: All-Dimension (`∀ d ≥ 1`, Including Full-Rank `d = 3`) 4-Rule
--             Pure-Interior Block-Coupled Trace Syzygy on `c39` & `c78`
-- ----------------------------------------------------------------------------

/-- Matrix trace `∑_{i < d} A_{i, i}` over `Nat`. -/
def natMatTrace (d : Nat) (A : Fin d -> Fin d -> Nat) : Nat :=
  natSumPrefix d (fun i => A i i) d

private theorem natMatTrace_mul_comm (d : Nat) (A B : Fin d -> Fin d -> Nat) :
    natMatTrace d (natMatMul d A B) = natMatTrace d (natMatMul d B A) := by
  unfold natMatTrace
  change natSumPrefix d (fun i => natSumPrefix d (fun k => A i k * B k i) d) d =
    natSumPrefix d (fun k => natSumPrefix d (fun i => B k i * A i k) d) d
  rw [natSumPrefix_swap_w14 d d (fun i k => A i k * B k i) d]
  have hcg : ∀ m : Nat,
      natSumPrefix d (fun k => natSumPrefix d (fun i => A i k * B k i) d) m =
        natSumPrefix d (fun k => natSumPrefix d (fun i => B k i * A i k) d) m := by
    intro m; induction m with
    | zero => rfl
    | succ m' ihm =>
      simp only [natSumPrefix]
      by_cases hm : m' < d
      · simp only [hm, dite_true, ihm]
        congr 1
        have hc2 : ∀ p : Nat,
            natSumPrefix d (fun i => A i ⟨m', hm⟩ * B ⟨m', hm⟩ i) p =
              natSumPrefix d (fun i => B ⟨m', hm⟩ i * A i ⟨m', hm⟩) p := by
          intro p; induction p with
          | zero => rfl
          | succ p' ihp =>
            simp only [natSumPrefix]
            by_cases hp : p' < d <;> simp [hp, ihp, Nat.mul_comm]
        exact hc2 d
      · simp [hm, ihm]
  exact hcg d

private theorem evalFinWordMat_two_eq_mul (N d : Nat) (M : Fin N -> Fin d -> Fin d -> Nat)
    (a b : Fin N) :
    evalFinWordMat N d M [a, b] = natMatMul d (M a) (M b) := by
  funext i j
  change natSumPrefix d (fun k =>
    M a i k * natSumPrefix d (fun l => M b k l * natMatId d l j) d) d =
    natSumPrefix d (fun k => M a i k * M b k j) d
  have hid_r : ∀ k : Fin d,
      natSumPrefix d (fun l => M b k l * natMatId d l j) d = M b k j := by
    intro k
    have hst : ∀ m : Nat, m ≤ d ->
        natSumPrefix d (fun l => M b k l * natMatId d l j) m =
          if j.val < m then M b k j else 0 := by
      intro m hm; induction m with
      | zero => simp [natSumPrefix]
      | succ m' ih =>
        have hm_lt : m' < d := hm
        simp only [natSumPrefix, hm_lt, dite_true, ih (Nat.le_of_lt hm)]
        by_cases heq : j.val = m'
        · have hjf : (⟨m', hm_lt⟩ : Fin d) = j := Fin.ext heq.symm
          rw [hjf, ite_false_of_w10 (by omega : ¬ (j.val < m')),
              ite_true_of_w10 (by omega : j.val < m' + 1)]
          simp [natMatId]
        · have hne : m' ≠ j.val := fun h => heq h.symm
          simp only [natMatId, hne, ite_false, Nat.mul_zero, Nat.add_zero]
          by_cases hlt : j.val < m'
          · rw [ite_true_of_w10 hlt, ite_true_of_w10 (by omega)]
          · rw [ite_false_of_w10 hlt, ite_false_of_w10 (by omega)]
    rw [hst d (Nat.le_refl d), ite_true_of_w10 j.isLt]
  have hcg : ∀ m : Nat,
      natSumPrefix d (fun k => M a i k * natSumPrefix d (fun l => M b k l * natMatId d l j) d) m =
        natSumPrefix d (fun k => M a i k * M b k j) m := by
    intro m; induction m with
    | zero => rfl
    | succ m' ihm =>
      simp only [natSumPrefix]
      by_cases hm : m' < d
      · simp only [hm, dite_true, hid_r]
      · simp only [hm, dite_false, ihm]
  exact hcg d

set_option maxRecDepth 65536 in
private theorem four_rule_interior_loops_in_c39_c78 :
    let c39 := filterFinParikhUnoriented 42 wtTwoSidedMod3OmitR3
      (twoSidedLabelledCollatzRules 3 (by decide) all11OmitR3List)
    let c78 := filterFinParikhUnoriented 84 wtTwoSidedMod6OmitR3
      (twoSidedLabelledCollatzRules 6 (by decide) all11OmitR3List)
    (hasTwoToTwoRuleBool 42 28 18 22 33 c39 = true ∧
     hasTwoToTwoRuleBool 42 33 22 17 37 c39 = true ∧
     hasTwoToTwoRuleBool 42 37 17 13 32 c39 = true ∧
     hasTwoToTwoRuleBool 42 32 13 18 28 c39 = true) ∧
    (hasTwoToTwoRuleBool 84 55 39 46 69 c78 = true ∧
     hasTwoToTwoRuleBool 84 69 46 32 76 c78 = true ∧
     hasTwoToTwoRuleBool 84 76 32 25 62 c78 = true ∧
     hasTwoToTwoRuleBool 84 62 25 39 55 c78 = true) := by decide

/--
  Theorem W14.1d (`twosided_c39_c78_all_dim_four_rule_trace_syzygy`,
  choice-free `zero custom axioms`):
  Universal All-Dimension (`∀ d ≥ 1`, Including `d = 2` & Full-Rank `d = 3`) 4-Rule Pure-Interior
  Block-Coupled Trace Syzygy on `c39` & `c78` (`Branch P4.3`).
-/
theorem twosided_c39_c78_all_dim_four_rule_trace_syzygy :
    let c39 := filterFinParikhUnoriented 42 wtTwoSidedMod3OmitR3
      (twoSidedLabelledCollatzRules 3 (by decide) all11OmitR3List)
    let c78 := filterFinParikhUnoriented 84 wtTwoSidedMod6OmitR3
      (twoSidedLabelledCollatzRules 6 (by decide) all11OmitR3List)
    (∀ (d : Nat) (A B : Fin d -> Fin d -> Nat),
      natMatTrace d (natMatMul d A B) = natMatTrace d (natMatMul d B A)) ∧
    (∀ (d : Nat) (M : Fin 42 -> Fin d -> Fin d -> Nat),
      (∀ r ∈ c39, ∀ i j : Fin d,
        evalFinWordMat 42 d M r.1 i j ≥ evalFinWordMat 42 d M r.2 i j) ->
      ∀ i : Fin d,
        evalFinWordMat 42 d M [⟨28, by decide⟩, ⟨18, by decide⟩] i i =
          evalFinWordMat 42 d M [⟨22, by decide⟩, ⟨33, by decide⟩] i i ∧
        evalFinWordMat 42 d M [⟨33, by decide⟩, ⟨22, by decide⟩] i i =
          evalFinWordMat 42 d M [⟨17, by decide⟩, ⟨37, by decide⟩] i i ∧
        evalFinWordMat 42 d M [⟨37, by decide⟩, ⟨17, by decide⟩] i i =
          evalFinWordMat 42 d M [⟨13, by decide⟩, ⟨32, by decide⟩] i i ∧
        evalFinWordMat 42 d M [⟨32, by decide⟩, ⟨13, by decide⟩] i i =
          evalFinWordMat 42 d M [⟨18, by decide⟩, ⟨28, by decide⟩] i i) ∧
    (∀ (d : Nat) (M : Fin 84 -> Fin d -> Fin d -> Nat),
      (∀ r ∈ c78, ∀ i j : Fin d,
        evalFinWordMat 84 d M r.1 i j ≥ evalFinWordMat 84 d M r.2 i j) ->
      ∀ i : Fin d,
        evalFinWordMat 84 d M [⟨55, by decide⟩, ⟨39, by decide⟩] i i =
          evalFinWordMat 84 d M [⟨46, by decide⟩, ⟨69, by decide⟩] i i ∧
        evalFinWordMat 84 d M [⟨69, by decide⟩, ⟨46, by decide⟩] i i =
          evalFinWordMat 84 d M [⟨32, by decide⟩, ⟨76, by decide⟩] i i ∧
        evalFinWordMat 84 d M [⟨76, by decide⟩, ⟨32, by decide⟩] i i =
          evalFinWordMat 84 d M [⟨25, by decide⟩, ⟨62, by decide⟩] i i ∧
        evalFinWordMat 84 d M [⟨62, by decide⟩, ⟨25, by decide⟩] i i =
          evalFinWordMat 84 d M [⟨39, by decide⟩, ⟨55, by decide⟩] i i) := by
  have hdiag_eq_of_trace : ∀ (d : Nat) (P Q : Fin d -> Fin d -> Nat),
      (∀ i : Fin d, P i i ≥ Q i i) ->
      natMatTrace d P ≥ natMatTrace d Q ∧
      (natMatTrace d P = natMatTrace d Q -> ∀ i : Fin d, P i i = Q i i) := by
    intro d P Q hge
    unfold natMatTrace
    have hst : ∀ m : Nat, m ≤ d ->
        natSumPrefix d (fun i => P i i) m ≥ natSumPrefix d (fun i => Q i i) m ∧
        (natSumPrefix d (fun i => P i i) m = natSumPrefix d (fun i => Q i i) m ->
          ∀ k : Nat, k < m -> (hk : k < d) -> P ⟨k, hk⟩ ⟨k, hk⟩ = Q ⟨k, hk⟩ ⟨k, hk⟩) := by
      intro m hm; induction m with
      | zero => exact ⟨Nat.le_refl 0, fun _ _ hk => by omega⟩
      | succ m' ih =>
        have hm_lt : m' < d := hm
        rcases ih (Nat.le_of_lt hm) with ⟨hle_m, heq_m⟩
        simp only [natSumPrefix, hm_lt, dite_true]
        have hcur := hge ⟨m', hm_lt⟩
        refine ⟨by omega, fun heq_s k hk_lt hk_d => ?_⟩
        by_cases hkeq : k = m'
        · subst hkeq; omega
        · exact heq_m (by omega) k (by omega) hk_d
    rcases hst d (Nat.le_refl d) with ⟨hle, heq⟩
    exact ⟨hle, fun ht i => heq ht i.val i.isLt i.isLt⟩
  have hfour_loop_gen : ∀ (N d : Nat) (M : Fin N -> Fin d -> Fin d -> Nat)
      (a1 b1 a2 b2 a3 b3 a4 b4 : Fin N),
      (∀ i : Fin d, evalFinWordMat N d M [a1, b1] i i ≥ evalFinWordMat N d M [a2, b2] i i) ->
      (∀ i : Fin d, evalFinWordMat N d M [b2, a2] i i ≥ evalFinWordMat N d M [a3, b3] i i) ->
      (∀ i : Fin d, evalFinWordMat N d M [b3, a3] i i ≥ evalFinWordMat N d M [a4, b4] i i) ->
      (∀ i : Fin d, evalFinWordMat N d M [b4, a4] i i ≥ evalFinWordMat N d M [b1, a1] i i) ->
      ∀ i : Fin d,
        evalFinWordMat N d M [a1, b1] i i = evalFinWordMat N d M [a2, b2] i i ∧
        evalFinWordMat N d M [b2, a2] i i = evalFinWordMat N d M [a3, b3] i i ∧
        evalFinWordMat N d M [b3, a3] i i = evalFinWordMat N d M [a4, b4] i i ∧
        evalFinWordMat N d M [b4, a4] i i = evalFinWordMat N d M [b1, a1] i i := by
    intro N d M a1 b1 a2 b2 a3 b3 a4 b4 h1 h2 h3 h4
    rcases hdiag_eq_of_trace d _ _ h1 with ⟨ht1, he1⟩
    rcases hdiag_eq_of_trace d _ _ h2 with ⟨ht2, he2⟩
    rcases hdiag_eq_of_trace d _ _ h3 with ⟨ht3, he3⟩
    rcases hdiag_eq_of_trace d _ _ h4 with ⟨ht4, he4⟩
    have hc1 : natMatTrace d (evalFinWordMat N d M [a2, b2]) =
        natMatTrace d (evalFinWordMat N d M [b2, a2]) := by
      rw [evalFinWordMat_two_eq_mul, evalFinWordMat_two_eq_mul]
      exact natMatTrace_mul_comm d (M a2) (M b2)
    have hc2 : natMatTrace d (evalFinWordMat N d M [a3, b3]) =
        natMatTrace d (evalFinWordMat N d M [b3, a3]) := by
      rw [evalFinWordMat_two_eq_mul, evalFinWordMat_two_eq_mul]
      exact natMatTrace_mul_comm d (M a3) (M b3)
    have hc3 : natMatTrace d (evalFinWordMat N d M [a4, b4]) =
        natMatTrace d (evalFinWordMat N d M [b4, a4]) := by
      rw [evalFinWordMat_two_eq_mul, evalFinWordMat_two_eq_mul]
      exact natMatTrace_mul_comm d (M a4) (M b4)
    have hc4 : natMatTrace d (evalFinWordMat N d M [b1, a1]) =
        natMatTrace d (evalFinWordMat N d M [a1, b1]) := by
      rw [evalFinWordMat_two_eq_mul, evalFinWordMat_two_eq_mul]
      exact natMatTrace_mul_comm d (M b1) (M a1)
    intro i
    exact ⟨he1 (by omega) i, he2 (by omega) i, he3 (by omega) i, he4 (by omega) i⟩
  rcases four_rule_interior_loops_in_c39_c78 with
    ⟨⟨hr3_1, hr3_2, hr3_3, hr3_4⟩, ⟨hr6_1, hr6_2, hr6_3, hr6_4⟩⟩
  refine ⟨natMatTrace_mul_comm, ?_, ?_⟩
  · intro d M hweak
    let c39 := filterFinParikhUnoriented 42 wtTwoSidedMod3OmitR3
      (twoSidedLabelledCollatzRules 3 (by decide) all11OmitR3List)
    exact hfour_loop_gen 42 d M
      ⟨28, by decide⟩ ⟨18, by decide⟩ ⟨22, by decide⟩ ⟨33, by decide⟩
      ⟨17, by decide⟩ ⟨37, by decide⟩ ⟨13, by decide⟩ ⟨32, by decide⟩
      (fun i => hweak _ (hasTwoToTwoRuleBool_sound_w14 42 _ _ _ _ c39 hr3_1) i i)
      (fun i => hweak _ (hasTwoToTwoRuleBool_sound_w14 42 _ _ _ _ c39 hr3_2) i i)
      (fun i => hweak _ (hasTwoToTwoRuleBool_sound_w14 42 _ _ _ _ c39 hr3_3) i i)
      (fun i => hweak _ (hasTwoToTwoRuleBool_sound_w14 42 _ _ _ _ c39 hr3_4) i i)
  · intro d M hweak
    let c78 := filterFinParikhUnoriented 84 wtTwoSidedMod6OmitR3
      (twoSidedLabelledCollatzRules 6 (by decide) all11OmitR3List)
    exact hfour_loop_gen 84 d M
      ⟨55, by decide⟩ ⟨39, by decide⟩ ⟨46, by decide⟩ ⟨69, by decide⟩
      ⟨32, by decide⟩ ⟨76, by decide⟩ ⟨25, by decide⟩ ⟨62, by decide⟩
      (fun i => hweak _ (hasTwoToTwoRuleBool_sound_w14 84 _ _ _ _ c78 hr6_1) i i)
      (fun i => hweak _ (hasTwoToTwoRuleBool_sound_w14 84 _ _ _ _ c78 hr6_2) i i)
      (fun i => hweak _ (hasTwoToTwoRuleBool_sound_w14 84 _ _ _ _ c78 hr6_3) i i)
      (fun i => hweak _ (hasTwoToTwoRuleBool_sound_w14 84 _ _ _ _ c78 hr6_4) i i)

-- ----------------------------------------------------------------------------
-- Section 1D: `∀ r ≥ 1` Iterated `leftAnchoredDP2Step` Affine-Carry Law,
--             `3^r * 2^A ≤ 10^r` Confinement, `1..5`-Cycle Freedom, `M1` Carry
--             Separation, & Exponential `2^r` 1-Block Steiner `DP2` Lock
-- ----------------------------------------------------------------------------

/-- `r`-step iterated `leftAnchoredDP2Step` chain `u_0 -> u_1 -> ... -> u_r`. -/
def dp2StepIter : Nat -> List MixedSRSSym -> List MixedSRSSym -> Prop
  | 0, u, v => u = v
  | r + 1, u, v => ∃ w : List MixedSRSSym, leftAnchoredDP2Step u w ∧ dp2StepIter r w v

/-- Shift-annotated `leftAnchoredDP2Step` chain explicitly recording step shifts `shifts : List Nat`. -/
def dp2AnnotatedChain : List MixedSRSSym -> List Nat -> List MixedSRSSym -> Prop
  | u, [], v => u = v
  | u, a :: rest, v =>
    a ≥ 1 ∧
    ∃ w : List MixedSRSSym,
      leftAnchoredDP2Step u w ∧
      2 ^ a * dp2GlobalOddVal w = 3 * dp2GlobalOddVal u + 1 ∧
      dp2AnnotatedChain w rest v

def dp2ShiftSum : List Nat -> Nat
  | [] => 0
  | a :: rest => a + dp2ShiftSum rest

def dp2IterCarry : List Nat -> Nat
  | [] => 0
  | a :: rest => 3 ^ rest.length + 2 ^ a * dp2IterCarry rest

private theorem dp2AnnotatedChain_homomorphism :
    ∀ (shifts : List Nat) (u0 ur : List MixedSRSSym),
      dp2AnnotatedChain u0 shifts ur ->
      (.R ∈ u0 ↔ .R ∈ ur) ∧
      (∀ a ∈ shifts, a ≥ 1) ∧
      2 ^ dp2ShiftSum shifts * dp2GlobalOddVal ur =
        3 ^ shifts.length * dp2GlobalOddVal u0 + dp2IterCarry shifts ∧
      3 ^ shifts.length * 2 ^ dp2ShiftSum shifts * dp2GlobalOddVal ur ≤
        10 ^ shifts.length * dp2GlobalOddVal u0
  | [], u0, ur, heq => by
    subst heq
    exact ⟨Iff.rfl, (fun _ h => by cases h),
           (by simp [dp2ShiftSum, dp2IterCarry]),
           (by simp [dp2ShiftSum])⟩
  | a :: rest, u0, ur, ⟨ha1, w, hstep, hsyr_step, htl⟩ => by
    have hR1 := (leftAnchoredDP2_r_carrying_syracuse_and_no_1_2_cycles.1 u0 w hstep).1
    rcases dp2AnnotatedChain_homomorphism rest w ur htl with ⟨hR_tl, hall_tl, heq_tl, h10_tl⟩
    refine ⟨hR1.trans hR_tl,
            fun x hx => (List.mem_cons.mp hx).elim (fun h => h ▸ ha1) (hall_tl x),
            ?_, ?_⟩
    · simp only [dp2ShiftSum, dp2IterCarry, List.length_cons]
      calc
        2 ^ (a + dp2ShiftSum rest) * dp2GlobalOddVal ur
            = 2 ^ a * (2 ^ dp2ShiftSum rest * dp2GlobalOddVal ur) := by
              rw [Nat.pow_add, Nat.mul_assoc]
        _ = 2 ^ a * (3 ^ rest.length * dp2GlobalOddVal w + dp2IterCarry rest) := by
              rw [heq_tl]
        _ = 3 ^ rest.length * (2 ^ a * dp2GlobalOddVal w) + 2 ^ a * dp2IterCarry rest := by
              rw [Nat.mul_add]; ac_rfl
        _ = 3 ^ rest.length * (3 * dp2GlobalOddVal u0 + 1) + 2 ^ a * dp2IterCarry rest := by
              rw [hsyr_step]
        _ = 3 ^ (rest.length + 1) * dp2GlobalOddVal u0 +
              (3 ^ rest.length + 2 ^ a * dp2IterCarry rest) := by
              rw [Nat.pow_succ, Nat.mul_add, Nat.mul_one]
              ac_rfl
    · simp only [dp2ShiftSum, List.length_cons]
      have hu0_ge3 : dp2GlobalOddVal u0 ≥ 3 := by unfold dp2GlobalOddVal; omega
      have hstep_10 : 3 * (2 ^ a * dp2GlobalOddVal w) ≤ 10 * dp2GlobalOddVal u0 := by
        rw [hsyr_step]; omega
      have h1 : 3 * (2 ^ a * (3 ^ rest.length * 2 ^ dp2ShiftSum rest * dp2GlobalOddVal ur)) ≤
          3 * (2 ^ a * (10 ^ rest.length * dp2GlobalOddVal w)) :=
        Nat.mul_le_mul_left 3 (Nat.mul_le_mul_left (2 ^ a) h10_tl)
      have h2 : 10 ^ rest.length * (3 * (2 ^ a * dp2GlobalOddVal w)) ≤
          10 ^ rest.length * (10 * dp2GlobalOddVal u0) :=
        Nat.mul_le_mul_left (10 ^ rest.length) hstep_10
      have hlhs : 3 ^ (rest.length + 1) * 2 ^ (a + dp2ShiftSum rest) * dp2GlobalOddVal ur =
          3 * (2 ^ a * (3 ^ rest.length * 2 ^ dp2ShiftSum rest * dp2GlobalOddVal ur)) := by
        rw [Nat.pow_succ, Nat.pow_add]; ac_rfl
      have hmid : 3 * (2 ^ a * (10 ^ rest.length * dp2GlobalOddVal w)) =
          10 ^ rest.length * (3 * (2 ^ a * dp2GlobalOddVal w)) := by ac_rfl
      have hrhs : 10 ^ rest.length * (10 * dp2GlobalOddVal u0) =
          10 ^ (rest.length + 1) * dp2GlobalOddVal u0 := by
        rw [Nat.pow_succ]; ac_rfl
      rw [hlhs, ← hrhs]
      exact Nat.le_trans h1 (by rw [hmid]; exact h2)

private theorem dp2IterCarry_pos_of_nonempty :
    ∀ (a : Nat) (rest : List Nat), dp2IterCarry (a :: rest) ≥ 1 := by
  intro a rest
  simp only [dp2IterCarry]
  have h3 := pow3_pos_nat rest.length
  omega

private theorem dp2IterCarry_steiner_closed :
    ∀ (k a_last : Nat),
      dp2IterCarry (List.replicate k 1 ++ [a_last]) = 3 ^ (k + 1) - 2 ^ (k + 1)
  | 0, a_last => by simp [dp2IterCarry]
  | k + 1, a_last => by
    have hlen : (List.replicate k 1 ++ [a_last]).length = k + 1 := by
      rw [List.length_append, List.length_replicate, List.length_singleton]
    have h2_le_3 : ∀ n : Nat, 2 ^ n ≤ 3 ^ n := by
      intro n; induction n with
      | zero => exact Nat.le_refl 1
      | succ n' ih => rw [Nat.pow_succ, Nat.pow_succ]; omega
    have hle := h2_le_3 (k + 1)
    simp only [List.replicate_succ, List.cons_append, dp2IterCarry, hlen,
               dp2IterCarry_steiner_closed k a_last, Nat.pow_one]
    rw [Nat.pow_succ 3 (k + 1), Nat.pow_succ 2 (k + 1)]
    omega

private theorem checkNoDivBy5Sum5 :
    ∀ a1 a2 a3 : Fin 4,
      (a1.val + 1) + (a2.val + 1) + (a3.val + 1) = 5 ->
      dp2IterCarry [a1.val + 1, a2.val + 1, a3.val + 1] % 5 ≠ 0 := by decide

private theorem checkNoDivBy13Sum8 :
    ∀ a1 a2 a3 a4 a5 : Fin 4,
      (a1.val + 1) + (a2.val + 1) + (a3.val + 1) + (a4.val + 1) + (a5.val + 1) = 8 ->
      dp2IterCarry [a1.val + 1, a2.val + 1, a3.val + 1, a4.val + 1, a5.val + 1] % 13 ≠ 0 := by
  decide

private theorem pow3_mod24_parity_cf : ∀ m : Nat, m ≥ 1 ->
    (m % 2 = 0 -> 3 ^ m % 24 = 9) ∧ (m % 2 = 1 -> 3 ^ m % 24 = 3)
  | 0, hm => by omega
  | 1, _ => ⟨fun h => by omega, fun _ => rfl⟩
  | m + 2, _ => by
    rcases pow3_mod24_parity_cf (m + 1) (by omega) with ⟨hev, hodd⟩
    refine ⟨fun he => ?_, fun ho => ?_⟩
    · have h1 := hodd (by omega)
      rw [Nat.pow_succ, Nat.mul_mod, h1]
    · have h1 := hev (by omega)
      rw [Nat.pow_succ, Nat.mul_mod, h1]

private theorem pow2_mod24_parity_cf : ∀ m : Nat, m ≥ 3 ->
    (m % 2 = 0 -> 2 ^ m % 24 = 16) ∧ (m % 2 = 1 -> 2 ^ m % 24 = 8)
  | 0, hm => by omega
  | 1, hm => by omega
  | 2, hm => by omega
  | 3, _ => ⟨fun h => by omega, fun _ => rfl⟩
  | m + 4, _ => by
    rcases pow2_mod24_parity_cf (m + 3) (by omega) with ⟨hev, hodd⟩
    refine ⟨fun he => ?_, fun ho => ?_⟩
    · have h1 := hodd (by omega)
      rw [Nat.pow_succ, Nat.mul_mod, h1]
    · have h1 := hev (by omega)
      rw [Nat.pow_succ, Nat.mul_mod, h1]

private theorem mod24_self_inv_solve (u k x b : Nat)
    (hu : u < 24) (hu2 : u * u = 24 * k + 1) (hx : x < 24) (hm : (u * x) % 24 = b) :
    x = (u * b) % 24 := by
  have h1 : (u * (u * x)) % 24 = (u * b) % 24 := by
    rw [Nat.mul_mod u (u * x), hm, Nat.mod_eq_of_lt hu]
  have h2 : u * (u * x) = x + 24 * (k * x) := by
    rw [← Nat.mul_assoc, hu2, Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
    omega
  rw [h2, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx] at h1
  exact h1

private theorem mod24_add_solve_one (d w k : Nat)
    (hd : d < 24) (hw : w < 24) (hadd : (d + w) % 24 = k) :
    d + w = k ∨ d + w = 24 + k := by
  cases hlt : Nat.ble 24 (d + w) with
  | false =>
    have h1 : d + w < 24 := by
      cases hc : decide (d + w < 24) with
      | true => exact of_decide_eq_true hc
      | false =>
        have hge : 24 ≤ d + w := Nat.le_of_not_lt (of_decide_eq_false hc)
        rw [Nat.ble_eq.mpr hge] at hlt; cases hlt
    rw [Nat.mod_eq_of_lt h1] at hadd
    exact Or.inl hadd
  | true =>
    have hge : 24 ≤ d + w := Nat.le_of_ble_eq_true hlt
    have hm : (d + w) % 24 = d + w - 24 := by
      conv => lhs; rw [show d + w = (d + w - 24) + 24 * 1 by omega]
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    rw [hm] at hadd
    exact Or.inr (by omega)

private theorem pow2_sub1_mod24 (n : Nat) (hp2 : 2 ^ n ≥ 2) :
    (2 ^ n % 24 = 16 -> (2 ^ n - 1) % 24 = 15) ∧
    (2 ^ n % 24 = 8 -> (2 ^ n - 1) % 24 = 7) := by
  have hdiv := (Nat.div_add_mod (2 ^ n) 24).symm
  refine ⟨fun h16 => ?_, fun h8 => ?_⟩
  · rw [h16] at hdiv
    have hsub : 2 ^ n - 1 = 15 + 24 * (2 ^ n / 24) := by omega
    rw [hsub, Nat.add_mul_mod_self_left]
  · rw [h8] at hdiv
    have hsub : 2 ^ n - 1 = 7 + 24 * (2 ^ n / 24) := by omega
    rw [hsub, Nat.add_mul_mod_self_left]

private theorem mod2_dichotomy_cf (m : Nat) : m % 2 = 0 ∨ m % 2 = 1 := by
  cases hb : decide (m % 2 = 0) with
  | true => exact Or.inl (of_decide_eq_true hb)
  | false =>
    have hne := of_decide_eq_false hb
    have hlt : m % 2 < 2 := Nat.mod_lt m (by decide)
    exact Or.inr (by omega)

private theorem one_block_steiner_cf (r a1 k_d : Nat)
    (hr2 : r ≥ 2) (ha1 : a1 ≥ 1) (hkd1 : k_d ≥ 1)
    (hgt : 3 ^ r < 2 ^ (r + a1))
    (hbrox : (2 ^ (r + a1) - 3 ^ r) * k_d = 2 ^ a1 - 1) :
    r ≥ 13 ∧ a1 ≥ 8 ∧ (∀ m : Nat, k_d ≠ 3 ^ m) ∧ k_d ≥ 17 := by
  have hD_le : 2 ^ (r + a1) - 3 ^ r ≤ 2 ^ a1 - 1 := by
    have hm := Nat.mul_le_mul_left (2 ^ (r + a1) - 3 ^ r) hkd1
    rw [Nat.mul_one, hbrox] at hm; exact hm
  rcases one_block_w1_ge_13_and_a1_ge_8 r a1 hr2 ha1 hgt hD_le with ⟨hr13, ha8⟩
  have hD_ge5 : 2 ^ (r + a1) - 3 ^ r ≥ 5 :=
    (det_mod24_and_ge5_constructive (r + a1) r (by omega) (by omega) hgt).2
  have hno_pow3 := one_block_no_pow3_quotient r a1 k_d (2 ^ (r + a1) - 3 ^ r)
    hr2 hr13 ha1 hgt rfl hD_ge5 hbrox
  let D := 2 ^ (r + a1) - 3 ^ r
  have hadd24 : (D % 24 + 3 ^ r % 24) % 24 = 2 ^ (r + a1) % 24 := by
    rw [← Nat.add_mod, show D + 3 ^ r = 2 ^ (r + a1) by dsimp [D]; omega]
  have hmul24 : ((D % 24) * (k_d % 24)) % 24 = (2 ^ a1 - 1) % 24 := by
    rw [← Nat.mul_mod]; dsimp [D]; rw [hbrox]
  have hd_lt : D % 24 < 24 := Nat.mod_lt _ (by decide)
  have hq_lt : k_d % 24 < 24 := Nat.mod_lt _ (by decide)
  rcases pow3_mod24_parity_cf r (by omega) with ⟨hw_ev, hw_od⟩
  rcases pow2_mod24_parity_cf (r + a1) (by omega) with ⟨hk_ev, hk_od⟩
  rcases pow2_mod24_parity_cf a1 (by omega) with ⟨ha_ev, ha_od⟩
  have hp2a : 2 ^ a1 ≥ 2 := by simpa using pow2_mono_nat (by omega : 1 ≤ a1)
  rcases pow2_sub1_mod24 a1 hp2a with ⟨hsub15, hsub7⟩
  have hne3 : k_d ≠ 3 := hno_pow3 1
  have hne9 : k_d ≠ 9 := hno_pow3 2
  have hge_of_mod : ∀ v : Nat, v ≥ 17 -> k_d % 24 = v -> k_d ≥ 17 := by
    intro v hv hqm
    have hdiv := (Nat.div_add_mod k_d 24).symm
    omega
  have hkd17 : k_d ≥ 17 := by
    rcases mod2_dichotomy_cf r with hr_e | hr_o
    · rcases mod2_dichotomy_cf a1 with ha_e | ha_o
      · have hw9 := hw_ev hr_e
        have hk16 := hk_ev (by rw [Nat.add_mod, hr_e, ha_e])
        rw [hw9, hk16] at hadd24
        have hd7 : D % 24 = 7 := by
          rcases mod24_add_solve_one (D % 24) 9 16 hd_lt (by decide) hadd24 with h | h <;> omega
        rw [hd7, hsub15 (ha_ev ha_e)] at hmul24
        have hq9 : k_d % 24 = 9 :=
          mod24_self_inv_solve 7 2 (k_d % 24) 15 (by decide) (by decide) hq_lt hmul24
        have hdiv := (Nat.div_add_mod k_d 24).symm
        omega
      · have hw9 := hw_ev hr_e
        have hk8 := hk_od (by rw [Nat.add_mod, hr_e, ha_o])
        rw [hw9, hk8] at hadd24
        have hd23 : D % 24 = 23 := by
          rcases mod24_add_solve_one (D % 24) 9 8 hd_lt (by decide) hadd24 with h | h <;> omega
        rw [hd23, hsub7 (ha_od ha_o)] at hmul24
        exact hge_of_mod 17 (by decide)
          (mod24_self_inv_solve 23 22 (k_d % 24) 7 (by decide) (by decide) hq_lt hmul24)
    · rcases mod2_dichotomy_cf a1 with ha_e | ha_o
      · have hw3 := hw_od hr_o
        have hk8 := hk_od (by rw [Nat.add_mod, hr_o, ha_e])
        rw [hw3, hk8] at hadd24
        have hd5 : D % 24 = 5 := by
          rcases mod24_add_solve_one (D % 24) 3 8 hd_lt (by decide) hadd24 with h | h <;> omega
        rw [hd5, hsub15 (ha_ev ha_e)] at hmul24
        have hq3 : k_d % 24 = 3 :=
          mod24_self_inv_solve 5 1 (k_d % 24) 15 (by decide) (by decide) hq_lt hmul24
        have hdiv := (Nat.div_add_mod k_d 24).symm
        omega
      · have hw3 := hw_od hr_o
        have hk16 := hk_ev (by rw [Nat.add_mod, hr_o, ha_o])
        rw [hw3, hk16] at hadd24
        have hd13 : D % 24 = 13 := by
          rcases mod24_add_solve_one (D % 24) 3 16 hd_lt (by decide) hadd24 with h | h <;> omega
        rw [hd13, hsub7 (ha_od ha_o)] at hmul24
        exact hge_of_mod 19 (by decide)
          (mod24_self_inv_solve 13 7 (k_d % 24) 7 (by decide) (by decide) hq_lt hmul24)
  exact ⟨hr13, ha8, hno_pow3, hkd17⟩

/--
  Theorem W14.1e (`leftAnchoredDP2_iterated_affine_carry_and_cycle_laws`,
  choice-free `zero custom axioms`):
  Exact `∀ r ≥ 1` Iterated `leftAnchoredDP2Step` Affine-Carry Homomorphism, `3^r * 2^A ≤ 10^r`
  Loop Confinement, Unconditional `1..5`-Cycle Freedom, `M1` Carry Separation, & Exponential `17 * 2^r`
  1-Block Steiner `DP2` Cycle Lock (`Branch P4.3`).
-/
theorem leftAnchoredDP2_iterated_affine_carry_and_cycle_laws :
    (∀ (r : Nat) (u0 ur : List MixedSRSSym),
      dp2StepIter r u0 ur ->
      (.R ∈ u0 ↔ .R ∈ ur) ∧
      ∃ shifts : List Nat,
        shifts.length = r ∧
        (∀ a ∈ shifts, a ≥ 1) ∧
        dp2AnnotatedChain u0 shifts ur ∧
        2 ^ dp2ShiftSum shifts * dp2GlobalOddVal ur =
          3 ^ r * dp2GlobalOddVal u0 + dp2IterCarry shifts ∧
        3 ^ r * 2 ^ dp2ShiftSum shifts * dp2GlobalOddVal ur ≤
          10 ^ r * dp2GlobalOddVal u0) ∧
    ((∀ (shifts : List Nat) (u0 : List MixedSRSSym),
        shifts.length ≥ 1 ->
        dp2AnnotatedChain u0 shifts u0 ->
        let r := shifts.length
        let A := dp2ShiftSum shifts
        3 ^ r < 2 ^ A ∧
        3 ^ r * 2 ^ A ≤ 10 ^ r ∧
        (2 ^ A - 3 ^ r) * dp2GlobalOddVal u0 = dp2IterCarry shifts ∧
        (2 ^ A - 3 ^ r) ∣ dp2IterCarry shifts) ∧
     (dp2IterCarry [1, 1, 3] = 19 ∧ 19 % (2 ^ 5 - 3 ^ 3) = 4 ∧
      dp2IterCarry [2, 1, 2] = 29 ∧ 29 % (2 ^ 5 - 3 ^ 3) = 4 ∧
      dp2IterCarry [1, 1, 2, 1, 3] = 251 ∧ 251 % (2 ^ 8 - 3 ^ 5) = 4)) ∧
    (∀ (r : Nat) (u : List MixedSRSSym),
      1 ≤ r -> r ≤ 5 -> ¬ dp2StepIter r u u) ∧
    (∀ (r a_last : Nat), r ≥ 1 ->
      dp2IterCarry (List.replicate (r - 1) 1 ++ [a_last]) = 3 ^ r - 2 ^ r ∧
      (∀ u0 : List MixedSRSSym,
        dp2AnnotatedChain u0 (List.replicate (r - 1) 1 ++ [a_last]) u0 ->
        r ≥ 13 ∧ a_last ≥ 9 ∧
        2 ^ r ∣ (dp2GlobalOddVal u0 + 1) ∧
        (∀ m : Nat, (dp2GlobalOddVal u0 + 1) / 2 ^ r ≠ 3 ^ m) ∧
        dp2GlobalOddVal u0 ≥ 17 * 2 ^ r - 1 ∧
        (2 ^ (r - 1 + a_last) - 3 ^ r) * (17 * 2 ^ r - 1) ≤ 3 ^ r - 2 ^ r)) := by
  have hiter_to_ann : ∀ (r : Nat) (u0 ur : List MixedSRSSym),
      dp2StepIter r u0 ur ->
      ∃ shifts : List Nat, shifts.length = r ∧ dp2AnnotatedChain u0 shifts ur := by
    intro r; induction r with
    | zero =>
      intro u0 ur h0; subst h0; exact ⟨[], rfl, rfl⟩
    | succ r' ih =>
      intro u0 ur ⟨w, hstep, htl⟩
      rcases (leftAnchoredDP2_r_carrying_syracuse_and_no_1_2_cycles.1 u0 w hstep).2 with
        ⟨a, ha1, hsyr⟩
      rcases ih w ur htl with ⟨rest, hlen, hann_tl⟩
      exact ⟨a :: rest, by simp [hlen], ha1, w, hstep, hsyr, hann_tl⟩
  have hpart1 : ∀ (r : Nat) (u0 ur : List MixedSRSSym),
      dp2StepIter r u0 ur ->
      (.R ∈ u0 ↔ .R ∈ ur) ∧
      ∃ shifts : List Nat,
        shifts.length = r ∧
        (∀ a ∈ shifts, a ≥ 1) ∧
        dp2AnnotatedChain u0 shifts ur ∧
        2 ^ dp2ShiftSum shifts * dp2GlobalOddVal ur =
          3 ^ r * dp2GlobalOddVal u0 + dp2IterCarry shifts ∧
        3 ^ r * 2 ^ dp2ShiftSum shifts * dp2GlobalOddVal ur ≤
          10 ^ r * dp2GlobalOddVal u0 := by
    intro r u0 ur hiter
    rcases hiter_to_ann r u0 ur hiter with ⟨shifts, hlen, hann⟩
    rcases dp2AnnotatedChain_homomorphism shifts u0 ur hann with ⟨hR, hall, heq, h10⟩
    rw [hlen] at heq h10
    exact ⟨hR, shifts, hlen, hall, hann, heq, h10⟩
  have hloop_conf : ∀ (shifts : List Nat) (u0 : List MixedSRSSym),
      shifts.length ≥ 1 ->
      dp2AnnotatedChain u0 shifts u0 ->
      let r := shifts.length
      let A := dp2ShiftSum shifts
      3 ^ r < 2 ^ A ∧
      3 ^ r * 2 ^ A ≤ 10 ^ r ∧
      (2 ^ A - 3 ^ r) * dp2GlobalOddVal u0 = dp2IterCarry shifts ∧
      (2 ^ A - 3 ^ r) ∣ dp2IterCarry shifts := by
    intro shifts u0 hr1 hann
    dsimp only
    rcases dp2AnnotatedChain_homomorphism shifts u0 u0 hann with ⟨_, _, heq, h10⟩
    have hu0_pos : 0 < dp2GlobalOddVal u0 := by unfold dp2GlobalOddVal; omega
    have hc_pos : dp2IterCarry shifts ≥ 1 := by
      cases shifts with
      | nil => simp at hr1
      | cons a tl => exact dp2IterCarry_pos_of_nonempty a tl
    have h3_lt_2 : 3 ^ shifts.length < 2 ^ dp2ShiftSum shifts := by
      by_cases hlt : 3 ^ shifts.length < 2 ^ dp2ShiftSum shifts
      · exact hlt
      · exfalso
        have hle : 2 ^ dp2ShiftSum shifts ≤ 3 ^ shifts.length := by omega
        have hm := Nat.mul_le_mul_right (dp2GlobalOddVal u0) hle
        omega
    have h10_div : 3 ^ shifts.length * 2 ^ dp2ShiftSum shifts ≤ 10 ^ shifts.length := by
      by_cases hle : 3 ^ shifts.length * 2 ^ dp2ShiftSum shifts ≤ 10 ^ shifts.length
      · exact hle
      · exfalso
        have hgt : 10 ^ shifts.length < 3 ^ shifts.length * 2 ^ dp2ShiftSum shifts := by omega
        have hm := Nat.mul_lt_mul_of_pos_right hgt hu0_pos
        omega
    have hsub_eq : (2 ^ dp2ShiftSum shifts - 3 ^ shifts.length) * dp2GlobalOddVal u0 =
        dp2IterCarry shifts := by
      rw [Nat.sub_mul, heq]; omega
    exact ⟨h3_lt_2, h10_div, hsub_eq, ⟨dp2GlobalOddVal u0, hsub_eq.symm⟩⟩
  have hno_1_5 : ∀ (r : Nat) (u : List MixedSRSSym),
      1 ≤ r -> r ≤ 5 -> ¬ dp2StepIter r u u := by
    intro r u hr1 hr5 hiter
    rcases hiter_to_ann r u u hiter with ⟨shifts, hlen, hann⟩
    rcases hloop_conf shifts u (by omega) hann with ⟨hlt, h10, hsub_eq, _⟩
    rw [hlen] at hlt h10 hsub_eq
    let A := dp2ShiftSum shifts
    change 3 ^ r < 2 ^ A at hlt
    change 3 ^ r * 2 ^ A ≤ 10 ^ r at h10
    rcases (by omega : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5) with rfl | rfl | rfl | rfl | rfl
    · omega
    · rcases (by omega : A ≤ 3 ∨ A ≥ 4) with hA3 | hA4
      · have hp : 2 ^ A ≤ 8 := by simpa using nat_pow_mono_exp_pos 2 A 3 (by decide) hA3
        omega
      · have hp : 2 ^ A ≥ 16 := by simpa using nat_pow_mono_exp_pos 2 4 A (by decide) hA4
        omega
    · have hA5 : A = 5 := by
        rcases (by omega : A ≤ 4 ∨ A = 5 ∨ A ≥ 6) with hA4 | h5 | hA6
        · have hp : 2 ^ A ≤ 16 := by simpa using nat_pow_mono_exp_pos 2 A 4 (by decide) hA4
          omega
        · exact h5
        · have hp : 2 ^ A ≥ 64 := by simpa using nat_pow_mono_exp_pos 2 6 A (by decide) hA6
          omega
      rcases dp2AnnotatedChain_homomorphism shifts u u hann with ⟨_, hall1, _, _⟩
      cases shifts with
      | nil => simp at hlen
      | cons s1 tl1 =>
        cases tl1 with
        | nil => simp at hlen
        | cons s2 tl2 =>
          cases tl2 with
          | nil => simp at hlen
          | cons s3 tl3 =>
            cases tl3 with
            | cons _ _ => simp at hlen
            | nil =>
              have hs1 := hall1 s1 (by simp)
              have hs2 := hall1 s2 (by simp)
              have hs3 := hall1 s3 (by simp)
              change s1 + (s2 + (s3 + 0)) = 5 at hA5
              have hmod0 : dp2IterCarry [s1, s2, s3] % 5 = 0 := by
                have hsub_u : (2 ^ A - 27) * dp2GlobalOddVal u = dp2IterCarry [s1, s2, s3] := hsub_eq
                have hA_eq : A = 5 := hA5
                rw [hA_eq] at hsub_u; omega
              exact checkNoDivBy5Sum5
                ⟨s1 - 1, by omega⟩ ⟨s2 - 1, by omega⟩ ⟨s3 - 1, by omega⟩
                (by dsimp; omega)
                (by dsimp; rwa [show s1 - 1 + 1 = s1 by omega,
                                show s2 - 1 + 1 = s2 by omega,
                                show s3 - 1 + 1 = s3 by omega])
    · rcases (by omega : A ≤ 6 ∨ A ≥ 7) with hA6 | hA7
      · have hp : 2 ^ A ≤ 64 := by simpa using nat_pow_mono_exp_pos 2 A 6 (by decide) hA6
        omega
      · have hp : 2 ^ A ≥ 128 := by simpa using nat_pow_mono_exp_pos 2 7 A (by decide) hA7
        omega
    · have hA8 : A = 8 := by
        rcases (by omega : A ≤ 7 ∨ A = 8 ∨ A ≥ 9) with hA7 | h8 | hA9
        · have hp : 2 ^ A ≤ 128 := by simpa using nat_pow_mono_exp_pos 2 A 7 (by decide) hA7
          omega
        · exact h8
        · have hp : 2 ^ A ≥ 512 := by simpa using nat_pow_mono_exp_pos 2 9 A (by decide) hA9
          omega
      rcases dp2AnnotatedChain_homomorphism shifts u u hann with ⟨_, hall1, _, _⟩
      cases shifts with
      | nil => simp at hlen
      | cons s1 t1 =>
        cases t1 with
        | nil => simp at hlen
        | cons s2 t2 =>
          cases t2 with
          | nil => simp at hlen
          | cons s3 t3 =>
            cases t3 with
            | nil => simp at hlen
            | cons s4 t4 =>
              cases t4 with
              | nil => simp at hlen
              | cons s5 t5 =>
                cases t5 with
                | cons _ _ => simp at hlen
                | nil =>
                  have hs1 := hall1 s1 (by simp)
                  have hs2 := hall1 s2 (by simp)
                  have hs3 := hall1 s3 (by simp)
                  have hs4 := hall1 s4 (by simp)
                  have hs5 := hall1 s5 (by simp)
                  change s1 + (s2 + (s3 + (s4 + (s5 + 0)))) = 8 at hA8
                  have hmod0 : dp2IterCarry [s1, s2, s3, s4, s5] % 13 = 0 := by
                    have hsub_u : (2 ^ A - 243) * dp2GlobalOddVal u = dp2IterCarry [s1, s2, s3, s4, s5] := hsub_eq
                    have hA_eq : A = 8 := hA8
                    rw [hA_eq] at hsub_u; omega
                  exact checkNoDivBy13Sum8
                    ⟨s1 - 1, by omega⟩ ⟨s2 - 1, by omega⟩ ⟨s3 - 1, by omega⟩
                    ⟨s4 - 1, by omega⟩ ⟨s5 - 1, by omega⟩
                    (by dsimp; omega)
                    (by dsimp; rwa [show s1 - 1 + 1 = s1 by omega,
                                    show s2 - 1 + 1 = s2 by omega,
                                    show s3 - 1 + 1 = s3 by omega,
                                    show s4 - 1 + 1 = s4 by omega,
                                    show s5 - 1 + 1 = s5 by omega])
  have hpart4 : ∀ (r a_last : Nat), r ≥ 1 ->
      dp2IterCarry (List.replicate (r - 1) 1 ++ [a_last]) = 3 ^ r - 2 ^ r ∧
      (∀ u0 : List MixedSRSSym,
        dp2AnnotatedChain u0 (List.replicate (r - 1) 1 ++ [a_last]) u0 ->
        r ≥ 13 ∧ a_last ≥ 9 ∧
        2 ^ r ∣ (dp2GlobalOddVal u0 + 1) ∧
        (∀ m : Nat, (dp2GlobalOddVal u0 + 1) / 2 ^ r ≠ 3 ^ m) ∧
        dp2GlobalOddVal u0 ≥ 17 * 2 ^ r - 1 ∧
        (2 ^ (r - 1 + a_last) - 3 ^ r) * (17 * 2 ^ r - 1) ≤ 3 ^ r - 2 ^ r) := by
    have hsum_rep1 : ∀ (k a_l : Nat),
        dp2ShiftSum (List.replicate k 1 ++ [a_l]) = k + a_l := by
      intro k a_l; induction k with
      | zero => simp [dp2ShiftSum]
      | succ k' ih =>
        simp only [List.replicate_succ, List.cons_append, dp2ShiftSum, ih]
        omega
    have h2_r1_le_3 : ∀ m : Nat, m ≥ 2 -> 2 ^ (m + 1) ≤ 3 ^ m := by
      intro m hm
      have hst : ∀ d : Nat, 2 ^ (2 + d + 1) ≤ 3 ^ (2 + d) := by
        intro d; induction d with
        | zero => decide
        | succ d' ih =>
          rw [show 2 + (d' + 1) + 1 = (2 + d' + 1) + 1 by omega,
              show 2 + (d' + 1) = (2 + d') + 1 by omega,
              Nat.pow_succ 2, Nat.pow_succ 3]
          omega
      simpa [show 2 + (m - 2) = m by omega] using hst (m - 2)
    have hcop_pow2_3 : ∀ r : Nat, Nat.Coprime (2 ^ r) (3 ^ r) := by
      intro r
      have h1 : Nat.Coprime 2 3 := by decide
      exact (h1.pow_left r).pow_right r
    intro r a_last hr1
    have hcar_eq : dp2IterCarry (List.replicate (r - 1) 1 ++ [a_last]) = 3 ^ r - 2 ^ r := by
      simpa [show r - 1 + 1 = r by omega] using dp2IterCarry_steiner_closed (r - 1) a_last
    refine ⟨hcar_eq, ?_⟩
    intro u0 hann
    have hlen_s : (List.replicate (r - 1) 1 ++ [a_last]).length = r := by
      rw [List.length_append, List.length_replicate, List.length_singleton]; omega
    have hsum_s : dp2ShiftSum (List.replicate (r - 1) 1 ++ [a_last]) = r - 1 + a_last :=
      hsum_rep1 (r - 1) a_last
    rcases hloop_conf _ u0 (by omega) hann with ⟨hlt, h10, hsub_eq, _⟩
    rw [hlen_s, hsum_s] at hlt h10 hsub_eq
    rw [hcar_eq] at hsub_eq
    have hsub_orig := hsub_eq
    have hN0_ge3 : dp2GlobalOddVal u0 ≥ 3 := by unfold dp2GlobalOddVal; omega
    have hr_ge2 : r ≥ 2 := by
      by_cases hr_eq1 : r = 1
      · exfalso
        rw [hr_eq1] at hlt hsub_eq
        simp only [Nat.sub_self, Nat.zero_add, Nat.pow_one] at hlt hsub_eq
        have hpos_d : 2 ^ a_last - 3 ≥ 1 := by omega
        have hm := Nat.mul_le_mul hpos_d hN0_ge3
        omega
      · omega
    have ha_ge3 : a_last ≥ 3 := by
      by_cases ha_le2 : a_last ≤ 2
      · exfalso
        have hA_le : r - 1 + a_last ≤ r + 1 := by omega
        have hp1 : 2 ^ (r - 1 + a_last) ≤ 2 ^ (r + 1) :=
          nat_pow_mono_exp_pos 2 _ _ (by decide) hA_le
        have hp2 := h2_r1_le_3 r hr_ge2
        omega
      · omega
    let N0 := dp2GlobalOddVal u0
    have h2_le_3r : 2 ^ r ≤ 3 ^ r := by
      have hst : ∀ n : Nat, 2 ^ n ≤ 3 ^ n := by
        intro n; induction n with
        | zero => exact Nat.le_refl 1
        | succ n' ih => rw [Nat.pow_succ, Nat.pow_succ]; omega
      exact hst r
    have hA_split : 2 ^ (r - 1 + a_last) = 2 ^ r * 2 ^ (a_last - 1) := by
      rw [← Nat.pow_add, show r + (a_last - 1) = r - 1 + a_last by omega]
    have hbal : 2 ^ r * (2 ^ (a_last - 1) * N0 + 1) = 3 ^ r * (N0 + 1) := by
      have hexp1 : 2 ^ (r - 1 + a_last) * N0 = 2 ^ r * (2 ^ (a_last - 1) * N0) := by
        rw [hA_split, Nat.mul_assoc]
      rw [Nat.sub_mul] at hsub_eq
      dsimp only [N0] at hexp1 ⊢
      rw [Nat.mul_add (2 ^ r), Nat.mul_one, ← hexp1, Nat.mul_add (3 ^ r), Nat.mul_one]
      have h3N0_le : 3 ^ r * dp2GlobalOddVal u0 ≤ 2 ^ (r - 1 + a_last) * dp2GlobalOddVal u0 :=
        Nat.mul_le_mul_right _ (Nat.le_of_lt hlt)
      omega
    have hdvd_prod : 2 ^ r ∣ 3 ^ r * (N0 + 1) :=
      ⟨2 ^ (a_last - 1) * N0 + 1, hbal.symm⟩
    have hdvd_N01 : 2 ^ r ∣ (N0 + 1) :=
      (hcop_pow2_3 r).dvd_of_dvd_mul_left hdvd_prod
    rcases hdvd_N01 with ⟨k_d, hkd⟩
    have hkd_pos : k_d ≥ 1 := by
      cases k_d with
      | zero => rw [Nat.mul_zero] at hkd; dsimp [N0] at hkd; omega
      | succ k' => omega
    have hpow2r_pos : 0 < 2 ^ r := nat_pow_pos_of_pos 2 (by decide) r
    have hbal_kd : 2 ^ r * (2 ^ (a_last - 1) * N0 + 1) = 2 ^ r * (3 ^ r * k_d) := by
      rw [hbal, hkd]; ac_rfl
    have hsyr_kd : 2 ^ (a_last - 1) * N0 + 1 = 3 ^ r * k_d :=
      Nat.eq_of_mul_eq_mul_left hpow2r_pos hbal_kd
    have ha1_ge1 : a_last - 1 ≥ 1 := by omega
    have hpow_a1_pos : 2 ^ (a_last - 1) ≥ 1 := nat_pow_pos_of_pos 2 (by decide) (a_last - 1)
    have hmul_N01 : 2 ^ (a_last - 1) * (N0 + 1) = 2 ^ (r + (a_last - 1)) * k_d := by
      rw [hkd, Nat.pow_add 2 r (a_last - 1)]; ac_rfl
    have hexp_N01 : 2 ^ (a_last - 1) * (N0 + 1) =
        (2 ^ (a_last - 1) * N0 + 1) + (2 ^ (a_last - 1) - 1) := by
      rw [Nat.mul_add, Nat.mul_one]; omega
    rw [hmul_N01, hsyr_kd] at hexp_N01
    have hgt_kd : 3 ^ r < 2 ^ (r + (a_last - 1)) := by
      rwa [show r + (a_last - 1) = r - 1 + a_last by omega]
    have hbrox_kd : (2 ^ (r + (a_last - 1)) - 3 ^ r) * k_d = 2 ^ (a_last - 1) - 1 := by
      rw [Nat.sub_mul, hexp_N01]; omega
    rcases one_block_steiner_cf r (a_last - 1) k_d hr_ge2 ha1_ge1 hkd_pos hgt_kd hbrox_kd with
      ⟨hr_ge13, ha1_ge8, hkd_no_pow3, hkd_ge17⟩
    have ha_ge9 : a_last ≥ 9 := by omega
    have hdiv_eq : (dp2GlobalOddVal u0 + 1) / 2 ^ r = k_d := by
      dsimp only [N0] at hkd
      rw [hkd, Nat.mul_comm (2 ^ r) k_d, Nat.mul_div_cancel k_d hpow2r_pos]
    have hno_pow3_div : ∀ m : Nat, (dp2GlobalOddVal u0 + 1) / 2 ^ r ≠ 3 ^ m := by
      rw [hdiv_eq]; exact hkd_no_pow3
    have hN0_ge_17 : N0 ≥ 17 * 2 ^ r - 1 := by
      have hm := Nat.mul_le_mul_left (2 ^ r) hkd_ge17
      rw [← hkd, Nat.mul_comm (2 ^ r) 17] at hm
      omega
    have hbound_st17 : (2 ^ (r - 1 + a_last) - 3 ^ r) * (17 * 2 ^ r - 1) ≤ 3 ^ r - 2 ^ r := by
      have hm := Nat.mul_le_mul_left (2 ^ (r - 1 + a_last) - 3 ^ r) hN0_ge_17
      dsimp only [N0] at hm
      rwa [hsub_orig] at hm
    exact ⟨hr_ge13, ha_ge9, ⟨k_d, hkd⟩, hno_pow3_div, hN0_ge_17, hbound_st17⟩
  exact ⟨hpart1, ⟨hloop_conf, by decide⟩, hno_1_5, hpart4⟩

-- ============================================================================
-- SECTION 2: Front B (Branches P3.3 & P3.4) — Third-Order Four-Block `(U = 4)`
--            Cyclotomic Mixed-Newton Confluent Divisibility, Majorant & Sharpness,
--            Joint Row+Column `6 × 6` LCM / Coprime Reduction & `(4, 7, 1)` Contrast,
--            Rank-3 `9 × 9` `(T = 3, U = 3)` All-`u` Cone Positivity & `u = 1..4`
--            Global Non-Vanishing, & Two-Pivot / `5 × d_mult` 2-Adic Brox Elimination
-- ============================================================================

-- ----------------------------------------------------------------------------
-- Section 2A: Four-Block `(U = 4)` Third-Order Cyclotomic Mixed-Newton
--             Confluent Factorization, Reduced Majorant, & Unit-Grid Sharpness
-- ----------------------------------------------------------------------------

def laurentColsRank4OrderT (T u : Nat) (j : Fin (4 * T)) : Nat × Nat :=
  if j.val < T then (j.val, 0)
  else if j.val < 2 * T then (j.val - T, u)
  else if j.val < 3 * T then (j.val - 2 * T, 2 * u)
  else (j.val - 3 * T, 3 * u)

def mixedNode4 (T P r : Nat) : Nat :=
  if r < T then 1
  else if r < 2 * T then P
  else if r < 3 * T then P * P
  else P * P * P

def mixedNewtonCoeff4 (T P : Nat) : Nat -> Nat -> Nat
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | x + 1, 0 => mixedNode4 T P 0 * mixedNewtonCoeff4 T P x 0
  | x + 1, r + 1 =>
    mixedNewtonCoeff4 T P x r + mixedNode4 T P (r + 1) * mixedNewtonCoeff4 T P x (r + 1)

def hasseNodePoly4 (T P : Nat) : Nat -> Nat -> Nat -> Nat
  | 0, _, 0 => 1
  | 0, _, _ + 1 => 0
  | r + 1, zv, 0 => (zv - mixedNode4 T P r) * hasseNodePoly4 T P r zv 0
  | r + 1, zv, t + 1 =>
    hasseNodePoly4 T P r zv t + (zv - mixedNode4 T P r) * hasseNodePoly4 T P r zv (t + 1)

def confluentFactorRank4 (T u : Nat) : Nat :=
  2 ^ ((3 * T * (T - 1) + 4 * (T * T)) * u) *
    (2 ^ u - 1) ^ (6 * (T * T)) *
    (2 ^ u + 1) ^ (2 * (T * T)) *
    (4 ^ u + 2 ^ u + 1) ^ (T * T)

private theorem natSumUpTo_congr_w14 (n : Nat) (f g : Nat -> Nat)
    (h : ∀ i : Nat, i < n -> f i = g i) : natSumUpTo n f = natSumUpTo n g := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [natSumUpTo]
    rw [ih (fun i hi => h i (Nat.lt_trans hi (Nat.lt_succ_self k))),
        h k (Nat.lt_succ_self k)]

private theorem natSumUpTo_mul_left_w14 (c n : Nat) (f : Nat -> Nat) :
    c * natSumUpTo n f = natSumUpTo n (fun i => c * f i) := by
  induction n with
  | zero => simp [natSumUpTo]
  | succ k ih => simp only [natSumUpTo, Nat.mul_add, ih]

private theorem two_mul_triNumNat_w14 : ∀ m : Nat, 2 * triNumNat m = m * (m - 1)
  | 0 => rfl
  | m + 1 => by
    simp only [triNumNat, Nat.add_sub_cancel]
    have ih := two_mul_triNumNat_w14 m
    cases m with
    | zero => simp [triNumNat]
    | succ m' =>
      simp only [Nat.add_sub_cancel] at ih
      rw [Nat.mul_add 2 (triNumNat (m' + 1)) (m' + 1), ih,
          Nat.mul_add (m' + 1 + 1) m' 1, Nat.add_mul (m' + 1) 1 m']
      omega

private theorem mixedNewtonCoeff4_zero_right (T P : Nat) (hT : T ≥ 1) :
    ∀ x : Nat, mixedNewtonCoeff4 T P x 0 = 1
  | 0 => rfl
  | x + 1 => by
    have h0T : 0 < T := hT
    simp only [mixedNewtonCoeff4, mixedNode4, h0T, ite_true, Nat.one_mul,
               mixedNewtonCoeff4_zero_right T P hT x]

private theorem mixedNewtonCoeff4_above_zero (T P : Nat) :
    ∀ (x r : Nat), x < r -> mixedNewtonCoeff4 T P x r = 0
  | 0, _ + 1, _ => rfl
  | x + 1, r + 1, hlt => by
    simp only [mixedNewtonCoeff4]
    rw [mixedNewtonCoeff4_above_zero T P x r (by omega),
        mixedNewtonCoeff4_above_zero T P x (r + 1) (by omega),
        Nat.mul_zero, Nat.add_zero]

private theorem mixedNewtonCoeff4_diag_one (T P : Nat) (hT : T ≥ 1) :
    ∀ r : Nat, mixedNewtonCoeff4 T P r r = 1
  | 0 => rfl
  | r + 1 => by
    simp only [mixedNewtonCoeff4, mixedNewtonCoeff4_diag_one T P hT r,
               mixedNewtonCoeff4_above_zero T P r (r + 1) (Nat.lt_succ_self r),
               Nat.mul_zero, Nat.add_zero]

private theorem mixedNewtonCoeff4_mono_x (T P : Nat) (hT : T ≥ 1) (hP : P ≥ 1) :
    ∀ (x r : Nat), mixedNewtonCoeff4 T P x r ≤ mixedNewtonCoeff4 T P (x + 1) r
  | x, 0 => by
    rw [mixedNewtonCoeff4_zero_right T P hT x, mixedNewtonCoeff4_zero_right T P hT (x + 1)]
    exact Nat.le_refl 1
  | x, r + 1 => by
    simp only [mixedNewtonCoeff4]
    have hn_pos : mixedNode4 T P (r + 1) ≥ 1 := by
      unfold mixedNode4
      by_cases h1 : r + 1 < T
      · simp [h1]
      · by_cases h2 : r + 1 < 2 * T
        · simp [h1, h2, hP]
        · by_cases h3 : r + 1 < 3 * T
          · simp only [h1, h2, h3, ite_false, ite_true]; exact Nat.mul_le_mul hP hP
          · simp only [h1, h2, h3, ite_false]
            exact Nat.mul_le_mul (Nat.mul_le_mul hP hP) hP
    have hm := Nat.mul_le_mul_right (mixedNewtonCoeff4 T P x (r + 1)) hn_pos
    omega

private theorem mixedNewtonCoeff4_le_of_le (T P : Nat) (hT : T ≥ 1) (hP : P ≥ 1) :
    ∀ (x1 x2 r : Nat), x1 ≤ x2 -> mixedNewtonCoeff4 T P x1 r ≤ mixedNewtonCoeff4 T P x2 r := by
  intro x1 x2 r hle
  have hst : ∀ d : Nat, mixedNewtonCoeff4 T P x1 r ≤ mixedNewtonCoeff4 T P (x1 + d) r := by
    intro d; induction d with
    | zero => exact Nat.le_refl _
    | succ d' ih => exact Nat.le_trans ih (mixedNewtonCoeff4_mono_x T P hT hP (x1 + d') r)
  simpa [show x1 + (x2 - x1) = x2 by omega] using hst (x2 - x1)

private theorem mixedNewtonCoeff4_pos_of_le (T P : Nat) (hT : T ≥ 1) :
    ∀ (r x : Nat), r ≤ x -> mixedNewtonCoeff4 T P x r ≥ 1
  | 0, x, _ => by rw [mixedNewtonCoeff4_zero_right T P hT x]; exact Nat.le_refl 1
  | r + 1, 0, h => by omega
  | r + 1, x + 1, h => by
    simp only [mixedNewtonCoeff4]
    have ih := mixedNewtonCoeff4_pos_of_le T P hT r x (by omega)
    omega

private theorem hasseNodePoly4_zero_right_block0 (T P zv : Nat) :
    ∀ k : Nat, k ≤ T -> hasseNodePoly4 T P k zv 0 = (zv - 1) ^ k
  | 0, _ => rfl
  | k + 1, hk => by
    have hk_lt : k < T := hk
    simp only [hasseNodePoly4, mixedNode4, hk_lt, ite_true]
    rw [hasseNodePoly4_zero_right_block0 T P zv k (Nat.le_of_lt hk),
        Nat.pow_succ, Nat.mul_comm]

private theorem hasseNodePoly4_zero_right_block1 (T P zv : Nat) :
    ∀ k : Nat, k ≤ T -> hasseNodePoly4 T P (T + k) zv 0 = (zv - 1) ^ T * (zv - P) ^ k
  | 0, _ => by
    rw [Nat.add_zero, Nat.pow_zero, Nat.mul_one]
    exact hasseNodePoly4_zero_right_block0 T P zv T (Nat.le_refl T)
  | k + 1, hk => by
    rw [Nat.add_succ]
    have hnot1 : ¬ (T + k < T) := by omega
    have hlt2 : T + k < 2 * T := by omega
    simp only [hasseNodePoly4, mixedNode4, hnot1, hlt2, ite_false, ite_true]
    rw [hasseNodePoly4_zero_right_block1 T P zv k (Nat.le_of_lt hk), Nat.pow_succ]
    ac_rfl

private theorem hasseNodePoly4_zero_right_block2 (T P zv : Nat) :
    ∀ k : Nat, k ≤ T ->
      hasseNodePoly4 T P (2 * T + k) zv 0 =
        (zv - 1) ^ T * (zv - P) ^ T * (zv - P * P) ^ k
  | 0, _ => by
    rw [Nat.add_zero, Nat.pow_zero, Nat.mul_one, show 2 * T = T + T by omega]
    exact hasseNodePoly4_zero_right_block1 T P zv T (Nat.le_refl T)
  | k + 1, hk => by
    rw [Nat.add_succ]
    have hnot1 : ¬ (2 * T + k < T) := by omega
    have hnot2 : ¬ (2 * T + k < 2 * T) := by omega
    have hlt3 : 2 * T + k < 3 * T := by omega
    simp only [hasseNodePoly4, mixedNode4, hnot1, hnot2, hlt3, ite_false, ite_true]
    rw [hasseNodePoly4_zero_right_block2 T P zv k (Nat.le_of_lt hk), Nat.pow_succ]
    ac_rfl

private theorem hasseNodePoly4_in_equal_block (T P b0 zv : Nat)
    (heq_node : ∀ s : Nat, s < T -> mixedNode4 T P (b0 + s) = zv) :
    ∀ (s t : Nat), s ≤ T ->
      hasseNodePoly4 T P (b0 + s) zv t =
        if s ≤ t then hasseNodePoly4 T P b0 zv (t - s) else 0
  | 0, t, _ => by simp
  | s + 1, 0, hsT => by
    rw [Nat.add_succ]
    simp only [hasseNodePoly4, heq_node s hsT, Nat.sub_self, Nat.zero_mul]
    simp
  | s + 1, t + 1, hsT => by
    rw [Nat.add_succ]
    simp only [hasseNodePoly4, heq_node s hsT, Nat.sub_self, Nat.zero_mul, Nat.add_zero]
    rw [hasseNodePoly4_in_equal_block T P b0 zv heq_node s t (Nat.le_of_lt hsT)]
    by_cases hst : s ≤ t
    · have hst1 : s + 1 ≤ t + 1 := by omega
      rw [ite_true_of_w10 hst, ite_true_of_w10 hst1, show t + 1 - (s + 1) = t - s by omega]
    · have hst1 : ¬ (s + 1 ≤ t + 1) := by omega
      rw [ite_false_of_w10 hst, ite_false_of_w10 hst1]

private theorem hasseNodePoly4_zero_after_block (T P b0 zv : Nat)
    (hz_base : ∀ t : Nat, t < T -> hasseNodePoly4 T P (b0 + T) zv t = 0) :
    ∀ (q t : Nat), t < T -> hasseNodePoly4 T P (b0 + T + q) zv t = 0
  | 0, t, ht => by simpa using hz_base t ht
  | q + 1, 0, ht => by
    rw [Nat.add_succ]
    simp only [hasseNodePoly4, hasseNodePoly4_zero_after_block T P b0 zv hz_base q 0 ht,
               Nat.mul_zero]
  | q + 1, t + 1, ht => by
    rw [Nat.add_succ]
    simp only [hasseNodePoly4,
               hasseNodePoly4_zero_after_block T P b0 zv hz_base q t (by omega),
               hasseNodePoly4_zero_after_block T P b0 zv hz_base q (t + 1) ht,
               Nat.mul_zero, Nat.add_zero]

private theorem mixedNewton4_hasse_col_identity (T P : Nat) (_hT : T ≥ 1) (hP : P ≥ 1) :
    ∀ (m t : Nat), m < 4 -> t < T ->
      let zv := if m = 0 then 1 else if m = 1 then P else if m = 2 then P * P else P * P * P
      (∀ r : Nat, m * T + t < r -> hasseNodePoly4 T P r zv t = 0) ∧
      hasseNodePoly4 T P (m * T + t) zv t =
        (if m = 0 then 1
         else if m = 1 then (P - 1) ^ T
         else if m = 2 then P ^ T * (P - 1) ^ (2 * T) * (P + 1) ^ T
         else P ^ (3 * T) * (P - 1) ^ (3 * T) * (P + 1) ^ T * (P * P + P + 1) ^ T) ∧
      (∀ x : Nat,
        zv ^ t * natSumUpTo (m * T + t + 1)
          (fun r => mixedNewtonCoeff4 T P x r * hasseNodePoly4 T P r zv t) =
        laurentInterpBinom x t * zv ^ x) := by
  intro m t hm4 htT
  dsimp only
  let zv := if m = 0 then 1 else if m = 1 then P else if m = 2 then P * P else P * P * P
  have heq_blk : ∀ (m' : Nat), m' < 4 -> ∀ s : Nat, s < T ->
      mixedNode4 T P (m' * T + s) =
        (if m' = 0 then 1 else if m' = 1 then P else if m' = 2 then P * P else P * P * P) := by
    intro m' hm' s hsT
    unfold mixedNode4
    rcases (by omega : m' = 0 ∨ m' = 1 ∨ m' = 2 ∨ m' = 3) with rfl | rfl | rfl | rfl
    · simp [hsT]
    · have h1 : ¬ (T + s < T) := by omega
      have h2 : T + s < 2 * T := by omega
      simp [h1, h2]
    · have h1 : ¬ (2 * T + s < T) := by omega
      have h2 : ¬ (2 * T + s < 2 * T) := by omega
      have h3 : 2 * T + s < 3 * T := by omega
      simp [h1, h2, h3]
    · have h1 : ¬ (3 * T + s < T) := by omega
      have h2 : ¬ (3 * T + s < 2 * T) := by omega
      have h3 : ¬ (3 * T + s < 3 * T) := by omega
      simp [h1, h2, h3]
  have hle_blk : ∀ r : Nat, r < m * T + T -> mixedNode4 T P r ≤ zv := by
    intro r hr_le
    unfold mixedNode4; dsimp [zv]
    have hp2 : P ≤ P * P := by simpa using Nat.mul_le_mul_left P hP
    have hp3 : P * P ≤ P * P * P := by simpa using Nat.mul_le_mul_left (P * P) hP
    have hp12 : 1 ≤ P * P := Nat.mul_le_mul hP hP
    have hp13 : 1 ≤ P * P * P := Nat.le_trans hp12 hp3
    rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3) with rfl | rfl | rfl | rfl
    · have h1 : r < T := by omega
      simp [h1]
    · by_cases h1 : r < T
      · simp [h1, hP]
      · have h2 : r < 2 * T := by omega
        simp [h1, h2]
    · by_cases h1 : r < T
      · simp [h1, hp12]
      · by_cases h2 : r < 2 * T
        · simp [h1, h2, hp2]
        · have h3 : r < 3 * T := by omega
          simp [h1, h2, h3]
    · by_cases h1 : r < T
      · simp [h1, hp13]
      · by_cases h2 : r < 2 * T
        · simp only [h1, h2, ite_false, ite_true]; exact Nat.le_trans hp2 hp3
        · by_cases h3 : r < 3 * T
          · simp [h1, h2, h3, hp3]
          · simp [h1, h2, h3]
  have hzero_gt_in_m : ∀ (m' t' r : Nat), m' < 4 -> t' < T -> m' * T + t' < r ->
      let zv' := if m' = 0 then 1 else if m' = 1 then P else if m' = 2 then P * P else P * P * P
      hasseNodePoly4 T P r zv' t' = 0 := by
    intro m' t' r hm' ht' hgt
    dsimp only
    let zv' := if m' = 0 then 1 else if m' = 1 then P else if m' = 2 then P * P else P * P * P
    by_cases hr_blk : r ≤ m' * T + T
    · have hrew : r = m' * T + (r - m' * T) := by omega
      rw [hrew, hasseNodePoly4_in_equal_block T P (m' * T) zv' (heq_blk m' hm') (r - m' * T) t' (by omega),
          ite_false_of_w10 (by omega : ¬ (r - m' * T ≤ t'))]
    · have hz_end : ∀ u_t : Nat, u_t < T -> hasseNodePoly4 T P (m' * T + T) zv' u_t = 0 := by
        intro u_t hut
        rw [hasseNodePoly4_in_equal_block T P (m' * T) zv' (heq_blk m' hm') T u_t (Nat.le_refl T),
            ite_false_of_w10 (by omega : ¬ (T ≤ u_t))]
      have hrew : r = m' * T + T + (r - (m' * T + T)) := by omega
      rw [hrew]
      exact hasseNodePoly4_zero_after_block T P (m' * T) zv' hz_end (r - (m' * T + T)) t' ht'
  have hmul_pow : ∀ (a b n : Nat), (a * b) ^ n = a ^ n * b ^ n := by
    intro a b n; induction n with
    | zero => simp
    | succ n' ih => rw [Nat.pow_succ, ih, Nat.pow_succ, Nat.pow_succ]; ac_rfl
  have hpp1 : P * P - 1 = (P - 1) * (P + 1) := by
    cases P with
    | zero => rfl
    | succ p' =>
      calc (p' + 1) * (p' + 1) - 1
          = (p' * p' + 2 * p' + 1) - 1 := by congr 1; rw [Nat.mul_add, Nat.add_mul]; omega
        _ = p' * p' + 2 * p' := Nat.add_sub_cancel _ 1
        _ = p' * (p' + 2) := by rw [Nat.mul_add, Nat.mul_comm p' 2]
  have hppp : P * P - P = P * (P - 1) := by
    cases P with
    | zero => omega
    | succ p' =>
      simp only [Nat.add_sub_cancel]
      rw [Nat.mul_add (p' + 1) p' 1, Nat.mul_one]
      omega
  have hp3_sub1 : P * P * P - 1 = (P - 1) * (P * P + P + 1) := by
    cases P with
    | zero => omega
    | succ p' =>
      simp only [Nat.add_sub_cancel]
      have hl : (p' + 1) * (p' + 1) * (p' + 1) =
          p' * ((p' + 1) * (p' + 1) + (p' + 1) + 1) + 1 := by
        calc
          (p' + 1) * (p' + 1) * (p' + 1)
              = (p' + 1) * (p' + 1) * p' + (p' + 1) * (p' + 1) := by rw [Nat.mul_add, Nat.mul_one]
          _ = p' * ((p' + 1) * (p' + 1)) + (p' * (p' + 1) + 1 * (p' + 1)) := by
                rw [Nat.mul_comm _ p', Nat.add_mul p' 1 (p' + 1)]
          _ = p' * ((p' + 1) * (p' + 1)) + p' * (p' + 1) + p' * 1 + 1 := by
                rw [Nat.one_mul, Nat.mul_one]; omega
          _ = p' * ((p' + 1) * (p' + 1) + (p' + 1) + 1) + 1 := by
                simp only [Nat.mul_add]
      rw [hl, Nat.add_sub_cancel]
  have hp3_subP : P * P * P - P = P * ((P - 1) * (P + 1)) := by
    rw [← hpp1, Nat.mul_sub_left_distrib, Nat.mul_one]
    ac_rfl
  have hp3_subP2 : P * P * P - P * P = (P * P) * (P - 1) := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_one]
  have hdiag : hasseNodePoly4 T P (m * T + t) zv t =
      (if m = 0 then 1
       else if m = 1 then (P - 1) ^ T
       else if m = 2 then P ^ T * (P - 1) ^ (2 * T) * (P + 1) ^ T
       else P ^ (3 * T) * (P - 1) ^ (3 * T) * (P + 1) ^ T * (P * P + P + 1) ^ T) := by
    rw [hasseNodePoly4_in_equal_block T P (m * T) zv (heq_blk m hm4) t t (Nat.le_of_lt htT),
        ite_true_of_w10 (Nat.le_refl t), Nat.sub_self]
    dsimp [zv]
    rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3) with rfl | rfl | rfl | rfl
    · simp [hasseNodePoly4]
    · simp only [Nat.one_mul, (by decide : ¬ ((1 : Nat) = 0)), ite_false, ite_true]
      exact hasseNodePoly4_zero_right_block0 T P P T (Nat.le_refl T)
    · simp only [(by decide : ¬ ((2 : Nat) = 0)), (by decide : ¬ ((2 : Nat) = 1)), ite_false, ite_true]
      have h := hasseNodePoly4_zero_right_block1 T P (P * P) T (Nat.le_refl T)
      rw [show 2 * T = T + T by omega, h, hpp1, hppp,
          hmul_pow (P - 1) (P + 1) T, hmul_pow P (P - 1) T, Nat.pow_add (P - 1) T T]
      ac_rfl
    · simp only [(by decide : ¬ ((3 : Nat) = 0)), (by decide : ¬ ((3 : Nat) = 1)),
                 (by decide : ¬ ((3 : Nat) = 2)), ite_false]
      have h := hasseNodePoly4_zero_right_block2 T P (P * P * P) T (Nat.le_refl T)
      rw [show 3 * T = 2 * T + T by omega, h, hp3_sub1, hp3_subP, hp3_subP2,
          hmul_pow (P - 1) (P * P + P + 1) T,
          hmul_pow P ((P - 1) * (P + 1)) T, hmul_pow (P - 1) (P + 1) T,
          hmul_pow (P * P) (P - 1) T, hmul_pow P P T,
          Nat.pow_add P (2 * T) T, show 2 * T = T + T by omega,
          Nat.pow_add P T T, Nat.pow_add (P - 1) (T + T) T, Nat.pow_add (P - 1) T T]
      ac_rfl
  refine ⟨fun r hr => hzero_gt_in_m m t r hm4 htT hr, hdiag, ?_⟩
  have hall_t : ∀ (x t0 : Nat), t0 < T ->
      zv ^ t0 * natSumUpTo (m * T + t0 + 1)
        (fun r => mixedNewtonCoeff4 T P x r * hasseNodePoly4 T P r zv t0) =
      laurentInterpBinom x t0 * zv ^ x := by
    intro x; induction x with
    | zero =>
      intro t0 _ht0
      have hsum0 : ∀ n : Nat,
          natSumUpTo (n + 1) (fun r => mixedNewtonCoeff4 T P 0 r * hasseNodePoly4 T P r zv t0) =
            hasseNodePoly4 T P 0 zv t0 := by
        intro n; induction n with
        | zero => simp [natSumUpTo, mixedNewtonCoeff4]
        | succ n' ihn =>
          conv => lhs; unfold natSumUpTo
          rw [ihn]; simp [mixedNewtonCoeff4]
      rw [hsum0 (m * T + t0)]
      cases t0 with
      | zero => simp [hasseNodePoly4, laurentInterpBinom]
      | succ t' => simp [hasseNodePoly4, laurentInterpBinom]
    | succ x' ihx =>
      intro t0 ht0
      have hsbp : ∀ (c : Nat) (g : Nat -> Nat),
          natSumUpTo (c + 1) (fun r => mixedNewtonCoeff4 T P (x' + 1) r * g r) =
            natSumUpTo c (fun r =>
              mixedNewtonCoeff4 T P x' r * (mixedNode4 T P r * g r + g (r + 1))) +
            mixedNewtonCoeff4 T P x' c * (mixedNode4 T P c * g c) := by
        intro c g; induction c with
        | zero =>
          simp only [natSumUpTo, mixedNewtonCoeff4, Nat.zero_add]
          ac_rfl
        | succ c' ihc =>
          conv => lhs; unfold natSumUpTo
          rw [ihc]
          simp only [mixedNewtonCoeff4, Nat.add_mul]
          conv => rhs; lhs; unfold natSumUpTo
          dsimp only
          simp only [Nat.mul_add]
          ac_rfl
      cases t0 with
      | zero =>
        simp only [Nat.add_zero, Nat.pow_zero, Nat.one_mul, laurentInterpBinom_zero_right]
        rw [hsbp (m * T) (fun r => hasseNodePoly4 T P r zv 0)]
        have hterm0 : ∀ r : Nat, r < m * T ->
            mixedNode4 T P r * hasseNodePoly4 T P r zv 0 + hasseNodePoly4 T P (r + 1) zv 0 =
              zv * hasseNodePoly4 T P r zv 0 := by
          intro r hr_lt
          have hle := hle_blk r (by omega)
          simp only [hasseNodePoly4, ← Nat.add_mul]
          rw [show mixedNode4 T P r + (zv - mixedNode4 T P r) = zv by omega]
        have htop0 : mixedNode4 T P (m * T) = zv := by
          simpa [zv] using heq_blk m hm4 0 _hT
        have hrew_sum :
            natSumUpTo (m * T) (fun r =>
              mixedNewtonCoeff4 T P x' r *
                (mixedNode4 T P r * hasseNodePoly4 T P r zv 0 + hasseNodePoly4 T P (r + 1) zv 0)) +
              mixedNewtonCoeff4 T P x' (m * T) * (mixedNode4 T P (m * T) * hasseNodePoly4 T P (m * T) zv 0) =
            zv * natSumUpTo (m * T + 1)
              (fun r => mixedNewtonCoeff4 T P x' r * hasseNodePoly4 T P r zv 0) := by
          rw [natSumUpTo_congr_w14 (m * T) _
              (fun r => zv * (mixedNewtonCoeff4 T P x' r * hasseNodePoly4 T P r zv 0))
              (fun r hr => by rw [hterm0 r hr]; ac_rfl),
              ← natSumUpTo_mul_left_w14 zv, htop0]
          conv => rhs; rhs; unfold natSumUpTo
          rw [Nat.mul_add]
          congr 1; ac_rfl
        have ih0 := ihx 0 _hT
        simp only [Nat.add_zero, Nat.pow_zero, Nat.one_mul, laurentInterpBinom_zero_right] at ih0
        rw [hrew_sum, ih0, Nat.pow_succ, Nat.mul_comm]
      | succ t' =>
        let c := m * T + (t' + 1)
        change zv ^ (t' + 1) * natSumUpTo (c + 1)
            (fun r => mixedNewtonCoeff4 T P (x' + 1) r * hasseNodePoly4 T P r zv (t' + 1)) =
          laurentInterpBinom (x' + 1) (t' + 1) * zv ^ (x' + 1)
        rw [hsbp c (fun r => hasseNodePoly4 T P r zv (t' + 1))]
        have hterm_s : ∀ r : Nat, r < c ->
            mixedNode4 T P r * hasseNodePoly4 T P r zv (t' + 1) +
              hasseNodePoly4 T P (r + 1) zv (t' + 1) =
            hasseNodePoly4 T P r zv t' + zv * hasseNodePoly4 T P r zv (t' + 1) := by
          intro r hr_lt
          have hle := hle_blk r (by dsimp [c] at hr_lt; generalize m * T = MT at hr_lt ⊢; omega)
          simp only [hasseNodePoly4]
          have hcomb : mixedNode4 T P r * hasseNodePoly4 T P r zv (t' + 1) +
              (zv - mixedNode4 T P r) * hasseNodePoly4 T P r zv (t' + 1) =
            zv * hasseNodePoly4 T P r zv (t' + 1) := by
            rw [← Nat.add_mul, show mixedNode4 T P r + (zv - mixedNode4 T P r) = zv by omega]
          calc
            mixedNode4 T P r * hasseNodePoly4 T P r zv (t' + 1) +
                (hasseNodePoly4 T P r zv t' + (zv - mixedNode4 T P r) * hasseNodePoly4 T P r zv (t' + 1))
                = hasseNodePoly4 T P r zv t' +
                    (mixedNode4 T P r * hasseNodePoly4 T P r zv (t' + 1) +
                     (zv - mixedNode4 T P r) * hasseNodePoly4 T P r zv (t' + 1)) := by ac_rfl
            _ = hasseNodePoly4 T P r zv t' + zv * hasseNodePoly4 T P r zv (t' + 1) := by rw [hcomb]
        have htop_c : mixedNode4 T P c = zv := by
          simpa [c, zv] using heq_blk m hm4 (t' + 1) ht0
        have hsplit_sum : ∀ (n : Nat) (f1 f2 : Nat -> Nat),
            natSumUpTo n (fun r => f1 r + f2 r) = natSumUpTo n f1 + natSumUpTo n f2 := by
          intro n f1 f2; induction n with
          | zero => rfl
          | succ n' ihn => simp only [natSumUpTo, ihn]; omega
        have hrew_sum :
            natSumUpTo c (fun r =>
              mixedNewtonCoeff4 T P x' r *
                (mixedNode4 T P r * hasseNodePoly4 T P r zv (t' + 1) +
                 hasseNodePoly4 T P (r + 1) zv (t' + 1))) +
              mixedNewtonCoeff4 T P x' c * (mixedNode4 T P c * hasseNodePoly4 T P c zv (t' + 1)) =
            natSumUpTo c (fun r => mixedNewtonCoeff4 T P x' r * hasseNodePoly4 T P r zv t') +
              zv * natSumUpTo (c + 1)
                (fun r => mixedNewtonCoeff4 T P x' r * hasseNodePoly4 T P r zv (t' + 1)) := by
          rw [natSumUpTo_congr_w14 c _
              (fun r => mixedNewtonCoeff4 T P x' r * hasseNodePoly4 T P r zv t' +
                zv * (mixedNewtonCoeff4 T P x' r * hasseNodePoly4 T P r zv (t' + 1)))
              (fun r hr => by rw [hterm_s r hr, Nat.mul_add]; ac_rfl),
              hsplit_sum c, ← natSumUpTo_mul_left_w14 zv, htop_c]
          conv => rhs; rhs; rhs; unfold natSumUpTo
          rw [Nat.mul_add]
          have hc_mul : mixedNewtonCoeff4 T P x' c * (zv * hasseNodePoly4 T P c zv (t' + 1)) =
              zv * (mixedNewtonCoeff4 T P x' c * hasseNodePoly4 T P c zv (t' + 1)) := by ac_rfl
          rw [hc_mul, Nat.add_assoc]
        have hc_eq : c = m * T + t' + 1 := by dsimp [c]; omega
        have ih_t' := ihx t' (by omega)
        have ih_t1 := ihx (t' + 1) ht0
        rw [hrew_sum, Nat.mul_add (zv ^ (t' + 1))]
        have hp_t : zv ^ (t' + 1) * natSumUpTo c
              (fun r => mixedNewtonCoeff4 T P x' r * hasseNodePoly4 T P r zv t') =
            zv * (laurentInterpBinom x' t' * zv ^ x') := by
          rw [Nat.pow_succ zv t', Nat.mul_comm (zv ^ t') zv, Nat.mul_assoc zv, hc_eq, ih_t']
        have hp_t1 : zv ^ (t' + 1) * (zv * natSumUpTo (c + 1)
              (fun r => mixedNewtonCoeff4 T P x' r * hasseNodePoly4 T P r zv (t' + 1))) =
            zv * (laurentInterpBinom x' (t' + 1) * zv ^ x') := by
          calc
            zv ^ (t' + 1) * (zv * natSumUpTo (c + 1)
                (fun r => mixedNewtonCoeff4 T P x' r * hasseNodePoly4 T P r zv (t' + 1)))
                = zv * (zv ^ (t' + 1) * natSumUpTo (m * T + (t' + 1) + 1)
                    (fun r => mixedNewtonCoeff4 T P x' r * hasseNodePoly4 T P r zv (t' + 1))) := by
              dsimp [c]; ac_rfl
            _ = zv * (laurentInterpBinom x' (t' + 1) * zv ^ x') := by rw [ih_t1]
        rw [hp_t, hp_t1]
        have hpas : laurentInterpBinom (x' + 1) (t' + 1) =
            laurentInterpBinom x' t' + laurentInterpBinom x' (t' + 1) := by
          simp [laurentInterpBinom]
        rw [hpas, Nat.add_mul, Nat.pow_succ zv x']
        ac_rfl
  exact fun x => hall_t x t htT

private def intDiagProdPrefix_w14 (N : Nat) (U : Fin N -> Fin N -> Int) : Nat -> Int
  | 0 => 1
  | k + 1 =>
    if h : k < N then intDiagProdPrefix_w14 N U k * U ⟨k, h⟩ ⟨k, h⟩
    else intDiagProdPrefix_w14 N U k

private theorem intDet_mul_upper_tri_w14 (N : Nat) (A U : Fin N -> Fin N -> Int)
    (hupper : ∀ r c : Fin N, c.val < r.val -> U r c = 0) :
    intDet N (fun i j => intSumPrefix N (fun r => A i r * U r j) N) =
      intDiagProdPrefix_w14 N U N * intDet N A := by
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
      intDet N (M_stage 0) = intDiagProdPrefix_w14 N U k * intDet N (M_stage k) := by
    intro k hk; induction k with
    | zero => simp [intDiagProdPrefix_w14]
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
      simp only [intDiagProdPrefix_w14, hk'_lt, dite_true]
      exact (Int.mul_assoc (intDiagProdPrefix_w14 N U k') (U jk jk) _).symm
  rw [h0_eq, hstep N (Nat.le_refl N), hN_eq]

private theorem intDet_unit_lower_tri_w14 :
    ∀ (N : Nat) (A : Fin N -> Fin N -> Int),
      (∀ i : Fin N, A i i = 1) ->
      (∀ i j : Fin N, i.val < j.val -> A i j = 0) ->
      intDet N A = 1
  | 0, _, _, _ => rfl
  | L + 1, A, hdiag, hup => by
    rw [intDet_lower_triangular (L + 1) A hup]
    dsimp only
    rw [hdiag ⟨0, Nat.zero_lt_succ L⟩, Int.one_mul]
    exact intDet_unit_lower_tri_w14 L (intSubMat A ⟨0, Nat.zero_lt_succ L⟩)
      (fun i => by
        unfold intSubMat skipFinIdx
        simp only [Nat.not_lt_zero, ite_false]
        exact hdiag ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
      (fun i j hij => by
        unfold intSubMat skipFinIdx
        simp only [Nat.not_lt_zero, ite_false]
        exact hup ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
          ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩ (by dsimp; omega))

/--
  Theorem W14.2a (`laurent_rank4_third_order_cyclotomic_confluent_divisibility`,
  `zero custom axioms`):
  Four-Block `(U = 4)` Third-Order Cyclotomic Mixed-Newton Confluent Factorization,
  Canonical `12 × 12` Divisibility, Strict Confluent-Reduced Majorant Bound, &
  Exact Unit-Grid Sharpness (`Branch P3.3`, `W14_H2`).
-/
theorem laurent_rank4_third_order_cyclotomic_confluent_divisibility :
    (∀ (W K T u : Nat) (rows : Fin (4 * T) -> Nat × Nat),
      T ≥ 1 -> u ≥ 1 ->
      let M0 : Fin (4 * T) -> Fin (4 * T) -> Int := fun i j =>
        (laurentZeroGapIntEntry W K (rows i).1 (rows i).2
          (laurentColsRank4OrderT T u j).1 (laurentColsRank4OrderT T u j).2 : Int)
      let A_newton4 : Fin (4 * T) -> Fin (4 * T) -> Int := fun i j =>
        Int.ofNat (mixedNewtonCoeff4 T (2 ^ u) ((rows i).1 * W + (rows i).2 * K) j.val)
      intDet (4 * T) M0 = Int.ofNat (confluentFactorRank4 T u) * intDet (4 * T) A_newton4 ∧
      ((confluentFactorRank4 T u : Nat) : Int) ∣ intDet (4 * T) M0) ∧
    (∀ (W K u : Nat) (rows12 : Fin 12 -> Nat × Nat), u ≥ 1 ->
      let M0_12 : Fin 12 -> Fin 12 -> Int := fun i j =>
        (laurentZeroGapIntEntry W K (rows12 i).1 (rows12 i).2
          (laurentColsRank4OrderT 3 u j).1 (laurentColsRank4OrderT 3 u j).2 : Int)
      ((2 ^ (54 * u) * (2 ^ u - 1) ^ 54 * (2 ^ u + 1) ^ 18 *
        (4 ^ u + 2 ^ u + 1) ^ 9 : Nat) : Int) ∣ intDet 12 M0_12) ∧
    (∀ (W K T u X_max : Nat) (rows : Fin (4 * T) -> Nat × Nat),
      T ≥ 1 -> u ≥ 1 -> X_max ≥ 4 * T ->
      (∀ i : Fin (4 * T), (rows i).1 * W + (rows i).2 * K ≤ X_max) ->
      let M0 : Fin (4 * T) -> Fin (4 * T) -> Int := fun i j =>
        (laurentZeroGapIntEntry W K (rows i).1 (rows i).2
          (laurentColsRank4OrderT T u j).1 (laurentColsRank4OrderT T u j).2 : Int)
      let redProd4 := confluentFactorRank4 T u *
        colBoundProdPrefix (4 * T) (fun j => mixedNewtonCoeff4 T (2 ^ u) X_max j.val) (4 * T)
      let rawProd4 := colBoundProdPrefix (4 * T)
        (fun j => laurentInterpBinom X_max (laurentColsRank4OrderT T u j).1 *
          2 ^ (X_max * (laurentColsRank4OrderT T u j).2)) (4 * T)
      (intDet (4 * T) M0).natAbs ≤ natFact (4 * T) * redProd4 ∧
      redProd4 < rawProd4) ∧
    (∀ (T u : Nat), T ≥ 1 -> u ≥ 1 ->
      let M0_unit : Fin (4 * T) -> Fin (4 * T) -> Int := fun i j =>
        (laurentZeroGapIntEntry 1 1 i.val 0
          (laurentColsRank4OrderT T u j).1 (laurentColsRank4OrderT T u j).2 : Int)
      intDet (4 * T) M0_unit = Int.ofNat (confluentFactorRank4 T u)) := by
  have hcore4 : ∀ (T u : Nat), T ≥ 1 -> u ≥ 1 ->
      let P := 2 ^ u
      let U_nat : Fin (4 * T) -> Fin (4 * T) -> Nat := fun r c =>
        let m := c.val / T
        let t := c.val % T
        let zv := if m = 0 then 1 else if m = 1 then P else if m = 2 then P * P else P * P * P
        zv ^ t * hasseNodePoly4 T P r.val zv t
      (∀ r c : Fin (4 * T), c.val < r.val -> U_nat r c = 0) ∧
      colBoundProdPrefix (4 * T) (fun c => U_nat c c) (4 * T) = confluentFactorRank4 T u ∧
      (∀ (x : Nat) (c : Fin (4 * T)),
        natSumUpTo (4 * T) (fun r =>
          if hr : r < 4 * T then mixedNewtonCoeff4 T P x r * U_nat ⟨r, hr⟩ c else 0) =
        laurentInterpBinom x (laurentColsRank4OrderT T u c).1 *
          2 ^ (x * (laurentColsRank4OrderT T u c).2)) := by
    intro T u hT hu
    dsimp only
    let P := 2 ^ u
    have hP_ge2 : P ≥ 2 := by dsimp [P]; simpa using pow2_mono_nat hu
    have hP_ge1 : P ≥ 1 := by omega
    let U_nat : Fin (4 * T) -> Fin (4 * T) -> Nat := fun r c =>
      let m := c.val / T
      let t := c.val % T
      let zv := if m = 0 then 1 else if m = 1 then P else if m = 2 then P * P else P * P * P
      zv ^ t * hasseNodePoly4 T P r.val zv t
    have hc_div : ∀ c : Fin (4 * T),
        c.val / T < 4 ∧ c.val % T < T ∧ (c.val / T) * T + c.val % T = c.val ∧
        laurentColsRank4OrderT T u c = (c.val % T, (c.val / T) * u) := by
      intro c
      have hlt4T := c.isLt
      have hmod_lt : c.val % T < T := Nat.mod_lt c.val hT
      have hdiv_eq : T * (c.val / T) + c.val % T = c.val := Nat.div_add_mod c.val T
      have hdiv_lt4 : c.val / T < 4 := by
        by_cases h : c.val / T < 4
        · exact h
        · have hm : T * 4 ≤ T * (c.val / T) := Nat.mul_le_mul_left T (by omega : 4 ≤ c.val / T)
          rw [Nat.mul_comm T 4] at hm; omega
      refine ⟨hdiv_lt4, hmod_lt, by rw [Nat.mul_comm]; exact hdiv_eq, ?_⟩
      unfold laurentColsRank4OrderT
      rcases (by generalize c.val / T = q at hdiv_lt4 ⊢; omega :
        c.val / T = 0 ∨ c.val / T = 1 ∨ c.val / T = 2 ∨ c.val / T = 3) with hd0 | hd1 | hd2 | hd3
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
        have h3 : c.val < 3 * T := by omega
        simp [h1, h2, h3]; omega
      · rw [hd3] at hdiv_eq ⊢
        have h1 : ¬ (c.val < T) := by omega
        have h2 : ¬ (c.val < 2 * T) := by omega
        have h3 : ¬ (c.val < 3 * T) := by omega
        simp [h1, h2, h3]; omega
    have hupper_nat : ∀ r c : Fin (4 * T), c.val < r.val -> U_nat r c = 0 := by
      intro r c hlt
      rcases hc_div c with ⟨hm4, htT, hceq, _⟩
      rcases mixedNewton4_hasse_col_identity T P hT hP_ge1 (c.val / T) (c.val % T) hm4 htT with
        ⟨hz_gt, _, _⟩
      dsimp [U_nat]
      rw [hz_gt r.val (by omega), Nat.mul_zero]
    have hdiag_val : ∀ c : Fin (4 * T),
        U_nat c c =
          let m := c.val / T
          let t := c.val % T
          if m = 0 then 1
          else if m = 1 then P ^ t * (P - 1) ^ T
          else if m = 2 then P ^ (2 * t + T) * (P - 1) ^ (2 * T) * (P + 1) ^ T
          else P ^ (3 * t + 3 * T) * (P - 1) ^ (3 * T) * (P + 1) ^ T * (P * P + P + 1) ^ T := by
      intro c
      rcases hc_div c with ⟨hm4, htT, hceq, _⟩
      rcases mixedNewton4_hasse_col_identity T P hT hP_ge1 (c.val / T) (c.val % T) hm4 htT with
        ⟨_, hdiag_c, _⟩
      rw [hceq] at hdiag_c
      dsimp [U_nat]; rw [hdiag_c]
      rcases (by generalize c.val / T = q at hm4 ⊢; omega :
        c.val / T = 0 ∨ c.val / T = 1 ∨ c.val / T = 2 ∨ c.val / T = 3) with hm0 | hm1 | hm2 | hm3
      · simp [hm0]
      · simp [hm1]
      · simp only [hm2, (by decide : ¬ ((2 : Nat) = 0)), (by decide : ¬ ((2 : Nat) = 1)), ite_false, ite_true]
        have hp2 : (P * P) ^ (c.val % T) = P ^ (2 * (c.val % T)) := by
          rw [← Nat.pow_two P, pow_pow_eq_mul_w5 P 2 (c.val % T)]
        rw [hp2, ← Nat.mul_assoc, ← Nat.mul_assoc, ← Nat.pow_add P (2 * (c.val % T)) T]
      · simp only [hm3, (by decide : ¬ ((3 : Nat) = 0)), (by decide : ¬ ((3 : Nat) = 1)),
                   (by decide : ¬ ((3 : Nat) = 2)), ite_false]
        have hp3_p : P * P * P = P ^ 3 := by
          simp only [show (3 : Nat) = 1 + 1 + 1 from rfl, Nat.pow_add, Nat.pow_one]
        have hp3 : (P * P * P) ^ (c.val % T) = P ^ (3 * (c.val % T)) := by
          rw [hp3_p, pow_pow_eq_mul_w5 P 3 (c.val % T)]
        rw [hp3]
        calc
          P ^ (3 * (c.val % T)) * (P ^ (3 * T) * (P - 1) ^ (3 * T) * (P + 1) ^ T * (P * P + P + 1) ^ T)
              = (P ^ (3 * (c.val % T)) * P ^ (3 * T)) * (P - 1) ^ (3 * T) * (P + 1) ^ T * (P * P + P + 1) ^ T := by ac_rfl
          _ = P ^ (3 * (c.val % T) + 3 * T) * (P - 1) ^ (3 * T) * (P + 1) ^ T * (P * P + P + 1) ^ T := by
                rw [← Nat.pow_add]
    have hprod_b0 : ∀ k : Nat, k ≤ T ->
        colBoundProdPrefix (4 * T) (fun c => U_nat c c) k = 1 := by
      intro k hk; induction k with
      | zero => rfl
      | succ k' ih =>
        have hk_lt : k' < 4 * T := by omega
        simp only [colBoundProdPrefix, hk_lt, dite_true, ih (Nat.le_of_lt hk), Nat.one_mul]
        rw [hdiag_val ⟨k', hk_lt⟩, Nat.div_eq_of_lt hk]; simp
    have hprod_b1 : ∀ k : Nat, k ≤ T ->
        colBoundProdPrefix (4 * T) (fun c => U_nat c c) (T + k) =
          P ^ (triNumNat k) * (P - 1) ^ (k * T) := by
      intro k hk; induction k with
      | zero => simp [triNumNat, hprod_b0 T (Nat.le_refl T)]
      | succ k' ih =>
        rw [Nat.add_succ]
        have hk_lt : T + k' < 4 * T := by omega
        simp only [colBoundProdPrefix, hk_lt, dite_true, ih (Nat.le_of_lt hk)]
        rw [hdiag_val ⟨T + k', hk_lt⟩]
        have hd1 : (T + k') / T = 1 := by
          have := Nat.add_mul_div_right k' 1 hT
          rw [Nat.one_mul, Nat.add_comm k' T, Nat.div_eq_of_lt hk] at this; exact this
        have hm1 : (T + k') % T = k' := by
          have := Nat.div_add_mod (T + k') T; rw [hd1, Nat.mul_one] at this; omega
        dsimp only; rw [hd1, hm1]
        simp only [(by decide : ¬ ((1 : Nat) = 0)), ite_false, ite_true, triNumNat]
        rw [Nat.pow_add P (triNumNat k') k',
            show (k' + 1) * T = k' * T + T by rw [Nat.add_mul, Nat.one_mul],
            Nat.pow_add (P - 1) (k' * T) T]
        ac_rfl
    have hprod_b2 : ∀ k : Nat, k ≤ T ->
        colBoundProdPrefix (4 * T) (fun c => U_nat c c) (2 * T + k) =
          P ^ (triNumNat T + 2 * triNumNat k + k * T) *
            (P - 1) ^ (T * T + k * (2 * T)) *
            (P + 1) ^ (k * T) := by
      intro k hk; induction k with
      | zero => simp [triNumNat, show 2 * T = T + T by omega, hprod_b1 T (Nat.le_refl T)]
      | succ k' ih =>
        rw [Nat.add_succ]
        have hk_lt : 2 * T + k' < 4 * T := by omega
        simp only [colBoundProdPrefix, hk_lt, dite_true, ih (Nat.le_of_lt hk)]
        rw [hdiag_val ⟨2 * T + k', hk_lt⟩]
        have hd2 : (2 * T + k') / T = 2 := by
          have := Nat.add_mul_div_right k' 2 hT
          rw [Nat.add_comm k' (2 * T), Nat.div_eq_of_lt hk, Nat.zero_add] at this; exact this
        have hm2 : (2 * T + k') % T = k' := by
          have := Nat.div_add_mod (2 * T + k') T; rw [hd2] at this; omega
        dsimp only; rw [hd2, hm2]
        simp only [(by decide : ¬ ((2 : Nat) = 0)), (by decide : ¬ ((2 : Nat) = 1)), ite_false, ite_true]
        let ep := triNumNat T + 2 * triNumNat k' + k' * T
        let eb := T * T + k' * (2 * T)
        have hp_e : triNumNat T + 2 * triNumNat (k' + 1) + (k' + 1) * T = ep + (2 * k' + T) := by
          dsimp [ep]; simp only [triNumNat, Nat.mul_add, Nat.add_mul, Nat.one_mul]; omega
        have hb_e : T * T + (k' + 1) * (2 * T) = eb + 2 * T := by
          dsimp [eb]; rw [Nat.add_mul k' 1 (2 * T), Nat.one_mul]; omega
        have hc_e : (k' + 1) * T = k' * T + T := by rw [Nat.add_mul, Nat.one_mul]
        change P ^ ep * (P - 1) ^ eb * (P + 1) ^ (k' * T) *
            (P ^ (2 * k' + T) * (P - 1) ^ (2 * T) * (P + 1) ^ T) = _
        rw [hp_e, hb_e, hc_e, Nat.pow_add P ep (2 * k' + T),
            Nat.pow_add (P - 1) eb (2 * T), Nat.pow_add (P + 1) (k' * T) T]
        ac_rfl
    have hprod_b3 : ∀ k : Nat, k ≤ T ->
        colBoundProdPrefix (4 * T) (fun c => U_nat c c) (3 * T + k) =
          P ^ (3 * triNumNat T + T * T + 3 * triNumNat k + k * (3 * T)) *
            (P - 1) ^ (3 * (T * T) + k * (3 * T)) *
            (P + 1) ^ (T * T + k * T) *
            (P * P + P + 1) ^ (k * T) := by
      intro k hk; induction k with
      | zero =>
        rw [Nat.add_zero, show 3 * T = 2 * T + T by omega, hprod_b2 T (Nat.le_refl T)]
        have he1 : triNumNat T + 2 * triNumNat T + T * T = 3 * triNumNat T + T * T := by omega
        have he2 : T * T + T * (2 * T) = 3 * (T * T) := by
          rw [Nat.mul_comm T (2 * T), Nat.mul_assoc 2 T T]; omega
        rw [he1, he2]
        have hz0 : triNumNat 0 = 0 := rfl
        simp only [hz0, Nat.mul_zero, Nat.zero_mul, Nat.add_zero, Nat.pow_zero, Nat.mul_one]
      | succ k' ih =>
        rw [Nat.add_succ]
        have hk_lt : 3 * T + k' < 4 * T := by omega
        simp only [colBoundProdPrefix, hk_lt, dite_true, ih (Nat.le_of_lt hk)]
        rw [hdiag_val ⟨3 * T + k', hk_lt⟩]
        have hd3 : (3 * T + k') / T = 3 := by
          have := Nat.add_mul_div_right k' 3 hT
          rw [Nat.add_comm k' (3 * T), Nat.div_eq_of_lt hk, Nat.zero_add] at this; exact this
        have hm3 : (3 * T + k') % T = k' := by
          have := Nat.div_add_mod (3 * T + k') T; rw [hd3] at this; omega
        dsimp only; rw [hd3, hm3]
        simp only [(by decide : ¬ ((3 : Nat) = 0)), (by decide : ¬ ((3 : Nat) = 1)),
                   (by decide : ¬ ((3 : Nat) = 2)), ite_false]
        let ep := 3 * triNumNat T + T * T + 3 * triNumNat k' + k' * (3 * T)
        let eb := 3 * (T * T) + k' * (3 * T)
        let ec := T * T + k' * T
        have hp_e : 3 * triNumNat T + T * T + 3 * triNumNat (k' + 1) + (k' + 1) * (3 * T) =
            ep + (3 * k' + 3 * T) := by
          dsimp [ep]; simp only [triNumNat, Nat.mul_add, Nat.add_mul, Nat.one_mul]; omega
        have hb_e : 3 * (T * T) + (k' + 1) * (3 * T) = eb + 3 * T := by
          dsimp [eb]; rw [Nat.add_mul k' 1 (3 * T), Nat.one_mul]; omega
        have hc_e : T * T + (k' + 1) * T = ec + T := by
          dsimp [ec]; rw [Nat.add_mul k' 1 T, Nat.one_mul]; omega
        have hd_e : (k' + 1) * T = k' * T + T := by rw [Nat.add_mul, Nat.one_mul]
        change P ^ ep * (P - 1) ^ eb * (P + 1) ^ ec * (P * P + P + 1) ^ (k' * T) *
            (P ^ (3 * k' + 3 * T) * (P - 1) ^ (3 * T) * (P + 1) ^ T * (P * P + P + 1) ^ T) = _
        rw [hp_e, hb_e, hc_e, hd_e,
            Nat.pow_add P ep (3 * k' + 3 * T),
            Nat.pow_add (P - 1) eb (3 * T),
            Nat.pow_add (P + 1) ec T,
            Nat.pow_add (P * P + P + 1) (k' * T) T]
        ac_rfl
    have hprod_all : colBoundProdPrefix (4 * T) (fun c => U_nat c c) (4 * T) =
        confluentFactorRank4 T u := by
      have hend := hprod_b3 T (Nat.le_refl T)
      rw [show 3 * T + T = 4 * T by omega] at hend
      rw [hend]
      unfold confluentFactorRank4
      dsimp [P]
      have htri : 3 * triNumNat T + T * T + 3 * triNumNat T + T * (3 * T) =
          3 * T * (T - 1) + 4 * (T * T) := by
        have h2t := two_mul_triNumNat_w14 T
        have h6t : 3 * triNumNat T + 3 * triNumNat T = 3 * (2 * triNumNat T) := by omega
        have hT3 : T * (3 * T) = 3 * (T * T) := by ac_rfl
        rw [hT3]
        calc
          3 * triNumNat T + T * T + 3 * triNumNat T + 3 * (T * T)
              = (3 * triNumNat T + 3 * triNumNat T) + 4 * (T * T) := by omega
          _ = 3 * (T * (T - 1)) + 4 * (T * T) := by rw [h6t, h2t]
          _ = 3 * T * (T - 1) + 4 * (T * T) := by rw [Nat.mul_assoc 3 T (T - 1)]
      have hb6 : 3 * (T * T) + T * (3 * T) = 6 * (T * T) := by
        rw [show T * (3 * T) = 3 * (T * T) by ac_rfl]; omega
      have hc2 : T * T + T * T = 2 * (T * T) := by omega
      have hp4 : 2 ^ u * 2 ^ u = 4 ^ u := by
        rw [← Nat.pow_two (2 ^ u), pow_pow_eq_mul_w5 2 u 2, Nat.mul_comm u 2,
            ← pow_pow_eq_mul_w5 2 2 u]
      rw [htri, hb6, hc2, hp4, pow_pow_eq_mul_w5 2 u, Nat.mul_comm u]
    refine ⟨hupper_nat, hprod_all, ?_⟩
    intro x c
    rcases hc_div c with ⟨hm4, htT, hceq, hcol_eq⟩
    rcases mixedNewton4_hasse_col_identity T P hT hP_ge1 (c.val / T) (c.val % T) hm4 htT with
      ⟨_, _, hsum_id⟩
    have htrunc_nat : ∀ n : Nat, c.val + 1 ≤ n -> n ≤ 4 * T ->
        natSumUpTo n (fun r =>
          if hr : r < 4 * T then mixedNewtonCoeff4 T P x r * U_nat ⟨r, hr⟩ c else 0) =
        natSumUpTo (c.val + 1) (fun r =>
          if hr : r < 4 * T then mixedNewtonCoeff4 T P x r * U_nat ⟨r, hr⟩ c else 0) := by
      intro n hge hle
      have hst : ∀ d : Nat, c.val + 1 + d ≤ 4 * T ->
          natSumUpTo (c.val + 1 + d) (fun r =>
            if hr : r < 4 * T then mixedNewtonCoeff4 T P x r * U_nat ⟨r, hr⟩ c else 0) =
          natSumUpTo (c.val + 1) (fun r =>
            if hr : r < 4 * T then mixedNewtonCoeff4 T P x r * U_nat ⟨r, hr⟩ c else 0) := by
        intro d hd; induction d with
        | zero => rfl
        | succ d' ih =>
          rw [Nat.add_succ]
          have hlt : c.val + 1 + d' < 4 * T := hd
          conv => lhs; unfold natSumUpTo
          simp only [hlt, dite_true]
          rw [ih (by omega), hupper_nat ⟨c.val + 1 + d', hlt⟩ c (by dsimp; omega),
              Nat.mul_zero, Nat.add_zero]
      simpa [show c.val + 1 + (n - (c.val + 1)) = n by omega] using hst (n - (c.val + 1)) (by omega)
    rw [htrunc_nat (4 * T) (by omega) (Nat.le_refl _)]
    let zv := if c.val / T = 0 then 1 else if c.val / T = 1 then P else if c.val / T = 2 then P * P else P * P * P
    have hcongr : natSumUpTo (c.val + 1) (fun r =>
          if hr : r < 4 * T then mixedNewtonCoeff4 T P x r * U_nat ⟨r, hr⟩ c else 0) =
        zv ^ (c.val % T) * natSumUpTo (c.val + 1)
          (fun r => mixedNewtonCoeff4 T P x r * hasseNodePoly4 T P r zv (c.val % T)) := by
      rw [natSumUpTo_mul_left_w14 (zv ^ (c.val % T))]
      apply natSumUpTo_congr_w14; intro r hr_lt
      have hr4T : r < 4 * T := by have := c.isLt; omega
      simp only [hr4T, dite_true]; dsimp [U_nat, zv]; ac_rfl
    have hsum_c := hsum_id x
    rw [hceq] at hsum_c
    rw [hcongr, hsum_c, hcol_eq]
    dsimp only [zv, P]
    rcases (by generalize c.val / T = q at hm4 ⊢; omega :
      c.val / T = 0 ∨ c.val / T = 1 ∨ c.val / T = 2 ∨ c.val / T = 3) with hd0 | hd1 | hd2 | hd3
    · simp [hd0]
    · simp only [hd1, (by decide : ¬ ((1 : Nat) = 0)), ite_false, ite_true, Nat.one_mul]
      rw [pow_pow_eq_mul_w5 2 u x, Nat.mul_comm u x]
    · simp only [hd2, (by decide : ¬ ((2 : Nat) = 0)), (by decide : ¬ ((2 : Nat) = 1)), ite_false, ite_true]
      rw [← Nat.pow_two (2 ^ u), pow_pow_eq_mul_w5 2 u 2,
          pow_pow_eq_mul_w5 2 (u * 2) x, show u * 2 * x = x * (2 * u) by ac_rfl]
    · simp only [hd3, (by decide : ¬ ((3 : Nat) = 0)), (by decide : ¬ ((3 : Nat) = 1)),
                 (by decide : ¬ ((3 : Nat) = 2)), ite_false]
      have hp3_2 : 2 ^ u * 2 ^ u * 2 ^ u = 2 ^ (u * 3) := by
        rw [show (3 : Nat) = 1 + 1 + 1 from rfl, Nat.mul_add, Nat.mul_add, Nat.mul_one,
            Nat.pow_add, Nat.pow_add]
      rw [hp3_2, pow_pow_eq_mul_w5 2 (u * 3) x, show u * 3 * x = x * (3 * u) by ac_rfl]
  have hpart1 : ∀ (W K T u : Nat) (rows : Fin (4 * T) -> Nat × Nat),
      T ≥ 1 -> u ≥ 1 ->
      let M0 : Fin (4 * T) -> Fin (4 * T) -> Int := fun i j =>
        (laurentZeroGapIntEntry W K (rows i).1 (rows i).2
          (laurentColsRank4OrderT T u j).1 (laurentColsRank4OrderT T u j).2 : Int)
      let A_newton4 : Fin (4 * T) -> Fin (4 * T) -> Int := fun i j =>
        Int.ofNat (mixedNewtonCoeff4 T (2 ^ u) ((rows i).1 * W + (rows i).2 * K) j.val)
      intDet (4 * T) M0 = Int.ofNat (confluentFactorRank4 T u) * intDet (4 * T) A_newton4 ∧
      ((confluentFactorRank4 T u : Nat) : Int) ∣ intDet (4 * T) M0 := by
    intro W K T u rows hT hu
    dsimp only
    rcases hcore4 T u hT hu with ⟨hup_n, hprod_n, hmat_n⟩
    let P := 2 ^ u
    let A_newton4 : Fin (4 * T) -> Fin (4 * T) -> Int := fun i j =>
      Int.ofNat (mixedNewtonCoeff4 T P ((rows i).1 * W + (rows i).2 * K) j.val)
    let U_int : Fin (4 * T) -> Fin (4 * T) -> Int := fun r c =>
      let m := c.val / T
      let t := c.val % T
      let zv := if m = 0 then 1 else if m = 1 then P else if m = 2 then P * P else P * P * P
      Int.ofNat (zv ^ t * hasseNodePoly4 T P r.val zv t)
    have hup_i : ∀ r c : Fin (4 * T), c.val < r.val -> U_int r c = 0 := by
      intro r c hlt
      have h0n := hup_n r c hlt; dsimp only at h0n; dsimp only [U_int, P]; rw [h0n]; rfl
    have hM0_eq : (fun i j : Fin (4 * T) =>
        (laurentZeroGapIntEntry W K (rows i).1 (rows i).2
          (laurentColsRank4OrderT T u j).1 (laurentColsRank4OrderT T u j).2 : Int)) =
        (fun i j : Fin (4 * T) => intSumPrefix (4 * T) (fun r => A_newton4 i r * U_int r j) (4 * T)) := by
      funext i j
      let x := (rows i).1 * W + (rows i).2 * K
      have hst : ∀ m : Nat, m ≤ 4 * T ->
          intSumPrefix (4 * T) (fun r => A_newton4 i r * U_int r j) m =
            Int.ofNat (natSumUpTo m (fun r =>
              if hr : r < 4 * T then
                mixedNewtonCoeff4 T P x r *
                  ((if j.val / T = 0 then 1 else if j.val / T = 1 then P else if j.val / T = 2 then P * P else P * P * P) ^ (j.val % T) *
                   hasseNodePoly4 T P r (if j.val / T = 0 then 1 else if j.val / T = 1 then P else if j.val / T = 2 then P * P else P * P * P) (j.val % T))
              else 0)) := by
        intro m hm; induction m with
        | zero => rfl
        | succ m' ih =>
          have hm_lt : m' < 4 * T := hm
          conv => lhs; unfold intSumPrefix
          conv => rhs; rhs; unfold natSumUpTo
          simp only [hm_lt, dite_true]; rw [ih (Nat.le_of_lt hm)]; rfl
      rw [hst (4 * T) (Nat.le_refl _), hmat_n x j]; rfl
    have hdiag_i : ∀ m : Nat, m ≤ 4 * T ->
        intDiagProdPrefix_w14 (4 * T) U_int m =
          Int.ofNat (colBoundProdPrefix (4 * T) (fun c =>
            let mb := c.val / T
            let t := c.val % T
            let zv := if mb = 0 then 1 else if mb = 1 then P else if mb = 2 then P * P else P * P * P
            zv ^ t * hasseNodePoly4 T P c.val zv t) m) := by
      intro m hm; induction m with
      | zero => rfl
      | succ m' ih =>
        have hm_lt : m' < 4 * T := hm
        conv => lhs; unfold intDiagProdPrefix_w14
        conv => rhs; rhs; unfold colBoundProdPrefix
        simp only [hm_lt, dite_true]; rw [ih (Nat.le_of_lt hm)]; rfl
    rw [hM0_eq, intDet_mul_upper_tri_w14 (4 * T) A_newton4 U_int hup_i,
        hdiag_i (4 * T) (Nat.le_refl _), hprod_n]
    exact ⟨rfl, ⟨intDet (4 * T) A_newton4, rfl⟩⟩
  refine ⟨hpart1, ?_, ?_, ?_⟩
  · intro W K u rows12 hu
    dsimp only
    have h12 := (hpart1 W K 3 u rows12 (by decide) hu).2
    have hexp12 : confluentFactorRank4 3 u =
        2 ^ (54 * u) * (2 ^ u - 1) ^ 54 * (2 ^ u + 1) ^ 18 * (4 ^ u + 2 ^ u + 1) ^ 9 := by
      unfold confluentFactorRank4; rfl
    simpa [hexp12] using h12
  · intro W K T u X_max rows hT hu hX hrows_le
    dsimp only
    rcases hcore4 T u hT hu with ⟨_, hprod_n, hmat_n⟩
    let P := 2 ^ u
    have hP_ge2 : P ≥ 2 := by dsimp [P]; simpa using pow2_mono_nat hu
    have hP_ge1 : P ≥ 1 := by omega
    have hdet_eq := (hpart1 W K T u rows hT hu).1
    let A_newton4 : Fin (4 * T) -> Fin (4 * T) -> Int := fun i j =>
      Int.ofNat (mixedNewtonCoeff4 T P ((rows i).1 * W + (rows i).2 * K) j.val)
    have hA_maj : (intDet (4 * T) A_newton4).natAbs ≤
        natFact (4 * T) *
          colBoundProdPrefix (4 * T) (fun j => mixedNewtonCoeff4 T P X_max j.val) (4 * T) :=
      intDet_natAbs_le_fact_mul_colProd (4 * T) A_newton4
        (fun j => mixedNewtonCoeff4 T P X_max j.val)
        (fun i j => mixedNewtonCoeff4_le_of_le T P hT hP_ge1 _ X_max j.val (hrows_le i))
    have hbd_red :
        (intDet (4 * T) (fun i j =>
          (laurentZeroGapIntEntry W K (rows i).1 (rows i).2
            (laurentColsRank4OrderT T u j).1 (laurentColsRank4OrderT T u j).2 : Int))).natAbs ≤
        natFact (4 * T) * (confluentFactorRank4 T u *
          colBoundProdPrefix (4 * T) (fun j => mixedNewtonCoeff4 T P X_max j.val) (4 * T)) := by
      rw [hdet_eq, Int.natAbs_mul]
      simp only [Int.ofNat_eq_natCast, Int.natAbs_natCast]
      have hm := Nat.mul_le_mul_left (confluentFactorRank4 T u) hA_maj
      rwa [show confluentFactorRank4 T u *
              (natFact (4 * T) * colBoundProdPrefix (4 * T) (fun j => mixedNewtonCoeff4 T P X_max j.val) (4 * T)) =
            natFact (4 * T) * (confluentFactorRank4 T u *
              colBoundProdPrefix (4 * T) (fun j => mixedNewtonCoeff4 T P X_max j.val) (4 * T)) by ac_rfl] at hm
    refine ⟨hbd_red, ?_⟩
    let U_nat : Fin (4 * T) -> Fin (4 * T) -> Nat := fun r c =>
      let m := c.val / T
      let t := c.val % T
      let zv := if m = 0 then 1 else if m = 1 then P else if m = 2 then P * P else P * P * P
      zv ^ t * hasseNodePoly4 T P r.val zv t
    let f_red : Fin (4 * T) -> Nat := fun c => U_nat c c * mixedNewtonCoeff4 T P X_max c.val
    let f_raw : Fin (4 * T) -> Nat := fun c =>
      laurentInterpBinom X_max (laurentColsRank4OrderT T u c).1 *
        2 ^ (X_max * (laurentColsRank4OrderT T u c).2)
    have hprod_mul : ∀ m : Nat, m ≤ 4 * T ->
        colBoundProdPrefix (4 * T) (fun c => U_nat c c) m *
          colBoundProdPrefix (4 * T) (fun c => mixedNewtonCoeff4 T P X_max c.val) m =
        colBoundProdPrefix (4 * T) f_red m := by
      intro m hm; induction m with
      | zero => rfl
      | succ m' ih =>
        have hm_lt : m' < 4 * T := hm
        simp only [colBoundProdPrefix, hm_lt, dite_true, ← ih (Nat.le_of_lt hm)]
        dsimp [f_red]; ac_rfl
    rw [← hprod_n, hprod_mul (4 * T) (Nat.le_refl _)]
    have hcf_pos : confluentFactorRank4 T u ≥ 1 := by
      unfold confluentFactorRank4
      have h1 := nat_pow_pos_of_pos 2 (by decide) ((3 * T * (T - 1) + 4 * (T * T)) * u)
      have h2 := nat_pow_pos_of_pos (2 ^ u - 1) (by omega) (6 * (T * T))
      have h3 := nat_pow_pos_of_pos (2 ^ u + 1) (Nat.succ_pos _) (2 * (T * T))
      have h4 := nat_pow_pos_of_pos (4 ^ u + 2 ^ u + 1) (Nat.succ_pos _) (T * T)
      exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3) h4
    have hUcc_pos : ∀ c : Fin (4 * T), U_nat c c ≥ 1 := by
      intro c
      by_cases hz : U_nat c c = 0
      · exfalso
        have hp0 : ∀ m : Nat, c.val < m -> m ≤ 4 * T ->
            colBoundProdPrefix (4 * T) (fun j => U_nat j j) m = 0 := by
          intro m hgt hle
          have hst : ∀ d : Nat, c.val + 1 + d ≤ 4 * T ->
              colBoundProdPrefix (4 * T) (fun j => U_nat j j) (c.val + 1 + d) = 0 := by
            intro d hd; induction d with
            | zero => simp only [colBoundProdPrefix, c.isLt, dite_true, hz, Nat.mul_zero]
            | succ d' ih =>
              rw [Nat.add_succ]
              have hlt : c.val + 1 + d' < 4 * T := hd
              simp only [colBoundProdPrefix, hlt, dite_true, ih (by omega), Nat.zero_mul]
          simpa [show c.val + 1 + (m - (c.val + 1)) = m by omega] using hst (m - (c.val + 1)) (by omega)
        have hbad := hp0 (4 * T) c.isLt (Nat.le_refl _)
        rw [hprod_n] at hbad; omega
      · omega
    have hfred_pos : ∀ c : Fin (4 * T), f_red c ≥ 1 := fun c =>
      Nat.mul_le_mul (hUcc_pos c)
        (mixedNewtonCoeff4_pos_of_le T P hT c.val X_max (by have := c.isLt; omega))
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
        · rw [heq] at hpos ⊢; have hg0 := hsum_ge_one m_n 0 g hpos; omega
        · have := ih (by omega); omega
    have hfred_le : ∀ c : Fin (4 * T), f_red c ≤ f_raw c := by
      intro c; dsimp [f_raw]; rw [← hmat_n X_max c]
      have h1 := hsum_ge_one (4 * T) c.val
        (fun r => if hr : r < 4 * T then mixedNewtonCoeff4 T P X_max r * U_nat ⟨r, hr⟩ c else 0)
        c.isLt
      simp only [c.isLt, dite_true] at h1; dsimp [f_red]; rwa [Nat.mul_comm]
    let cT : Fin (4 * T) := ⟨T, by omega⟩
    have hfred_lt_cT : f_red cT < f_raw cT := by
      dsimp [f_raw]; rw [← hmat_n X_max cT]
      have h2 := hsum_ge_two (4 * T) T
        (fun r => if hr : r < 4 * T then mixedNewtonCoeff4 T P X_max r * U_nat ⟨r, hr⟩ cT else 0)
        hT (by omega)
      have h0_4T : 0 < 4 * T := by omega
      have hT_4T : T < 4 * T := by omega
      simp only [h0_4T, hT_4T, dite_true] at h2
      have h0_val : mixedNewtonCoeff4 T P X_max 0 * U_nat ⟨0, h0_4T⟩ cT = 1 := by
        rw [mixedNewtonCoeff4_zero_right T P hT X_max, Nat.one_mul]
        dsimp [U_nat, cT]; rw [Nat.mod_self T, Nat.pow_zero, Nat.one_mul]; rfl
      rw [h0_val, Nat.mul_comm (mixedNewtonCoeff4 T P X_max T)] at h2
      have hf_eq : U_nat ⟨T, hT_4T⟩ cT * mixedNewtonCoeff4 T P X_max T = f_red cT := rfl
      rw [hf_eq] at h2
      exact Nat.lt_of_lt_of_le (by omega : f_red cT < 1 + f_red cT) h2
    have hprod_le : ∀ m : Nat, m ≤ 4 * T ->
        colBoundProdPrefix (4 * T) f_red m ≤ colBoundProdPrefix (4 * T) f_raw m := by
      intro m hm; induction m with
      | zero => exact Nat.le_refl 1
      | succ m' ih =>
        have hm_lt : m' < 4 * T := hm
        simp only [colBoundProdPrefix, hm_lt, dite_true]
        exact Nat.mul_le_mul (ih (Nat.le_of_lt hm)) (hfred_le ⟨m', hm_lt⟩)
    have hprod_pos : ∀ m : Nat, m ≤ 4 * T -> colBoundProdPrefix (4 * T) f_red m ≥ 1 := by
      intro m hm; induction m with
      | zero => exact Nat.le_refl 1
      | succ m' ih =>
        have hm_lt : m' < 4 * T := hm
        simp only [colBoundProdPrefix, hm_lt, dite_true]
        exact Nat.mul_le_mul (ih (Nat.le_of_lt hm)) (hfred_pos ⟨m', hm_lt⟩)
    have hprod_lt : ∀ d : Nat, T + 1 + d ≤ 4 * T ->
        colBoundProdPrefix (4 * T) f_red (T + 1 + d) <
          colBoundProdPrefix (4 * T) f_raw (T + 1 + d) := by
      intro d hd; induction d with
      | zero =>
        simp only [colBoundProdPrefix, (by omega : T < 4 * T), dite_true]
        exact Nat.lt_of_lt_of_le
          (Nat.mul_lt_mul_of_pos_left hfred_lt_cT (hprod_pos T (by omega)))
          (Nat.mul_le_mul_right (f_raw cT) (hprod_le T (by omega)))
      | succ d' ih =>
        rw [Nat.add_succ]
        have hlt : T + 1 + d' < 4 * T := hd
        simp only [colBoundProdPrefix, hlt, dite_true]
        exact Nat.lt_of_lt_of_le
          (Nat.mul_lt_mul_of_pos_right (ih (by omega)) (hfred_pos ⟨T + 1 + d', hlt⟩))
          (Nat.mul_le_mul_left _ (hfred_le ⟨T + 1 + d', hlt⟩))
    simpa [show T + 1 + (4 * T - (T + 1)) = 4 * T by omega] using hprod_lt (4 * T - (T + 1)) (by omega)
  · intro T u hT hu
    dsimp only
    have hfac := (hpart1 1 1 T u (fun i => (i.val, 0)) hT hu).1
    dsimp only at hfac
    have hunit_det : intDet (4 * T) (fun i j : Fin (4 * T) =>
        Int.ofNat (mixedNewtonCoeff4 T (2 ^ u) (i.val * 1 + 0 * 1) j.val)) = 1 := by
      apply intDet_unit_lower_tri_w14
      · intro i
        simp only [Nat.mul_one, Nat.add_zero]
        rw [mixedNewtonCoeff4_diag_one T (2 ^ u) hT i.val]; rfl
      · intro i j hij
        simp only [Nat.mul_one, Nat.add_zero]
        rw [mixedNewtonCoeff4_above_zero T (2 ^ u) i.val j.val hij]; rfl
    rw [hfac, hunit_det, Int.mul_one]

-- ----------------------------------------------------------------------------
-- Section 2B: Joint Row+Column Confluent LCM / Coprime Divisibility, Strictly
--             Sharper Reduced Quotient Majorant, & `(4, 7, 1)` Overlap Contrast
-- ----------------------------------------------------------------------------

private theorem int_nat_lcm_dvd_w14 (a b : Nat) (z : Int)
    (ha : ((a : Nat) : Int) ∣ z) (hb : ((b : Nat) : Int) ∣ z) :
    ((Nat.lcm a b : Nat) : Int) ∣ z := by
  have hdvd_abs : ∀ d : Nat, ((d : Nat) : Int) ∣ z -> d ∣ z.natAbs := by
    intro d ⟨q, hq⟩
    refine ⟨q.natAbs, ?_⟩
    rw [hq, Int.natAbs_mul, Int.natAbs_natCast]
  rcases Nat.lcm_dvd (hdvd_abs a ha) (hdvd_abs b hb) with ⟨k, hk⟩
  cases z with
  | ofNat n =>
    simp only [Int.natAbs] at hk
    exact ⟨(k : Int), by simp [Int.natCast_mul, hk]⟩
  | negSucc n =>
    change n + 1 = Nat.lcm a b * k at hk
    refine ⟨-(k : Int), ?_⟩
    rw [Int.mul_neg, ← Int.natCast_mul, ← hk]
    omega

private theorem coprime_10368_mersenne_odd (W : Nat) (hW3 : W ≥ 3) (hodd : W % 2 = 1) :
    Nat.Coprime 10368 ((2 ^ W - 1) ^ 3) := by
  have hp2_ge8 : 2 ^ W ≥ 8 := by
    simpa using nat_pow_mono_exp_pos 2 3 W (by decide) hW3
  have hm_odd : (2 ^ W - 1) % 2 = 1 := by
    have hev : 2 ^ W = 2 * 2 ^ (W - 1) := by
      conv => lhs; rw [show W = (W - 1) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
    omega
  have hpow2_odd_mod3 : ∀ q : Nat, 2 ^ (2 * q + 1) % 3 = 2 := by
    intro q; induction q with
    | zero => decide
    | succ q' ih =>
      rw [show 2 * (q' + 1) + 1 = (2 * q' + 1) + 2 by omega, Nat.pow_add, Nat.mul_mod, ih]
  have hm_mod3 : (2 ^ W - 1) % 3 = 1 := by
    have hw_eq : W = 2 * (W / 2) + 1 := by omega
    have h2m : 2 ^ W % 3 = 2 := by rw [hw_eq]; exact hpow2_odd_mod3 (W / 2)
    omega
  have hcop2 : Nat.Coprime 2 (2 ^ W - 1) := by
    unfold Nat.Coprime
    let g := Nat.gcd 2 (2 ^ W - 1)
    have hg2 : g ∣ 2 := Nat.gcd_dvd_left 2 (2 ^ W - 1)
    have hgm : g ∣ (2 ^ W - 1) := Nat.gcd_dvd_right 2 (2 ^ W - 1)
    have hgle : g ≤ 2 := Nat.le_of_dvd (by decide) hg2
    have hgpos : g ≥ 1 := Nat.gcd_pos_of_pos_left _ (by decide)
    rcases (by omega : g = 1 ∨ g = 2) with hg1 | hg_eq2
    · exact hg1
    · exfalso; rw [hg_eq2] at hgm; rcases hgm with ⟨c, hc⟩; omega
  have hcop3 : Nat.Coprime 3 (2 ^ W - 1) := by
    unfold Nat.Coprime
    let g := Nat.gcd 3 (2 ^ W - 1)
    have hg3 : g ∣ 3 := Nat.gcd_dvd_left 3 (2 ^ W - 1)
    have hgm : g ∣ (2 ^ W - 1) := Nat.gcd_dvd_right 3 (2 ^ W - 1)
    have hgle : g ≤ 3 := Nat.le_of_dvd (by decide) hg3
    have hgpos : g ≥ 1 := Nat.gcd_pos_of_pos_left _ (by decide)
    rcases (by omega : g = 1 ∨ g = 2 ∨ g = 3) with hg1 | hg_eq2 | hg_eq3
    · exact hg1
    · exfalso; rw [hg_eq2] at hg3; rcases hg3 with ⟨c, hc⟩; omega
    · exfalso; rw [hg_eq3] at hgm; rcases hgm with ⟨c, hc⟩; omega
  have h10368 : 2 ^ 7 * 3 ^ 4 = 10368 := by decide
  rw [← h10368]
  exact ((hcop2.pow_left 7).mul_left (hcop3.pow_left 4)).pow_right 3

/--
  Theorem W14.2b (`laurent_rect_6x6_joint_row_col_lcm_and_reduced_bound`,
  `zero custom axioms`):
  Joint Row+Column Confluent LCM / Coprime Divisibility on Rectangular `6 × 6` `(T = 2, U = 3)`,
  Strictly Sharper Odd-`W` Reduced Quotient Majorant Bound, `8 × 8` `(T = 2, U = 4)` Specialization,
  & Even-`W` `(4, 7, 1)` Cyclotomic `3^3 = 27` Overlap Certificate (`Branch P3.3`, `W14_H2`).
-/
theorem laurent_rect_6x6_joint_row_col_lcm_and_reduced_bound :
    (∀ (W K u : Nat), W ≥ 1 -> u ≥ 1 ->
      let M0_r3s2 : Fin 6 -> Fin 6 -> Int := fun i j =>
        (laurentZeroGapIntEntry W K (laurentRowsRectR3S2_6 i).1 (laurentRowsRectR3S2_6 i).2
          (laurentColsC23_6 u j).1 (laurentColsC23_6 u j).2 : Int)
      ((Nat.lcm (confluentFactorRank3 2 u)
        (2 ^ ((2 * W + K) * u) * (2 ^ (W * u) - 1) ^ 3) : Nat) : Int) ∣ intDet 6 M0_r3s2) ∧
    (∀ (W K X_max : Nat),
      W ≥ 3 -> W % 2 = 1 -> X_max ≥ 6 -> 2 * W + K ≤ X_max ->
      let M0_r3s2 : Fin 6 -> Fin 6 -> Int := fun i j =>
        (laurentZeroGapIntEntry W K (laurentRowsRectR3S2_6 i).1 (laurentRowsRectR3S2_6 i).2
          (laurentColsC23_6 1 j).1 (laurentColsC23_6 1 j).2 : Int)
      let colNewtonBound :=
        colBoundProdPrefix 6 (fun j => mixedNewtonCoeff 2 2 X_max j.val) 6
      Nat.Coprime 10368 ((2 ^ W - 1) ^ 3) ∧
      ((10368 * (2 ^ W - 1) ^ 3 : Nat) : Int) ∣ intDet 6 M0_r3s2 ∧
      (∃ Q_joint : Int,
        intDet 6 M0_r3s2 = ((10368 * (2 ^ W - 1) ^ 3 : Nat) : Int) * Q_joint ∧
        Q_joint.natAbs * (2 ^ W - 1) ^ 3 ≤ natFact 6 * colNewtonBound ∧
        Q_joint.natAbs < natFact 6 * colNewtonBound)) ∧
    (∀ (W K u : Nat) (rows8 : Fin 8 -> Nat × Nat), u ≥ 1 ->
      let M0_8 : Fin 8 -> Fin 8 -> Int := fun i j =>
        (laurentZeroGapIntEntry W K (rows8 i).1 (rows8 i).2
          (laurentColsRank4OrderT 2 u j).1 (laurentColsRank4OrderT 2 u j).2 : Int)
      ((2 ^ (22 * u) * (2 ^ u - 1) ^ 24 * (2 ^ u + 1) ^ 8 *
        (4 ^ u + 2 ^ u + 1) ^ 4 : Nat) : Int) ∣ intDet 8 M0_8) ∧
    (let M0_47 : Fin 6 -> Fin 6 -> Int := fun i j =>
       (laurentZeroGapIntEntry 4 7 (laurentRowsRectR3S2_6 i).1 (laurentRowsRectR3S2_6 i).2
         (laurentColsC23_6 1 j).1 (laurentColsC23_6 1 j).2 : Int)
     intDet 6 M0_47 = 571581437275275264000 ∧
     Nat.lcm 10368 (2 ^ 15 * 15 ^ 3) = 331776000 ∧
     ((331776000 : Nat) : Int) ∣ intDet 6 M0_47 ∧
     ¬ (((10368 * 15 ^ 2 : Nat) : Int) ∣ intDet 6 M0_47)) := by
  have hc6_eq : ∀ u : Nat, laurentColsC23_6 u = laurentColsRank3OrderT 2 u := by
    intro u; funext j
    rcases (by have := j.isLt; omega :
      j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 ∨ j.val = 4 ∨ j.val = 5) with
      h | h | h | h | h | h <;>
    · simp [laurentColsC23_6, laurentColsRank3OrderT, h]
  have hpart1 : ∀ (W K u : Nat), W ≥ 1 -> u ≥ 1 ->
      let M0_r3s2 : Fin 6 -> Fin 6 -> Int := fun i j =>
        (laurentZeroGapIntEntry W K (laurentRowsRectR3S2_6 i).1 (laurentRowsRectR3S2_6 i).2
          (laurentColsC23_6 u j).1 (laurentColsC23_6 u j).2 : Int)
      ((Nat.lcm (confluentFactorRank3 2 u)
        (2 ^ ((2 * W + K) * u) * (2 ^ (W * u) - 1) ^ 3) : Nat) : Int) ∣ intDet 6 M0_r3s2 := by
    intro W K u hW hu
    dsimp only
    have hcol := (laurent_rank3_second_order_confluent_and_reduced_bound.1
      W K 2 u laurentRowsRectR3S2_6 (by decide) hu).2
    rw [← hc6_eq u] at hcol
    have hrow := (laurent_rect_6x6_t2u3_row_vandermonde_divisibility.1 W K u hW hu).1
    exact int_nat_lcm_dvd_w14 _ _ _ hcol hrow
  refine ⟨hpart1, ?_, ?_, ⟨by decide, by decide, by decide, by decide⟩⟩
  · intro W K X_max hW3 hodd hX6 hWK_le
    dsimp only
    have hcop := coprime_10368_mersenne_odd W hW3 hodd
    have hlcm_dvd := hpart1 W K 1 (by omega) (by decide)
    dsimp only at hlcm_dvd
    have hcf1 : confluentFactorRank3 2 1 = 10368 := by decide
    rw [hcf1] at hlcm_dvd
    have hprod_lcm : (10368 * (2 ^ W - 1) ^ 3) ∣
        Nat.lcm 10368 (2 ^ ((2 * W + K) * 1) * (2 ^ (W * 1) - 1) ^ 3) := by
      have hd1 : 10368 ∣ Nat.lcm 10368 (2 ^ ((2 * W + K) * 1) * (2 ^ (W * 1) - 1) ^ 3) :=
        Nat.dvd_lcm_left _ _
      have hd2 : (2 ^ W - 1) ^ 3 ∣
          Nat.lcm 10368 (2 ^ ((2 * W + K) * 1) * (2 ^ (W * 1) - 1) ^ 3) := by
        rw [Nat.mul_one W]
        exact Nat.dvd_trans ⟨2 ^ ((2 * W + K) * 1), Nat.mul_comm _ _⟩ (Nat.dvd_lcm_right _ _)
      rcases hd1 with ⟨q1, hq1⟩
      rw [hq1] at hd2
      rcases hcop.symm.dvd_of_dvd_mul_left hd2 with ⟨k2, hk2⟩
      exact ⟨k2, by rw [hq1, hk2, ← Nat.mul_assoc]⟩
    have hprod_dvd : ((10368 * (2 ^ W - 1) ^ 3 : Nat) : Int) ∣
        intDet 6 (fun i j =>
          (laurentZeroGapIntEntry W K (laurentRowsRectR3S2_6 i).1 (laurentRowsRectR3S2_6 i).2
            (laurentColsC23_6 1 j).1 (laurentColsC23_6 1 j).2 : Int)) := by
      rcases hprod_lcm with ⟨c_l, hcl⟩
      rcases hlcm_dvd with ⟨q_l, hql⟩
      refine ⟨(c_l : Int) * q_l, ?_⟩
      rw [hql, hcl, Int.natCast_mul, Int.mul_assoc]
    rcases hprod_dvd with ⟨Q_joint, hQ_eq⟩
    have hrows_le : ∀ i : Fin 6,
        (laurentRowsRectR3S2_6 i).1 * W + (laurentRowsRectR3S2_6 i).2 * K ≤ X_max := by
      intro i
      rcases (by have := i.isLt; omega :
        i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5) with
        h | h | h | h | h | h <;>
      · simp only [laurentRowsRectR3S2_6, laurentRowsTwoBase6, h]; omega
    have hred_bd := (laurent_rank3_second_order_confluent_and_reduced_bound.2.2
      W K 2 1 X_max laurentRowsRectR3S2_6 (by decide) (by decide) hX6 hrows_le).1
    rw [← hc6_eq 1, hcf1, hQ_eq, Int.natAbs_mul, Int.natAbs_natCast] at hred_bd
    let colNB := colBoundProdPrefix 6 (fun j => mixedNewtonCoeff 2 2 X_max j.val) 6
    change 10368 * (2 ^ W - 1) ^ 3 * Q_joint.natAbs ≤ natFact 6 * (10368 * colNB) at hred_bd
    have hmul_10368 : 10368 * (Q_joint.natAbs * (2 ^ W - 1) ^ 3) ≤
        10368 * (natFact 6 * colNB) := by
      have hl : 10368 * (2 ^ W - 1) ^ 3 * Q_joint.natAbs =
          10368 * (Q_joint.natAbs * (2 ^ W - 1) ^ 3) := by ac_rfl
      have hr : natFact 6 * (10368 * colNB) = 10368 * (natFact 6 * colNB) := by ac_rfl
      omega
    have hQ_le : Q_joint.natAbs * (2 ^ W - 1) ^ 3 ≤ natFact 6 * colNB := by omega
    have hcolNB_pos : colNB ≥ 1 := by
      dsimp [colNB]
      have hst : ∀ m : Nat, m ≤ 6 ->
          colBoundProdPrefix 6 (fun j => mixedNewtonCoeff 2 2 X_max j.val) m ≥ 1 := by
        intro m hm; induction m with
        | zero => exact Nat.le_refl 1
        | succ m' ih =>
          have hm_lt : m' < 6 := hm
          simp only [colBoundProdPrefix, hm_lt, dite_true]
          have hc_pos : mixedNewtonCoeff 2 2 X_max m' ≥ 1 := by
            have hp : ∀ (r x : Nat), r ≤ x -> mixedNewtonCoeff 2 2 x r ≥ 1 := by
              intro r; induction r with
              | zero =>
                intro x _; induction x with
                | zero => exact Nat.le_refl 1
                | succ x' ihx =>
                  simp only [mixedNewtonCoeff, mixedNode, (by decide : 0 < 2), ite_true, Nat.one_mul]
                  exact ihx (Nat.zero_le x')
              | succ r' ihr =>
                intro x hx; cases x with
                | zero => omega
                | succ x' =>
                  simp only [mixedNewtonCoeff]
                  have := ihr x' (by omega); omega
            exact hp m' X_max (by omega)
          exact Nat.mul_le_mul (ih (Nat.le_of_lt hm)) hc_pos
      exact hst 6 (Nat.le_refl 6)
    have hnf6_pos : natFact 6 * colNB ≥ 1 :=
      Nat.mul_le_mul (by decide : natFact 6 ≥ 1) hcolNB_pos
    have hm3_ge8 : (2 ^ W - 1) ^ 3 ≥ 343 := by
      have hp8 : 2 ^ W ≥ 8 := by simpa using nat_pow_mono_exp_pos 2 3 W (by decide) hW3
      have hm7 : 2 ^ W - 1 ≥ 7 := by omega
      calc (2 ^ W - 1) ^ 3
          = (2 ^ W - 1) * (2 ^ W - 1) * (2 ^ W - 1) := by
              rw [show (3 : Nat) = 1 + 1 + 1 from rfl, Nat.pow_add, Nat.pow_add, Nat.pow_one]
        _ ≥ 7 * 7 * 7 := Nat.mul_le_mul (Nat.mul_le_mul hm7 hm7) hm7
        _ = 343 := rfl
    have hQ_lt : Q_joint.natAbs < natFact 6 * colNB := by
      by_cases hqz : Q_joint.natAbs = 0
      · omega
      · have hgt1 : Q_joint.natAbs * 1 < Q_joint.natAbs * (2 ^ W - 1) ^ 3 :=
          Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
        omega
    exact ⟨hcop, ⟨Q_joint, hQ_eq⟩, ⟨Q_joint, hQ_eq, hQ_le, hQ_lt⟩⟩
  · intro W K u rows8 hu
    dsimp only
    have h8 := (laurent_rank4_third_order_cyclotomic_confluent_divisibility.1
      W K 2 u rows8 (by decide) hu).2
    have hexp8 : confluentFactorRank4 2 u =
        2 ^ (22 * u) * (2 ^ u - 1) ^ 24 * (2 ^ u + 1) ^ 8 * (4 ^ u + 2 ^ u + 1) ^ 4 := by
      unfold confluentFactorRank4; rfl
    simpa [hexp8] using h8

-- ----------------------------------------------------------------------------
-- Section 2C: Rank-3 `9 × 9` `(T = 3, U = 3)` Exact All-`u` Closed Form,
--             All-`u` Collatz-Cone Positivity, & `u ∈ {1, 2, 3, 4}` Non-Vanishing
-- ----------------------------------------------------------------------------

def t3u3GenA9Expr (i j : Fin 9) : Expr4 :=
  let rs := laurentRowsTwoBase9 i
  let r := rs.1
  let s := rs.2
  let n : Expr4 := .add (.mul (.const (r : Int)) .v0) (.mul (.const (s : Int)) .v1)
  let b2 : Expr4 := .mul n (.sub n (.const 1))
  let pq1 : Expr4 := .mul (expr4Pow .v2 r) (expr4Pow .v3 s)
  let pq2 : Expr4 := .mul pq1 pq1
  if j.val = 0 then .const 1
  else if j.val = 1 then n
  else if j.val = 2 then b2
  else if j.val = 3 then pq1
  else if j.val = 4 then .mul pq1 n
  else if j.val = 5 then .mul pq1 b2
  else if j.val = 6 then pq2
  else if j.val = 7 then .mul pq2 n
  else .mul pq2 b2

def t3u3GenB8Expr (i j : Fin 8) : Expr4 :=
  let r9 : Fin 9 := ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
  let c9 : Fin 9 := ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
  if j.val = 2 || j.val = 5 then
    .sub (t3u3GenA9Expr r9 c9) (.const 1)
  else
    t3u3GenA9Expr r9 c9

def t3u3GenC8Expr (i j : Fin 8) : Expr4 :=
  let c0 := t3u3GenB8Expr i ⟨0, by decide⟩
  let c1 := t3u3GenB8Expr i ⟨1, by decide⟩
  let c2 := t3u3GenB8Expr i ⟨2, by decide⟩
  let P := Expr4.v2
  let P2 := Expr4.mul P P
  match j.val with
  | 0 => c0
  | 1 => c1
  | 2 => c2
  | 3 => .sub (t3u3GenB8Expr i ⟨3, by decide⟩) (.mul P c0)
  | 4 => .sub (t3u3GenB8Expr i ⟨4, by decide⟩) (.mul P c1)
  | 5 => .sub (t3u3GenB8Expr i ⟨5, by decide⟩) (.mul (.add P (.const 1)) c2)
  | 6 => .sub (t3u3GenB8Expr i ⟨6, by decide⟩) (.mul P2 c0)
  | _ => .sub (t3u3GenB8Expr i ⟨7, by decide⟩) (.mul P2 c1)

def t3u3GenC7Expr (i j : Fin 7) : Expr4 :=
  let W := Expr4.v0
  let P := Expr4.v2
  let P2 := Expr4.mul P P
  let Pm1 := Expr4.sub P (.const 1)
  let Wb2 := Expr4.mul W (.sub W (.const 1))
  if i.val = 0 then
    match j.val with
    | 0 => .mul (.sub (.const 1) P) W
    | 1 => .mul W (.sub (.add (.mul (.const 3) W) P) (.add (.mul P W) (.const 1)))
    | 2 => .mul (.const 2) (.mul W P)
    | 3 => .mul (.mul (.const 2) (.mul W P)) (.sub (.mul (.const 2) W) (.const 1))
    | 4 => .mul P (.sub P2 (.const 1))
    | 5 => .mul (.mul (.const 2) (.mul W P)) (.add P2 P)
    | _ => .mul (.mul (.const 2) (.mul W P)) (.mul (.sub (.mul (.const 2) W) (.const 1)) (.add P2 P))
  else
    let r8 : Fin 8 := ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
    match j.val with
    | 0 => .sub (.mul Pm1 (t3u3GenC8Expr r8 ⟨0, by decide⟩)) (.mul W (t3u3GenC8Expr r8 ⟨2, by decide⟩))
    | 1 => .sub (.mul Pm1 (t3u3GenC8Expr r8 ⟨1, by decide⟩)) (.mul Wb2 (t3u3GenC8Expr r8 ⟨2, by decide⟩))
    | 2 => t3u3GenC8Expr r8 ⟨3, by decide⟩
    | 3 => t3u3GenC8Expr r8 ⟨4, by decide⟩
    | 4 => t3u3GenC8Expr r8 ⟨5, by decide⟩
    | 5 => t3u3GenC8Expr r8 ⟨6, by decide⟩
    | _ => t3u3GenC8Expr r8 ⟨7, by decide⟩

def t3u3GenD7Expr (i j : Fin 7) : Expr4 :=
  let W := Expr4.v0
  let P := Expr4.v2
  let P2 := Expr4.mul P P
  let twoWm1 := Expr4.sub (.mul (.const 2) W) (.const 1)
  let P2pP := Expr4.add P2 P
  let r2 := t3u3GenC7Expr i ⟨2, by decide⟩
  match j.val with
  | 0 => t3u3GenC7Expr i ⟨0, by decide⟩
  | 1 => t3u3GenC7Expr i ⟨1, by decide⟩
  | 2 => r2
  | 3 => .sub (t3u3GenC7Expr i ⟨3, by decide⟩) (.mul twoWm1 r2)
  | 4 => t3u3GenC7Expr i ⟨4, by decide⟩
  | 5 => .sub (t3u3GenC7Expr i ⟨5, by decide⟩) (.mul P2pP r2)
  | _ => .sub (t3u3GenC7Expr i ⟨6, by decide⟩) (.mul (.mul twoWm1 P2pP) r2)

def t3u3GenE6Expr (i j : Fin 6) : Expr4 :=
  let W := Expr4.v0
  let P := Expr4.v2
  let P2 := Expr4.mul P P
  let twoP := Expr4.mul (.const 2) P
  let twoW := Expr4.mul (.const 2) W
  let f0 := Expr4.sub (.const 1) P
  let f1 := Expr4.sub (.add (.mul (.const 3) W) P) (.add (.mul P W) (.const 1))
  let f4 := Expr4.sub P2 (.const 1)
  let r7 : Fin 7 := ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
  let r2 := t3u3GenD7Expr r7 ⟨2, by decide⟩
  match j.val with
  | 0 => .sub (.mul twoP (t3u3GenD7Expr r7 ⟨0, by decide⟩)) (.mul f0 r2)
  | 1 => .sub (.mul twoP (t3u3GenD7Expr r7 ⟨1, by decide⟩)) (.mul f1 r2)
  | 2 => t3u3GenD7Expr r7 ⟨3, by decide⟩
  | 3 => .sub (.mul twoW (t3u3GenD7Expr r7 ⟨4, by decide⟩)) (.mul f4 r2)
  | 4 => t3u3GenD7Expr r7 ⟨5, by decide⟩
  | _ => t3u3GenD7Expr r7 ⟨6, by decide⟩

-- Fast monomorphic 4-variable polynomial representation (`FM`) and 2-variable
-- `(2^u, 3^u)` slice representation (`CDS`) avoiding nested-pair elaborator MVar overhead.

private inductive FM where
  | p (a b c d v : Nat)
  | n (a b c d v : Nat)
  deriving DecidableEq

private def fmKey : FM -> Nat
  | .p a b c d _ => ((a * 64 + b) * 64 + c) * 64 + d
  | .n a b c d _ => ((a * 64 + b) * 64 + c) * 64 + d

private def fmNegOne : FM -> FM
  | .p a b c d v => .n a b c d v
  | .n a b c d v => .p a b c d v

private def fmAddSame (x y : FM) : Option FM :=
  match x, y with
  | .p a b c d v1, .p _ _ _ _ v2 => some (.p a b c d (v1 + v2))
  | .n a b c d v1, .n _ _ _ _ v2 => some (.n a b c d (v1 + v2))
  | .p a b c d v1, .n _ _ _ _ v2 =>
    match Nat.beq v1 v2 with
    | true => none
    | false =>
      match Nat.ble v2 v1 with
      | true => some (.p a b c d (v1 - v2))
      | false => some (.n a b c d (v2 - v1))
  | .n a b c d v1, .p _ _ _ _ v2 =>
    match Nat.beq v1 v2 with
    | true => none
    | false =>
      match Nat.ble v2 v1 with
      | true => some (.n a b c d (v1 - v2))
      | false => some (.p a b c d (v2 - v1))

private def fmMergeAux : Nat -> List FM -> List FM -> List FM
  | 0, xs, ys => xs ++ ys
  | _ + 1, [], ys => ys
  | _ + 1, xs, [] => xs
  | fuel + 1, x :: xs, y :: ys =>
    let kx := fmKey x
    let ky := fmKey y
    match Nat.beq kx ky with
    | true =>
      match fmAddSame x y with
      | none => fmMergeAux fuel xs ys
      | some z => z :: fmMergeAux fuel xs ys
    | false =>
      match Nat.ble kx ky with
      | true => x :: fmMergeAux fuel xs (y :: ys)
      | false => y :: fmMergeAux fuel (x :: xs) ys

private def fmMerge (xs ys : List FM) : List FM :=
  fmMergeAux 2048 xs ys

private def fmNeg : List FM -> List FM := List.map fmNegOne

private def fmMulOne (m x : FM) : FM :=
  match m, x with
  | .p a1 b1 c1 d1 v1, .p a2 b2 c2 d2 v2 => .p (a1 + a2) (b1 + b2) (c1 + c2) (d1 + d2) (v1 * v2)
  | .n a1 b1 c1 d1 v1, .n a2 b2 c2 d2 v2 => .p (a1 + a2) (b1 + b2) (c1 + c2) (d1 + d2) (v1 * v2)
  | .p a1 b1 c1 d1 v1, .n a2 b2 c2 d2 v2 => .n (a1 + a2) (b1 + b2) (c1 + c2) (d1 + d2) (v1 * v2)
  | .n a1 b1 c1 d1 v1, .p a2 b2 c2 d2 v2 => .n (a1 + a2) (b1 + b2) (c1 + c2) (d1 + d2) (v1 * v2)

private def fmMul : List FM -> List FM -> List FM
  | [], _ => []
  | m :: ms, ys => fmMerge (ys.map (fmMulOne m)) (fmMul ms ys)

private def fmSubMat {L : Nat} (M : Fin (L + 1) -> Fin (L + 1) -> List FM) (j : Fin (L + 1)) :
    Fin L -> Fin L -> List FM :=
  fun r c => M ⟨r.val + 1, Nat.succ_lt_succ r.isLt⟩ (skipFinIdx j c)

private def fmSumPrefix (N : Nat) (f : Fin N -> List FM) : Nat -> List FM
  | 0 => []
  | k + 1 => if hk : k < N then fmMerge (fmSumPrefix N f k) (f ⟨k, hk⟩) else fmSumPrefix N f k

private def fmDet : (n : Nat) -> (Fin n -> Fin n -> List FM) -> List FM
  | 0, _ => [.p 0 0 0 0 1]
  | L + 1, M =>
    fmSumPrefix (L + 1) (fun j =>
      let p0j := M ⟨0, Nat.zero_lt_succ L⟩ j
      let s := if j.val % 2 = 0 then p0j else fmNeg p0j
      fmMul s (fmDet L (fmSubMat M j))) (L + 1)

private def fmOneToMono4 : FM -> Mono4
  | .p a b c d v => (a, b, c, d, (v : Int))
  | .n a b c d v => (a, b, c, d, -(v : Int))

private def fmToPoly4 : List FM -> List Mono4 := List.map fmOneToMono4

private def evalFMOne (x0 x1 x2 x3 : Int) (m : FM) : Int :=
  evalMono4 x0 x1 x2 x3 (fmOneToMono4 m)

private def evalFM (x0 x1 x2 x3 : Int) : List FM -> Int
  | [] => 0
  | m :: ms => evalFMOne x0 x1 x2 x3 m + evalFM x0 x1 x2 x3 ms

private theorem evalFM_eq_evalPoly4 (x0 x1 x2 x3 : Int) :
    ∀ xs : List FM, evalFM x0 x1 x2 x3 xs = evalPoly4 x0 x1 x2 x3 (fmToPoly4 xs)
  | [] => rfl
  | m :: ms => by
    simp only [evalFM, fmToPoly4, List.map_cons, evalPoly4, evalFMOne,
               evalFM_eq_evalPoly4 x0 x1 x2 x3 ms]

private theorem evalFM_append (x0 x1 x2 x3 : Int) :
    ∀ xs ys : List FM,
      evalFM x0 x1 x2 x3 (xs ++ ys) = evalFM x0 x1 x2 x3 xs + evalFM x0 x1 x2 x3 ys
  | [], _ => by simp [evalFM]
  | m :: ms, ys => by
    simp only [List.cons_append, evalFM, evalFM_append x0 x1 x2 x3 ms ys, Int.add_assoc]

private theorem fmKey_inj (a1 b1 c1 d1 a2 b2 c2 d2 : Nat)
    (hb1 : b1 < 64) (hc1 : c1 < 64) (hd1 : d1 < 64)
    (hb2 : b2 < 64) (hc2 : c2 < 64) (hd2 : d2 < 64)
    (hk : ((a1 * 64 + b1) * 64 + c1) * 64 + d1 = ((a2 * 64 + b2) * 64 + c2) * 64 + d2) :
    a1 = a2 ∧ b1 = b2 ∧ c1 = c2 ∧ d1 = d2 := by
  omega

private def fmValid64 : FM -> Bool
  | .p _ b c d _ => decide (b < 64 ∧ c < 64 ∧ d < 64)
  | .n _ b c d _ => decide (b < 64 ∧ c < 64 ∧ d < 64)

private theorem fmAddSame_valid_and_eval (x0 x1 x2 x3 : Int) (x y : FM)
    (hx : fmValid64 x = true) (hy : fmValid64 y = true) (hk : fmKey x = fmKey y) :
    (match fmAddSame x y with
     | none => True
     | some z => fmValid64 z = true) ∧
    (match fmAddSame x y with
     | none => evalFMOne x0 x1 x2 x3 x + evalFMOne x0 x1 x2 x3 y = 0
     | some z => evalFMOne x0 x1 x2 x3 z = evalFMOne x0 x1 x2 x3 x + evalFMOne x0 x1 x2 x3 y) := by
  cases x with
  | p a1 b1 c1 d1 v1 =>
    cases y with
    | p a2 b2 c2 d2 v2 =>
      simp only [fmValid64, decide_eq_true_eq] at hx hy
      simp only [fmKey] at hk
      rcases fmKey_inj a1 b1 c1 d1 a2 b2 c2 d2 hx.1 hx.2.1 hx.2.2 hy.1 hy.2.1 hy.2.2 hk with
        ⟨rfl, rfl, rfl, rfl⟩
      simp only [fmAddSame, fmValid64, decide_eq_true_eq, evalFMOne, fmOneToMono4, evalMono4]
      exact ⟨hx, by rw [Int.natCast_add, Int.add_mul]⟩
    | n a2 b2 c2 d2 v2 =>
      simp only [fmValid64, decide_eq_true_eq] at hx hy
      simp only [fmKey] at hk
      rcases fmKey_inj a1 b1 c1 d1 a2 b2 c2 d2 hx.1 hx.2.1 hx.2.2 hy.1 hy.2.1 hy.2.2 hk with
        ⟨rfl, rfl, rfl, rfl⟩
      simp only [fmAddSame]
      cases heq : Nat.beq v1 v2 with
      | true =>
        simp only [evalFMOne, fmOneToMono4, evalMono4]
        have hv : v1 = v2 := Nat.eq_of_beq_eq_true heq
        subst hv
        exact ⟨trivial, by rw [← Int.add_mul, Int.add_right_neg, Int.zero_mul]⟩
      | false =>
        cases hble : Nat.ble v2 v1 with
        | true =>
          have hle : v2 ≤ v1 := Nat.le_of_ble_eq_true hble
          simp only [fmValid64, decide_eq_true_eq, evalFMOne, fmOneToMono4, evalMono4]
          refine ⟨hx, ?_⟩
          rw [← Int.add_mul, Int.ofNat_sub hle]
          rfl
        | false =>
          have hle : v1 ≤ v2 := by
            by_cases h : v2 ≤ v1
            · rw [Nat.ble_eq.mpr h] at hble; cases hble
            · omega
          simp only [fmValid64, decide_eq_true_eq, evalFMOne, fmOneToMono4, evalMono4]
          refine ⟨hx, ?_⟩
          rw [← Int.add_mul, Int.ofNat_sub hle]
          congr 1; omega
  | n a1 b1 c1 d1 v1 =>
    cases y with
    | p a2 b2 c2 d2 v2 =>
      simp only [fmValid64, decide_eq_true_eq] at hx hy
      simp only [fmKey] at hk
      rcases fmKey_inj a1 b1 c1 d1 a2 b2 c2 d2 hx.1 hx.2.1 hx.2.2 hy.1 hy.2.1 hy.2.2 hk with
        ⟨rfl, rfl, rfl, rfl⟩
      simp only [fmAddSame]
      cases heq : Nat.beq v1 v2 with
      | true =>
        simp only [evalFMOne, fmOneToMono4, evalMono4]
        have hv : v1 = v2 := Nat.eq_of_beq_eq_true heq
        subst hv
        exact ⟨trivial, by rw [← Int.add_mul, Int.add_left_neg, Int.zero_mul]⟩
      | false =>
        cases hble : Nat.ble v2 v1 with
        | true =>
          have hle : v2 ≤ v1 := Nat.le_of_ble_eq_true hble
          simp only [fmValid64, decide_eq_true_eq, evalFMOne, fmOneToMono4, evalMono4]
          refine ⟨hx, ?_⟩
          rw [← Int.add_mul, Int.ofNat_sub hle]
          congr 1; omega
        | false =>
          have hle : v1 ≤ v2 := by
            by_cases h : v2 ≤ v1
            · rw [Nat.ble_eq.mpr h] at hble; cases hble
            · omega
          simp only [fmValid64, decide_eq_true_eq, evalFMOne, fmOneToMono4, evalMono4]
          refine ⟨hx, ?_⟩
          rw [← Int.add_mul, Int.ofNat_sub hle]
          congr 1; omega
    | n a2 b2 c2 d2 v2 =>
      simp only [fmValid64, decide_eq_true_eq] at hx hy
      simp only [fmKey] at hk
      rcases fmKey_inj a1 b1 c1 d1 a2 b2 c2 d2 hx.1 hx.2.1 hx.2.2 hy.1 hy.2.1 hy.2.2 hk with
        ⟨rfl, rfl, rfl, rfl⟩
      simp only [fmAddSame, fmValid64, decide_eq_true_eq, evalFMOne, fmOneToMono4, evalMono4]
      refine ⟨hx, ?_⟩
      rw [← Int.add_mul, Int.natCast_add]; congr 1; omega

private theorem fmMergeAux_valid_and_eval (x0 x1 x2 x3 : Int) :
    ∀ (fuel : Nat) (xs ys : List FM),
      xs.all fmValid64 = true -> ys.all fmValid64 = true ->
      (fmMergeAux fuel xs ys).all fmValid64 = true ∧
      evalFM x0 x1 x2 x3 (fmMergeAux fuel xs ys) =
        evalFM x0 x1 x2 x3 xs + evalFM x0 x1 x2 x3 ys
  | 0, xs, ys, hxs, hys => by
    simp only [fmMergeAux, List.all_append, hxs, hys, Bool.and_self,
               evalFM_append, and_self]
  | _ + 1, [], ys, _, hys => by simp [fmMergeAux, evalFM, hys]
  | _ + 1, x :: xs, [], hxs, _ => by simp [fmMergeAux, evalFM, hxs]
  | fuel + 1, x :: xs, y :: ys, hxs, hys => by
    simp only [List.all_cons, Bool.and_eq_true] at hxs hys
    simp only [fmMergeAux]
    cases hk : Nat.beq (fmKey x) (fmKey y) with
    | true =>
      have hkeq : fmKey x = fmKey y := Nat.eq_of_beq_eq_true hk
      rcases fmAddSame_valid_and_eval x0 x1 x2 x3 x y hxs.1 hys.1 hkeq with ⟨hvz, hevz⟩
      rcases fmMergeAux_valid_and_eval x0 x1 x2 x3 fuel xs ys hxs.2 hys.2 with ⟨hvm, hevm⟩
      cases hadd : fmAddSame x y with
      | none =>
        rw [hadd] at hevz
        refine ⟨hvm, ?_⟩
        simp only [evalFM, hevm]
        let ex := evalFMOne x0 x1 x2 x3 x
        let ey := evalFMOne x0 x1 x2 x3 y
        let exs := evalFM x0 x1 x2 x3 xs
        let eys := evalFM x0 x1 x2 x3 ys
        change exs + eys = (ex + exs) + (ey + eys)
        change ex + ey = 0 at hevz
        omega
      | some z =>
        rw [hadd] at hvz hevz
        refine ⟨by simp only [List.all_cons, hvz, hvm, Bool.and_self], ?_⟩
        simp only [evalFM, hevz, hevm]
        ac_rfl
    | false =>
      cases hlt : Nat.ble (fmKey x) (fmKey y) with
      | true =>
        have hy_all : (y :: ys).all fmValid64 = true := by
          simp only [List.all_cons, hys.1, hys.2, Bool.and_self]
        rcases fmMergeAux_valid_and_eval x0 x1 x2 x3 fuel xs (y :: ys) hxs.2 hy_all with ⟨hvm, hevm⟩
        refine ⟨by simp only [List.all_cons, hxs.1, hvm, Bool.and_self], ?_⟩
        simp only [evalFM] at hevm ⊢
        rw [hevm]; ac_rfl
      | false =>
        have hx_all : (x :: xs).all fmValid64 = true := by
          simp only [List.all_cons, hxs.1, hxs.2, Bool.and_self]
        rcases fmMergeAux_valid_and_eval x0 x1 x2 x3 fuel (x :: xs) ys hx_all hys.2 with ⟨hvm, hevm⟩
        refine ⟨by simp only [List.all_cons, hys.1, hvm, Bool.and_self], ?_⟩
        simp only [evalFM] at hevm ⊢
        rw [hevm]; ac_rfl

private def fmBound (B : Nat) : FM -> Bool
  | .p _ b c d _ => decide (b ≤ B ∧ c ≤ B ∧ d ≤ B)
  | .n _ b c d _ => decide (b ≤ B ∧ c ≤ B ∧ d ≤ B)

private theorem fmBound_imp_valid64 (B : Nat) (hB : B < 64) (m : FM)
    (hb : fmBound B m = true) : fmValid64 m = true := by
  cases m <;> (simp only [fmBound, fmValid64, decide_eq_true_eq] at hb ⊢; omega)

private theorem fmBound_mono (B1 B2 : Nat) (hle : B1 ≤ B2) (m : FM)
    (hb : fmBound B1 m = true) : fmBound B2 m = true := by
  cases m <;> (simp only [fmBound, decide_eq_true_eq] at hb ⊢; omega)

private theorem fmMerge_bound_and_eval (x0 x1 x2 x3 : Int) (B : Nat) (hB : B < 64)
    (xs ys : List FM)
    (hxs : xs.all (fmBound B) = true) (hys : ys.all (fmBound B) = true) :
    (fmMerge xs ys).all (fmBound B) = true ∧
    evalFM x0 x1 x2 x3 (fmMerge xs ys) = evalFM x0 x1 x2 x3 xs + evalFM x0 x1 x2 x3 ys := by
  have hval_of : ∀ zs : List FM, zs.all (fmBound B) = true -> zs.all fmValid64 = true := by
    intro zs hz; apply List.all_eq_true.mpr; intro m hm
    exact fmBound_imp_valid64 B hB m (List.all_eq_true.mp hz m hm)
  have hb_aux : ∀ (fuel : Nat) (us vs : List FM),
      us.all (fmBound B) = true -> vs.all (fmBound B) = true ->
      (fmMergeAux fuel us vs).all (fmBound B) = true := by
    intro fuel; induction fuel with
    | zero => intro us vs hu hv; simp [fmMergeAux, List.all_append, hu, hv]
    | succ f' ih =>
      intro us vs hu hv
      cases us with
      | nil => simpa [fmMergeAux] using hv
      | cons u ut =>
        cases vs with
        | nil => simpa [fmMergeAux] using hu
        | cons v vt =>
          simp only [List.all_cons, Bool.and_eq_true] at hu hv
          simp only [fmMergeAux]
          cases hk : Nat.beq (fmKey u) (fmKey v) with
          | true =>
            have hsame : match fmAddSame u v with | none => True | some z => fmBound B z = true := by
              cases u with
              | p a1 b1 c1 d1 v1 =>
                cases v with
                | p a2 b2 c2 d2 v2 =>
                  simp only [fmAddSame]; exact hu.1
                | n a2 b2 c2 d2 v2 =>
                  simp only [fmAddSame]
                  cases h1 : Nat.beq v1 v2 with
                  | true => trivial
                  | false =>
                    cases h2 : Nat.ble v2 v1 <;> exact hu.1
              | n a1 b1 c1 d1 v1 =>
                cases v with
                | p a2 b2 c2 d2 v2 =>
                  simp only [fmAddSame]
                  cases h1 : Nat.beq v1 v2 with
                  | true => trivial
                  | false =>
                    cases h2 : Nat.ble v2 v1 <;> exact hu.1
                | n a2 b2 c2 d2 v2 =>
                  simp only [fmAddSame]; exact hu.1
            cases hadd : fmAddSame u v with
            | none => exact ih ut vt hu.2 hv.2
            | some z =>
              rw [hadd] at hsame
              simp only [List.all_cons, hsame, ih ut vt hu.2 hv.2, Bool.and_self]
          | false =>
            cases hlt : Nat.ble (fmKey u) (fmKey v) with
            | true =>
              simp only [List.all_cons, hu.1,
                         ih ut (v :: vt) hu.2 (by simp only [List.all_cons, hv.1, hv.2, Bool.and_self]),
                         Bool.and_self]
            | false =>
              simp only [List.all_cons, hv.1,
                         ih (u :: ut) vt (by simp only [List.all_cons, hu.1, hu.2, Bool.and_self]) hv.2,
                         Bool.and_self]
  exact ⟨hb_aux 2048 xs ys hxs hys,
         (fmMergeAux_valid_and_eval x0 x1 x2 x3 2048 xs ys (hval_of xs hxs) (hval_of ys hys)).2⟩

private theorem fmNeg_bound_and_eval (x0 x1 x2 x3 : Int) (B : Nat) :
    ∀ xs : List FM,
      xs.all (fmBound B) = true ->
      (fmNeg xs).all (fmBound B) = true ∧
      evalFM x0 x1 x2 x3 (fmNeg xs) = -evalFM x0 x1 x2 x3 xs
  | [], _ => by simp [fmNeg, evalFM]
  | m :: ms, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    rcases fmNeg_bound_and_eval x0 x1 x2 x3 B ms h.2 with ⟨hbm, hevm⟩
    unfold fmNeg at hbm hevm ⊢
    have hb1 : fmBound B (fmNegOne m) = true := by cases m <;> exact h.1
    have hev1 : evalFMOne x0 x1 x2 x3 (fmNegOne m) = -evalFMOne x0 x1 x2 x3 m := by
      cases m <;> simp [fmNegOne, evalFMOne, fmOneToMono4, evalMono4, Int.neg_mul]
    refine ⟨by simp only [List.map_cons, List.all_cons, hb1, hbm, Bool.and_self], ?_⟩
    simp only [List.map_cons, evalFM, hev1, hevm]
    omega

private theorem intPowNat_add_w14 (s : Int) (a : Nat) :
    ∀ b : Nat, intPowNat s (a + b) = intPowNat s a * intPowNat s b
  | 0 => by simp [intPowNat]
  | b + 1 => by
    rw [show a + (b + 1) = (a + b) + 1 by omega]
    simp only [intPowNat, intPowNat_add_w14 s a b]
    ac_rfl

private theorem fmMulOne_bound_and_eval (x0 x1 x2 x3 : Int) (B1 B2 : Nat) (m x : FM)
    (hm : fmBound B1 m = true) (hx : fmBound B2 x = true) :
    fmBound (B1 + B2) (fmMulOne m x) = true ∧
    evalFMOne x0 x1 x2 x3 (fmMulOne m x) =
      evalFMOne x0 x1 x2 x3 m * evalFMOne x0 x1 x2 x3 x := by
  cases m with
  | p a1 b1 c1 d1 v1 =>
    cases x with
    | p a2 b2 c2 d2 v2 =>
      simp only [fmBound, decide_eq_true_eq] at hm hx
      simp only [fmMulOne, fmBound, decide_eq_true_eq, evalFMOne, fmOneToMono4, evalMono4,
                 Int.natCast_mul, intPowNat_add_w14]
      exact ⟨by omega, by ac_rfl⟩
    | n a2 b2 c2 d2 v2 =>
      simp only [fmBound, decide_eq_true_eq] at hm hx
      simp only [fmMulOne, fmBound, decide_eq_true_eq, evalFMOne, fmOneToMono4, evalMono4,
                 Int.natCast_mul, intPowNat_add_w14]
      refine ⟨by omega, ?_⟩
      simp only [Int.neg_mul, Int.mul_neg]
      congr 1; ac_rfl
  | n a1 b1 c1 d1 v1 =>
    cases x with
    | p a2 b2 c2 d2 v2 =>
      simp only [fmBound, decide_eq_true_eq] at hm hx
      simp only [fmMulOne, fmBound, decide_eq_true_eq, evalFMOne, fmOneToMono4, evalMono4,
                 Int.natCast_mul, intPowNat_add_w14]
      refine ⟨by omega, ?_⟩
      simp only [Int.neg_mul]
      congr 1; ac_rfl
    | n a2 b2 c2 d2 v2 =>
      simp only [fmBound, decide_eq_true_eq] at hm hx
      simp only [fmMulOne, fmBound, decide_eq_true_eq, evalFMOne, fmOneToMono4, evalMono4,
                 Int.natCast_mul, intPowNat_add_w14]
      refine ⟨by omega, ?_⟩
      simp only [Int.neg_mul, Int.mul_neg, Int.neg_neg]
      ac_rfl

private theorem fmMul_bound_and_eval (x0 x1 x2 x3 : Int) (B1 B2 : Nat)
    (hB : B1 + B2 < 64) :
    ∀ (xs ys : List FM),
      xs.all (fmBound B1) = true -> ys.all (fmBound B2) = true ->
      (fmMul xs ys).all (fmBound (B1 + B2)) = true ∧
      evalFM x0 x1 x2 x3 (fmMul xs ys) = evalFM x0 x1 x2 x3 xs * evalFM x0 x1 x2 x3 ys
  | [], _, _, _ => by simp [fmMul, evalFM]
  | m :: ms, ys, hxs, hys => by
    simp only [List.all_cons, Bool.and_eq_true] at hxs
    have hmap : ∀ zs : List FM, zs.all (fmBound B2) = true ->
        (zs.map (fmMulOne m)).all (fmBound (B1 + B2)) = true ∧
        evalFM x0 x1 x2 x3 (zs.map (fmMulOne m)) =
          evalFMOne x0 x1 x2 x3 m * evalFM x0 x1 x2 x3 zs := by
      intro zs; induction zs with
      | nil => intro _; simp [evalFM]
      | cons z zt ihz =>
        intro hz
        simp only [List.all_cons, Bool.and_eq_true] at hz
        rcases fmMulOne_bound_and_eval x0 x1 x2 x3 B1 B2 m z hxs.1 hz.1 with ⟨hb1, he1⟩
        rcases ihz hz.2 with ⟨hbt, het⟩
        simp only [List.map_cons, List.all_cons, hb1, hbt, Bool.and_self, true_and,
                   evalFM, he1, het, Int.mul_add]
    rcases hmap ys hys with ⟨hb_hd, he_hd⟩
    rcases fmMul_bound_and_eval x0 x1 x2 x3 B1 B2 hB ms ys hxs.2 hys with ⟨hb_tl, he_tl⟩
    rcases fmMerge_bound_and_eval x0 x1 x2 x3 (B1 + B2) hB _ _ hb_hd hb_tl with ⟨hbm, hevm⟩
    simp only [fmMul]
    exact ⟨hbm, by rw [hevm, he_hd, he_tl, evalFM, Int.add_mul]⟩

private theorem fmDet_bound_and_eval (x0 x1 x2 x3 : Int) :
    ∀ (n : Nat) (M : Fin n -> Fin n -> List FM),
      4 * n < 64 ->
      (∀ i j : Fin n, (M i j).all (fmBound 4) = true) ->
      (fmDet n M).all (fmBound (4 * n)) = true ∧
      evalFM x0 x1 x2 x3 (fmDet n M) =
        intDet n (fun i j => evalFM x0 x1 x2 x3 (M i j))
  | 0, _, _, _ => by
    simp [fmDet, fmBound, evalFM, evalFMOne, fmOneToMono4, evalMono4, intPowNat, intDet]
  | L + 1, M, hBn, hM => by
    have hBL : 4 * L < 64 := by omega
    have h4L1 : 4 + 4 * L = 4 * (L + 1) := by omega
    let z0 : Fin (L + 1) := ⟨0, Nat.zero_lt_succ L⟩
    let term : Fin (L + 1) -> List FM := fun j =>
      let p0j := M z0 j
      let s := if j.val % 2 = 0 then p0j else fmNeg p0j
      fmMul s (fmDet L (fmSubMat M j))
    have hterm : ∀ j : Fin (L + 1),
        (term j).all (fmBound (4 * (L + 1))) = true ∧
        evalFM x0 x1 x2 x3 (term j) =
          (if j.val % 2 = 0 then (1 : Int) else -1) *
            evalFM x0 x1 x2 x3 (M z0 j) *
            intDet L (intSubMat (fun r c => evalFM x0 x1 x2 x3 (M r c)) j) := by
      intro j
      rcases fmDet_bound_and_eval x0 x1 x2 x3 L (fmSubMat M j) hBL
        (fun r c => hM _ _) with ⟨hb_sub, he_sub⟩
      have hp0 : (M z0 j).all (fmBound 4) = true := hM z0 j
      let s := if j.val % 2 = 0 then M z0 j else fmNeg (M z0 j)
      have hs : s.all (fmBound 4) = true ∧
          evalFM x0 x1 x2 x3 s =
            (if j.val % 2 = 0 then (1 : Int) else -1) *
              evalFM x0 x1 x2 x3 (M z0 j) := by
        dsimp only [s]
        by_cases hev : j.val % 2 = 0
        · simp only [hev, ite_true, hp0, Int.one_mul, and_self]
        · rcases fmNeg_bound_and_eval x0 x1 x2 x3 4 (M z0 j) hp0 with ⟨hbn, hen⟩
          simp only [hev, ite_false, hbn, hen, Int.neg_one_mul, and_self]
      rcases fmMul_bound_and_eval x0 x1 x2 x3 4 (4 * L) (by omega) s (fmDet L (fmSubMat M j))
        hs.1 hb_sub with ⟨hbm, hem⟩
      rw [h4L1] at hbm
      refine ⟨hbm, ?_⟩
      change evalFM x0 x1 x2 x3 (fmMul s (fmDet L (fmSubMat M j))) = _
      rw [hem, hs.2, he_sub]
      rfl
    have hsum : ∀ k : Nat, k ≤ L + 1 ->
        (fmSumPrefix (L + 1) term k).all (fmBound (4 * (L + 1))) = true ∧
        evalFM x0 x1 x2 x3 (fmSumPrefix (L + 1) term k) =
          intSumPrefix (L + 1) (fun j =>
            (if j.val % 2 = 0 then (1 : Int) else -1) *
              evalFM x0 x1 x2 x3 (M z0 j) *
              intDet L (intSubMat (fun r c => evalFM x0 x1 x2 x3 (M r c)) j)) k := by
      intro k hk; induction k with
      | zero => simp [fmSumPrefix, intSumPrefix, evalFM]
      | succ k' ih =>
        have hlt : k' < L + 1 := hk
        rcases ih (Nat.le_of_lt hk) with ⟨hbk, hek⟩
        rcases hterm ⟨k', hlt⟩ with ⟨hbj, hej⟩
        rcases fmMerge_bound_and_eval x0 x1 x2 x3 (4 * (L + 1)) hBn _ _ hbk hbj with ⟨hbm, hem⟩
        simp only [fmSumPrefix, intSumPrefix, hlt, dite_true]
        exact ⟨hbm, by rw [hem, hek, hej]⟩
    exact hsum (L + 1) (Nat.le_refl _)

private def g2FM (i j : Fin 6) : List FM :=
  match i.val, j.val with
  | 0, 0 => [.n 0 1 0 1 1, .n 0 1 1 0 1, .p 0 1 1 1 1, .p 0 1 2 0 1, .p 1 0 1 0 2, .n 1 0 1 1 2]
  | 0, 1 => [.n 0 2 1 0 2, .p 0 2 2 0 2, .n 1 1 0 1 3, .p 1 1 1 0 3, .p 1 1 1 1 1, .n 1 1 2 0 1,
          .p 2 0 1 0 2, .n 2 0 1 1 2]
  | 0, 2 => [.p 0 2 0 1 1, .n 0 2 1 0 1, .n 1 1 0 1 2, .p 1 1 1 0 2]
  | 0, 3 => [.p 0 1 0 1 1, .n 0 1 0 2 1, .n 0 1 1 0 1, .p 0 1 1 1 1, .n 1 0 0 1 2, .p 1 0 0 2 2,
          .p 1 0 1 0 2, .n 1 0 1 1 2]
  | 0, 4 => [.p 0 1 0 2 1, .n 0 1 1 1 1, .n 0 1 2 1 1, .p 0 1 3 0 1]
  | 0, _ => [.p 0 2 0 2 1, .n 0 2 2 0 1, .n 1 1 1 1 2, .p 1 1 2 0 2, .n 1 1 2 1 2, .p 1 1 3 0 2]
  | 1, 0 => [.n 0 1 1 0 1, .n 0 1 1 1 1, .p 0 1 2 0 1, .p 0 1 2 1 1, .p 1 0 1 0 1, .n 1 0 1 1 1,
          .p 1 0 2 0 1, .n 1 0 2 1 1]
  | 1, 1 => [.n 0 2 1 0 2, .p 0 2 2 0 2, .n 1 1 1 0 1, .n 1 1 1 1 3, .p 1 1 2 0 3, .p 1 1 2 1 1,
          .p 2 0 1 0 3, .n 2 0 1 1 3, .p 2 0 2 0 1, .n 2 0 2 1 1]
  | 1, 2 => [.n 0 2 1 0 1, .p 0 2 1 1 1, .p 2 0 1 0 1, .n 2 0 1 1 1]
  | 1, 3 => [.n 0 1 1 0 1, .p 0 1 1 1 1, .p 0 1 2 1 1, .n 0 1 2 2 1, .p 1 0 1 0 1, .n 1 0 1 1 1,
          .n 1 0 2 1 1, .p 1 0 2 2 1]
  | 1, 4 => [.n 0 1 2 1 1, .p 0 1 2 2 1, .p 0 1 3 0 1, .n 0 1 3 1 1, .n 1 0 2 1 1, .p 1 0 2 2 1,
          .p 1 0 3 0 1, .n 1 0 3 1 1]
  | 1, _ => [.n 0 2 2 0 1, .p 0 2 2 2 1, .n 1 1 2 1 2, .p 1 1 2 2 2, .p 1 1 3 0 2, .n 1 1 3 1 2,
          .p 2 0 2 0 1, .n 2 0 2 1 2, .p 2 0 2 2 1, .p 2 0 3 0 2, .n 2 0 3 1 2]
  | 2, 0 => [.n 0 1 1 0 1, .p 0 1 2 0 1, .n 0 1 2 1 1, .p 0 1 3 1 1, .p 1 0 2 0 2, .n 1 0 2 1 2]
  | 2, 1 => [.n 0 2 1 0 2, .p 0 2 2 0 2, .n 1 1 1 0 5, .p 1 1 2 0 7, .n 1 1 2 1 3, .p 1 1 3 1 1,
          .p 2 0 2 0 6, .n 2 0 2 1 6]
  | 2, 2 => [.n 0 2 1 0 1, .p 0 2 2 1 1, .n 1 1 1 0 2, .p 1 1 2 1 2]
  | 2, 3 => [.n 0 1 1 0 1, .p 0 1 2 1 1, .p 0 1 3 1 1, .n 0 1 4 2 1]
  | 2, 4 => [.p 0 1 3 0 1, .n 0 1 3 1 1, .n 0 1 4 1 1, .p 0 1 4 2 1, .p 1 0 3 0 2, .n 1 0 3 1 2,
          .n 1 0 4 1 2, .p 1 0 4 2 2]
  | 2, _ => [.n 0 2 2 0 1, .p 0 2 4 2 1, .n 1 1 2 0 2, .p 1 1 3 0 2, .n 1 1 3 1 2, .n 1 1 4 1 2,
          .p 1 1 4 2 4, .p 2 0 3 0 4, .n 2 0 3 1 4, .n 2 0 4 1 4, .p 2 0 4 2 4]
  | 3, 0 => [.n 0 1 0 2 2, .n 0 1 1 0 2, .p 0 1 1 2 2, .p 0 1 2 0 2, .p 1 0 1 0 2, .n 1 0 1 2 2]
  | 3, 1 => [.n 0 2 1 0 8, .p 0 2 2 0 8, .n 1 1 0 2 6, .p 1 1 1 0 6, .p 1 1 1 2 2, .n 1 1 2 0 2,
          .p 2 0 1 0 2, .n 2 0 1 2 2]
  | 3, 2 => [.p 0 2 0 2 4, .n 0 2 1 0 4, .n 1 1 0 2 4, .p 1 1 1 0 4]
  | 3, 3 => [.p 0 1 0 2 2, .n 0 1 0 4 2, .n 0 1 1 0 2, .p 0 1 1 2 2, .n 1 0 0 2 2, .p 1 0 0 4 2,
          .p 1 0 1 0 2, .n 1 0 1 2 2]
  | 3, 4 => [.p 0 1 0 4 2, .n 0 1 1 2 2, .n 0 1 2 2 2, .p 0 1 3 0 2]
  | 3, _ => [.p 0 2 0 4 4, .n 0 2 2 0 4, .n 1 1 1 2 4, .p 1 1 2 0 4, .n 1 1 2 2 4, .p 1 1 3 0 4]
  | 4, 0 => [.n 0 1 1 0 2, .n 0 1 1 2 2, .p 0 1 2 0 2, .p 0 1 2 2 2, .p 1 0 1 0 1, .n 1 0 1 2 1,
          .p 1 0 2 0 1, .n 1 0 2 2 1]
  | 4, 1 => [.n 0 2 1 0 8, .p 0 2 2 0 8, .n 1 1 1 0 2, .n 1 1 1 2 6, .p 1 1 2 0 6, .p 1 1 2 2 2,
          .p 2 0 1 0 3, .n 2 0 1 2 3, .p 2 0 2 0 1, .n 2 0 2 2 1]
  | 4, 2 => [.n 0 2 1 0 4, .p 0 2 1 2 4, .p 2 0 1 0 1, .n 2 0 1 2 1]
  | 4, 3 => [.n 0 1 1 0 2, .p 0 1 1 2 2, .p 0 1 2 2 2, .n 0 1 2 4 2, .p 1 0 1 0 1, .n 1 0 1 2 1,
          .n 1 0 2 2 1, .p 1 0 2 4 1]
  | 4, 4 => [.n 0 1 2 2 2, .p 0 1 2 4 2, .p 0 1 3 0 2, .n 0 1 3 2 2, .n 1 0 2 2 1, .p 1 0 2 4 1,
          .p 1 0 3 0 1, .n 1 0 3 2 1]
  | 4, _ => [.n 0 2 2 0 4, .p 0 2 2 4 4, .n 1 1 2 2 4, .p 1 1 2 4 4, .p 1 1 3 0 4, .n 1 1 3 2 4,
          .p 2 0 2 0 1, .n 2 0 2 2 2, .p 2 0 2 4 1, .p 2 0 3 0 2, .n 2 0 3 2 2]
  | _, 0 => [.n 0 1 1 0 2, .p 0 1 2 0 2, .n 0 1 2 2 2, .p 0 1 3 2 2, .p 1 0 2 0 2, .n 1 0 2 2 2]
  | _, 1 => [.n 0 2 1 0 8, .p 0 2 2 0 8, .n 1 1 1 0 10, .p 1 1 2 0 14, .n 1 1 2 2 6, .p 1 1 3 2 2,
          .p 2 0 2 0 6, .n 2 0 2 2 6]
  | _, 2 => [.n 0 2 1 0 4, .p 0 2 2 2 4, .n 1 1 1 0 4, .p 1 1 2 2 4]
  | _, 3 => [.n 0 1 1 0 2, .p 0 1 2 2 2, .p 0 1 3 2 2, .n 0 1 4 4 2]
  | _, 4 => [.p 0 1 3 0 2, .n 0 1 3 2 2, .n 0 1 4 2 2, .p 0 1 4 4 2, .p 1 0 3 0 2, .n 1 0 3 2 2,
          .n 1 0 4 2 2, .p 1 0 4 4 2]
  | _, _ => [.n 0 2 2 0 4, .p 0 2 4 4 4, .n 1 1 2 0 4, .p 1 1 3 0 4, .n 1 1 3 2 4, .n 1 1 4 2 4,
          .p 1 1 4 4 8, .p 2 0 3 0 4, .n 2 0 3 2 4, .n 2 0 4 2 4, .p 2 0 4 4 4]

private def t3u3GenG2Expr (i j : Fin 6) : Expr4 :=
  if j.val = 1 then .add (t3u3GenE6Expr i ⟨1, by decide⟩) (t3u3GenE6Expr i ⟨0, by decide⟩)
  else if j.val = 5 then .add (t3u3GenE6Expr i ⟨5, by decide⟩) (t3u3GenE6Expr i ⟨4, by decide⟩)
  else if j.val = 3 then .sub (t3u3GenE6Expr i ⟨3, by decide⟩) (t3u3GenE6Expr i ⟨4, by decide⟩)
  else t3u3GenE6Expr i j

private theorem t3u3_g2_and_row20_certs :
    (∀ i j : Fin 6, (g2FM i j).all (fmBound 4) = true) ∧
    (∀ i j : Fin 6, fmToPoly4 (g2FM i j) = normExpr4 (t3u3GenG2Expr i j)) ∧
    (∀ j : Fin 7,
      let Pm1 := Expr4.sub .v2 (.const 1)
      let W := Expr4.v0
      let Wb2 := Expr4.mul W (.sub W (.const 1))
      let raw_j : Expr4 :=
        match j.val with
        | 0 => .sub (.mul Pm1 (t3u3GenC8Expr ⟨1, by decide⟩ ⟨0, by decide⟩))
                    (.mul W (t3u3GenC8Expr ⟨1, by decide⟩ ⟨2, by decide⟩))
        | 1 => .sub (.mul Pm1 (t3u3GenC8Expr ⟨1, by decide⟩ ⟨1, by decide⟩))
                    (.mul Wb2 (t3u3GenC8Expr ⟨1, by decide⟩ ⟨2, by decide⟩))
        | 2 => t3u3GenC8Expr ⟨1, by decide⟩ ⟨3, by decide⟩
        | 3 => t3u3GenC8Expr ⟨1, by decide⟩ ⟨4, by decide⟩
        | 4 => t3u3GenC8Expr ⟨1, by decide⟩ ⟨5, by decide⟩
        | 5 => t3u3GenC8Expr ⟨1, by decide⟩ ⟨6, by decide⟩
        | _ => t3u3GenC8Expr ⟨1, by decide⟩ ⟨7, by decide⟩
      normExpr4 (.sub (.mul Pm1 (t3u3GenC7Expr ⟨0, by decide⟩ j)) raw_j) = []) := by decide

private inductive CDS where
  | p (c d v : Nat)
  | n (c d v : Nat)
  deriving DecidableEq

private def cdsToPoly4 (k : Nat) : List CDS -> List Mono4
  | [] => []
  | .p c d v :: tl => (9 - k, k, c, d, (v : Int)) :: cdsToPoly4 k tl
  | .n c d v :: tl => (9 - k, k, c, d, -(v : Int)) :: cdsToPoly4 k tl

private def cdsToFM (k : Nat) : List CDS -> List FM
  | [] => []
  | .p c d v :: tl => .p (9 - k) k c d v :: cdsToFM k tl
  | .n c d v :: tl => .n (9 - k) k c d v :: cdsToFM k tl

private def t3u3CoreWSlice (k : Fin 10) : List CDS :=
  match k.val with
  | 9 => [.p 0 6 4, .n 1 6 24, .p 2 6 48, .n 3 6 8, .n 4 6 108, .p 5 6 144, .n 7 6 144,
         .p 8 6 108, .p 9 6 8, .n 10 6 48, .p 11 6 24, .n 12 6 4]
  | 8 => []
  | 7 => [.n 1 4 2, .n 1 5 16, .p 1 6 36, .n 1 7 16, .n 1 8 2, .n 2 2 1, .p 2 5 64,
         .n 2 6 126, .p 2 7 64, .n 2 10 1, .p 3 2 6, .p 3 4 42, .n 3 5 48, .n 3 7 48,
         .p 3 8 42, .p 3 10 6, .n 4 2 14, .n 4 4 128, .n 4 5 128, .p 4 6 540, .n 4 7 128,
         .n 4 8 128, .n 4 10 14, .p 5 2 14, .p 5 4 140, .p 5 5 224, .n 5 6 756, .p 5 7 224,
         .p 5 8 140, .p 5 10 14, .n 7 2 14, .n 7 4 140, .n 7 5 224, .p 7 6 756, .n 7 7 224,
         .n 7 8 140, .n 7 10 14, .p 8 2 14, .p 8 4 128, .p 8 5 128, .n 8 6 540, .p 8 7 128,
         .p 8 8 128, .p 8 10 14, .n 9 2 6, .n 9 4 42, .p 9 5 48, .p 9 7 48, .n 9 8 42,
         .n 9 10 6, .p 10 2 1, .n 10 5 64, .p 10 6 126, .n 10 7 64, .p 10 10 1, .p 11 4 2,
         .p 11 5 16, .n 11 6 36, .p 11 7 16, .p 11 8 2]
  | 6 => [.p 1 4 4, .n 1 5 8, .p 1 7 8, .n 1 8 4, .p 2 2 5, .n 2 4 6, .n 2 5 8,
         .p 2 7 8, .p 2 8 6, .n 2 10 5, .n 3 2 24, .n 3 4 12, .p 3 5 120, .n 3 7 120,
         .p 3 8 12, .p 3 10 24, .p 4 2 44, .n 4 4 8, .n 4 5 160, .p 4 7 160, .p 4 8 8,
         .n 4 10 44, .n 5 2 40, .p 5 4 136, .n 5 5 112, .p 5 7 112, .n 5 8 136, .p 5 10 40,
         .p 6 2 30, .n 6 4 228, .p 6 5 336, .n 6 7 336, .p 6 8 228, .n 6 10 30, .n 7 2 40,
         .p 7 4 136, .n 7 5 112, .p 7 7 112, .n 7 8 136, .p 7 10 40, .p 8 2 44, .n 8 4 8,
         .n 8 5 160, .p 8 7 160, .p 8 8 8, .n 8 10 44, .n 9 2 24, .n 9 4 12, .p 9 5 120,
         .n 9 7 120, .p 9 8 12, .p 9 10 24, .p 10 2 5, .n 10 4 6, .n 10 5 8, .p 10 7 8,
         .p 10 8 6, .n 10 10 5, .p 11 4 4, .n 11 5 8, .p 11 7 8, .n 11 8 4]
  | 5 => [.n 1 4 2, .p 1 5 8, .n 1 6 12, .p 1 7 8, .n 1 8 2, .n 2 2 10, .p 2 3 12,
         .p 2 4 36, .n 2 5 92, .p 2 6 108, .n 2 7 92, .p 2 8 36, .p 2 9 12, .n 2 10 10,
         .p 3 2 30, .n 3 4 150, .p 3 5 120, .p 3 7 120, .n 3 8 150, .p 3 10 30, .n 4 2 20,
         .n 4 3 120, .p 4 4 280, .p 4 5 280, .n 4 6 840, .p 4 7 280, .p 4 8 280, .n 4 9 120,
         .n 4 10 20, .n 5 2 10, .p 5 3 192, .n 5 4 244, .n 5 5 592, .p 5 6 1308, .n 5 7 592,
         .n 5 8 244, .p 5 9 192, .n 5 10 10, .p 7 2 10, .n 7 3 192, .p 7 4 244, .p 7 5 592,
         .n 7 6 1308, .p 7 7 592, .p 7 8 244, .n 7 9 192, .p 7 10 10, .p 8 2 20, .p 8 3 120,
         .n 8 4 280, .n 8 5 280, .p 8 6 840, .n 8 7 280, .n 8 8 280, .p 8 9 120, .p 8 10 20,
         .n 9 2 30, .p 9 4 150, .n 9 5 120, .n 9 7 120, .p 9 8 150, .n 9 10 30, .p 10 2 10,
         .n 10 3 12, .n 10 4 36, .p 10 5 92, .n 10 6 108, .p 10 7 92, .n 10 8 36, .n 10 9 12,
         .p 10 10 10, .p 11 4 2, .n 11 5 8, .p 11 6 12, .n 11 7 8, .p 11 8 2]
  | 4 => [.p 2 2 10, .n 2 3 30, .p 2 4 20, .p 2 5 10, .n 2 7 10, .n 2 8 20, .p 2 9 30,
         .n 2 10 10, .n 3 2 12, .p 3 4 120, .n 3 5 192, .p 3 7 192, .n 3 8 120, .p 3 10 12,
         .p 4 1 2, .n 4 2 36, .p 4 3 150, .n 4 4 280, .p 4 5 244, .n 4 7 244, .p 4 8 280,
         .n 4 9 150, .p 4 10 36, .n 4 11 2, .n 5 1 8, .p 5 2 92, .n 5 3 120, .n 5 4 280,
         .p 5 5 592, .n 5 7 592, .p 5 8 280, .p 5 9 120, .n 5 10 92, .p 5 11 8, .p 6 1 12,
         .n 6 2 108, .p 6 4 840, .n 6 5 1308, .p 6 7 1308, .n 6 8 840, .p 6 10 108, .n 6 11 12,
         .n 7 1 8, .p 7 2 92, .n 7 3 120, .n 7 4 280, .p 7 5 592, .n 7 7 592, .p 7 8 280,
         .p 7 9 120, .n 7 10 92, .p 7 11 8, .p 8 1 2, .n 8 2 36, .p 8 3 150, .n 8 4 280,
         .p 8 5 244, .n 8 7 244, .p 8 8 280, .n 8 9 150, .p 8 10 36, .n 8 11 2, .n 9 2 12,
         .p 9 4 120, .n 9 5 192, .p 9 7 192, .n 9 8 120, .p 9 10 12, .p 10 2 10, .n 10 3 30,
         .p 10 4 20, .p 10 5 10, .n 10 7 10, .n 10 8 20, .p 10 9 30, .n 10 10 10]
  | 3 => [.n 2 2 5, .p 2 3 24, .n 2 4 44, .p 2 5 40, .n 2 6 30, .p 2 7 40, .n 2 8 44,
         .p 2 9 24, .n 2 10 5, .n 4 1 4, .p 4 2 6, .p 4 3 12, .p 4 4 8, .n 4 5 136,
         .p 4 6 228, .n 4 7 136, .p 4 8 8, .p 4 9 12, .p 4 10 6, .n 4 11 4, .p 5 1 8,
         .p 5 2 8, .n 5 3 120, .p 5 4 160, .p 5 5 112, .n 5 6 336, .p 5 7 112, .p 5 8 160,
         .n 5 9 120, .p 5 10 8, .p 5 11 8, .n 7 1 8, .n 7 2 8, .p 7 3 120, .n 7 4 160,
         .n 7 5 112, .p 7 6 336, .n 7 7 112, .n 7 8 160, .p 7 9 120, .n 7 10 8, .n 7 11 8,
         .p 8 1 4, .n 8 2 6, .n 8 3 12, .n 8 4 8, .p 8 5 136, .n 8 6 228, .p 8 7 136,
         .n 8 8 8, .n 8 9 12, .n 8 10 6, .p 8 11 4, .p 10 2 5, .n 10 3 24, .p 10 4 44,
         .n 10 5 40, .p 10 6 30, .n 10 7 40, .p 10 8 44, .n 10 9 24, .p 10 10 5]
  | 2 => [.p 2 2 1, .n 2 3 6, .p 2 4 14, .n 2 5 14, .p 2 7 14, .n 2 8 14, .p 2 9 6,
         .n 2 10 1, .p 4 1 2, .n 4 3 42, .p 4 4 128, .n 4 5 140, .p 4 7 140, .n 4 8 128,
         .p 4 9 42, .n 4 11 2, .p 5 1 16, .n 5 2 64, .p 5 3 48, .p 5 4 128, .n 5 5 224,
         .p 5 7 224, .n 5 8 128, .n 5 9 48, .p 5 10 64, .n 5 11 16, .n 6 1 36, .p 6 2 126,
         .n 6 4 540, .p 6 5 756, .n 6 7 756, .p 6 8 540, .n 6 10 126, .p 6 11 36, .p 7 1 16,
         .n 7 2 64, .p 7 3 48, .p 7 4 128, .n 7 5 224, .p 7 7 224, .n 7 8 128, .n 7 9 48,
         .p 7 10 64, .n 7 11 16, .p 8 1 2, .n 8 3 42, .p 8 4 128, .n 8 5 140, .p 8 7 140,
         .n 8 8 128, .p 8 9 42, .n 8 11 2, .p 10 2 1, .n 10 3 6, .p 10 4 14, .n 10 5 14,
         .p 10 7 14, .n 10 8 14, .p 10 9 6, .n 10 10 1]
  | 1 => []
  | _ => [.n 6 0 4, .p 6 1 24, .n 6 2 48, .p 6 3 8, .p 6 4 108, .n 6 5 144, .p 6 7 144,
         .n 6 8 108, .n 6 9 8, .p 6 10 48, .n 6 11 24, .p 6 12 4]

/-- Exact 420-monomial core polynomial of `4 * det_9(M_{t3u3}(W, K, u)) / (2^(3u) * 3^(3u))`
    assembled in ascending `(a, b, c, d)` order from its 10 homogeneous `W^(9-k) * K^k` slices. -/
def t3u3CorePoly : List Mono4 :=
  cdsToPoly4 9 (t3u3CoreWSlice ⟨9, by decide⟩) ++
  cdsToPoly4 8 (t3u3CoreWSlice ⟨8, by decide⟩) ++
  cdsToPoly4 7 (t3u3CoreWSlice ⟨7, by decide⟩) ++
  cdsToPoly4 6 (t3u3CoreWSlice ⟨6, by decide⟩) ++
  cdsToPoly4 5 (t3u3CoreWSlice ⟨5, by decide⟩) ++
  cdsToPoly4 4 (t3u3CoreWSlice ⟨4, by decide⟩) ++
  cdsToPoly4 3 (t3u3CoreWSlice ⟨3, by decide⟩) ++
  cdsToPoly4 2 (t3u3CoreWSlice ⟨2, by decide⟩) ++
  cdsToPoly4 1 (t3u3CoreWSlice ⟨1, by decide⟩) ++
  cdsToPoly4 0 (t3u3CoreWSlice ⟨0, by decide⟩)

private def t3u3CoreFM : List FM :=
  cdsToFM 9 (t3u3CoreWSlice ⟨9, by decide⟩) ++
  cdsToFM 8 (t3u3CoreWSlice ⟨8, by decide⟩) ++
  cdsToFM 7 (t3u3CoreWSlice ⟨7, by decide⟩) ++
  cdsToFM 6 (t3u3CoreWSlice ⟨6, by decide⟩) ++
  cdsToFM 5 (t3u3CoreWSlice ⟨5, by decide⟩) ++
  cdsToFM 4 (t3u3CoreWSlice ⟨4, by decide⟩) ++
  cdsToFM 3 (t3u3CoreWSlice ⟨3, by decide⟩) ++
  cdsToFM 2 (t3u3CoreWSlice ⟨2, by decide⟩) ++
  cdsToFM 1 (t3u3CoreWSlice ⟨1, by decide⟩) ++
  cdsToFM 0 (t3u3CoreWSlice ⟨0, by decide⟩)

private theorem fmToPoly4_t3u3CoreFM : fmToPoly4 t3u3CoreFM = t3u3CorePoly := by
  have h1 : ∀ (k : Nat) (sl : List CDS), (cdsToFM k sl).map fmOneToMono4 = cdsToPoly4 k sl := by
    intro k sl; induction sl with
    | nil => rfl
    | cons x tl ih =>
      cases x <;> simp only [cdsToFM, List.map_cons, fmOneToMono4, cdsToPoly4] <;>
        exact congrArg _ ih
  unfold t3u3CoreFM t3u3CorePoly fmToPoly4
  simp only [List.map_append, h1]

private def g2Sub4_0 (r c : Fin 4) : List FM :=
  g2FM ⟨r.val + 2, by omega⟩ (match c.val with | 0 => ⟨0, by decide⟩ | 1 => ⟨1, by decide⟩ | 2 => ⟨2, by decide⟩ | _ => ⟨3, by decide⟩)

private def g2Val4_0 : List FM :=
  [.p 0 6 3 6 32, .n 0 6 4 6 128, .p 0 6 4 7 32, .p 0 6 5 6 160, .n 0 6 5 7 128, .p 0 6 6 7 160,
   .n 0 6 7 6 160, .p 0 6 8 6 128, .n 0 6 8 7 160, .n 0 6 9 6 32, .p 0 6 9 7 128, .n 0 6 10 7 32,
   .n 1 5 3 4 32, .n 1 5 3 6 16, .n 1 5 4 3 32, .p 1 5 4 4 112, .n 1 5 4 5 16, .p 1 5 4 6 32,
   .p 1 5 4 7 32, .p 1 5 4 8 16, .p 1 5 5 3 112, .n 1 5 5 4 128, .p 1 5 5 5 32, .p 1 5 5 6 48,
   .n 1 5 5 7 48, .n 1 5 5 8 64, .n 1 5 6 3 128, .p 1 5 6 4 64, .p 1 5 6 5 16, .n 1 5 6 6 224,
   .n 1 5 6 7 64, .p 1 5 6 8 96, .p 1 5 7 3 32, .n 1 5 7 4 96, .n 1 5 7 5 64, .p 1 5 7 6 336,
   .p 1 5 7 7 96, .n 1 5 7 8 64, .p 1 5 8 3 32, .p 1 5 8 4 176, .p 1 5 8 5 16, .n 1 5 8 6 288,
   .p 1 5 8 7 96, .p 1 5 8 8 16, .n 1 5 9 3 16, .n 1 5 9 4 128, .p 1 5 9 5 32, .p 1 5 9 6 144,
   .n 1 5 9 7 176, .p 1 5 10 4 32, .n 1 5 10 5 16, .n 1 5 10 6 32, .p 1 5 10 7 64, .p 2 4 3 4 16,
   .n 2 4 3 6 16, .p 2 4 4 2 16, .p 2 4 4 3 64, .n 2 4 4 4 88, .n 2 4 4 5 40, .p 2 4 4 6 112,
   .n 2 4 4 7 88, .p 2 4 4 8 24, .n 2 4 5 2 48, .n 2 4 5 3 152, .p 2 4 5 4 160, .p 2 4 5 5 80,
   .n 2 4 5 6 272, .p 2 4 5 7 328, .n 2 4 5 8 96, .p 2 4 6 2 48, .p 2 4 6 3 80, .n 2 4 6 4 144,
   .p 2 4 6 5 24, .p 2 4 6 6 144, .n 2 4 6 7 296, .p 2 4 6 8 144, .n 2 4 7 2 16, .p 2 4 7 3 32,
   .p 2 4 7 4 80, .n 2 4 7 5 128, .p 2 4 7 6 288, .n 2 4 7 7 160, .n 2 4 7 8 96, .n 2 4 8 3 16,
   .p 2 4 8 4 8, .p 2 4 8 5 40, .n 2 4 8 6 352, .p 2 4 8 7 296, .p 2 4 8 8 24, .n 2 4 9 3 8,
   .n 2 4 9 4 64, .p 2 4 9 5 48, .p 2 4 9 6 64, .n 2 4 9 7 40, .p 2 4 10 4 32, .n 2 4 10 5 24,
   .p 2 4 10 6 32, .n 2 4 10 7 40, .n 3 3 4 2 40, .p 3 3 4 3 24, .n 3 3 4 4 16, .p 3 3 4 5 72,
   .n 3 3 4 7 32, .n 3 3 4 8 8, .p 3 3 5 2 112, .n 3 3 5 3 112, .p 3 3 5 4 80, .n 3 3 5 5 128,
   .n 3 3 5 6 48, .p 3 3 5 7 48, .p 3 3 5 8 48, .n 3 3 6 2 104, .p 3 3 6 3 120, .n 3 3 6 4 32,
   .n 3 3 6 5 48, .p 3 3 6 6 112, .p 3 3 6 7 64, .n 3 3 6 8 104, .n 3 3 6 9 8, .p 3 3 7 2 32,
   .n 3 3 7 4 32, .p 3 3 7 5 144, .n 3 3 7 6 224, .n 3 3 7 7 32, .p 3 3 7 8 96, .p 3 3 7 9 16,
   .n 3 3 8 3 32, .n 3 3 8 4 72, .p 3 3 8 6 296, .n 3 3 8 7 152, .n 3 3 8 8 32, .n 3 3 8 9 8,
   .p 3 3 9 4 64, .n 3 3 9 5 32, .n 3 3 9 6 128, .p 3 3 9 7 96, .p 3 3 10 4 8, .n 3 3 10 5 8,
   .n 3 3 10 6 8, .p 3 3 10 7 8, .p 4 2 4 2 32, .n 4 2 4 3 56, .p 4 2 4 4 8, .p 4 2 4 5 16,
   .n 4 2 4 6 16, .p 4 2 4 7 40, .n 4 2 4 8 24, .n 4 2 5 2 48, .p 4 2 5 3 128, .n 4 2 5 4 112,
   .p 4 2 5 6 112, .n 4 2 5 7 128, .p 4 2 5 8 48, .n 4 2 6 1 8, .n 4 2 6 3 40, .p 4 2 6 4 144,
   .n 4 2 6 5 72, .n 4 2 6 6 96, .p 4 2 6 7 104, .n 4 2 6 8 48, .p 4 2 6 9 16, .p 4 2 7 1 8,
   .p 4 2 7 2 16, .n 4 2 7 3 48, .p 4 2 7 4 16, .p 4 2 7 5 32, .n 4 2 7 6 80, .p 4 2 7 7 48,
   .p 4 2 7 8 48, .n 4 2 7 9 40, .p 4 2 8 3 16, .n 4 2 8 4 56, .p 4 2 8 5 24, .p 4 2 8 6 80,
   .n 4 2 8 7 64, .n 4 2 8 8 24, .p 4 2 8 9 24, .n 5 1 4 2 8, .p 5 1 4 3 16, .p 5 1 4 4 8,
   .n 5 1 4 5 32, .p 5 1 4 6 8, .p 5 1 4 7 16, .n 5 1 4 8 8, .n 5 1 6 1 8, .p 5 1 6 2 32,
   .n 5 1 6 3 32, .n 5 1 6 4 32, .p 5 1 6 5 80, .n 5 1 6 6 32, .n 5 1 6 7 32, .p 5 1 6 8 32,
   .n 5 1 6 9 8, .p 5 1 7 1 16, .n 5 1 7 2 32, .p 5 1 7 4 32, .n 5 1 7 5 32, .p 5 1 7 6 32,
   .n 5 1 7 8 32, .p 5 1 7 9 16, .n 5 1 8 2 8, .p 5 1 8 4 40, .n 5 1 8 5 16, .n 5 1 8 6 56,
   .p 5 1 8 7 32, .p 5 1 8 8 24, .n 5 1 8 9 16]

set_option maxRecDepth 65536 in
private theorem g2_det4_0 : fmDet 4 g2Sub4_0 = g2Val4_0 := by decide

private def g2Sub4_1 (r c : Fin 4) : List FM :=
  g2FM ⟨r.val + 2, by omega⟩ (match c.val with | 0 => ⟨0, by decide⟩ | 1 => ⟨1, by decide⟩ | 2 => ⟨2, by decide⟩ | _ => ⟨4, by decide⟩)

private def g2Val4_1 : List FM :=
  [.n 0 6 3 6 32, .p 0 6 4 6 128, .n 0 6 4 7 32, .n 0 6 5 6 160, .p 0 6 5 7 128, .n 0 6 6 7 160,
   .p 0 6 7 6 160, .n 0 6 8 6 128, .p 0 6 8 7 160, .p 0 6 9 6 32, .n 0 6 9 7 128, .p 0 6 10 7 32,
   .n 1 5 3 6 16, .p 1 5 4 4 16, .p 1 5 4 5 16, .p 1 5 4 6 96, .n 1 5 4 7 64, .n 1 5 4 8 16,
   .p 1 5 5 3 16, .n 1 5 5 4 32, .n 1 5 5 5 32, .n 1 5 5 6 208, .p 1 5 5 7 176, .p 1 5 5 8 64,
   .n 1 5 6 3 32, .n 1 5 6 4 64, .n 1 5 6 5 16, .p 1 5 6 6 224, .n 1 5 6 7 96, .n 1 5 6 8 96,
   .n 1 5 7 3 32, .p 1 5 7 4 256, .p 1 5 7 5 64, .n 1 5 7 6 176, .n 1 5 7 7 96, .p 1 5 7 8 64,
   .p 1 5 8 3 128, .n 1 5 8 4 304, .n 1 5 8 5 16, .p 1 5 8 6 160, .p 1 5 8 7 64, .n 1 5 8 8 16,
   .n 1 5 9 3 112, .p 1 5 9 4 160, .n 1 5 9 5 32, .n 1 5 9 6 112, .p 1 5 9 7 48, .p 1 5 10 3 32,
   .n 1 5 10 4 32, .p 1 5 10 5 16, .p 1 5 10 6 32, .n 1 5 10 7 32, .p 2 4 4 4 8, .p 2 4 4 5 40,
   .n 2 4 4 6 32, .p 2 4 4 7 24, .n 2 4 4 8 40, .n 2 4 5 2 16, .n 2 4 5 3 8, .p 2 4 5 4 16,
   .n 2 4 5 5 80, .p 2 4 5 6 96, .n 2 4 5 7 168, .p 2 4 5 8 160, .p 2 4 6 2 48, .n 2 4 6 3 16,
   .n 2 4 6 4 144, .n 2 4 6 5 24, .p 2 4 6 6 144, .p 2 4 6 7 232, .n 2 4 6 8 240, .n 2 4 7 2 48,
   .p 2 4 7 3 32, .p 2 4 7 4 352, .p 2 4 7 5 128, .n 2 4 7 6 720, .p 2 4 7 7 96, .p 2 4 7 8 160,
   .p 2 4 8 2 16, .p 2 4 8 3 80, .n 2 4 8 4 472, .n 2 4 8 5 40, .p 2 4 8 6 816, .n 2 4 8 7 360,
   .n 2 4 8 8 40, .n 2 4 9 3 152, .p 2 4 9 4 336, .n 2 4 9 5 48, .n 2 4 9 6 336, .p 2 4 9 7 200,
   .p 2 4 10 3 64, .n 2 4 10 4 96, .p 2 4 10 5 24, .p 2 4 10 6 32, .n 2 4 10 7 24, .n 3 3 4 4 8,
   .p 3 3 4 5 8, .n 3 3 4 6 24, .p 3 3 4 7 56, .n 3 3 4 8 32, .p 3 3 5 2 32, .n 3 3 5 3 64,
   .p 3 3 5 4 32, .n 3 3 5 5 32, .p 3 3 5 6 160, .n 3 3 5 7 224, .p 3 3 5 8 96, .n 3 3 6 2 88,
   .p 3 3 6 3 96, .p 3 3 6 4 32, .n 3 3 6 6 112, .p 3 3 6 7 152, .n 3 3 6 8 88, .p 3 3 6 9 8,
   .p 3 3 7 2 80, .p 3 3 7 3 128, .n 3 3 7 4 336, .p 3 3 7 5 112, .n 3 3 7 6 144, .p 3 3 7 7 160,
   .p 3 3 7 8 16, .n 3 3 7 9 16, .n 3 3 8 2 24, .n 3 3 8 3 248, .p 3 3 8 4 416, .n 3 3 8 5 80,
   .p 3 3 8 6 48, .n 3 3 8 7 128, .p 3 3 8 8 8, .p 3 3 8 9 8, .p 3 3 9 3 48, .n 3 3 9 4 64,
   .n 3 3 9 5 64, .p 3 3 9 6 128, .n 3 3 9 7 48, .p 3 3 10 3 40, .n 3 3 10 4 72, .p 3 3 10 5 56,
   .n 3 3 10 6 56, .p 3 3 10 7 32, .p 4 2 4 4 8, .n 4 2 4 5 16, .p 4 2 4 7 16, .n 4 2 4 8 8,
   .n 4 2 5 2 16, .p 4 2 5 3 32, .n 4 2 5 4 16, .p 4 2 5 6 16, .n 4 2 5 7 32, .p 4 2 5 8 16,
   .n 4 2 6 3 16, .p 4 2 6 5 72, .n 4 2 6 6 48, .n 4 2 6 7 48, .p 4 2 6 8 48, .n 4 2 6 9 8,
   .p 4 2 7 1 8, .p 4 2 7 2 48, .p 4 2 7 3 16, .n 4 2 7 4 208, .n 4 2 7 5 32, .p 4 2 7 6 272,
   .n 4 2 7 7 16, .n 4 2 7 8 112, .p 4 2 7 9 24, .n 4 2 8 1 8, .n 4 2 8 2 32, .n 4 2 8 3 136,
   .p 4 2 8 4 424, .n 4 2 8 5 24, .n 4 2 8 6 448, .p 4 2 8 7 184, .p 4 2 8 8 56, .n 4 2 8 9 16,
   .p 4 2 9 3 96, .n 4 2 9 4 192, .p 4 2 9 6 192, .n 4 2 9 7 96, .p 4 2 10 3 8, .n 4 2 10 4 16,
   .p 4 2 10 6 16, .n 4 2 10 7 8, .p 5 1 6 2 16, .n 5 1 6 3 32, .n 5 1 6 4 16, .p 5 1 6 5 64,
   .n 5 1 6 6 16, .n 5 1 6 7 32, .p 5 1 6 8 16, .p 5 1 7 1 16, .n 5 1 7 2 32, .p 5 1 7 4 32,
   .n 5 1 7 5 32, .p 5 1 7 6 32, .n 5 1 7 8 32, .p 5 1 7 9 16, .n 5 1 8 1 24, .p 5 1 8 2 32,
   .p 5 1 8 3 48, .n 5 1 8 4 64, .n 5 1 8 5 32, .p 5 1 8 6 32, .p 5 1 8 7 16, .n 5 1 8 9 8,
   .n 6 0 8 1 16, .p 6 0 8 2 32, .p 6 0 8 3 32, .n 6 0 8 4 96, .p 6 0 8 6 96, .n 6 0 8 7 32,
   .n 6 0 8 8 32, .p 6 0 8 9 16]

set_option maxRecDepth 65536 in
private theorem g2_det4_1 : fmDet 4 g2Sub4_1 = g2Val4_1 := by decide

private def g2Sub4_2 (r c : Fin 4) : List FM :=
  g2FM ⟨r.val + 2, by omega⟩ (match c.val with | 0 => ⟨0, by decide⟩ | 1 => ⟨1, by decide⟩ | 2 => ⟨2, by decide⟩ | _ => ⟨5, by decide⟩)

private def g2Val4_2 : List FM :=
  [.n 0 7 3 6 64, .p 0 7 4 6 256, .n 0 7 4 7 64, .n 0 7 5 6 320, .p 0 7 5 7 256, .n 0 7 6 7 320,
   .p 0 7 7 6 320, .n 0 7 8 6 256, .p 0 7 8 7 320, .p 0 7 9 6 64, .n 0 7 9 7 256, .p 0 7 10 7 64,
   .n 1 6 3 6 32, .p 1 6 4 5 32, .p 1 6 4 6 224, .n 1 6 4 7 128, .n 1 6 4 8 32, .n 1 6 5 5 64,
   .n 1 6 5 6 480, .p 1 6 5 7 384, .p 1 6 5 8 128, .n 1 6 6 4 32, .n 1 6 6 5 32, .p 1 6 6 6 352,
   .n 1 6 6 7 256, .n 1 6 6 8 192, .p 1 6 7 4 128, .p 1 6 7 5 128, .p 1 6 7 6 32, .n 1 6 7 7 256,
   .p 1 6 7 8 128, .n 1 6 8 4 192, .n 1 6 8 5 32, .n 1 6 8 6 96, .p 1 6 8 7 384, .n 1 6 8 8 32,
   .p 1 6 9 4 128, .n 1 6 9 5 64, .n 1 6 9 6 32, .n 1 6 9 7 128, .n 1 6 10 4 32, .p 1 6 10 5 32,
   .p 1 6 10 6 32, .p 2 5 4 4 16, .p 2 5 4 5 80, .n 2 5 4 6 64, .p 2 5 4 7 48, .n 2 5 4 8 80,
   .p 2 5 5 3 16, .n 2 5 5 4 32, .n 2 5 5 5 160, .p 2 5 5 6 128, .n 2 5 5 7 304, .p 2 5 5 8 352,
   .n 2 5 6 3 32, .n 2 5 6 4 160, .n 2 5 6 5 112, .p 2 5 6 6 416, .p 2 5 6 7 464, .n 2 5 6 8 576,
   .n 2 5 7 3 64, .p 2 5 7 4 672, .p 2 5 7 5 384, .n 2 5 7 6 1472, .p 2 5 7 7 64, .p 2 5 7 8 416,
   .p 2 5 8 3 224, .n 2 5 8 4 976, .n 2 5 8 5 80, .p 2 5 8 6 1600, .n 2 5 8 7 656, .n 2 5 8 8 112,
   .n 2 5 9 3 208, .p 2 5 9 4 640, .n 2 5 9 5 224, .n 2 5 9 6 704, .p 2 5 9 7 496, .p 2 5 10 3 64,
   .n 2 5 10 4 160, .p 2 5 10 5 112, .p 2 5 10 6 96, .n 2 5 10 7 112, .n 3 4 4 4 8, .p 3 4 4 5 16,
   .n 3 4 4 6 56, .p 3 4 4 7 112, .n 3 4 4 8 64, .n 3 4 5 2 16, .n 3 4 5 3 8, .p 3 4 5 4 16,
   .n 3 4 5 5 64, .p 3 4 5 6 368, .n 3 4 5 7 568, .p 3 4 5 8 272, .p 3 4 6 2 64, .n 3 4 6 3 16,
   .n 3 4 6 4 152, .n 3 4 6 6 8, .p 3 4 6 7 512, .n 3 4 6 8 416, .p 3 4 6 9 16, .n 3 4 7 2 80,
   .p 3 4 7 3 16, .p 3 4 7 4 496, .p 3 4 7 5 224, .n 3 4 7 6 1456, .p 3 4 7 7 560, .p 3 4 7 8 272,
   .n 3 4 7 9 32, .p 3 4 8 2 32, .p 3 4 8 3 176, .n 3 4 8 4 824, .n 3 4 8 5 160, .p 3 4 8 6 1752,
   .n 3 4 8 7 928, .n 3 4 8 8 64, .p 3 4 8 9 16, .n 3 4 9 3 296, .p 3 4 9 4 736, .n 3 4 9 5 128,
   .n 3 4 9 6 608, .p 3 4 9 7 296, .p 3 4 10 3 128, .n 3 4 10 4 264, .p 3 4 10 5 112, .p 3 4 10 6 8,
   .p 3 4 10 7 16, .p 4 3 4 4 16, .n 4 3 4 5 32, .p 4 3 4 7 32, .n 4 3 4 8 16, .p 4 3 5 2 32,
   .n 4 3 5 3 64, .p 4 3 5 4 32, .p 4 3 5 6 96, .n 4 3 5 7 192, .p 4 3 5 8 96, .n 4 3 6 2 112,
   .p 4 3 6 3 96, .n 4 3 6 4 16, .p 4 3 6 5 144, .n 4 3 6 6 112, .p 4 3 6 7 32, .n 4 3 6 8 16,
   .n 4 3 6 9 16, .p 4 3 7 2 128, .p 4 3 7 3 256, .n 4 3 7 4 704, .p 4 3 7 5 32, .p 4 3 7 6 256,
   .p 4 3 7 7 192, .n 4 3 7 8 192, .p 4 3 7 9 32, .n 4 3 8 2 48, .n 4 3 8 3 464, .p 4 3 8 4 1088,
   .n 4 3 8 5 208, .n 4 3 8 6 656, .p 4 3 8 7 176, .p 4 3 8 8 128, .n 4 3 8 9 16, .p 4 3 9 3 96,
   .n 4 3 9 4 256, .n 4 3 9 5 64, .p 4 3 9 6 512, .n 4 3 9 7 288, .p 4 3 10 3 80, .n 4 3 10 4 160,
   .p 4 3 10 5 128, .n 4 3 10 6 96, .p 4 3 10 7 48, .n 5 2 5 2 16, .p 5 2 5 3 32, .n 5 2 5 4 16,
   .p 5 2 5 6 16, .n 5 2 5 7 32, .p 5 2 5 8 16, .p 5 2 6 2 8, .n 5 2 6 3 16, .n 5 2 6 4 56,
   .p 5 2 6 5 128, .n 5 2 6 6 8, .n 5 2 6 7 112, .p 5 2 6 8 56, .p 5 2 7 1 8, .p 5 2 7 2 80,
   .p 5 2 7 3 80, .n 5 2 7 4 432, .n 5 2 7 5 64, .p 5 2 7 6 560, .n 5 2 7 7 80, .n 5 2 7 8 208,
   .p 5 2 7 9 56, .n 5 2 8 1 16, .n 5 2 8 2 56, .n 5 2 8 3 288, .p 5 2 8 4 872, .n 5 2 8 5 64,
   .n 5 2 8 6 936, .p 5 2 8 7 416, .p 5 2 8 8 120, .n 5 2 8 9 48, .p 5 2 9 3 192, .n 5 2 9 4 384,
   .p 5 2 9 6 384, .n 5 2 9 7 192, .p 5 2 10 3 16, .n 5 2 10 4 32, .p 5 2 10 6 32, .n 5 2 10 7 16,
   .p 6 1 6 2 16, .n 6 1 6 3 32, .n 6 1 6 4 16, .p 6 1 6 5 64, .n 6 1 6 6 16, .n 6 1 6 7 32,
   .p 6 1 6 8 16, .p 6 1 7 1 16, .n 6 1 7 2 32, .p 6 1 7 4 32, .n 6 1 7 5 32, .p 6 1 7 6 32,
   .n 6 1 7 8 32, .p 6 1 7 9 16, .n 6 1 8 1 48, .p 6 1 8 2 80, .p 6 1 8 3 96, .n 6 1 8 4 208,
   .n 6 1 8 5 32, .p 6 1 8 6 176, .n 6 1 8 7 32, .n 6 1 8 8 48, .p 6 1 8 9 16, .n 7 0 8 1 32,
   .p 7 0 8 2 64, .p 7 0 8 3 64, .n 7 0 8 4 192, .p 7 0 8 6 192, .n 7 0 8 7 64, .n 7 0 8 8 64,
   .p 7 0 8 9 32]

set_option maxRecDepth 65536 in
private theorem g2_det4_2 : fmDet 4 g2Sub4_2 = g2Val4_2 := by decide

private def g2Sub4_3 (r c : Fin 4) : List FM :=
  g2FM ⟨r.val + 2, by omega⟩ (match c.val with | 0 => ⟨0, by decide⟩ | 1 => ⟨1, by decide⟩ | 2 => ⟨3, by decide⟩ | _ => ⟨4, by decide⟩)

private def g2Val4_3 : List FM :=
  [.n 0 5 3 6 32, .p 0 5 4 6 128, .n 0 5 5 6 128, .n 0 5 6 6 128, .p 0 5 7 6 320, .n 0 5 8 6 128,
   .n 0 5 9 6 128, .p 0 5 10 6 128, .n 0 5 11 6 32, .p 1 4 4 5 32, .n 1 4 4 7 32, .n 1 4 5 5 64,
   .p 1 4 5 7 64, .n 1 4 6 4 32, .n 1 4 6 5 64, .p 1 4 6 7 64, .p 1 4 6 8 32, .p 1 4 7 4 128,
   .p 1 4 7 5 192, .n 1 4 7 7 192, .n 1 4 7 8 128, .n 1 4 8 4 160, .p 1 4 8 8 160, .n 1 4 9 5 192,
   .p 1 4 9 7 192, .p 1 4 10 4 160, .p 1 4 10 5 64, .n 1 4 10 7 64, .n 1 4 10 8 160, .n 1 4 11 4 128,
   .p 1 4 11 5 64, .n 1 4 11 7 64, .p 1 4 11 8 128, .p 1 4 12 4 32, .n 1 4 12 5 32, .p 1 4 12 7 32,
   .n 1 4 12 8 32, .p 2 3 4 5 16, .n 2 3 4 6 32, .p 2 3 4 7 16, .n 2 3 5 2 8, .p 2 3 5 3 16,
   .n 2 3 5 5 48, .p 2 3 5 6 80, .n 2 3 5 7 48, .p 2 3 5 9 16, .n 2 3 5 10 8, .p 2 3 6 2 32,
   .n 2 3 6 3 32, .n 2 3 6 4 32, .n 2 3 6 5 32, .p 2 3 6 6 128, .n 2 3 6 7 32, .n 2 3 6 8 32,
   .n 2 3 6 9 32, .p 2 3 6 10 32, .n 2 3 7 2 48, .n 2 3 7 3 16, .p 2 3 7 4 128, .p 2 3 7 5 176,
   .n 2 3 7 6 480, .p 2 3 7 7 176, .p 2 3 7 8 128, .n 2 3 7 9 16, .n 2 3 7 10 48, .p 2 3 8 2 32,
   .p 2 3 8 3 64, .n 2 3 8 4 160, .n 2 3 8 5 32, .p 2 3 8 6 192, .n 2 3 8 7 32, .n 2 3 8 8 160,
   .p 2 3 8 9 64, .p 2 3 8 10 32, .n 2 3 9 2 8, .n 2 3 9 3 16, .n 2 3 9 5 208, .p 2 3 9 6 464,
   .n 2 3 9 7 208, .n 2 3 9 9 16, .n 2 3 9 10 8, .n 2 3 10 3 32, .p 2 3 10 4 160, .p 2 3 10 5 96,
   .n 2 3 10 6 448, .p 2 3 10 7 96, .p 2 3 10 8 160, .n 2 3 10 9 32, .p 2 3 11 3 16, .n 2 3 11 4 128,
   .p 2 3 11 5 80, .p 2 3 11 6 64, .p 2 3 11 7 80, .n 2 3 11 8 128, .p 2 3 11 9 16, .p 2 3 12 4 32,
   .n 2 3 12 5 48, .p 2 3 12 6 32, .n 2 3 12 7 48, .p 2 3 12 8 32, .p 3 2 4 4 8, .n 3 2 4 5 16,
   .p 3 2 4 7 16, .n 3 2 4 8 8, .p 3 2 5 2 16, .n 3 2 5 3 40, .p 3 2 5 5 56, .n 3 2 5 7 56,
   .p 3 2 5 9 40, .n 3 2 5 10 16, .n 3 2 6 2 64, .p 3 2 6 3 64, .p 3 2 6 5 64, .n 3 2 6 7 64,
   .n 3 2 6 9 64, .p 3 2 6 10 64, .p 3 2 7 2 96, .p 3 2 7 3 24, .n 3 2 7 4 128, .n 3 2 7 5 200,
   .p 3 2 7 7 200, .p 3 2 7 8 128, .n 3 2 7 9 24, .n 3 2 7 10 96, .n 3 2 8 2 64, .n 3 2 8 3 64,
   .p 3 2 8 4 240, .n 3 2 8 5 32, .p 3 2 8 7 32, .n 3 2 8 8 240, .p 3 2 8 9 64, .p 3 2 8 10 64,
   .p 3 2 9 2 16, .p 3 2 9 3 8, .n 3 2 9 4 128, .p 3 2 9 5 168, .n 3 2 9 7 168, .p 3 2 9 8 128,
   .n 3 2 9 9 8, .n 3 2 9 10 16, .p 3 2 11 3 8, .n 3 2 11 5 24, .p 3 2 11 7 24, .n 3 2 11 9 8,
   .p 3 2 12 4 8, .n 3 2 12 5 16, .p 3 2 12 7 16, .n 3 2 12 8 8, .n 4 1 5 2 8, .p 4 1 5 3 16,
   .n 4 1 5 5 16, .p 4 1 5 6 16, .n 4 1 5 7 16, .p 4 1 5 9 16, .n 4 1 5 10 8, .p 4 1 6 2 24,
   .n 4 1 6 3 32, .n 4 1 6 4 32, .p 4 1 6 5 32, .p 4 1 6 6 16, .p 4 1 6 7 32, .n 4 1 6 8 32,
   .n 4 1 6 9 32, .p 4 1 6 10 24, .p 4 1 7 1 8, .n 4 1 7 2 16, .p 4 1 7 3 40, .n 4 1 7 4 64,
   .n 4 1 7 5 48, .p 4 1 7 6 160, .n 4 1 7 7 48, .n 4 1 7 8 64, .p 4 1 7 9 40, .n 4 1 7 10 16,
   .p 4 1 7 11 8, .n 4 1 8 1 16, .n 4 1 8 3 16, .p 4 1 8 4 128, .p 4 1 8 5 32, .n 4 1 8 6 256,
   .p 4 1 8 7 32, .p 4 1 8 8 128, .n 4 1 8 9 16, .n 4 1 8 11 16, .p 4 1 9 1 8, .n 4 1 9 2 8,
   .n 4 1 9 3 40, .p 4 1 9 4 64, .p 4 1 9 5 32, .n 4 1 9 6 112, .p 4 1 9 7 32, .p 4 1 9 8 64,
   .n 4 1 9 9 40, .n 4 1 9 10 8, .p 4 1 9 11 8, .p 4 1 10 2 8, .p 4 1 10 3 32, .n 4 1 10 4 96,
   .n 4 1 10 5 32, .p 4 1 10 6 176, .n 4 1 10 7 32, .n 4 1 10 8 96, .p 4 1 10 9 32, .p 4 1 10 10 8,
   .n 5 0 8 1 16, .p 5 0 8 2 32, .p 5 0 8 3 16, .n 5 0 8 4 64, .p 5 0 8 5 32, .n 5 0 8 7 32,
   .p 5 0 8 8 64, .n 5 0 8 9 16, .n 5 0 8 10 32, .p 5 0 8 11 16, .p 5 0 9 1 16, .n 5 0 9 2 32,
   .n 5 0 9 3 16, .p 5 0 9 4 64, .n 5 0 9 5 32, .p 5 0 9 7 32, .n 5 0 9 8 64, .p 5 0 9 9 16,
   .p 5 0 9 10 32, .n 5 0 9 11 16]

set_option maxRecDepth 65536 in
private theorem g2_det4_3 : fmDet 4 g2Sub4_3 = g2Val4_3 := by decide

private def g2Sub4_4 (r c : Fin 4) : List FM :=
  g2FM ⟨r.val + 2, by omega⟩ (match c.val with | 0 => ⟨0, by decide⟩ | 1 => ⟨1, by decide⟩ | 2 => ⟨3, by decide⟩ | _ => ⟨5, by decide⟩)

private def g2Val4_4 : List FM :=
  [.n 0 6 3 6 64, .p 0 6 4 6 224, .n 0 6 5 6 192, .n 0 6 6 6 160, .n 0 6 6 8 32, .p 0 6 7 6 320,
   .p 0 6 7 8 128, .n 0 6 8 6 96, .n 0 6 8 8 160, .n 0 6 9 6 64, .p 0 6 10 6 32, .p 0 6 10 8 160,
   .n 0 6 11 8 128, .p 0 6 12 8 32, .p 1 5 4 5 64, .p 1 5 4 6 64, .n 1 5 4 7 64, .n 1 5 4 8 16,
   .n 1 5 5 5 96, .n 1 5 5 6 144, .p 1 5 5 7 128, .p 1 5 5 8 32, .n 1 5 5 9 32, .p 1 5 5 10 16,
   .n 1 5 6 4 32, .n 1 5 6 5 128, .n 1 5 6 6 80, .p 1 5 6 7 64, .p 1 5 6 8 80, .p 1 5 6 9 64,
   .n 1 5 6 10 64, .p 1 5 7 4 112, .p 1 5 7 5 224, .p 1 5 7 6 384, .n 1 5 7 7 256, .n 1 5 7 8 304,
   .p 1 5 7 9 32, .p 1 5 7 10 96, .n 1 5 8 4 128, .p 1 5 8 5 64, .n 1 5 8 6 112, .p 1 5 8 7 64,
   .p 1 5 8 8 304, .n 1 5 8 9 128, .n 1 5 8 10 64, .p 1 5 9 4 32, .n 1 5 9 5 160, .n 1 5 9 6 336,
   .p 1 5 9 7 128, .p 1 5 9 9 32, .p 1 5 9 10 16, .p 1 5 10 4 32, .p 1 5 10 6 272, .n 1 5 10 7 64,
   .n 1 5 10 8 208, .p 1 5 10 9 64, .n 1 5 11 4 16, .p 1 5 11 5 32, .n 1 5 11 6 32, .p 1 5 11 8 144,
   .n 1 5 11 9 32, .n 1 5 12 6 16, .n 1 5 12 8 32, .n 2 4 4 4 16, .p 2 4 4 5 32, .n 2 4 4 6 56,
   .p 2 4 4 7 32, .p 2 4 4 8 8, .p 2 4 5 4 16, .n 2 4 5 5 96, .p 2 4 5 6 136, .n 2 4 5 7 64,
   .p 2 4 5 8 32, .n 2 4 5 9 32, .p 2 4 5 10 8, .n 2 4 6 4 64, .n 2 4 6 5 128, .p 2 4 6 6 192,
   .p 2 4 6 7 32, .n 2 4 6 8 16, .p 2 4 6 9 32, .n 2 4 6 10 48, .p 2 4 7 4 344, .p 2 4 7 5 416,
   .n 2 4 7 6 592, .n 2 4 7 8 296, .p 2 4 7 9 32, .p 2 4 7 10 96, .n 2 4 8 4 480, .p 2 4 8 5 32,
   .p 2 4 8 6 144, .n 2 4 8 7 96, .p 2 4 8 8 480, .n 2 4 8 10 80, .p 2 4 9 4 48, .n 2 4 9 5 480,
   .p 2 4 9 6 344, .p 2 4 9 7 192, .n 2 4 9 8 96, .n 2 4 9 9 32, .p 2 4 9 10 24, .p 2 4 10 4 368,
   .p 2 4 10 5 128, .n 2 4 10 6 144, .n 2 4 10 7 32, .n 2 4 10 8 288, .n 2 4 10 9 32, .n 2 4 11 4 280,
   .p 2 4 11 5 160, .n 2 4 11 6 16, .n 2 4 11 7 128, .p 2 4 11 8 232, .p 2 4 11 9 32, .p 2 4 12 4 64,
   .n 2 4 12 5 64, .n 2 4 12 6 8, .p 2 4 12 7 64, .n 2 4 12 8 56, .p 3 3 4 4 24, .n 3 3 4 5 32,
   .n 3 3 4 6 16, .p 3 3 4 7 32, .n 3 3 4 8 8, .n 3 3 5 2 8, .p 3 3 5 3 16, .n 3 3 5 4 24,
   .p 3 3 5 5 24, .p 3 3 5 6 80, .n 3 3 5 7 144, .n 3 3 5 8 8, .p 3 3 5 9 104, .n 3 3 5 10 40,
   .p 3 3 6 2 48, .n 3 3 6 3 32, .n 3 3 6 4 80, .p 3 3 6 5 96, .p 3 3 6 6 88, .n 3 3 6 7 96,
   .n 3 3 6 8 32, .n 3 3 6 9 160, .p 3 3 6 10 168, .n 3 3 7 2 88, .n 3 3 7 3 48, .p 3 3 7 4 152,
   .p 3 3 7 5 88, .n 3 3 7 6 672, .p 3 3 7 7 512, .p 3 3 7 8 488, .n 3 3 7 9 152, .n 3 3 7 10 264,
   .n 3 3 7 11 16, .p 3 3 8 2 64, .p 3 3 8 3 128, .n 3 3 8 4 104, .n 3 3 8 5 160, .p 3 3 8 6 352,
   .n 3 3 8 7 96, .n 3 3 8 8 680, .p 3 3 8 9 288, .p 3 3 8 10 176, .p 3 3 8 11 32, .n 3 3 9 2 16,
   .n 3 3 9 3 32, .n 3 3 9 4 88, .n 3 3 9 5 280, .p 3 3 9 6 912, .n 3 3 9 7 464, .n 3 3 9 8 8,
   .p 3 3 9 9 24, .n 3 3 9 10 32, .n 3 3 9 11 16, .n 3 3 10 3 64, .p 3 3 10 4 320, .p 3 3 10 5 192,
   .n 3 3 10 6 936, .p 3 3 10 7 192, .p 3 3 10 8 432, .n 3 3 10 9 128, .n 3 3 10 10 8, .p 3 3 11 3 32,
   .n 3 3 11 4 264, .p 3 3 11 5 168, .p 3 3 11 6 128, .p 3 3 11 7 160, .n 3 3 11 8 248, .p 3 3 11 9 24,
   .p 3 3 12 4 64, .n 3 3 12 5 96, .p 3 3 12 6 64, .n 3 3 12 7 96, .p 3 3 12 8 64, .p 4 2 5 2 16,
   .n 4 2 5 3 40, .p 4 2 5 4 8, .p 4 2 5 5 40, .p 4 2 5 6 24, .n 4 2 5 7 88, .n 4 2 5 8 8,
   .p 4 2 5 9 88, .n 4 2 5 10 40, .n 4 2 6 2 88, .p 4 2 6 3 64, .p 4 2 6 5 128, .n 4 2 6 7 32,
   .n 4 2 6 8 64, .n 4 2 6 9 160, .p 4 2 6 10 152, .p 4 2 7 2 168, .p 4 2 7 3 72, .n 4 2 7 4 320,
   .n 4 2 7 5 336, .p 4 2 7 6 176, .p 4 2 7 7 224, .p 4 2 7 8 192, .p 4 2 7 9 16, .n 4 2 7 10 216,
   .p 4 2 7 11 24, .n 4 2 8 2 120, .n 4 2 8 3 128, .p 4 2 8 4 544, .n 4 2 8 5 96, .n 4 2 8 6 192,
   .p 4 2 8 7 160, .n 4 2 8 8 416, .p 4 2 8 9 128, .p 4 2 8 10 184, .n 4 2 8 11 64, .p 4 2 9 2 24,
   .p 4 2 9 3 16, .n 4 2 9 4 232, .p 4 2 9 5 344, .n 4 2 9 6 72, .n 4 2 9 7 312, .p 4 2 9 8 360,
   .n 4 2 9 9 88, .n 4 2 9 10 80, .p 4 2 9 11 40, .n 4 2 10 4 16, .p 4 2 10 6 64, .n 4 2 10 7 32,
   .n 4 2 10 8 48, .p 4 2 10 9 32, .p 4 2 11 3 16, .n 4 2 11 5 48, .p 4 2 11 7 48, .n 4 2 11 9 16,
   .p 4 2 12 4 16, .n 4 2 12 5 32, .p 4 2 12 7 32, .n 4 2 12 8 16, .n 5 1 5 2 8, .p 5 1 5 3 16,
   .n 5 1 5 5 16, .p 5 1 5 6 16, .n 5 1 5 7 16, .p 5 1 5 9 16, .n 5 1 5 10 8, .p 5 1 6 2 32,
   .n 5 1 6 3 32, .n 5 1 6 4 64, .p 5 1 6 5 32, .p 5 1 6 6 64, .p 5 1 6 7 32, .n 5 1 6 8 64,
   .n 5 1 6 9 32, .p 5 1 6 10 32, .p 5 1 7 1 8, .n 5 1 7 2 16, .p 5 1 7 3 72, .n 5 1 7 4 128,
   .n 5 1 7 5 80, .p 5 1 7 6 288, .n 5 1 7 7 80, .n 5 1 7 8 128, .p 5 1 7 9 72, .n 5 1 7 10 16,
   .p 5 1 7 11 8, .n 5 1 8 1 32, .p 5 1 8 2 16, .n 5 1 8 3 32, .p 5 1 8 4 192, .p 5 1 8 5 96,
   .n 5 1 8 6 480, .p 5 1 8 7 32, .p 5 1 8 8 320, .n 5 1 8 9 64, .n 5 1 8 10 48, .p 5 1 9 1 16,
   .n 5 1 9 2 24, .n 5 1 9 3 80, .p 5 1 9 4 160, .p 5 1 9 5 48, .n 5 1 9 6 240, .p 5 1 9 7 80,
   .p 5 1 9 8 96, .n 5 1 9 9 64, .p 5 1 9 10 8, .p 5 1 10 2 16, .p 5 1 10 3 64, .n 5 1 10 4 192,
   .n 5 1 10 5 64, .p 5 1 10 6 352, .n 5 1 10 7 64, .n 5 1 10 8 192, .p 5 1 10 9 64, .p 5 1 10 10 16,
   .n 6 0 8 1 32, .p 6 0 8 2 64, .p 6 0 8 3 32, .n 6 0 8 4 128, .p 6 0 8 5 64, .n 6 0 8 7 64,
   .p 6 0 8 8 128, .n 6 0 8 9 32, .n 6 0 8 10 64, .p 6 0 8 11 32, .p 6 0 9 1 32, .n 6 0 9 2 64,
   .n 6 0 9 3 32, .p 6 0 9 4 128, .n 6 0 9 5 64, .p 6 0 9 7 64, .n 6 0 9 8 128, .p 6 0 9 9 32,
   .p 6 0 9 10 64, .n 6 0 9 11 32]

set_option maxRecDepth 65536 in
private theorem g2_det4_4 : fmDet 4 g2Sub4_4 = g2Val4_4 := by decide

private def g2Sub4_5 (r c : Fin 4) : List FM :=
  g2FM ⟨r.val + 2, by omega⟩ (match c.val with | 0 => ⟨0, by decide⟩ | 1 => ⟨1, by decide⟩ | 2 => ⟨4, by decide⟩ | _ => ⟨5, by decide⟩)

private def g2Val4_5 : List FM :=
  [.p 0 6 4 6 32, .n 0 6 5 6 64, .n 0 6 6 6 96, .p 0 6 6 8 32, .p 0 6 7 6 320, .n 0 6 7 8 128,
   .n 0 6 8 6 160, .p 0 6 8 8 160, .n 0 6 9 6 192, .p 0 6 10 6 224, .n 0 6 10 8 160, .n 0 6 11 6 64,
   .p 0 6 11 8 128, .n 0 6 12 8 32, .p 1 5 4 8 16, .n 1 5 5 5 32, .p 1 5 5 6 16, .n 1 5 5 8 32,
   .p 1 5 5 9 32, .n 1 5 5 10 16, .n 1 5 6 6 112, .p 1 5 6 7 64, .p 1 5 6 8 16, .n 1 5 6 9 64,
   .p 1 5 6 10 64, .p 1 5 7 4 16, .p 1 5 7 5 160, .p 1 5 7 6 256, .n 1 5 7 7 128, .n 1 5 7 8 80,
   .n 1 5 7 9 32, .n 1 5 7 10 96, .n 1 5 8 4 32, .n 1 5 8 5 64, .n 1 5 8 6 208, .n 1 5 8 7 64,
   .p 1 5 8 8 176, .p 1 5 8 9 128, .p 1 5 8 10 64, .n 1 5 9 4 32, .n 1 5 9 5 224, .n 1 5 9 6 48,
   .p 1 5 9 7 256, .n 1 5 9 9 32, .n 1 5 9 10 16, .p 1 5 10 4 128, .p 1 5 10 5 128, .p 1 5 10 6 176,
   .n 1 5 10 7 64, .n 1 5 10 8 272, .n 1 5 10 9 64, .n 1 5 11 4 112, .p 1 5 11 5 96, .n 1 5 11 6 96,
   .n 1 5 11 7 128, .p 1 5 11 8 240, .p 1 5 11 9 32, .p 1 5 12 4 32, .n 1 5 12 5 64, .p 1 5 12 6 16,
   .p 1 5 12 7 64, .n 1 5 12 8 64, .n 2 4 4 6 8, .p 2 4 4 8 8, .p 2 4 5 4 16, .n 2 4 5 5 32,
   .p 2 4 5 6 24, .n 2 4 5 8 64, .p 2 4 5 9 96, .n 2 4 5 10 40, .n 2 4 6 4 16, .p 2 4 6 6 64,
   .n 2 4 6 7 32, .n 2 4 6 8 32, .n 2 4 6 9 160, .p 2 4 6 10 176, .p 2 4 7 4 8, .p 2 4 7 5 224,
   .n 2 4 7 6 368, .p 2 4 7 7 64, .p 2 4 7 8 456, .n 2 4 7 9 96, .n 2 4 7 10 288, .n 2 4 8 4 48,
   .n 2 4 8 5 96, .p 2 4 8 6 240, .p 2 4 8 7 32, .n 2 4 8 8 592, .p 2 4 8 9 256, .p 2 4 8 10 208,
   .n 2 4 9 4 80, .n 2 4 9 5 416, .p 2 4 9 6 584, .n 2 4 9 7 128, .p 2 4 9 8 128, .n 2 4 9 9 32,
   .n 2 4 9 10 56, .p 2 4 10 4 352, .p 2 4 10 5 256, .n 2 4 10 6 752, .p 2 4 10 7 32, .p 2 4 10 8 208,
   .n 2 4 10 9 96, .n 2 4 11 4 328, .p 2 4 11 5 224, .p 2 4 11 6 144, .p 2 4 11 7 64, .n 2 4 11 8 136,
   .p 2 4 11 9 32, .p 2 4 12 4 96, .n 2 4 12 5 160, .p 2 4 12 6 72, .n 2 4 12 7 32, .p 2 4 12 8 24,
   .n 3 3 5 4 24, .p 3 3 5 5 56, .n 3 3 5 6 32, .n 3 3 5 8 40, .p 3 3 5 9 72, .n 3 3 5 10 32,
   .p 3 3 6 4 32, .p 3 3 6 6 40, .n 3 3 6 7 64, .n 3 3 6 8 16, .n 3 3 6 9 128, .p 3 3 6 10 136,
   .n 3 3 7 2 8, .p 3 3 7 4 56, .n 3 3 7 5 200, .n 3 3 7 6 64, .p 3 3 7 7 176, .p 3 3 7 8 232,
   .p 3 3 7 9 8, .n 3 3 7 10 216, .p 3 3 7 11 16, .p 3 3 8 2 16, .n 3 3 8 4 56, .p 3 3 8 5 32,
   .p 3 3 8 6 128, .p 3 3 8 7 96, .n 3 3 8 8 440, .p 3 3 8 9 96, .p 3 3 8 10 160, .n 3 3 8 11 32,
   .n 3 3 9 2 8, .p 3 3 9 3 16, .n 3 3 9 4 120, .p 3 3 9 5 72, .p 3 3 9 6 256, .n 3 3 9 7 416,
   .p 3 3 9 8 312, .n 3 3 9 9 72, .n 3 3 9 10 56, .p 3 3 9 11 16, .n 3 3 10 3 32, .p 3 3 10 4 240,
   .p 3 3 10 5 96, .n 3 3 10 6 568, .p 3 3 10 7 96, .p 3 3 10 8 128, .p 3 3 10 9 32, .p 3 3 10 10 8,
   .p 3 3 11 3 16, .n 3 3 11 4 200, .p 3 3 11 5 72, .p 3 3 11 6 160, .p 3 3 11 7 176, .n 3 3 11 8 216,
   .n 3 3 11 9 8, .p 3 3 12 4 72, .n 3 3 12 5 128, .p 3 3 12 6 80, .n 3 3 12 7 64, .p 3 3 12 8 40,
   .p 4 2 5 4 8, .n 4 2 5 5 16, .p 4 2 5 6 8, .n 4 2 5 8 8, .p 4 2 5 9 16, .n 4 2 5 10 8,
   .n 4 2 6 4 16, .p 4 2 6 6 32, .p 4 2 6 7 32, .n 4 2 6 8 48, .n 4 2 6 9 32, .p 4 2 6 10 32,
   .p 4 2 7 2 8, .p 4 2 7 4 16, .n 4 2 7 5 136, .p 4 2 7 6 144, .p 4 2 7 7 56, .n 4 2 7 8 144,
   .p 4 2 7 9 72, .n 4 2 7 10 24, .p 4 2 7 11 8, .n 4 2 8 2 24, .p 4 2 8 4 96, .p 4 2 8 5 96,
   .n 4 2 8 6 320, .n 4 2 8 7 32, .p 4 2 8 8 288, .n 4 2 8 9 64, .n 4 2 8 10 40, .p 4 2 9 2 8,
   .n 4 2 9 3 8, .n 4 2 9 4 72, .p 4 2 9 5 208, .n 4 2 9 6 152, .n 4 2 9 7 112, .p 4 2 9 8 200,
   .n 4 2 9 9 80, .p 4 2 9 10 16, .n 4 2 9 11 8, .p 4 2 10 2 8, .n 4 2 10 4 64, .n 4 2 10 5 64,
   .p 4 2 10 6 288, .n 4 2 10 7 32, .n 4 2 10 8 256, .p 4 2 10 9 96, .p 4 2 10 10 24, .p 4 2 11 3 8,
   .p 4 2 11 4 16, .n 4 2 11 5 56, .p 4 2 11 7 56, .n 4 2 11 8 16, .n 4 2 11 9 8, .p 4 2 12 4 16,
   .n 4 2 12 5 32, .p 4 2 12 7 32, .n 4 2 12 8 16, .n 5 1 8 2 16, .p 5 1 8 4 64, .p 5 1 8 5 32,
   .n 5 1 8 6 160, .n 5 1 8 7 32, .p 5 1 8 8 192, .n 5 1 8 9 32, .n 5 1 8 10 80, .p 5 1 8 11 32,
   .p 5 1 9 1 8, .n 5 1 9 2 16, .n 5 1 9 3 40, .p 5 1 9 4 96, .n 5 1 9 5 16, .n 5 1 9 6 64,
   .p 5 1 9 7 80, .n 5 1 9 8 96, .p 5 1 9 9 8, .p 5 1 9 10 80, .n 5 1 9 11 40, .p 5 1 10 2 16,
   .p 5 1 10 3 32, .n 5 1 10 4 128, .n 5 1 10 5 32, .p 5 1 10 6 224, .n 5 1 10 7 32, .n 5 1 10 8 128,
   .p 5 1 10 9 32, .p 5 1 10 10 16, .p 6 0 9 1 16, .n 6 0 9 2 32, .n 6 0 9 3 16, .p 6 0 9 4 64,
   .n 6 0 9 5 32, .p 6 0 9 7 32, .n 6 0 9 8 64, .p 6 0 9 9 16, .p 6 0 9 10 32, .n 6 0 9 11 16]

set_option maxRecDepth 65536 in
private theorem g2_det4_5 : fmDet 4 g2Sub4_5 = g2Val4_5 := by decide

private def g2Sub4_6 (r c : Fin 4) : List FM :=
  g2FM ⟨r.val + 2, by omega⟩ (match c.val with | 0 => ⟨0, by decide⟩ | 1 => ⟨2, by decide⟩ | 2 => ⟨3, by decide⟩ | _ => ⟨4, by decide⟩)

private def g2Val4_6 : List FM :=
  [.n 0 5 3 6 16, .p 0 5 4 6 48, .p 0 5 4 7 16, .n 0 5 5 6 16, .n 0 5 5 7 48, .n 0 5 6 6 80,
   .p 0 5 6 7 16, .p 0 5 7 6 80, .p 0 5 7 7 80, .p 0 5 8 6 16, .n 0 5 8 7 80, .n 0 5 9 6 48,
   .n 0 5 9 7 16, .p 0 5 10 6 16, .p 0 5 10 7 48, .n 0 5 11 7 16, .p 1 4 4 5 16, .n 1 4 4 6 16,
   .n 1 4 4 7 16, .p 1 4 4 8 16, .n 1 4 5 5 16, .p 1 4 5 6 48, .p 1 4 5 7 16, .n 1 4 5 8 48,
   .n 1 4 6 4 16, .n 1 4 6 5 48, .n 1 4 6 6 48, .p 1 4 6 7 48, .p 1 4 6 8 64, .p 1 4 7 4 48,
   .p 1 4 7 5 48, .p 1 4 7 6 16, .n 1 4 7 7 48, .n 1 4 7 8 64, .n 1 4 8 4 32, .p 1 4 8 5 48,
   .p 1 4 8 6 16, .n 1 4 8 7 48, .p 1 4 8 8 16, .n 1 4 9 4 32, .n 1 4 9 5 48, .n 1 4 9 6 48,
   .p 1 4 9 7 48, .p 1 4 9 8 80, .p 1 4 10 4 48, .n 1 4 10 5 16, .p 1 4 10 6 48, .p 1 4 10 7 16,
   .n 1 4 10 8 96, .n 1 4 11 4 16, .p 1 4 11 5 16, .n 1 4 11 6 16, .n 1 4 11 7 16, .p 1 4 11 8 32,
   .p 2 3 4 5 8, .n 2 3 4 6 8, .n 2 3 4 7 8, .p 2 3 4 8 8, .n 2 3 5 2 4, .p 2 3 5 3 8,
   .n 2 3 5 4 8, .n 2 3 5 5 8, .n 2 3 5 6 8, .p 2 3 5 7 48, .n 2 3 5 8 32, .p 2 3 5 9 16,
   .n 2 3 5 10 12, .p 2 3 6 2 12, .n 2 3 6 3 12, .p 2 3 6 4 8, .n 2 3 6 5 40, .p 2 3 6 6 88,
   .n 2 3 6 7 56, .n 2 3 6 8 16, .n 2 3 6 9 16, .p 2 3 6 10 36, .n 2 3 6 11 4, .n 2 3 7 2 12,
   .n 2 3 7 3 4, .p 2 3 7 4 16, .p 2 3 7 5 40, .n 2 3 7 6 48, .n 2 3 7 7 80, .p 2 3 7 8 152,
   .n 2 3 7 9 32, .n 2 3 7 10 44, .p 2 3 7 11 12, .p 2 3 8 2 4, .p 2 3 8 3 4, .p 2 3 8 5 56,
   .n 2 3 8 6 160, .p 2 3 8 7 176, .n 2 3 8 8 136, .p 2 3 8 9 32, .p 2 3 8 10 36, .n 2 3 8 11 12,
   .p 2 3 9 3 12, .n 2 3 9 4 56, .n 2 3 9 5 56, .p 2 3 9 6 176, .n 2 3 9 7 40, .n 2 3 9 8 32,
   .p 2 3 9 9 16, .n 2 3 9 10 24, .p 2 3 9 11 4, .n 2 3 10 3 8, .p 2 3 10 4 56, .n 2 3 10 5 24,
   .n 2 3 10 6 16, .n 2 3 10 7 80, .p 2 3 10 8 80, .n 2 3 10 9 16, .p 2 3 10 10 8, .n 2 3 11 4 16,
   .p 2 3 11 5 24, .n 2 3 11 6 24, .p 2 3 11 7 40, .n 2 3 11 8 24, .p 3 2 4 4 4, .n 3 2 4 5 8,
   .p 3 2 4 7 8, .n 3 2 4 8 4, .p 3 2 5 2 8, .n 3 2 5 3 20, .p 3 2 5 4 16, .p 3 2 5 5 12,
   .n 3 2 5 6 20, .n 3 2 5 7 20, .p 3 2 5 8 16, .p 3 2 5 9 28, .n 3 2 5 10 20, .n 3 2 6 2 24,
   .p 3 2 6 3 24, .n 3 2 6 4 24, .p 3 2 6 5 52, .p 3 2 6 6 36, .n 3 2 6 7 52, .n 3 2 6 8 40,
   .n 3 2 6 9 12, .p 3 2 6 10 52, .n 3 2 6 11 12, .p 3 2 7 2 24, .p 3 2 7 3 12, .n 3 2 7 4 44,
   .n 3 2 7 5 40, .n 3 2 7 6 16, .p 3 2 7 7 48, .p 3 2 7 8 76, .n 3 2 7 9 32, .n 3 2 7 10 40,
   .p 3 2 7 11 12, .n 3 2 8 2 8, .n 3 2 8 3 20, .p 3 2 8 4 76, .n 3 2 8 5 56, .n 3 2 8 6 16,
   .p 3 2 8 7 64, .n 3 2 8 8 44, .n 3 2 8 10 8, .p 3 2 8 11 12, .p 3 2 9 3 8, .n 3 2 9 4 32,
   .p 3 2 9 5 20, .p 3 2 9 6 36, .n 3 2 9 7 20, .n 3 2 9 8 32, .p 3 2 9 9 4, .p 3 2 9 10 28,
   .n 3 2 9 11 12, .n 3 2 10 3 4, .p 3 2 10 4 8, .p 3 2 10 5 12, .n 3 2 10 6 20, .n 3 2 10 7 20,
   .p 3 2 10 8 24, .p 3 2 10 9 12, .n 3 2 10 10 12, .n 3 2 11 4 4, .p 3 2 11 5 8, .n 3 2 11 7 8,
   .p 3 2 11 8 4, .n 4 1 5 2 4, .p 4 1 5 3 8, .n 4 1 5 4 4, .p 4 1 5 6 12, .n 4 1 5 7 24,
   .p 4 1 5 8 4, .p 4 1 5 9 16, .n 4 1 5 10 8, .p 4 1 6 2 8, .n 4 1 6 3 16, .n 4 1 6 4 4,
   .p 4 1 6 5 16, .p 4 1 6 6 4, .p 4 1 6 7 8, .n 4 1 6 8 28, .p 4 1 6 10 20, .n 4 1 6 11 8,
   .p 4 1 7 1 4, .n 4 1 7 3 4, .n 4 1 7 4 16, .n 4 1 7 5 16, .p 4 1 7 6 64, .p 4 1 7 7 16,
   .n 4 1 7 8 80, .p 4 1 7 9 12, .p 4 1 7 10 32, .n 4 1 7 11 12, .n 4 1 8 1 4, .p 4 1 8 3 20,
   .n 4 1 8 4 16, .n 4 1 8 7 32, .p 4 1 8 8 48, .p 4 1 8 9 4, .n 4 1 8 10 32, .p 4 1 8 11 12,
   .n 4 1 9 2 4, .n 4 1 9 3 8, .p 4 1 9 4 36, .p 4 1 9 5 8, .n 4 1 9 6 76, .p 4 1 9 7 16,
   .p 4 1 9 8 60, .n 4 1 9 9 24, .n 4 1 9 10 16, .p 4 1 9 11 8, .p 4 1 10 4 4, .n 4 1 10 5 8,
   .n 4 1 10 6 4, .p 4 1 10 7 16, .n 4 1 10 8 4, .n 4 1 10 9 8, .p 4 1 10 10 4, .p 5 0 7 3 8,
   .n 5 0 7 4 16, .n 5 0 7 5 16, .p 5 0 7 6 48, .n 5 0 7 8 48, .p 5 0 7 9 16, .p 5 0 7 10 16,
   .n 5 0 7 11 8, .n 5 0 8 1 8, .p 5 0 8 2 16, .p 5 0 8 3 16, .n 5 0 8 4 48, .p 5 0 8 6 48,
   .n 5 0 8 7 16, .n 5 0 8 8 16, .p 5 0 8 9 8]

set_option maxRecDepth 65536 in
private theorem g2_det4_6 : fmDet 4 g2Sub4_6 = g2Val4_6 := by decide

private def g2Sub4_7 (r c : Fin 4) : List FM :=
  g2FM ⟨r.val + 2, by omega⟩ (match c.val with | 0 => ⟨0, by decide⟩ | 1 => ⟨2, by decide⟩ | 2 => ⟨3, by decide⟩ | _ => ⟨5, by decide⟩)

private def g2Val4_7 : List FM :=
  [.n 0 6 3 6 32, .p 0 6 4 6 96, .p 0 6 4 7 32, .n 0 6 5 6 64, .n 0 6 5 7 64, .n 0 6 6 6 64,
   .n 0 6 6 7 32, .n 0 6 6 8 32, .p 0 6 7 6 96, .p 0 6 7 7 128, .p 0 6 7 8 96, .n 0 6 8 6 32,
   .n 0 6 8 7 32, .n 0 6 8 8 64, .n 0 6 9 7 64, .n 0 6 9 8 64, .p 0 6 10 7 32, .p 0 6 10 8 96,
   .n 0 6 11 8 32, .n 1 5 4 4 16, .p 1 5 4 5 32, .n 1 5 4 6 8, .n 1 5 4 7 32, .p 1 5 4 8 24,
   .n 1 5 5 3 16, .p 1 5 5 4 40, .n 1 5 5 5 24, .p 1 5 5 6 32, .p 1 5 5 7 32, .n 1 5 5 8 64,
   .n 1 5 5 9 24, .p 1 5 5 10 24, .p 1 5 6 3 40, .n 1 5 6 4 40, .n 1 5 6 5 72, .n 1 5 6 6 64,
   .p 1 5 6 7 64, .p 1 5 6 8 112, .p 1 5 6 9 24, .n 1 5 6 10 72, .p 1 5 6 11 8, .n 1 5 7 3 24,
   .p 1 5 7 4 48, .p 1 5 7 5 48, .p 1 5 7 6 8, .n 1 5 7 7 16, .n 1 5 7 8 168, .p 1 5 7 9 48,
   .p 1 5 7 10 80, .n 1 5 7 11 24, .n 1 5 8 3 8, .n 1 5 8 4 64, .p 1 5 8 5 48, .p 1 5 8 6 152,
   .n 1 5 8 7 144, .p 1 5 8 8 88, .n 1 5 8 9 48, .n 1 5 8 10 48, .p 1 5 8 11 24, .p 1 5 9 3 8,
   .p 1 5 9 4 40, .n 1 5 9 5 24, .n 1 5 9 6 176, .p 1 5 9 7 80, .p 1 5 9 8 80, .n 1 5 9 9 24,
   .p 1 5 9 10 24, .n 1 5 9 11 8, .n 1 5 10 4 8, .n 1 5 10 5 8, .p 1 5 10 6 48, .p 1 5 10 7 48,
   .n 1 5 10 8 96, .p 1 5 10 9 24, .n 1 5 10 10 8, .p 1 5 11 6 8, .n 1 5 11 7 32, .p 1 5 11 8 24,
   .p 2 4 4 5 16, .n 2 4 4 6 20, .n 2 4 4 7 16, .p 2 4 4 8 20, .p 2 4 5 2 8, .p 2 4 5 3 32,
   .n 2 4 5 4 36, .n 2 4 5 5 44, .p 2 4 5 6 88, .p 2 4 5 7 32, .n 2 4 5 8 64, .n 2 4 5 9 20,
   .p 2 4 5 10 4, .n 2 4 6 2 16, .n 2 4 6 3 44, .p 2 4 6 4 12, .n 2 4 6 5 76, .n 2 4 6 6 72,
   .p 2 4 6 7 112, .p 2 4 6 8 96, .n 2 4 6 9 4, .n 2 4 6 10 20, .p 2 4 6 11 12, .p 2 4 7 2 8,
   .n 2 4 7 3 4, .p 2 4 7 4 104, .p 2 4 7 5 128, .p 2 4 7 6 4, .n 2 4 7 7 160, .n 2 4 7 8 132,
   .p 2 4 7 9 32, .p 2 4 7 10 16, .p 2 4 7 11 4, .p 2 4 8 3 12, .n 2 4 8 4 72, .p 2 4 8 5 96,
   .n 2 4 8 6 4, .n 2 4 8 7 80, .p 2 4 8 8 52, .p 2 4 8 9 16, .p 2 4 8 10 24, .n 2 4 8 11 44,
   .p 2 4 9 3 4, .n 2 4 9 4 68, .n 2 4 9 5 116, .n 2 4 9 6 64, .p 2 4 9 7 96, .p 2 4 9 8 168,
   .n 2 4 9 9 12, .n 2 4 9 10 36, .p 2 4 9 11 28, .p 2 4 10 4 92, .n 2 4 10 5 36, .p 2 4 10 6 96,
   .p 2 4 10 7 48, .n 2 4 10 8 200, .n 2 4 10 9 12, .p 2 4 10 10 12, .n 2 4 11 4 32, .p 2 4 11 5 32,
   .n 2 4 11 6 28, .n 2 4 11 7 32, .p 2 4 11 8 60, .p 3 3 4 4 12, .n 3 3 4 5 16, .n 3 3 4 6 8,
   .p 3 3 4 7 16, .n 3 3 4 8 4, .n 3 3 5 2 24, .p 3 3 5 3 20, .n 3 3 5 4 16, .p 3 3 5 5 44,
   .n 3 3 5 6 32, .n 3 3 5 7 4, .p 3 3 5 9 68, .n 3 3 5 10 56, .p 3 3 6 2 56, .n 3 3 6 3 56,
   .p 3 3 6 4 32, .p 3 3 6 6 68, .n 3 3 6 7 128, .n 3 3 6 8 56, .n 3 3 6 9 48, .p 3 3 6 10 156,
   .n 3 3 6 11 24, .n 3 3 7 2 40, .p 3 3 7 3 4, .n 3 3 7 4 16, .n 3 3 7 5 16, .n 3 3 7 6 16,
   .n 3 3 7 7 24, .p 3 3 7 8 416, .n 3 3 7 9 160, .n 3 3 7 10 216, .p 3 3 7 11 68, .p 3 3 8 2 8,
   .p 3 3 8 3 24, .p 3 3 8 4 68, .p 3 3 8 5 64, .n 3 3 8 6 376, .p 3 3 8 7 368, .n 3 3 8 8 332,
   .p 3 3 8 9 80, .p 3 3 8 10 120, .n 3 3 8 11 24, .p 3 3 9 3 24, .n 3 3 9 4 160, .n 3 3 9 5 76,
   .p 3 3 9 6 448, .n 3 3 9 7 148, .n 3 3 9 8 144, .p 3 3 9 9 92, .n 3 3 9 10 16, .n 3 3 9 11 20,
   .n 3 3 10 3 16, .p 3 3 10 4 112, .n 3 3 10 5 48, .n 3 3 10 6 36, .n 3 3 10 7 160, .p 3 3 10 8 168,
   .n 3 3 10 9 32, .p 3 3 10 10 12, .n 3 3 11 4 32, .p 3 3 11 5 48, .n 3 3 11 6 48, .p 3 3 11 7 80,
   .n 3 3 11 8 48, .p 4 2 5 2 24, .n 4 2 5 3 48, .p 4 2 5 4 20, .p 4 2 5 5 16, .p 4 2 5 6 4,
   .n 4 2 5 7 48, .n 4 2 5 8 4, .p 4 2 5 9 80, .n 4 2 5 10 44, .n 4 2 6 2 44, .p 4 2 6 3 60,
   .n 4 2 6 4 84, .p 4 2 6 5 96, .p 4 2 6 6 124, .n 4 2 6 7 104, .n 4 2 6 8 124, .n 4 2 6 9 16,
   .p 4 2 6 10 128, .n 4 2 6 11 36, .n 4 2 7 1 4, .p 4 2 7 2 40, .p 4 2 7 3 40, .n 4 2 7 4 84,
   .n 4 2 7 5 80, .n 4 2 7 6 28, .p 4 2 7 7 88, .p 4 2 7 8 132, .n 4 2 7 9 60, .n 4 2 7 10 60,
   .p 4 2 7 11 16, .n 4 2 8 2 12, .n 4 2 8 3 48, .p 4 2 8 4 172, .n 4 2 8 5 128, .n 4 2 8 6 60,
   .p 4 2 8 7 144, .n 4 2 8 8 60, .n 4 2 8 10 40, .p 4 2 8 11 32, .p 4 2 9 3 16, .n 4 2 9 4 64,
   .p 4 2 9 5 48, .p 4 2 9 6 48, .n 4 2 9 7 32, .n 4 2 9 8 32, .n 4 2 9 9 16, .p 4 2 9 10 48,
   .n 4 2 9 11 16, .n 4 2 10 3 8, .p 4 2 10 4 16, .p 4 2 10 5 24, .n 4 2 10 6 40, .n 4 2 10 7 40,
   .p 4 2 10 8 48, .p 4 2 10 9 24, .n 4 2 10 10 24, .n 4 2 11 4 8, .p 4 2 11 5 16, .n 4 2 11 7 16,
   .p 4 2 11 8 8, .n 5 1 5 2 8, .p 5 1 5 3 16, .n 5 1 5 5 16, .p 5 1 5 6 16, .n 5 1 5 7 16,
   .p 5 1 5 9 16, .n 5 1 5 10 8, .p 5 1 6 2 8, .n 5 1 6 3 8, .n 5 1 6 4 16, .p 5 1 6 6 32,
   .p 5 1 6 7 16, .n 5 1 6 8 48, .p 5 1 6 10 24, .n 5 1 6 11 8, .p 5 1 7 2 16, .n 5 1 7 3 8,
   .n 5 1 7 4 56, .n 5 1 7 5 16, .p 5 1 7 6 152, .p 5 1 7 7 16, .n 5 1 7 8 200, .p 5 1 7 9 48,
   .p 5 1 7 10 88, .n 5 1 7 11 40, .n 5 1 8 1 8, .p 5 1 8 2 8, .p 5 1 8 3 40, .n 5 1 8 4 72,
   .p 5 1 8 5 16, .p 5 1 8 6 56, .n 5 1 8 7 96, .p 5 1 8 8 72, .p 5 1 8 9 24, .n 5 1 8 10 64,
   .p 5 1 8 11 24, .n 5 1 9 2 8, .n 5 1 9 3 16, .p 5 1 9 4 72, .p 5 1 9 5 16, .n 5 1 9 6 152,
   .p 5 1 9 7 32, .p 5 1 9 8 120, .n 5 1 9 9 48, .n 5 1 9 10 32, .p 5 1 9 11 16, .p 5 1 10 4 8,
   .n 5 1 10 5 16, .n 5 1 10 6 8, .p 5 1 10 7 32, .n 5 1 10 8 8, .n 5 1 10 9 16, .p 5 1 10 10 8,
   .p 6 0 7 3 16, .n 6 0 7 4 32, .n 6 0 7 5 32, .p 6 0 7 6 96, .n 6 0 7 8 96, .p 6 0 7 9 32,
   .p 6 0 7 10 32, .n 6 0 7 11 16, .n 6 0 8 1 16, .p 6 0 8 2 32, .p 6 0 8 3 32, .n 6 0 8 4 96,
   .p 6 0 8 6 96, .n 6 0 8 7 32, .n 6 0 8 8 32, .p 6 0 8 9 16]

set_option maxRecDepth 65536 in
private theorem g2_det4_7 : fmDet 4 g2Sub4_7 = g2Val4_7 := by decide

private def g2Sub4_8 (r c : Fin 4) : List FM :=
  g2FM ⟨r.val + 2, by omega⟩ (match c.val with | 0 => ⟨0, by decide⟩ | 1 => ⟨2, by decide⟩ | 2 => ⟨4, by decide⟩ | _ => ⟨5, by decide⟩)

private def g2Val4_8 : List FM :=
  [.p 0 6 5 6 32, .n 0 6 5 7 32, .n 0 6 6 6 96, .p 0 6 6 7 64, .p 0 6 6 8 32, .p 0 6 7 6 64,
   .p 0 6 7 7 32, .n 0 6 7 8 96, .p 0 6 8 6 64, .n 0 6 8 7 128, .p 0 6 8 8 64, .n 0 6 9 6 96,
   .p 0 6 9 7 32, .p 0 6 9 8 64, .p 0 6 10 6 32, .p 0 6 10 7 64, .n 0 6 10 8 96, .n 0 6 11 7 32,
   .p 0 6 11 8 32, .n 1 5 4 6 8, .p 1 5 4 8 8, .p 1 5 5 4 8, .n 1 5 5 5 8, .p 1 5 5 6 80,
   .n 1 5 5 7 48, .n 1 5 5 8 32, .p 1 5 5 9 24, .n 1 5 5 10 24, .p 1 5 6 3 8, .n 1 5 6 4 8,
   .n 1 5 6 5 24, .n 1 5 6 6 176, .p 1 5 6 7 112, .p 1 5 6 8 48, .n 1 5 6 9 24, .p 1 5 6 10 72,
   .n 1 5 6 11 8, .n 1 5 7 3 8, .n 1 5 7 4 32, .p 1 5 7 5 48, .p 1 5 7 6 136, .p 1 5 7 7 16,
   .n 1 5 7 8 56, .n 1 5 7 9 48, .n 1 5 7 10 80, .p 1 5 7 11 24, .n 1 5 8 3 24, .p 1 5 8 4 80,
   .p 1 5 8 5 48, .n 1 5 8 6 8, .n 1 5 8 7 176, .p 1 5 8 8 8, .p 1 5 8 9 48, .p 1 5 8 10 48,
   .n 1 5 8 11 24, .p 1 5 9 3 40, .n 1 5 9 4 88, .n 1 5 9 5 72, .n 1 5 9 6 64, .p 1 5 9 7 32,
   .p 1 5 9 8 144, .p 1 5 9 9 24, .n 1 5 9 10 24, .p 1 5 9 11 8, .n 1 5 10 3 16, .p 1 5 10 4 56,
   .n 1 5 10 5 24, .p 1 5 10 6 64, .p 1 5 10 7 128, .n 1 5 10 8 192, .n 1 5 10 9 24, .p 1 5 10 10 8,
   .n 1 5 11 4 16, .p 1 5 11 5 32, .n 1 5 11 6 24, .n 1 5 11 7 64, .p 1 5 11 8 72, .n 2 4 4 6 4,
   .p 2 4 4 8 4, .p 2 4 5 4 12, .p 2 4 5 5 4, .n 2 4 5 6 24, .p 2 4 5 7 48, .n 2 4 5 8 64,
   .p 2 4 5 9 76, .n 2 4 5 10 52, .n 2 4 6 2 8, .n 2 4 6 3 4, .p 2 4 6 4 12, .n 2 4 6 5 44,
   .p 2 4 6 6 104, .n 2 4 6 7 128, .n 2 4 6 8 16, .n 2 4 6 9 52, .p 2 4 6 10 164, .n 2 4 6 11 28,
   .p 2 4 7 2 16, .n 2 4 7 3 12, .n 2 4 7 4 56, .p 2 4 7 5 64, .n 2 4 7 6 12, .n 2 4 7 7 80,
   .p 2 4 7 8 364, .n 2 4 7 9 144, .n 2 4 7 10 184, .p 2 4 7 11 44, .n 2 4 8 2 8, .p 2 4 8 3 4,
   .p 2 4 8 4 104, .p 2 4 8 5 96, .n 2 4 8 6 340, .p 2 4 8 7 320, .n 2 4 8 8 364, .p 2 4 8 9 96,
   .p 2 4 8 10 96, .n 2 4 8 11 4, .p 2 4 9 3 44, .n 2 4 9 4 196, .n 2 4 9 5 148, .p 2 4 9 6 368,
   .n 2 4 9 7 80, .n 2 4 9 8 8, .p 2 4 9 9 68, .n 2 4 9 10 36, .n 2 4 9 11 12, .n 2 4 10 3 32,
   .p 2 4 10 4 172, .n 2 4 10 5 52, .n 2 4 10 6 16, .n 2 4 10 7 128, .p 2 4 10 8 88, .n 2 4 10 9 44,
   .p 2 4 10 10 12, .n 2 4 11 4 48, .p 2 4 11 5 80, .n 2 4 11 6 76, .p 2 4 11 7 48, .n 2 4 11 8 4,
   .n 3 3 5 4 16, .p 3 3 5 5 32, .n 3 3 5 6 36, .p 3 3 5 7 32, .n 3 3 5 8 40, .p 3 3 5 9 64,
   .n 3 3 5 10 36, .p 3 3 6 2 16, .n 3 3 6 3 32, .p 3 3 6 4 16, .p 3 3 6 5 4, .p 3 3 6 6 128,
   .n 3 3 6 7 164, .n 3 3 6 8 16, .n 3 3 6 9 36, .p 3 3 6 10 112, .n 3 3 6 11 28, .n 3 3 7 2 32,
   .p 3 3 7 3 16, .p 3 3 7 4 52, .n 3 3 7 5 80, .p 3 3 7 6 8, .n 3 3 7 7 16, .p 3 3 7 8 148,
   .n 3 3 7 9 48, .n 3 3 7 10 48, .p 3 3 8 2 16, .p 3 3 8 3 76, .n 3 3 8 4 112, .p 3 3 8 5 32,
   .n 3 3 8 6 176, .p 3 3 8 7 328, .n 3 3 8 8 208, .p 3 3 8 9 32, .n 3 3 8 10 32, .p 3 3 8 11 44,
   .n 3 3 9 3 32, .n 3 3 9 4 32, .n 3 3 9 5 16, .p 3 3 9 6 180, .n 3 3 9 7 48, .n 3 3 9 8 40,
   .n 3 3 9 9 16, .p 3 3 9 10 20, .n 3 3 9 11 16, .n 3 3 10 3 28, .p 3 3 10 4 128, .n 3 3 10 5 36,
   .n 3 3 10 6 48, .n 3 3 10 7 196, .p 3 3 10 8 192, .p 3 3 10 9 4, .n 3 3 10 10 16, .n 3 3 11 4 36,
   .p 3 3 11 5 64, .n 3 3 11 6 56, .p 3 3 11 7 64, .n 3 3 11 8 36, .p 4 2 5 4 8, .n 4 2 5 5 16,
   .p 4 2 5 6 8, .n 4 2 5 8 8, .p 4 2 5 9 16, .n 4 2 5 10 8, .n 4 2 6 2 8, .p 4 2 6 3 16,
   .n 4 2 6 4 8, .n 4 2 6 5 8, .p 4 2 6 6 16, .p 4 2 6 7 8, .n 4 2 6 8 24, .n 4 2 6 9 8,
   .p 4 2 6 10 24, .n 4 2 6 11 8, .n 4 2 7 2 4, .p 4 2 7 3 8, .n 4 2 7 4 4, .n 4 2 7 5 48,
   .p 4 2 7 6 92, .p 4 2 7 7 48, .n 4 2 7 8 172, .p 4 2 7 9 32, .p 4 2 7 10 88, .n 4 2 7 11 40,
   .p 4 2 8 1 4, .p 4 2 8 2 8, .p 4 2 8 3 16, .n 4 2 8 4 68, .p 4 2 8 6 60, .n 4 2 8 7 56,
   .p 4 2 8 8 84, .n 4 2 8 9 4, .n 4 2 8 10 84, .p 4 2 8 11 40, .n 4 2 9 2 4, .n 4 2 9 3 44,
   .p 4 2 9 4 92, .p 4 2 9 5 56, .n 4 2 9 6 188, .p 4 2 9 7 32, .p 4 2 9 8 116, .n 4 2 9 9 56,
   .n 4 2 9 10 16, .p 4 2 9 11 12, .n 4 2 10 3 8, .p 4 2 10 4 20, .p 4 2 10 5 8, .n 4 2 10 6 36,
   .n 4 2 10 7 8, .p 4 2 10 8 28, .p 4 2 10 9 8, .n 4 2 10 10 12, .n 4 2 11 4 8, .p 4 2 11 5 16,
   .n 4 2 11 7 16, .p 4 2 11 8 8, .p 5 1 7 2 8, .n 5 1 7 3 16, .n 5 1 7 4 8, .p 5 1 7 5 16,
   .p 5 1 7 6 24, .n 5 1 7 8 56, .p 5 1 7 9 16, .p 5 1 7 10 32, .n 5 1 7 11 16, .p 5 1 8 1 8,
   .n 5 1 8 2 16, .p 5 1 8 4 8, .p 5 1 8 5 16, .n 5 1 8 6 8, .n 5 1 8 7 48, .p 5 1 8 8 56,
   .p 5 1 8 9 8, .n 5 1 8 10 40, .p 5 1 8 11 16, .n 5 1 9 2 8, .n 5 1 9 3 8, .p 5 1 9 4 56,
   .n 5 1 9 6 104, .p 5 1 9 7 32, .p 5 1 9 8 72, .n 5 1 9 9 32, .n 5 1 9 10 16, .p 5 1 9 11 8,
   .p 5 1 10 4 8, .n 5 1 10 5 16, .n 5 1 10 6 8, .p 5 1 10 7 32, .n 5 1 10 8 8, .n 5 1 10 9 16,
   .p 5 1 10 10 8]

set_option maxRecDepth 65536 in
private theorem g2_det4_8 : fmDet 4 g2Sub4_8 = g2Val4_8 := by decide

private def g2Sub4_9 (r c : Fin 4) : List FM :=
  g2FM ⟨r.val + 2, by omega⟩ (match c.val with | 0 => ⟨0, by decide⟩ | 1 => ⟨3, by decide⟩ | 2 => ⟨4, by decide⟩ | _ => ⟨5, by decide⟩)

private def g2Val4_9 : List FM :=
  [.n 0 5 4 6 16, .p 0 5 5 6 48, .n 0 5 6 6 16, .p 0 5 6 8 16, .n 0 5 7 6 80, .n 0 5 7 8 48,
   .p 0 5 8 6 80, .p 0 5 8 8 16, .p 0 5 9 6 16, .p 0 5 9 8 80, .n 0 5 10 6 48, .n 0 5 10 8 80,
   .p 0 5 11 6 16, .n 0 5 11 8 16, .p 0 5 12 8 48, .n 0 5 13 8 16, .p 1 4 5 5 16, .p 1 4 5 6 16,
   .n 1 4 5 7 32, .p 1 4 5 9 16, .n 1 4 5 10 16, .n 1 4 6 5 16, .n 1 4 6 6 48, .p 1 4 6 7 32,
   .n 1 4 6 9 16, .p 1 4 6 10 48, .n 1 4 7 4 16, .n 1 4 7 5 48, .p 1 4 7 6 32, .p 1 4 7 7 96,
   .p 1 4 7 8 16, .n 1 4 7 9 48, .n 1 4 7 10 32, .p 1 4 8 4 48, .p 1 4 8 5 48, .p 1 4 8 6 32,
   .n 1 4 8 7 96, .n 1 4 8 8 48, .p 1 4 8 9 48, .n 1 4 8 10 32, .n 1 4 9 4 32, .p 1 4 9 5 48,
   .n 1 4 9 6 48, .n 1 4 9 7 96, .p 1 4 9 8 32, .p 1 4 9 9 48, .p 1 4 9 10 48, .n 1 4 10 4 32,
   .n 1 4 10 5 48, .p 1 4 10 6 16, .p 1 4 10 7 96, .p 1 4 10 8 32, .n 1 4 10 9 48, .n 1 4 10 10 16,
   .p 1 4 11 4 48, .n 1 4 11 5 16, .p 1 4 11 7 32, .n 1 4 11 8 48, .n 1 4 11 9 16, .n 1 4 12 4 16,
   .p 1 4 12 5 16, .n 1 4 12 7 32, .p 1 4 12 8 16, .p 1 4 12 9 16, .p 2 3 5 5 8, .n 2 3 5 6 32,
   .p 2 3 5 7 32, .n 2 3 5 8 16, .p 2 3 5 9 24, .n 2 3 5 10 16, .n 2 3 6 2 4, .p 2 3 6 3 8,
   .n 2 3 6 5 24, .p 2 3 6 6 72, .n 2 3 6 7 32, .n 2 3 6 8 48, .n 2 3 6 9 8, .p 2 3 6 10 44,
   .n 2 3 6 11 8, .p 2 3 7 2 12, .n 2 3 7 3 8, .n 2 3 7 4 16, .n 2 3 7 5 24, .p 2 3 7 6 56,
   .n 2 3 7 7 96, .p 2 3 7 8 160, .n 2 3 7 9 72, .n 2 3 7 10 20, .p 2 3 7 11 8, .n 2 3 8 2 12,
   .n 2 3 8 3 16, .p 2 3 8 4 52, .p 2 3 8 5 72, .n 2 3 8 6 184, .p 2 3 8 7 96, .n 2 3 8 8 8,
   .p 2 3 8 9 24, .n 2 3 8 10 44, .p 2 3 8 11 16, .p 2 3 8 12 4, .p 2 3 9 2 4, .p 2 3 9 3 16,
   .n 2 3 9 4 44, .p 2 3 9 5 24, .n 2 3 9 6 8, .p 2 3 9 7 96, .n 2 3 9 8 184, .p 2 3 9 9 72,
   .p 2 3 9 10 52, .n 2 3 9 11 16, .n 2 3 9 12 12, .p 2 3 10 3 8, .n 2 3 10 4 20, .n 2 3 10 5 72,
   .p 2 3 10 6 160, .n 2 3 10 7 96, .p 2 3 10 8 56, .n 2 3 10 9 24, .n 2 3 10 10 16, .n 2 3 10 11 8,
   .p 2 3 10 12 12, .n 2 3 11 3 8, .p 2 3 11 4 44, .n 2 3 11 5 8, .n 2 3 11 6 48, .n 2 3 11 7 32,
   .p 2 3 11 8 72, .n 2 3 11 9 24, .p 2 3 11 11 8, .n 2 3 11 12 4, .n 2 3 12 4 16, .p 2 3 12 5 24,
   .n 2 3 12 6 16, .p 2 3 12 7 32, .n 2 3 12 8 32, .p 2 3 12 9 8, .p 3 2 5 4 4, .n 3 2 5 5 8,
   .p 3 2 5 6 4, .n 3 2 5 8 4, .p 3 2 5 9 8, .n 3 2 5 10 4, .p 3 2 6 2 8, .n 3 2 6 3 20,
   .p 3 2 6 4 4, .p 3 2 6 5 24, .p 3 2 6 6 4, .n 3 2 6 7 40, .n 3 2 6 8 4, .p 3 2 6 9 40,
   .n 3 2 6 10 12, .n 3 2 6 11 4, .n 3 2 7 2 24, .p 3 2 7 3 12, .p 3 2 7 4 4, .p 3 2 7 5 56,
   .p 3 2 7 6 4, .n 3 2 7 7 72, .n 3 2 7 8 4, .p 3 2 7 9 8, .p 3 2 7 10 20, .n 3 2 7 11 4,
   .p 3 2 8 2 24, .p 3 2 8 3 24, .n 3 2 8 4 52, .n 3 2 8 5 40, .n 3 2 8 6 60, .p 3 2 8 7 112,
   .p 3 2 8 8 60, .n 3 2 8 9 88, .p 3 2 8 10 36, .n 3 2 8 11 8, .n 3 2 8 12 8, .n 3 2 9 2 8,
   .n 3 2 9 3 8, .p 3 2 9 4 36, .n 3 2 9 5 88, .p 3 2 9 6 60, .p 3 2 9 7 112, .n 3 2 9 8 60,
   .n 3 2 9 9 40, .n 3 2 9 10 52, .p 3 2 9 11 24, .p 3 2 9 12 24, .n 3 2 10 3 4, .p 3 2 10 4 20,
   .p 3 2 10 5 8, .n 3 2 10 6 4, .n 3 2 10 7 72, .p 3 2 10 8 4, .p 3 2 10 9 56, .p 3 2 10 10 4,
   .p 3 2 10 11 12, .n 3 2 10 12 24, .n 3 2 11 3 4, .n 3 2 11 4 12, .p 3 2 11 5 40, .n 3 2 11 6 4,
   .n 3 2 11 7 40, .p 3 2 11 8 4, .p 3 2 11 9 24, .p 3 2 11 10 4, .n 3 2 11 11 20, .p 3 2 11 12 8,
   .n 3 2 12 4 4, .p 3 2 12 5 8, .n 3 2 12 6 4, .p 3 2 12 8 4, .n 3 2 12 9 8, .p 3 2 12 10 4,
   .n 4 1 6 2 4, .p 4 1 6 3 8, .n 4 1 6 5 8, .p 4 1 6 6 8, .n 4 1 6 7 8, .p 4 1 6 9 8,
   .n 4 1 6 10 4, .p 4 1 7 2 8, .n 4 1 7 3 8, .n 4 1 7 4 20, .n 4 1 7 5 8, .p 4 1 7 6 64,
   .p 4 1 7 7 24, .n 4 1 7 8 104, .p 4 1 7 9 8, .p 4 1 7 10 56, .n 4 1 7 11 16, .n 4 1 7 12 4,
   .p 4 1 8 1 4, .p 4 1 8 3 8, .n 4 1 8 4 48, .n 4 1 8 5 12, .p 4 1 8 6 112, .n 4 1 8 7 16,
   .n 4 1 8 8 80, .p 4 1 8 9 12, .p 4 1 8 10 16, .p 4 1 8 11 8, .n 4 1 8 13 4, .n 4 1 9 1 4,
   .p 4 1 9 3 8, .p 4 1 9 4 16, .p 4 1 9 5 12, .n 4 1 9 6 80, .n 4 1 9 7 16, .p 4 1 9 8 112,
   .n 4 1 9 9 12, .n 4 1 9 10 48, .p 4 1 9 11 8, .p 4 1 9 13 4, .n 4 1 10 2 4, .n 4 1 10 3 16,
   .p 4 1 10 4 56, .p 4 1 10 5 8, .n 4 1 10 6 104, .p 4 1 10 7 24, .p 4 1 10 8 64, .n 4 1 10 9 8,
   .n 4 1 10 10 20, .n 4 1 10 11 8, .p 4 1 10 12 8, .n 4 1 11 4 4, .p 4 1 11 5 8, .n 4 1 11 7 8,
   .p 4 1 11 8 8, .n 4 1 11 9 8, .p 4 1 11 11 8, .n 4 1 11 12 4, .p 5 0 8 3 8, .n 5 0 8 4 16,
   .n 5 0 8 5 8, .p 5 0 8 6 32, .n 5 0 8 7 16, .p 5 0 8 9 16, .n 5 0 8 10 32, .p 5 0 8 11 8,
   .p 5 0 8 12 16, .n 5 0 8 13 8, .n 5 0 9 1 8, .p 5 0 9 2 16, .p 5 0 9 3 8, .n 5 0 9 4 32,
   .p 5 0 9 5 16, .n 5 0 9 7 16, .p 5 0 9 8 32, .n 5 0 9 9 8, .n 5 0 9 10 16, .p 5 0 9 11 8]

set_option maxRecDepth 65536 in
private theorem g2_det4_9 : fmDet 4 g2Sub4_9 = g2Val4_9 := by decide

private def g2Sub4_10 (r c : Fin 4) : List FM :=
  g2FM ⟨r.val + 2, by omega⟩ (match c.val with | 0 => ⟨1, by decide⟩ | 1 => ⟨2, by decide⟩ | 2 => ⟨3, by decide⟩ | _ => ⟨4, by decide⟩)

private def g2Val4_10 : List FM :=
  [.n 0 6 3 6 32, .p 0 6 4 6 96, .p 0 6 4 7 32, .n 0 6 5 6 32, .n 0 6 5 7 96, .n 0 6 6 6 160,
   .p 0 6 6 7 32, .p 0 6 7 6 160, .p 0 6 7 7 160, .p 0 6 8 6 32, .n 0 6 8 7 160, .n 0 6 9 6 96,
   .n 0 6 9 7 32, .p 0 6 10 6 32, .p 0 6 10 7 96, .n 0 6 11 7 32, .n 1 5 3 6 32, .p 1 5 4 4 16,
   .p 1 5 4 5 16, .p 1 5 4 6 64, .p 1 5 4 7 16, .p 1 5 4 8 16, .p 1 5 5 3 16, .n 1 5 5 4 48,
   .n 1 5 5 5 16, .p 1 5 5 6 64, .n 1 5 5 7 96, .n 1 5 5 8 48, .n 1 5 6 3 48, .n 1 5 6 5 48,
   .n 1 5 6 6 256, .p 1 5 6 7 128, .p 1 5 6 8 96, .p 1 5 7 3 32, .p 1 5 7 4 128, .p 1 5 7 5 48,
   .p 1 5 7 6 192, .p 1 5 7 7 80, .n 1 5 7 8 160, .p 1 5 8 3 32, .n 1 5 8 4 112, .p 1 5 8 5 48,
   .p 1 5 8 6 64, .n 1 5 8 7 240, .p 1 5 8 8 80, .n 1 5 9 3 48, .n 1 5 9 4 48, .n 1 5 9 5 48,
   .n 1 5 9 6 192, .p 1 5 9 7 64, .p 1 5 9 8 144, .p 1 5 10 3 16, .p 1 5 10 4 96, .n 1 5 10 5 16,
   .p 1 5 10 6 128, .p 1 5 10 7 96, .n 1 5 10 8 192, .n 1 5 11 4 32, .p 1 5 11 5 16, .n 1 5 11 6 32,
   .n 1 5 11 7 48, .p 1 5 11 8 64, .p 2 4 4 4 8, .p 2 4 4 5 56, .n 2 4 4 6 64, .n 2 4 4 7 56,
   .p 2 4 4 8 56, .n 2 4 5 2 16, .n 2 4 5 3 8, .n 2 4 5 4 8, .n 2 4 5 5 40, .p 2 4 5 6 96,
   .p 2 4 5 7 160, .n 2 4 5 8 184, .p 2 4 5 9 16, .n 2 4 5 10 16, .p 2 4 6 2 48, .p 2 4 6 3 8,
   .n 2 4 6 4 64, .n 2 4 6 5 200, .p 2 4 6 6 80, .n 2 4 6 7 48, .p 2 4 6 8 144, .n 2 4 6 9 16,
   .p 2 4 6 10 48, .n 2 4 7 2 48, .p 2 4 7 3 16, .p 2 4 7 4 192, .p 2 4 7 5 152, .n 2 4 7 6 80,
   .n 2 4 7 7 264, .p 2 4 7 8 112, .n 2 4 7 9 32, .n 2 4 7 10 48, .p 2 4 8 2 16, .n 2 4 8 3 16,
   .n 2 4 8 4 152, .p 2 4 8 5 232, .n 2 4 8 6 192, .p 2 4 8 7 264, .n 2 4 8 8 200, .p 2 4 8 9 32,
   .p 2 4 8 10 16, .n 2 4 9 3 8, .n 2 4 9 4 104, .n 2 4 9 5 184, .p 2 4 9 6 160, .p 2 4 9 7 48,
   .p 2 4 9 8 72, .p 2 4 9 9 16, .p 2 4 10 3 8, .p 2 4 10 4 208, .n 2 4 10 5 88, .p 2 4 10 6 48,
   .n 2 4 10 7 160, .n 2 4 10 9 16, .n 2 4 11 4 80, .p 2 4 11 5 72, .n 2 4 11 6 48, .p 2 4 11 7 56,
   .n 3 3 4 4 8, .p 3 3 4 5 16, .n 3 3 4 7 16, .p 3 3 4 8 8, .p 3 3 5 2 28, .n 3 3 5 3 56,
   .p 3 3 5 4 56, .n 3 3 5 5 40, .n 3 3 5 6 88, .p 3 3 5 7 136, .n 3 3 5 8 56, .p 3 3 5 9 88,
   .n 3 3 5 10 68, .n 3 3 6 2 76, .p 3 3 6 3 116, .n 3 3 6 4 40, .n 3 3 6 5 32, .p 3 3 6 6 312,
   .n 3 3 6 7 248, .n 3 3 6 8 120, .n 3 3 6 9 80, .p 3 3 6 10 180, .n 3 3 6 11 12, .p 3 3 7 2 68,
   .n 3 3 7 3 12, .n 3 3 7 4 160, .p 3 3 7 5 120, .n 3 3 7 6 176, .n 3 3 7 7 128, .p 3 3 7 8 576,
   .n 3 3 7 9 136, .n 3 3 7 10 180, .p 3 3 7 11 28, .n 3 3 8 2 20, .n 3 3 8 3 124, .p 3 3 8 4 288,
   .p 3 3 8 5 56, .n 3 3 8 6 400, .p 3 3 8 7 480, .n 3 3 8 8 480, .p 3 3 8 9 120, .p 3 3 8 10 100,
   .n 3 3 8 11 20, .p 3 3 9 3 100, .n 3 3 9 4 224, .n 3 3 9 5 160, .p 3 3 9 6 488, .n 3 3 9 7 120,
   .n 3 3 9 8 96, .p 3 3 9 9 48, .n 3 3 9 10 40, .p 3 3 9 11 4, .n 3 3 10 3 24, .p 3 3 10 4 144,
   .n 3 3 10 5 40, .n 3 3 10 6 104, .n 3 3 10 7 152, .p 3 3 10 8 208, .n 3 3 10 9 40, .p 3 3 10 10 8,
   .n 3 3 11 4 56, .p 3 3 11 5 80, .n 3 3 11 6 32, .p 3 3 11 7 48, .n 3 3 11 8 40, .p 4 2 4 4 12,
   .n 4 2 4 5 24, .p 4 2 4 7 24, .n 4 2 4 8 12, .n 4 2 5 2 8, .p 4 2 5 3 12, .p 4 2 5 4 24,
   .p 4 2 5 5 4, .n 4 2 5 6 28, .n 4 2 5 7 116, .p 4 2 5 8 88, .p 4 2 5 9 100, .n 4 2 5 10 76,
   .n 4 2 6 2 24, .n 4 2 6 3 16, .n 4 2 6 4 40, .p 4 2 6 5 156, .p 4 2 6 6 68, .n 4 2 6 7 52,
   .n 4 2 6 8 168, .n 4 2 6 9 52, .p 4 2 6 10 164, .n 4 2 6 11 36, .p 4 2 7 1 8, .p 4 2 7 2 72,
   .n 4 2 7 3 20, .n 4 2 7 4 132, .n 4 2 7 5 80, .p 4 2 7 6 64, .p 4 2 7 7 136, .p 4 2 7 8 68,
   .n 4 2 7 9 80, .n 4 2 7 10 72, .p 4 2 7 11 36, .n 4 2 8 1 8, .n 4 2 8 2 40, .p 4 2 8 3 4,
   .p 4 2 8 4 196, .n 4 2 8 5 112, .n 4 2 8 6 128, .p 4 2 8 7 88, .n 4 2 8 8 4, .p 4 2 8 9 16,
   .n 4 2 8 10 24, .p 4 2 8 11 12, .p 4 2 9 3 32, .n 4 2 9 4 72, .p 4 2 9 5 36, .p 4 2 9 6 28,
   .n 4 2 9 7 44, .p 4 2 9 8 24, .n 4 2 9 9 12, .p 4 2 9 10 20, .n 4 2 9 11 12, .n 4 2 10 3 12,
   .p 4 2 10 4 24, .n 4 2 10 5 4, .n 4 2 10 6 4, .n 4 2 10 7 12, .n 4 2 10 8 8, .p 4 2 10 9 28,
   .n 4 2 10 10 12, .n 4 2 11 4 12, .p 4 2 11 5 24, .n 4 2 11 7 24, .p 4 2 11 8 12, .n 5 1 5 2 4,
   .p 5 1 5 3 8, .n 5 1 5 4 20, .p 5 1 5 5 32, .p 5 1 5 6 28, .n 5 1 5 7 88, .p 5 1 5 8 20,
   .p 5 1 5 9 48, .n 5 1 5 10 24, .p 5 1 6 2 24, .n 5 1 6 3 64, .p 5 1 6 4 12, .p 5 1 6 5 80,
   .n 5 1 6 6 44, .p 5 1 6 7 8, .n 5 1 6 8 44, .p 5 1 6 10 52, .n 5 1 6 11 24, .p 5 1 7 1 20,
   .n 5 1 7 2 32, .p 5 1 7 3 20, .n 5 1 7 4 16, .n 5 1 7 5 128, .p 5 1 7 6 224, .p 5 1 7 7 80,
   .n 5 1 7 8 272, .p 5 1 7 9 44, .p 5 1 7 10 96, .n 5 1 7 11 36, .n 5 1 8 1 28, .p 5 1 8 2 32,
   .p 5 1 8 3 100, .n 5 1 8 4 144, .n 5 1 8 5 32, .p 5 1 8 6 96, .n 5 1 8 7 80, .p 5 1 8 8 112,
   .n 5 1 8 9 4, .n 5 1 8 10 96, .p 5 1 8 11 44, .n 5 1 9 2 4, .n 5 1 9 3 40, .p 5 1 9 4 100,
   .p 5 1 9 5 40, .n 5 1 9 6 204, .p 5 1 9 7 48, .p 5 1 9 8 124, .n 5 1 9 9 56, .n 5 1 9 10 16,
   .p 5 1 9 11 8, .p 5 1 10 4 4, .n 5 1 10 5 8, .n 5 1 10 6 4, .p 5 1 10 7 16, .n 5 1 10 8 4,
   .n 5 1 10 9 8, .p 5 1 10 10 4, .p 6 0 7 3 24, .n 6 0 7 4 48, .n 6 0 7 5 48, .p 6 0 7 6 144,
   .n 6 0 7 8 144, .p 6 0 7 9 48, .p 6 0 7 10 48, .n 6 0 7 11 24, .n 6 0 8 1 24, .p 6 0 8 2 48,
   .p 6 0 8 3 48, .n 6 0 8 4 144, .p 6 0 8 6 144, .n 6 0 8 7 48, .n 6 0 8 8 48, .p 6 0 8 9 24]

set_option maxRecDepth 65536 in
private theorem g2_det4_10 : fmDet 4 g2Sub4_10 = g2Val4_10 := by decide

private def g2Sub4_11 (r c : Fin 4) : List FM :=
  g2FM ⟨r.val + 2, by omega⟩ (match c.val with | 0 => ⟨1, by decide⟩ | 1 => ⟨2, by decide⟩ | 2 => ⟨3, by decide⟩ | _ => ⟨5, by decide⟩)

private def g2Val4_11 : List FM :=
  [.n 0 7 3 6 64, .p 0 7 4 6 192, .p 0 7 4 7 64, .n 0 7 5 6 128, .n 0 7 5 7 128, .n 0 7 6 6 128,
   .n 0 7 6 7 64, .n 0 7 6 8 64, .p 0 7 7 6 192, .p 0 7 7 7 256, .p 0 7 7 8 192, .n 0 7 8 6 64,
   .n 0 7 8 7 64, .n 0 7 8 8 128, .n 0 7 9 7 128, .n 0 7 9 8 128, .p 0 7 10 7 64, .p 0 7 10 8 192,
   .n 0 7 11 8 64, .n 1 6 3 6 64, .p 1 6 4 5 32, .p 1 6 4 6 160, .p 1 6 4 7 32, .p 1 6 4 8 32,
   .n 1 6 5 5 32, .n 1 6 5 6 32, .n 1 6 5 7 128, .n 1 6 5 8 64, .n 1 6 5 9 32, .p 1 6 5 10 32,
   .n 1 6 6 4 32, .n 1 6 6 5 64, .n 1 6 6 6 256, .p 1 6 6 7 96, .p 1 6 6 8 64, .p 1 6 6 9 32,
   .n 1 6 6 10 96, .p 1 6 7 4 96, .p 1 6 7 5 64, .p 1 6 7 6 224, .p 1 6 7 7 192, .n 1 6 7 8 96,
   .p 1 6 7 9 64, .p 1 6 7 10 96, .n 1 6 8 4 96, .p 1 6 8 5 32, .p 1 6 8 6 128, .n 1 6 8 7 288,
   .p 1 6 8 8 64, .n 1 6 8 9 64, .n 1 6 8 10 32, .p 1 6 9 4 32, .n 1 6 9 5 32, .n 1 6 9 6 256,
   .p 1 6 9 8 32, .n 1 6 9 9 32, .p 1 6 10 6 96, .p 1 6 10 7 160, .n 1 6 10 8 32, .p 1 6 10 9 32,
   .n 1 6 11 7 64, .p 2 5 4 5 112, .n 2 5 4 6 104, .n 2 5 4 7 112, .p 2 5 4 8 104, .n 2 5 5 4 8,
   .n 2 5 5 5 104, .p 2 5 5 6 272, .p 2 5 5 7 144, .n 2 5 5 8 288, .n 2 5 5 9 104, .p 2 5 5 10 88,
   .n 2 5 6 3 8, .n 2 5 6 4 104, .n 2 5 6 5 312, .n 2 5 6 6 272, .p 2 5 6 7 336, .p 2 5 6 8 496,
   .p 2 5 6 9 88, .n 2 5 6 10 248, .p 2 5 6 11 24, .p 2 5 7 3 8, .p 2 5 7 4 416, .p 2 5 7 5 272,
   .p 2 5 7 6 8, .n 2 5 7 7 336, .n 2 5 7 8 744, .p 2 5 7 9 176, .p 2 5 7 10 256, .n 2 5 7 11 56,
   .p 2 5 8 3 40, .n 2 5 8 4 448, .p 2 5 8 5 256, .p 2 5 8 6 456, .n 2 5 8 7 448, .p 2 5 8 8 376,
   .n 2 5 8 9 144, .n 2 5 8 10 128, .p 2 5 8 11 40, .n 2 5 9 3 72, .p 2 5 9 4 40, .n 2 5 9 5 200,
   .n 2 5 9 6 624, .p 2 5 9 7 416, .p 2 5 9 8 480, .n 2 5 9 9 72, .p 2 5 9 10 40, .n 2 5 9 11 8,
   .p 2 5 10 3 32, .p 2 5 10 4 168, .n 2 5 10 5 56, .p 2 5 10 6 304, .p 2 5 10 7 96, .n 2 5 10 8 592,
   .p 2 5 10 9 56, .n 2 5 10 10 8, .n 2 5 11 4 64, .p 2 5 11 5 32, .n 2 5 11 6 40, .n 2 5 11 7 96,
   .p 2 5 11 8 168, .n 3 4 4 4 8, .p 3 4 4 5 32, .n 3 4 4 6 12, .n 3 4 4 7 32, .p 3 4 4 8 20,
   .n 3 4 5 2 8, .p 3 4 5 3 24, .n 3 4 5 4 44, .n 3 4 5 5 28, .p 3 4 5 6 56, .p 3 4 5 7 216,
   .n 3 4 5 8 192, .p 3 4 5 9 44, .n 3 4 5 10 68, .p 3 4 6 2 48, .n 3 4 6 3 36, .p 3 4 6 4 36,
   .n 3 4 6 5 260, .p 3 4 6 6 32, .n 3 4 6 7 160, .p 3 4 6 8 208, .n 3 4 6 9 92, .p 3 4 6 10 188,
   .p 3 4 6 11 36, .n 3 4 7 2 72, .n 3 4 7 3 4, .p 3 4 7 4 216, .p 3 4 7 5 240, .n 3 4 7 6 52,
   .n 3 4 7 7 352, .p 3 4 7 8 404, .n 3 4 7 9 128, .n 3 4 7 10 240, .n 3 4 7 11 12, .p 3 4 8 2 32,
   .p 3 4 8 3 4, .n 3 4 8 4 176, .p 3 4 8 5 416, .n 3 4 8 6 476, .p 3 4 8 7 464, .n 3 4 8 8 540,
   .p 3 4 8 9 192, .p 3 4 8 10 136, .n 3 4 8 11 52, .n 3 4 9 3 4, .n 3 4 9 4 268, .n 3 4 9 5 356,
   .p 3 4 9 6 496, .n 3 4 9 7 8, .p 3 4 9 8 56, .p 3 4 9 9 84, .n 3 4 9 10 28, .p 3 4 9 11 28,
   .p 3 4 10 3 16, .p 3 4 10 4 404, .n 3 4 10 5 188, .p 3 4 10 6 40, .n 3 4 10 7 240, .p 3 4 10 8 56,
   .n 3 4 10 9 100, .p 3 4 10 10 12, .n 3 4 11 4 160, .p 3 4 11 5 144, .n 3 4 11 6 84, .p 3 4 11 7 112,
   .n 3 4 11 8 12, .p 4 3 4 4 28, .n 4 3 4 5 48, .n 4 3 4 6 8, .p 4 3 4 7 48, .n 4 3 4 8 20,
   .p 4 3 5 2 8, .n 4 3 5 3 44, .p 4 3 5 4 48, .p 4 3 5 5 28, .n 4 3 5 6 144, .n 4 3 5 7 20,
   .p 4 3 5 8 80, .p 4 3 5 9 292, .n 4 3 5 10 248, .n 4 3 6 2 56, .p 4 3 6 3 72, .n 4 3 6 4 48,
   .p 4 3 6 5 176, .p 4 3 6 6 452, .n 4 3 6 7 464, .n 4 3 6 8 456, .n 4 3 6 9 224, .p 4 3 6 10 620,
   .n 4 3 6 11 72, .p 4 3 7 2 88, .p 4 3 7 3 20, .n 4 3 7 4 384, .p 4 3 7 5 16, .n 4 3 7 6 192,
   .p 4 3 7 7 8, .p 4 3 7 8 1408, .n 4 3 7 9 496, .n 4 3 7 10 664, .p 4 3 7 11 196, .n 4 3 8 2 40,
   .n 4 3 8 3 200, .p 4 3 8 4 788, .n 4 3 8 5 48, .n 4 3 8 6 1112, .p 4 3 8 7 1088, .n 4 3 8 8 988,
   .p 4 3 8 9 288, .p 4 3 8 10 328, .n 4 3 8 11 104, .p 4 3 9 3 200, .n 4 3 9 4 608, .n 4 3 9 5 204,
   .p 4 3 9 6 1264, .n 4 3 9 7 436, .n 4 3 9 8 352, .p 4 3 9 9 204, .n 4 3 9 10 48, .n 4 3 9 11 20,
   .n 4 3 10 3 48, .p 4 3 10 4 288, .n 4 3 10 5 80, .n 4 3 10 6 196, .n 4 3 10 7 320, .p 4 3 10 8 408,
   .n 4 3 10 9 64, .p 4 3 10 10 12, .n 4 3 11 4 112, .p 4 3 11 5 160, .n 4 3 11 6 64, .p 4 3 11 7 96,
   .n 4 3 11 8 80, .p 5 2 5 2 8, .n 5 2 5 3 16, .p 5 2 5 4 28, .p 5 2 5 6 60, .n 5 2 5 7 240,
   .p 5 2 5 8 52, .p 5 2 5 9 256, .n 5 2 5 10 148, .n 5 2 6 2 36, .p 5 2 6 3 20, .n 5 2 6 4 188,
   .p 5 2 6 5 272, .p 5 2 6 6 260, .n 5 2 6 7 120, .n 5 2 6 8 404, .n 5 2 6 9 64, .p 5 2 6 10 368,
   .n 5 2 6 11 108, .p 5 2 7 1 4, .p 5 2 7 2 120, .p 5 2 7 3 8, .n 5 2 7 4 252, .n 5 2 7 5 160,
   .p 5 2 7 6 140, .p 5 2 7 7 248, .p 5 2 7 8 76, .n 5 2 7 9 148, .n 5 2 7 10 84, .p 5 2 7 11 48,
   .n 5 2 8 1 16, .n 5 2 8 2 68, .n 5 2 8 3 16, .p 5 2 8 4 420, .n 5 2 8 5 256, .n 5 2 8 6 276,
   .p 5 2 8 7 208, .p 5 2 8 8 44, .p 5 2 8 9 16, .n 5 2 8 10 120, .p 5 2 8 11 64, .p 5 2 9 3 64,
   .n 5 2 9 4 128, .p 5 2 9 5 80, .n 5 2 9 6 32, .n 5 2 9 7 48, .p 5 2 9 8 128, .n 5 2 9 9 80,
   .p 5 2 9 10 32, .n 5 2 9 11 16, .n 5 2 10 3 24, .p 5 2 10 4 48, .n 5 2 10 5 8, .n 5 2 10 6 8,
   .n 5 2 10 7 24, .n 5 2 10 8 16, .p 5 2 10 9 56, .n 5 2 10 10 24, .n 5 2 11 4 24, .p 5 2 11 5 48,
   .n 5 2 11 7 48, .p 5 2 11 8 24, .n 6 1 5 2 8, .p 6 1 5 3 16, .n 6 1 5 4 16, .p 6 1 5 5 16,
   .p 6 1 5 6 32, .n 6 1 5 7 80, .p 6 1 5 8 16, .p 6 1 5 9 48, .n 6 1 5 10 24, .p 6 1 6 2 24,
   .n 6 1 6 3 56, .p 6 1 6 5 64, .n 6 1 6 6 16, .p 6 1 6 7 16, .n 6 1 6 8 64, .p 6 1 6 10 56,
   .n 6 1 6 11 24, .p 6 1 7 1 16, .n 6 1 7 2 16, .p 6 1 7 3 40, .n 6 1 7 4 104, .n 6 1 7 5 208,
   .p 6 1 7 6 520, .p 6 1 7 7 112, .n 6 1 7 8 664, .p 6 1 7 9 160, .p 6 1 7 10 264, .n 6 1 7 11 120,
   .n 6 1 8 1 56, .p 6 1 8 2 88, .p 6 1 8 3 200, .n 6 1 8 4 408, .n 6 1 8 5 16, .p 6 1 8 6 360,
   .n 6 1 8 7 256, .p 6 1 8 8 152, .p 6 1 8 9 40, .n 6 1 8 10 192, .p 6 1 8 11 88, .n 6 1 9 2 8,
   .n 6 1 9 3 80, .p 6 1 9 4 200, .p 6 1 9 5 80, .n 6 1 9 6 408, .p 6 1 9 7 96, .p 6 1 9 8 248,
   .n 6 1 9 9 112, .n 6 1 9 10 32, .p 6 1 9 11 16, .p 6 1 10 4 8, .n 6 1 10 5 16, .n 6 1 10 6 8,
   .p 6 1 10 7 32, .n 6 1 10 8 8, .n 6 1 10 9 16, .p 6 1 10 10 8, .p 7 0 7 3 48, .n 7 0 7 4 96,
   .n 7 0 7 5 96, .p 7 0 7 6 288, .n 7 0 7 8 288, .p 7 0 7 9 96, .p 7 0 7 10 96, .n 7 0 7 11 48,
   .n 7 0 8 1 48, .p 7 0 8 2 96, .p 7 0 8 3 96, .n 7 0 8 4 288, .p 7 0 8 6 288, .n 7 0 8 7 96,
   .n 7 0 8 8 96, .p 7 0 8 9 48]

set_option maxRecDepth 65536 in
private theorem g2_det4_11 : fmDet 4 g2Sub4_11 = g2Val4_11 := by decide

private def g2Sub4_12 (r c : Fin 4) : List FM :=
  g2FM ⟨r.val + 2, by omega⟩ (match c.val with | 0 => ⟨1, by decide⟩ | 1 => ⟨2, by decide⟩ | 2 => ⟨4, by decide⟩ | _ => ⟨5, by decide⟩)

private def g2Val4_12 : List FM :=
  [.p 0 7 5 6 64, .n 0 7 5 7 64, .n 0 7 6 6 192, .p 0 7 6 7 128, .p 0 7 6 8 64, .p 0 7 7 6 128,
   .p 0 7 7 7 64, .n 0 7 7 8 192, .p 0 7 8 6 128, .n 0 7 8 7 256, .p 0 7 8 8 128, .n 0 7 9 6 192,
   .p 0 7 9 7 64, .p 0 7 9 8 128, .p 0 7 10 6 64, .p 0 7 10 7 128, .n 0 7 10 8 192, .n 0 7 11 7 64,
   .p 0 7 11 8 64, .p 1 6 5 6 192, .n 1 6 5 7 160, .n 1 6 5 8 32, .p 1 6 5 9 32, .n 1 6 5 10 32,
   .n 1 6 6 5 32, .n 1 6 6 6 544, .p 1 6 6 7 320, .p 1 6 6 8 192, .n 1 6 6 9 32, .p 1 6 6 10 96,
   .p 1 6 7 5 32, .p 1 6 7 6 384, .p 1 6 7 7 160, .n 1 6 7 8 416, .n 1 6 7 9 64, .n 1 6 7 10 96,
   .p 1 6 8 4 32, .p 1 6 8 5 64, .p 1 6 8 6 224, .n 1 6 8 7 640, .p 1 6 8 8 224, .p 1 6 8 9 64,
   .p 1 6 8 10 32, .n 1 6 9 4 96, .n 1 6 9 5 64, .n 1 6 9 6 416, .p 1 6 9 7 160, .p 1 6 9 8 384,
   .p 1 6 9 9 32, .p 1 6 10 4 96, .n 1 6 10 5 32, .p 1 6 10 6 192, .p 1 6 10 7 320, .n 1 6 10 8 544,
   .n 1 6 10 9 32, .n 1 6 11 4 32, .p 1 6 11 5 32, .n 1 6 11 6 32, .n 1 6 11 7 160, .p 1 6 11 8 192,
   .n 2 5 4 6 8, .p 2 5 4 8 8, .p 2 5 5 4 8, .n 2 5 5 5 8, .p 2 5 5 6 96, .p 2 5 5 7 32,
   .n 2 5 5 8 144, .p 2 5 5 9 168, .n 2 5 5 10 152, .p 2 5 6 3 8, .n 2 5 6 4 8, .n 2 5 6 5 120,
   .n 2 5 6 6 96, .n 2 5 6 7 96, .p 2 5 6 8 48, .n 2 5 6 9 152, .p 2 5 6 10 440, .n 2 5 6 11 24,
   .n 2 5 7 3 8, .n 2 5 7 4 48, .p 2 5 7 5 160, .p 2 5 7 6 168, .n 2 5 7 7 96, .p 2 5 7 8 520,
   .n 2 5 7 9 304, .n 2 5 7 10 448, .p 2 5 7 11 56, .n 2 5 8 3 40, .p 2 5 8 4 224, .p 2 5 8 5 272,
   .n 2 5 8 6 600, .p 2 5 8 7 304, .n 2 5 8 8 584, .p 2 5 8 9 272, .p 2 5 8 10 192, .n 2 5 8 11 40,
   .p 2 5 9 3 72, .n 2 5 9 4 456, .n 2 5 9 5 328, .p 2 5 9 6 512, .n 2 5 9 7 80, .p 2 5 9 8 176,
   .p 2 5 9 9 136, .n 2 5 9 10 40, .p 2 5 9 11 8, .n 2 5 10 3 32, .p 2 5 10 4 424, .n 2 5 10 5 152,
   .p 2 5 10 6 64, .n 2 5 10 7 80, .n 2 5 10 8 112, .n 2 5 10 9 120, .p 2 5 10 10 8, .n 2 5 11 4 144,
   .p 2 5 11 5 176, .n 2 5 11 6 136, .p 2 5 11 7 16, .p 2 5 11 8 88, .n 3 4 4 6 4, .p 3 4 4 8 4,
   .p 3 4 5 4 12, .p 3 4 5 5 4, .n 3 4 5 6 128, .p 3 4 5 7 208, .n 3 4 5 8 176, .p 3 4 5 9 300,
   .n 3 4 5 10 220, .n 3 4 6 2 8, .n 3 4 6 3 4, .p 3 4 6 4 12, .n 3 4 6 5 100, .p 3 4 6 6 584,
   .n 3 4 6 7 616, .n 3 4 6 8 176, .n 3 4 6 9 220, .p 3 4 6 10 612, .n 3 4 6 11 84, .p 3 4 7 2 16,
   .n 3 4 7 3 12, .n 3 4 7 4 112, .p 3 4 7 5 144, .n 3 4 7 6 156, .n 3 4 7 7 320, .p 3 4 7 8 1332,
   .n 3 4 7 9 448, .n 3 4 7 10 568, .p 3 4 7 11 124, .n 3 4 8 2 8, .n 3 4 8 3 20, .p 3 4 8 4 264,
   .p 3 4 8 5 320, .n 3 4 8 6 1268, .p 3 4 8 7 1456, .n 3 4 8 8 1292, .p 3 4 8 9 320, .p 3 4 8 10 256,
   .n 3 4 8 11 28, .p 3 4 9 3 124, .n 3 4 9 4 580, .n 3 4 9 5 452, .p 3 4 9 6 1336, .n 3 4 9 7 320,
   .n 3 4 9 8 152, .p 3 4 9 9 148, .n 3 4 9 10 92, .n 3 4 9 11 12, .n 3 4 10 3 88, .p 3 4 10 4 620,
   .n 3 4 10 5 220, .n 3 4 10 6 176, .n 3 4 10 7 616, .p 3 4 10 8 568, .n 3 4 10 9 100, .p 3 4 10 10 12,
   .n 3 4 11 4 216, .p 3 4 11 5 304, .n 3 4 11 6 188, .p 3 4 11 7 208, .n 3 4 11 8 108, .n 4 3 5 4 16,
   .p 4 3 5 5 32, .n 4 3 5 6 44, .p 4 3 5 7 16, .n 4 3 5 8 72, .p 4 3 5 9 208, .n 4 3 5 10 124,
   .p 4 3 6 2 16, .n 4 3 6 3 32, .p 4 3 6 4 16, .p 4 3 6 5 28, .p 4 3 6 6 240, .n 4 3 6 7 300,
   .n 4 3 6 8 80, .n 4 3 6 9 124, .p 4 3 6 10 320, .n 4 3 6 11 84, .n 4 3 7 2 32, .p 4 3 7 3 16,
   .n 4 3 7 4 4, .n 4 3 7 5 160, .p 4 3 7 6 216, .p 4 3 7 8 108, .n 4 3 7 9 112, .n 4 3 7 10 32,
   .p 4 3 8 2 16, .p 4 3 8 3 132, .n 4 3 8 4 192, .p 4 3 8 5 96, .n 4 3 8 6 352, .p 4 3 8 7 600,
   .n 4 3 8 8 384, .p 4 3 8 9 96, .n 4 3 8 10 112, .p 4 3 8 11 100, .n 4 3 9 3 32, .n 4 3 9 4 16,
   .n 4 3 9 5 80, .p 4 3 9 6 140, .n 4 3 9 7 32, .p 4 3 9 8 168, .n 4 3 9 9 96, .n 4 3 9 10 36,
   .n 4 3 9 11 16, .n 4 3 10 3 84, .p 4 3 10 4 336, .n 4 3 10 5 124, .n 4 3 10 6 112, .n 4 3 10 7 332,
   .p 4 3 10 8 304, .p 4 3 10 9 28, .n 4 3 10 10 16, .n 4 3 11 4 124, .p 4 3 11 5 208, .n 4 3 11 6 88,
   .p 4 3 11 7 48, .n 4 3 11 8 44, .p 5 2 5 4 8, .n 5 2 5 5 16, .p 5 2 5 6 24, .n 5 2 5 7 32,
   .n 5 2 5 8 8, .p 5 2 5 9 48, .n 5 2 5 10 24, .n 5 2 6 2 8, .p 5 2 6 3 16, .n 5 2 6 4 8,
   .p 5 2 6 5 8, .n 5 2 6 6 16, .p 5 2 6 7 24, .n 5 2 6 8 24, .n 5 2 6 9 24, .p 5 2 6 10 56,
   .n 5 2 6 11 24, .n 5 2 7 2 4, .p 5 2 7 3 8, .n 5 2 7 4 20, .n 5 2 7 5 160, .p 5 2 7 6 348,
   .p 5 2 7 7 160, .n 5 2 7 8 604, .p 5 2 7 9 112, .p 5 2 7 10 280, .n 5 2 7 11 120, .p 5 2 8 1 4,
   .p 5 2 8 2 8, .p 5 2 8 3 112, .n 5 2 8 4 260, .p 5 2 8 6 252, .n 5 2 8 7 248, .p 5 2 8 8 276,
   .n 5 2 8 9 4, .n 5 2 8 10 276, .p 5 2 8 11 136, .n 5 2 9 2 4, .n 5 2 9 3 124, .p 5 2 9 4 284,
   .p 5 2 9 5 136, .n 5 2 9 6 620, .p 5 2 9 7 144, .p 5 2 9 8 372, .n 5 2 9 9 168, .n 5 2 9 10 32,
   .p 5 2 9 11 12, .n 5 2 10 3 24, .p 5 2 10 4 52, .n 5 2 10 5 8, .n 5 2 10 6 36, .p 5 2 10 7 8,
   .n 5 2 10 8 4, .p 5 2 10 9 24, .n 5 2 10 10 12, .n 5 2 11 4 24, .p 5 2 11 5 48, .n 5 2 11 7 48,
   .p 5 2 11 8 24, .p 6 1 7 2 8, .n 6 1 7 3 16, .n 6 1 7 4 8, .n 6 1 7 5 16, .p 6 1 7 6 88,
   .p 6 1 7 7 32, .n 6 1 7 8 184, .p 6 1 7 9 48, .p 6 1 7 10 96, .n 6 1 7 11 48, .p 6 1 8 1 8,
   .n 6 1 8 2 16, .p 6 1 8 3 32, .n 6 1 8 4 56, .p 6 1 8 5 16, .p 6 1 8 6 56, .n 6 1 8 7 112,
   .p 6 1 8 8 120, .p 6 1 8 9 8, .n 6 1 8 10 104, .p 6 1 8 11 48, .n 6 1 9 2 8, .n 6 1 9 3 40,
   .p 6 1 9 4 120, .p 6 1 9 5 32, .n 6 1 9 6 232, .p 6 1 9 7 64, .p 6 1 9 8 136, .n 6 1 9 9 64,
   .n 6 1 9 10 16, .p 6 1 9 11 8, .p 6 1 10 4 8, .n 6 1 10 5 16, .n 6 1 10 6 8, .p 6 1 10 7 32,
   .n 6 1 10 8 8, .n 6 1 10 9 16, .p 6 1 10 10 8]

set_option maxRecDepth 65536 in
private theorem g2_det4_12 : fmDet 4 g2Sub4_12 = g2Val4_12 := by decide

private def g2Sub4_13 (r c : Fin 4) : List FM :=
  g2FM ⟨r.val + 2, by omega⟩ (match c.val with | 0 => ⟨1, by decide⟩ | 1 => ⟨3, by decide⟩ | 2 => ⟨4, by decide⟩ | _ => ⟨5, by decide⟩)

private def g2Val4_13 : List FM :=
  [.n 0 6 4 6 32, .p 0 6 5 6 96, .n 0 6 6 6 32, .p 0 6 6 8 32, .n 0 6 7 6 160, .n 0 6 7 8 96,
   .p 0 6 8 6 160, .p 0 6 8 8 32, .p 0 6 9 6 32, .p 0 6 9 8 160, .n 0 6 10 6 96, .n 0 6 10 8 160,
   .p 0 6 11 6 32, .n 0 6 11 8 32, .p 0 6 12 8 96, .n 0 6 13 8 32, .n 1 5 4 6 16, .n 1 5 4 8 16,
   .p 1 5 5 5 32, .p 1 5 5 6 96, .n 1 5 5 7 64, .p 1 5 5 8 16, .p 1 5 5 9 32, .n 1 5 5 10 16,
   .n 1 5 6 5 32, .n 1 5 6 6 144, .p 1 5 6 7 64, .p 1 5 6 8 96, .n 1 5 6 9 32, .p 1 5 6 10 48,
   .n 1 5 7 4 16, .n 1 5 7 5 96, .n 1 5 7 6 64, .p 1 5 7 7 192, .n 1 5 7 8 144, .n 1 5 7 9 96,
   .n 1 5 7 10 32, .p 1 5 8 4 48, .p 1 5 8 5 96, .p 1 5 8 6 288, .n 1 5 8 7 192, .n 1 5 8 8 112,
   .p 1 5 8 9 96, .n 1 5 8 10 32, .n 1 5 9 4 32, .p 1 5 9 5 96, .n 1 5 9 6 112, .n 1 5 9 7 192,
   .p 1 5 9 8 288, .p 1 5 9 9 96, .p 1 5 9 10 48, .n 1 5 10 4 32, .n 1 5 10 5 96, .n 1 5 10 6 144,
   .p 1 5 10 7 192, .n 1 5 10 8 64, .n 1 5 10 9 96, .n 1 5 10 10 16, .p 1 5 11 4 48, .n 1 5 11 5 32,
   .p 1 5 11 6 96, .p 1 5 11 7 64, .n 1 5 11 8 144, .n 1 5 11 9 32, .n 1 5 12 4 16, .p 1 5 12 5 32,
   .p 1 5 12 6 16, .n 1 5 12 7 64, .p 1 5 12 8 96, .p 1 5 12 9 32, .n 1 5 13 6 16, .n 1 5 13 8 16,
   .p 2 4 4 6 8, .n 2 4 4 8 8, .n 2 4 5 4 16, .p 2 4 5 5 48, .n 2 4 5 6 32, .n 2 4 5 8 8,
   .p 2 4 5 9 80, .n 2 4 5 10 72, .p 2 4 6 4 16, .n 2 4 6 5 48, .p 2 4 6 6 24, .n 2 4 6 8 112,
   .n 2 4 6 9 80, .p 2 4 6 10 200, .n 2 4 7 4 24, .n 2 4 7 5 176, .p 2 4 7 6 192, .p 2 4 7 8 312,
   .n 2 4 7 9 208, .n 2 4 7 10 96, .p 2 4 8 4 152, .p 2 4 8 5 176, .n 2 4 8 6 336, .n 2 4 8 8 40,
   .p 2 4 8 9 208, .n 2 4 8 10 160, .n 2 4 9 4 160, .p 2 4 9 5 208, .n 2 4 9 6 40, .n 2 4 9 8 336,
   .p 2 4 9 9 176, .p 2 4 9 10 152, .n 2 4 10 4 96, .n 2 4 10 5 208, .p 2 4 10 6 312, .p 2 4 10 8 192,
   .n 2 4 10 9 176, .n 2 4 10 10 24, .p 2 4 11 4 200, .n 2 4 11 5 80, .n 2 4 11 6 112, .p 2 4 11 8 24,
   .n 2 4 11 9 48, .p 2 4 11 10 16, .n 2 4 12 4 72, .p 2 4 12 5 80, .n 2 4 12 6 8, .n 2 4 12 8 32,
   .p 2 4 12 9 48, .n 2 4 12 10 16, .n 2 4 13 6 8, .p 2 4 13 8 8, .p 3 3 5 4 24, .n 3 3 5 5 48,
   .n 3 3 5 6 40, .p 3 3 5 7 96, .n 3 3 5 8 56, .p 3 3 5 9 80, .n 3 3 5 10 56, .n 3 3 6 2 4,
   .p 3 3 6 3 8, .n 3 3 6 4 32, .n 3 3 6 5 16, .p 3 3 6 6 248, .n 3 3 6 7 144, .n 3 3 6 8 192,
   .p 3 3 6 9 48, .p 3 3 6 10 108, .n 3 3 6 11 24, .p 3 3 7 2 20, .n 3 3 7 3 8, .n 3 3 7 4 80,
   .p 3 3 7 5 144, .n 3 3 7 6 8, .n 3 3 7 7 368, .p 3 3 7 8 496, .n 3 3 7 9 176, .n 3 3 7 10 44,
   .p 3 3 7 11 24, .n 3 3 8 2 28, .n 3 3 8 3 32, .p 3 3 8 4 164, .p 3 3 8 5 112, .n 3 3 8 6 624,
   .p 3 3 8 7 416, .p 3 3 8 8 176, .n 3 3 8 9 144, .n 3 3 8 10 84, .p 3 3 8 11 32, .p 3 3 8 12 12,
   .p 3 3 9 2 12, .p 3 3 9 3 32, .n 3 3 9 4 84, .n 3 3 9 5 144, .p 3 3 9 6 176, .p 3 3 9 7 416,
   .n 3 3 9 8 624, .p 3 3 9 9 112, .p 3 3 9 10 164, .n 3 3 9 11 32, .n 3 3 9 12 28, .p 3 3 10 3 24,
   .n 3 3 10 4 44, .n 3 3 10 5 176, .p 3 3 10 6 496, .n 3 3 10 7 368, .n 3 3 10 8 8, .p 3 3 10 9 144,
   .n 3 3 10 10 80, .n 3 3 10 11 8, .p 3 3 10 12 20, .n 3 3 11 3 24, .p 3 3 11 4 108, .p 3 3 11 5 48,
   .n 3 3 11 6 192, .n 3 3 11 7 144, .p 3 3 11 8 248, .n 3 3 11 9 16, .n 3 3 11 10 32, .p 3 3 11 11 8,
   .n 3 3 11 12 4, .n 3 3 12 4 56, .p 3 3 12 5 80, .n 3 3 12 6 56, .p 3 3 12 7 96, .n 3 3 12 8 40,
   .n 3 3 12 9 48, .p 3 3 12 10 24, .n 4 2 5 4 4, .p 4 2 5 5 8, .p 4 2 5 6 12, .n 4 2 5 7 32,
   .p 4 2 5 8 4, .p 4 2 5 9 24, .n 4 2 5 10 12, .p 4 2 6 2 8, .n 4 2 6 3 20, .p 4 2 6 4 20,
   .p 4 2 6 5 32, .n 4 2 6 6 12, .n 4 2 6 7 128, .p 4 2 6 8 44, .p 4 2 6 9 128, .n 4 2 6 10 60,
   .n 4 2 6 11 12, .n 4 2 7 2 32, .p 4 2 7 3 12, .n 4 2 7 4 36, .p 4 2 7 5 96, .p 4 2 7 6 116,
   .n 4 2 7 7 96, .n 4 2 7 8 148, .p 4 2 7 10 108, .n 4 2 7 11 12, .n 4 2 7 12 8, .p 4 2 8 2 48,
   .p 4 2 8 3 32, .n 4 2 8 4 164, .n 4 2 8 5 56, .p 4 2 8 6 60, .p 4 2 8 7 256, .n 4 2 8 8 76,
   .n 4 2 8 9 232, .p 4 2 8 10 148, .n 4 2 8 12 16, .n 4 2 9 2 16, .p 4 2 9 4 148, .n 4 2 9 5 232,
   .n 4 2 9 6 76, .p 4 2 9 7 256, .p 4 2 9 8 60, .n 4 2 9 9 56, .n 4 2 9 10 164, .p 4 2 9 11 32,
   .p 4 2 9 12 48, .n 4 2 10 2 8, .n 4 2 10 3 12, .p 4 2 10 4 108, .n 4 2 10 6 148, .n 4 2 10 7 96,
   .p 4 2 10 8 116, .p 4 2 10 9 96, .n 4 2 10 10 36, .p 4 2 10 11 12, .n 4 2 10 12 32, .n 4 2 11 3 12,
   .n 4 2 11 4 60, .p 4 2 11 5 128, .p 4 2 11 6 44, .n 4 2 11 7 128, .n 4 2 11 8 12, .p 4 2 11 9 32,
   .p 4 2 11 10 20, .n 4 2 11 11 20, .p 4 2 11 12 8, .n 4 2 12 4 12, .p 4 2 12 5 24, .p 4 2 12 6 4,
   .n 4 2 12 7 32, .p 4 2 12 8 12, .p 4 2 12 9 8, .n 4 2 12 10 4, .n 5 1 6 2 4, .p 5 1 6 3 8,
   .n 5 1 6 5 8, .p 5 1 6 6 8, .n 5 1 6 7 8, .p 5 1 6 9 8, .n 5 1 6 10 4, .p 5 1 7 2 8,
   .n 5 1 7 3 8, .n 5 1 7 4 36, .n 5 1 7 5 40, .p 5 1 7 6 192, .p 5 1 7 7 56, .n 5 1 7 8 328,
   .p 5 1 7 9 40, .p 5 1 7 10 184, .n 5 1 7 11 48, .n 5 1 7 12 20, .p 5 1 8 1 4, .p 5 1 8 2 16,
   .p 5 1 8 3 48, .n 5 1 8 4 192, .n 5 1 8 5 52, .p 5 1 8 6 368, .n 5 1 8 7 64, .n 5 1 8 8 208,
   .p 5 1 8 9 60, .p 5 1 8 11 16, .p 5 1 8 12 16, .n 5 1 8 13 12, .n 5 1 9 1 12, .p 5 1 9 2 16,
   .p 5 1 9 3 16, .p 5 1 9 5 60, .n 5 1 9 6 208, .n 5 1 9 7 64, .p 5 1 9 8 368, .n 5 1 9 9 52,
   .n 5 1 9 10 192, .p 5 1 9 11 48, .p 5 1 9 12 16, .p 5 1 9 13 4, .n 5 1 10 2 20, .n 5 1 10 3 48,
   .p 5 1 10 4 184, .p 5 1 10 5 40, .n 5 1 10 6 328, .p 5 1 10 7 56, .p 5 1 10 8 192, .n 5 1 10 9 40,
   .n 5 1 10 10 36, .n 5 1 10 11 8, .p 5 1 10 12 8, .n 5 1 11 4 4, .p 5 1 11 5 8, .n 5 1 11 7 8,
   .p 5 1 11 8 8, .n 5 1 11 9 8, .p 5 1 11 11 8, .n 5 1 11 12 4, .p 6 0 8 3 24, .n 6 0 8 4 48,
   .n 6 0 8 5 24, .p 6 0 8 6 96, .n 6 0 8 7 48, .p 6 0 8 9 48, .n 6 0 8 10 96, .p 6 0 8 11 24,
   .p 6 0 8 12 48, .n 6 0 8 13 24, .n 6 0 9 1 24, .p 6 0 9 2 48, .p 6 0 9 3 24, .n 6 0 9 4 96,
   .p 6 0 9 5 48, .n 6 0 9 7 48, .p 6 0 9 8 96, .n 6 0 9 9 24, .n 6 0 9 10 48, .p 6 0 9 11 24]

set_option maxRecDepth 65536 in
private theorem g2_det4_13 : fmDet 4 g2Sub4_13 = g2Val4_13 := by decide

private def g2Sub4_14 (r c : Fin 4) : List FM :=
  g2FM ⟨r.val + 2, by omega⟩ (match c.val with | 0 => ⟨2, by decide⟩ | 1 => ⟨3, by decide⟩ | 2 => ⟨4, by decide⟩ | _ => ⟨5, by decide⟩)

private def g2Val4_14 : List FM :=
  [.p 1 5 4 6 8, .n 1 5 4 8 8, .n 1 5 5 4 8, .p 1 5 5 5 8, .n 1 5 5 6 8, .n 1 5 5 7 16,
   .p 1 5 5 8 8, .p 1 5 5 9 8, .p 1 5 5 10 8, .n 1 5 6 3 8, .p 1 5 6 4 16, .n 1 5 6 6 16,
   .p 1 5 6 7 16, .p 1 5 6 8 16, .n 1 5 6 10 16, .n 1 5 6 11 8, .p 1 5 7 3 16, .p 1 5 7 4 8,
   .n 1 5 7 5 24, .p 1 5 7 6 8, .p 1 5 7 7 16, .n 1 5 7 8 8, .n 1 5 7 9 24, .n 1 5 7 10 8,
   .p 1 5 7 11 16, .n 1 5 8 4 32, .p 1 5 8 6 16, .n 1 5 8 8 16, .p 1 5 8 10 32, .n 1 5 9 3 16,
   .p 1 5 9 4 8, .p 1 5 9 5 24, .p 1 5 9 6 8, .n 1 5 9 7 16, .n 1 5 9 8 8, .p 1 5 9 9 24,
   .n 1 5 9 10 8, .n 1 5 9 11 16, .p 1 5 10 3 8, .p 1 5 10 4 16, .n 1 5 10 6 16, .n 1 5 10 7 16,
   .p 1 5 10 8 16, .n 1 5 10 10 16, .p 1 5 10 11 8, .n 1 5 11 4 8, .n 1 5 11 5 8, .n 1 5 11 6 8,
   .p 1 5 11 7 16, .p 1 5 11 8 8, .n 1 5 11 9 8, .p 1 5 11 10 8, .p 1 5 12 6 8, .n 1 5 12 8 8,
   .p 2 4 4 6 4, .n 2 4 4 8 4, .n 2 4 5 4 12, .n 2 4 5 5 4, .p 2 4 5 6 20, .n 2 4 5 8 12,
   .p 2 4 5 9 4, .p 2 4 5 10 4, .p 2 4 6 2 8, .p 2 4 6 3 4, .n 2 4 6 6 16, .p 2 4 6 10 8,
   .n 2 4 6 11 4, .n 2 4 7 2 16, .p 2 4 7 4 20, .p 2 4 7 5 4, .p 2 4 7 6 4, .p 2 4 7 8 4,
   .n 2 4 7 9 4, .n 2 4 7 10 12, .p 2 4 8 2 8, .n 2 4 8 3 8, .n 2 4 8 4 8, .n 2 4 8 6 24,
   .p 2 4 8 8 24, .p 2 4 8 10 8, .p 2 4 8 11 8, .n 2 4 8 12 8, .p 2 4 9 4 12, .p 2 4 9 5 4,
   .n 2 4 9 6 4, .n 2 4 9 8 4, .n 2 4 9 9 4, .n 2 4 9 10 20, .p 2 4 9 12 16, .p 2 4 10 3 4,
   .n 2 4 10 4 8, .p 2 4 10 8 16, .n 2 4 10 11 4, .n 2 4 10 12 8, .n 2 4 11 4 4, .n 2 4 11 5 4,
   .p 2 4 11 6 12, .n 2 4 11 8 20, .p 2 4 11 9 4, .p 2 4 11 10 12, .p 2 4 12 6 4, .n 2 4 12 8 4,
   .p 3 3 5 4 16, .n 3 3 5 5 32, .p 3 3 5 7 32, .n 3 3 5 8 16, .n 3 3 6 2 16, .p 3 3 6 3 32,
   .n 3 3 6 4 32, .p 3 3 6 6 64, .n 3 3 6 7 32, .n 3 3 6 8 32, .p 3 3 6 10 16, .p 3 3 7 2 32,
   .n 3 3 7 3 32, .n 3 3 7 4 32, .p 3 3 7 5 64, .n 3 3 7 6 48, .n 3 3 7 7 32, .p 3 3 7 8 32,
   .p 3 3 7 9 32, .p 3 3 7 10 16, .n 3 3 7 11 32, .n 3 3 8 2 16, .n 3 3 8 3 32, .p 3 3 8 4 80,
   .n 3 3 8 6 32, .p 3 3 8 8 32, .n 3 3 8 10 80, .p 3 3 8 11 32, .p 3 3 8 12 16, .p 3 3 9 3 32,
   .n 3 3 9 4 16, .n 3 3 9 5 32, .n 3 3 9 6 32, .p 3 3 9 7 32, .p 3 3 9 8 48, .n 3 3 9 9 64,
   .p 3 3 9 10 32, .p 3 3 9 11 32, .n 3 3 9 12 32, .n 3 3 10 4 16, .p 3 3 10 6 32, .p 3 3 10 7 32,
   .n 3 3 10 8 64, .p 3 3 10 10 32, .n 3 3 10 11 32, .p 3 3 10 12 16, .p 3 3 11 6 16, .n 3 3 11 7 32,
   .p 3 3 11 9 32, .n 3 3 11 10 16, .n 4 2 5 4 8, .p 4 2 5 5 16, .n 4 2 5 7 16, .p 4 2 5 8 8,
   .p 4 2 6 2 8, .n 4 2 6 3 16, .n 4 2 6 4 4, .p 4 2 6 5 16, .p 4 2 6 6 12, .n 4 2 6 7 16,
   .n 4 2 6 8 12, .p 4 2 6 9 16, .n 4 2 6 10 4, .p 4 2 7 2 4, .p 4 2 7 3 4, .n 4 2 7 4 12,
   .n 4 2 7 5 8, .p 4 2 7 6 24, .n 4 2 7 7 16, .n 4 2 7 8 16, .p 4 2 7 9 24, .p 4 2 7 10 4,
   .n 4 2 7 11 4, .n 4 2 7 12 4, .n 4 2 8 1 4, .n 4 2 8 2 8, .p 4 2 8 3 24, .n 4 2 8 4 16,
   .n 4 2 8 5 4, .p 4 2 8 6 24, .n 4 2 8 8 24, .p 4 2 8 9 4, .p 4 2 8 10 16, .n 4 2 8 11 24,
   .p 4 2 8 12 8, .p 4 2 8 13 4, .p 4 2 9 2 4, .p 4 2 9 3 4, .n 4 2 9 4 4, .n 4 2 9 5 24,
   .p 4 2 9 6 16, .p 4 2 9 7 16, .n 4 2 9 8 24, .p 4 2 9 9 8, .p 4 2 9 10 12, .n 4 2 9 11 4,
   .n 4 2 9 12 4, .p 4 2 10 4 4, .n 4 2 10 5 16, .p 4 2 10 6 12, .p 4 2 10 7 16, .n 4 2 10 8 12,
   .n 4 2 10 9 16, .p 4 2 10 10 4, .p 4 2 10 11 16, .n 4 2 10 12 8, .n 4 2 11 6 8, .p 4 2 11 7 16,
   .n 4 2 11 9 16, .p 4 2 11 10 8, .p 5 1 6 4 8, .n 5 1 6 5 16, .n 5 1 6 6 8, .p 5 1 6 7 32,
   .n 5 1 6 8 8, .n 5 1 6 9 16, .p 5 1 6 10 8, .n 5 1 7 2 8, .p 5 1 7 3 24, .n 5 1 7 4 8,
   .n 5 1 7 5 48, .p 5 1 7 6 48, .p 5 1 7 7 32, .n 5 1 7 8 48, .n 5 1 7 9 16, .p 5 1 7 10 24,
   .p 5 1 7 11 8, .n 5 1 7 12 8, .n 5 1 8 1 8, .p 5 1 8 2 16, .p 5 1 8 3 16, .n 5 1 8 4 48,
   .n 5 1 8 5 8, .p 5 1 8 6 64, .n 5 1 8 8 64, .p 5 1 8 9 8, .p 5 1 8 10 48, .n 5 1 8 11 16,
   .n 5 1 8 12 16, .p 5 1 8 13 8, .p 5 1 9 2 8, .n 5 1 9 3 8, .n 5 1 9 4 24, .p 5 1 9 5 16,
   .p 5 1 9 6 48, .n 5 1 9 7 32, .n 5 1 9 8 48, .p 5 1 9 9 48, .p 5 1 9 10 8, .n 5 1 9 11 24,
   .p 5 1 9 12 8, .n 5 1 10 4 8, .p 5 1 10 5 16, .p 5 1 10 6 8, .n 5 1 10 7 32, .p 5 1 10 8 8,
   .p 5 1 10 9 16, .n 5 1 10 10 8]

set_option maxRecDepth 65536 in
private theorem g2_det4_14 : fmDet 4 g2Sub4_14 = g2Val4_14 := by decide

private theorem fmSumPrefix_five (f : Fin 5 -> List FM) :
    fmSumPrefix 5 f 5 =
      fmMerge (fmMerge (fmMerge (fmMerge (fmMerge []
        (f ⟨0, by decide⟩)) (f ⟨1, by decide⟩)) (f ⟨2, by decide⟩))
        (f ⟨3, by decide⟩)) (f ⟨4, by decide⟩) := by
  simp only [fmSumPrefix, dite_true,
             (by decide : 0 < 5), (by decide : 1 < 5), (by decide : 2 < 5),
             (by decide : 3 < 5), (by decide : 4 < 5)]

private theorem fmSumPrefix_six (f : Fin 6 -> List FM) :
    fmSumPrefix 6 f 6 =
      fmMerge (fmMerge (fmMerge (fmMerge (fmMerge (fmMerge []
        (f ⟨0, by decide⟩)) (f ⟨1, by decide⟩)) (f ⟨2, by decide⟩))
        (f ⟨3, by decide⟩)) (f ⟨4, by decide⟩)) (f ⟨5, by decide⟩) := by
  simp only [fmSumPrefix, dite_true,
             (by decide : 0 < 6), (by decide : 1 < 6), (by decide : 2 < 6),
             (by decide : 3 < 6), (by decide : 4 < 6), (by decide : 5 < 6)]

private theorem fin4Mat_eq_of_vals (A B : Fin 4 -> Fin 4 -> List FM)
    (h : ∀ r c : Fin 4, A r c = B r c) : A = B :=
  funext (fun r => funext (fun c => h r c))

private theorem fmDet5_of_sub4 (M : Fin 5 -> Fin 5 -> List FM)
    (S0 S1 S2 S3 S4 : Fin 4 -> Fin 4 -> List FM)
    (v0 v1 v2 v3 v4 res : List FM)
    (hs0 : fmSubMat M ⟨0, by decide⟩ = S0) (hd0 : fmDet 4 S0 = v0)
    (hs1 : fmSubMat M ⟨1, by decide⟩ = S1) (hd1 : fmDet 4 S1 = v1)
    (hs2 : fmSubMat M ⟨2, by decide⟩ = S2) (hd2 : fmDet 4 S2 = v2)
    (hs3 : fmSubMat M ⟨3, by decide⟩ = S3) (hd3 : fmDet 4 S3 = v3)
    (hs4 : fmSubMat M ⟨4, by decide⟩ = S4) (hd4 : fmDet 4 S4 = v4)
    (hcomb :
      fmMerge (fmMerge (fmMerge (fmMerge (fmMerge []
        (fmMul (M ⟨0, by decide⟩ ⟨0, by decide⟩) v0))
        (fmMul (fmNeg (M ⟨0, by decide⟩ ⟨1, by decide⟩)) v1))
        (fmMul (M ⟨0, by decide⟩ ⟨2, by decide⟩) v2))
        (fmMul (fmNeg (M ⟨0, by decide⟩ ⟨3, by decide⟩)) v3))
        (fmMul (M ⟨0, by decide⟩ ⟨4, by decide⟩) v4) = res) :
    fmDet 5 M = res := by
  conv => lhs; unfold fmDet
  rw [fmSumPrefix_five]
  dsimp only
  simp only [(by decide : 0 % 2 = 0), (by decide : ¬ (1 % 2 = 0)), ite_true, ite_false]
  rw [hs0, hd0, hs1, hd1, hs2, hd2, hs3, hd3, hs4, hd4]
  exact hcomb

private theorem fmDet5_of_sub4_split (M : Fin 5 -> Fin 5 -> List FM)
    (S0 S1 S2 S3 S4 : Fin 4 -> Fin 4 -> List FM)
    (v0 v1 v2 v3 v4 m01 m012 res : List FM)
    (hs0 : fmSubMat M ⟨0, by decide⟩ = S0) (hd0 : fmDet 4 S0 = v0)
    (hs1 : fmSubMat M ⟨1, by decide⟩ = S1) (hd1 : fmDet 4 S1 = v1)
    (hs2 : fmSubMat M ⟨2, by decide⟩ = S2) (hd2 : fmDet 4 S2 = v2)
    (hs3 : fmSubMat M ⟨3, by decide⟩ = S3) (hd3 : fmDet 4 S3 = v3)
    (hs4 : fmSubMat M ⟨4, by decide⟩ = S4) (hd4 : fmDet 4 S4 = v4)
    (hc01 : fmMerge (fmMerge [] (fmMul (M ⟨0, by decide⟩ ⟨0, by decide⟩) v0))
              (fmMul (fmNeg (M ⟨0, by decide⟩ ⟨1, by decide⟩)) v1) = m01)
    (hc012 : fmMerge m01 (fmMul (M ⟨0, by decide⟩ ⟨2, by decide⟩) v2) = m012)
    (hc34 : fmMerge (fmMerge m012 (fmMul (fmNeg (M ⟨0, by decide⟩ ⟨3, by decide⟩)) v3))
              (fmMul (M ⟨0, by decide⟩ ⟨4, by decide⟩) v4) = res) :
    fmDet 5 M = res := by
  apply fmDet5_of_sub4 M S0 S1 S2 S3 S4 v0 v1 v2 v3 v4 res
    hs0 hd0 hs1 hd1 hs2 hd2 hs3 hd3 hs4 hd4
  rw [hc01, hc012]
  exact hc34

private theorem fmDet6_of_sub5 (M : Fin 6 -> Fin 6 -> List FM)
    (v0 v1 v2 v3 v4 v5 res : List FM)
    (hd0 : fmDet 5 (fmSubMat M ⟨0, by decide⟩) = v0)
    (hd1 : fmDet 5 (fmSubMat M ⟨1, by decide⟩) = v1)
    (hd2 : fmDet 5 (fmSubMat M ⟨2, by decide⟩) = v2)
    (hd3 : fmDet 5 (fmSubMat M ⟨3, by decide⟩) = v3)
    (hd4 : fmDet 5 (fmSubMat M ⟨4, by decide⟩) = v4)
    (hd5 : fmDet 5 (fmSubMat M ⟨5, by decide⟩) = v5)
    (hcomb :
      fmMerge (fmMerge (fmMerge (fmMerge (fmMerge (fmMerge []
        (fmMul (M ⟨0, by decide⟩ ⟨0, by decide⟩) v0))
        (fmMul (fmNeg (M ⟨0, by decide⟩ ⟨1, by decide⟩)) v1))
        (fmMul (M ⟨0, by decide⟩ ⟨2, by decide⟩) v2))
        (fmMul (fmNeg (M ⟨0, by decide⟩ ⟨3, by decide⟩)) v3))
        (fmMul (M ⟨0, by decide⟩ ⟨4, by decide⟩) v4))
        (fmMul (fmNeg (M ⟨0, by decide⟩ ⟨5, by decide⟩)) v5) = res) :
    fmDet 6 M = res := by
  conv => lhs; unfold fmDet
  rw [fmSumPrefix_six]
  dsimp only
  simp only [(by decide : 0 % 2 = 0), (by decide : ¬ (1 % 2 = 0)), ite_true, ite_false]
  rw [hd0, hd1, hd2, hd3, hd4, hd5]
  exact hcomb

private def g2Val5_0 : List FM :=
  [.n 0 8 5 7 32, .p 0 8 5 8 32, .p 0 8 6 7 128, .n 0 8 6 8 96, .n 0 8 6 9 32, .n 0 8 7 7 128,
   .p 0 8 7 9 128, .n 0 8 8 7 128, .p 0 8 8 8 256, .n 0 8 8 9 128, .p 0 8 9 7 320, .n 0 8 9 8 192,
   .n 0 8 9 9 128, .n 0 8 10 7 128, .n 0 8 10 8 192, .p 0 8 10 9 320, .n 0 8 11 7 128, .p 0 8 11 8 256,
   .n 0 8 11 9 128, .p 0 8 12 7 128, .n 0 8 12 9 128, .n 0 8 13 7 32, .n 0 8 13 8 96, .p 0 8 13 9 128,
   .p 0 8 14 8 32, .n 0 8 14 9 32, .n 1 7 5 7 48, .p 1 7 5 8 32, .p 1 7 5 9 16, .p 1 7 6 6 16,
   .p 1 7 6 7 160, .n 1 7 6 8 96, .n 1 7 6 9 48, .n 1 7 6 10 16, .n 1 7 6 11 16, .p 1 7 7 5 16,
   .n 1 7 7 6 48, .n 1 7 7 7 128, .p 1 7 7 9 48, .p 1 7 7 10 48, .p 1 7 7 11 64, .n 1 7 8 5 64,
   .p 1 7 8 6 16, .n 1 7 8 7 112, .p 1 7 8 8 256, .n 1 7 8 10 16, .n 1 7 8 11 80, .p 1 7 9 5 80,
   .p 1 7 9 6 80, .p 1 7 9 7 224, .n 1 7 9 8 192, .n 1 7 9 9 112, .n 1 7 9 10 80, .n 1 7 10 6 80,
   .n 1 7 10 7 112, .n 1 7 10 8 192, .p 1 7 10 9 224, .p 1 7 10 10 80, .p 1 7 10 11 80, .n 1 7 11 5 80,
   .n 1 7 11 6 16, .p 1 7 11 8 256, .n 1 7 11 9 112, .p 1 7 11 10 16, .n 1 7 11 11 64, .p 1 7 12 5 64,
   .p 1 7 12 6 48, .p 1 7 12 7 48, .n 1 7 12 9 128, .n 1 7 12 10 48, .p 1 7 12 11 16, .n 1 7 13 5 16,
   .n 1 7 13 6 16, .n 1 7 13 7 48, .n 1 7 13 8 96, .p 1 7 13 9 160, .p 1 7 13 10 16, .p 1 7 14 7 16,
   .p 1 7 14 8 32, .n 1 7 14 9 48, .n 2 6 5 7 8, .n 2 6 5 8 32, .p 2 6 5 9 40, .p 2 6 6 5 16,
   .p 2 6 6 6 136, .n 2 6 6 7 288, .p 2 6 6 8 208, .n 2 6 6 9 8, .p 2 6 6 10 8, .n 2 6 6 11 72,
   .n 2 6 7 4 16, .n 2 6 7 5 8, .n 2 6 7 6 328, .p 2 6 7 7 592, .p 2 6 7 8 48, .n 2 6 7 9 584,
   .p 2 6 7 10 56, .p 2 6 7 11 256, .n 2 6 7 12 16, .p 2 6 8 4 48, .n 2 6 8 5 160, .p 2 6 8 6 40,
   .p 2 6 8 7 456, .n 2 6 8 8 1072, .p 2 6 8 9 976, .n 2 6 8 10 88, .n 2 6 8 11 248, .p 2 6 8 12 48,
   .n 2 6 9 4 32, .p 2 6 9 5 328, .p 2 6 9 6 408, .n 2 6 9 7 1552, .p 2 6 9 8 848, .p 2 6 9 9 376,
   .n 2 6 9 10 232, .n 2 6 9 11 112, .n 2 6 9 12 32, .n 2 6 10 4 32, .n 2 6 10 5 112, .n 2 6 10 6 232,
   .p 2 6 10 7 376, .p 2 6 10 8 848, .n 2 6 10 9 1552, .p 2 6 10 10 408, .p 2 6 10 11 328, .n 2 6 10 12 32,
   .p 2 6 11 4 48, .n 2 6 11 5 248, .n 2 6 11 6 88, .p 2 6 11 7 976, .n 2 6 11 8 1072, .p 2 6 11 9 456,
   .p 2 6 11 10 40, .n 2 6 11 11 160, .p 2 6 11 12 48, .n 2 6 12 4 16, .p 2 6 12 5 256, .p 2 6 12 6 56,
   .n 2 6 12 7 584, .p 2 6 12 8 48, .p 2 6 12 9 592, .n 2 6 12 10 328, .n 2 6 12 11 8, .n 2 6 12 12 16,
   .n 2 6 13 5 72, .p 2 6 13 6 8, .n 2 6 13 7 8, .p 2 6 13 8 208, .n 2 6 13 9 288, .p 2 6 13 10 136,
   .p 2 6 13 11 16, .p 2 6 14 7 40, .n 2 6 14 8 32, .n 2 6 14 9 8, .p 3 5 5 7 16, .n 3 5 5 8 32,
   .p 3 5 5 9 16, .n 3 5 6 5 16, .p 3 5 6 6 176, .n 3 5 6 7 272, .p 3 5 6 8 64, .p 3 5 6 10 112,
   .n 3 5 6 11 64, .n 3 5 7 3 4, .p 3 5 7 4 4, .n 3 5 7 5 120, .n 3 5 7 6 104, .p 3 5 7 7 368,
   .p 3 5 7 8 80, .n 3 5 7 9 168, .n 3 5 7 10 184, .p 3 5 7 11 180, .n 3 5 7 12 52, .p 3 5 8 3 24,
   .n 3 5 8 4 20, .p 3 5 8 5 236, .n 3 5 8 6 408, .p 3 5 8 7 328, .n 3 5 8 8 304, .p 3 5 8 9 384,
   .n 3 5 8 10 456, .p 3 5 8 11 64, .p 3 5 8 12 164, .n 3 5 8 13 12, .n 3 5 9 3 48, .p 3 5 9 4 88,
   .p 3 5 9 5 184, .n 3 5 9 6 64, .n 3 5 9 7 640, .p 3 5 9 8 192, .n 3 5 9 9 32, .p 3 5 9 10 928,
   .n 3 5 9 11 464, .n 3 5 9 12 184, .p 3 5 9 13 40, .p 3 5 10 3 40, .n 3 5 10 4 184, .n 3 5 10 5 464,
   .p 3 5 10 6 928, .n 3 5 10 7 32, .p 3 5 10 8 192, .n 3 5 10 9 640, .n 3 5 10 10 64, .p 3 5 10 11 184,
   .p 3 5 10 12 88, .n 3 5 10 13 48, .n 3 5 11 3 12, .p 3 5 11 4 164, .p 3 5 11 5 64, .n 3 5 11 6 456,
   .p 3 5 11 7 384, .n 3 5 11 8 304, .p 3 5 11 9 328, .n 3 5 11 10 408, .p 3 5 11 11 236, .n 3 5 11 12 20,
   .p 3 5 11 13 24, .n 3 5 12 4 52, .p 3 5 12 5 180, .n 3 5 12 6 184, .n 3 5 12 7 168, .p 3 5 12 8 80,
   .p 3 5 12 9 368, .n 3 5 12 10 104, .n 3 5 12 11 120, .p 3 5 12 12 4, .n 3 5 12 13 4, .n 3 5 13 5 64,
   .p 3 5 13 6 112, .p 3 5 13 8 64, .n 3 5 13 9 272, .p 3 5 13 10 176, .n 3 5 13 11 16, .p 3 5 14 7 16,
   .n 3 5 14 8 32, .p 3 5 14 9 16, .n 4 4 6 5 32, .n 4 4 6 6 40, .p 4 4 6 7 248, .n 4 4 6 8 208,
   .p 4 4 6 9 16, .n 4 4 6 10 8, .p 4 4 6 11 24, .p 4 4 7 3 16, .p 4 4 7 4 32, .n 4 4 7 5 96,
   .p 4 4 7 6 408, .n 4 4 7 7 728, .n 4 4 7 8 32, .p 4 4 7 9 688, .n 4 4 7 10 168, .n 4 4 7 11 136,
   .p 4 4 7 12 16, .n 4 4 8 3 48, .n 4 4 8 4 176, .p 4 4 8 5 504, .n 4 4 8 6 408, .n 4 4 8 7 320,
   .p 4 4 8 8 1600, .n 4 4 8 9 1304, .n 4 4 8 10 280, .p 4 4 8 11 416, .p 4 4 8 12 32, .n 4 4 8 13 16,
   .p 4 4 9 3 32, .p 4 4 9 4 320, .n 4 4 9 5 376, .n 4 4 9 6 888, .p 4 4 9 7 1952, .n 4 4 9 8 1360,
   .n 4 4 9 9 552, .p 4 4 9 10 1384, .n 4 4 9 11 304, .n 4 4 9 12 224, .p 4 4 9 13 16, .p 4 4 10 3 16,
   .n 4 4 10 4 224, .n 4 4 10 5 304, .p 4 4 10 6 1384, .n 4 4 10 7 552, .n 4 4 10 8 1360, .p 4 4 10 9 1952,
   .n 4 4 10 10 888, .n 4 4 10 11 376, .p 4 4 10 12 320, .p 4 4 10 13 32, .n 4 4 11 3 16, .p 4 4 11 4 32,
   .p 4 4 11 5 416, .n 4 4 11 6 280, .n 4 4 11 7 1304, .p 4 4 11 8 1600, .n 4 4 11 9 320, .n 4 4 11 10 408,
   .p 4 4 11 11 504, .n 4 4 11 12 176, .n 4 4 11 13 48, .p 4 4 12 4 16, .n 4 4 12 5 136, .n 4 4 12 6 168,
   .p 4 4 12 7 688, .n 4 4 12 8 32, .n 4 4 12 9 728, .p 4 4 12 10 408, .n 4 4 12 11 96, .p 4 4 12 12 32,
   .p 4 4 12 13 16, .p 4 4 13 5 24, .n 4 4 13 6 8, .p 4 4 13 7 16, .n 4 4 13 8 208, .p 4 4 13 9 248,
   .n 4 4 13 10 40, .n 4 4 13 11 32, .p 5 3 6 5 44, .n 5 3 6 6 120, .p 5 3 6 7 84, .n 5 3 6 8 16,
   .p 5 3 6 9 84, .n 5 3 6 10 120, .p 5 3 6 11 44, .n 5 3 7 3 24, .p 5 3 7 4 16, .p 5 3 7 5 44,
   .p 5 3 7 6 80, .n 5 3 7 7 172, .n 5 3 7 8 120, .p 5 3 7 9 180, .p 5 3 7 10 192, .n 5 3 7 11 284,
   .p 5 3 7 12 88, .p 5 3 8 3 12, .p 5 3 8 4 8, .n 5 3 8 5 288, .p 5 3 8 6 560, .n 5 3 8 7 124,
   .n 5 3 8 8 248, .n 5 3 8 9 300, .p 5 3 8 10 576, .n 5 3 8 11 112, .n 5 3 8 12 128, .p 5 3 8 13 44,
   .p 5 3 9 3 140, .n 5 3 9 4 208, .n 5 3 9 5 136, .p 5 3 9 6 104, .p 5 3 9 7 68, .p 5 3 9 8 384,
   .p 5 3 9 9 180, .n 5 3 9 10 1272, .p 5 3 9 11 688, .p 5 3 9 12 224, .n 5 3 9 13 172, .n 5 3 10 3 172,
   .p 5 3 10 4 224, .p 5 3 10 5 688, .n 5 3 10 6 1272, .p 5 3 10 7 180, .p 5 3 10 8 384, .p 5 3 10 9 68,
   .p 5 3 10 10 104, .n 5 3 10 11 136, .n 5 3 10 12 208, .p 5 3 10 13 140, .p 5 3 11 3 44, .n 5 3 11 4 128,
   .n 5 3 11 5 112, .p 5 3 11 6 576, .n 5 3 11 7 300, .n 5 3 11 8 248, .n 5 3 11 9 124, .p 5 3 11 10 560,
   .n 5 3 11 11 288, .p 5 3 11 12 8, .p 5 3 11 13 12, .p 5 3 12 4 88, .n 5 3 12 5 284, .p 5 3 12 6 192,
   .p 5 3 12 7 180, .n 5 3 12 8 120, .n 5 3 12 9 172, .p 5 3 12 10 80, .p 5 3 12 11 44, .p 5 3 12 12 16,
   .n 5 3 12 13 24, .p 5 3 13 5 44, .n 5 3 13 6 120, .p 5 3 13 7 84, .n 5 3 13 8 16, .p 5 3 13 9 84,
   .n 5 3 13 10 120, .p 5 3 13 11 44, .n 6 2 6 5 12, .p 6 2 6 6 48, .n 6 2 6 7 60, .p 6 2 6 9 60,
   .n 6 2 6 10 48, .p 6 2 6 11 12, .p 6 2 7 3 16, .n 6 2 7 4 52, .p 6 2 7 5 36, .p 6 2 7 6 8,
   .p 6 2 7 7 84, .n 6 2 7 8 176, .p 6 2 7 9 12, .p 6 2 7 10 184, .n 6 2 7 11 148, .p 6 2 7 12 36,
   .p 6 2 8 3 12, .n 6 2 8 4 12, .n 6 2 8 5 200, .p 6 2 8 6 472, .n 6 2 8 7 4, .n 6 2 8 8 784,
   .p 6 2 8 9 452, .p 6 2 8 10 360, .n 6 2 8 11 312, .n 6 2 8 12 36, .p 6 2 8 13 52, .p 6 2 9 2 4,
   .p 6 2 9 3 76, .n 6 2 9 4 208, .p 6 2 9 5 88, .p 6 2 9 6 300, .n 6 2 9 7 820, .p 6 2 9 8 848,
   .p 6 2 9 9 340, .n 6 2 9 10 1188, .p 6 2 9 11 440, .p 6 2 9 12 256, .n 6 2 9 13 124, .n 6 2 9 14 12,
   .n 6 2 10 2 12, .n 6 2 10 3 124, .p 6 2 10 4 256, .p 6 2 10 5 440, .n 6 2 10 6 1188, .p 6 2 10 7 340,
   .p 6 2 10 8 848, .n 6 2 10 9 820, .p 6 2 10 10 300, .p 6 2 10 11 88, .n 6 2 10 12 208, .p 6 2 10 13 76,
   .p 6 2 10 14 4, .p 6 2 11 3 52, .n 6 2 11 4 36, .n 6 2 11 5 312, .p 6 2 11 6 360, .p 6 2 11 7 452,
   .n 6 2 11 8 784, .n 6 2 11 9 4, .p 6 2 11 10 472, .n 6 2 11 11 200, .n 6 2 11 12 12, .p 6 2 11 13 12,
   .p 6 2 12 4 36, .n 6 2 12 5 148, .p 6 2 12 6 184, .p 6 2 12 7 12, .n 6 2 12 8 176, .p 6 2 12 9 84,
   .p 6 2 12 10 8, .p 6 2 12 11 36, .n 6 2 12 12 52, .p 6 2 12 13 16, .p 6 2 13 5 12, .n 6 2 13 6 48,
   .p 6 2 13 7 60, .n 6 2 13 9 60, .p 6 2 13 10 48, .n 6 2 13 11 12, .n 7 1 7 3 4, .p 7 1 7 4 16,
   .n 7 1 7 5 16, .n 7 1 7 6 16, .p 7 1 7 7 40, .n 7 1 7 8 16, .n 7 1 7 9 16, .p 7 1 7 10 16,
   .n 7 1 7 11 4, .p 7 1 8 4 8, .n 7 1 8 5 28, .p 7 1 8 6 16, .p 7 1 8 7 48, .n 7 1 8 8 64,
   .n 7 1 8 9 8, .p 7 1 8 10 48, .n 7 1 8 11 16, .n 7 1 8 12 8, .p 7 1 8 13 4, .n 7 1 9 2 4,
   .p 7 1 9 3 16, .p 7 1 9 4 16, .n 7 1 9 5 144, .p 7 1 9 6 132, .p 7 1 9 7 256, .n 7 1 9 8 480,
   .p 7 1 9 10 484, .n 7 1 9 11 272, .n 7 1 9 12 112, .p 7 1 9 13 144, .n 7 1 9 14 36, .n 7 1 10 2 36,
   .p 7 1 10 3 144, .n 7 1 10 4 112, .n 7 1 10 5 272, .p 7 1 10 6 484, .n 7 1 10 8 480, .p 7 1 10 9 256,
   .p 7 1 10 10 132, .n 7 1 10 11 144, .p 7 1 10 12 16, .p 7 1 10 13 16, .n 7 1 10 14 4, .p 7 1 11 3 4,
   .n 7 1 11 4 8, .n 7 1 11 5 16, .p 7 1 11 6 48, .n 7 1 11 7 8, .n 7 1 11 8 64, .p 7 1 11 9 48,
   .p 7 1 11 10 16, .n 7 1 11 11 28, .p 7 1 11 12 8, .n 7 1 12 5 4, .p 7 1 12 6 16, .n 7 1 12 7 16,
   .n 7 1 12 8 16, .p 7 1 12 9 40, .n 7 1 12 10 16, .n 7 1 12 11 16, .p 7 1 12 12 16, .n 7 1 12 13 4,
   .p 8 0 9 4 24, .n 8 0 9 5 96, .p 8 0 9 6 72, .p 8 0 9 7 192, .n 8 0 9 8 336, .p 8 0 9 10 336,
   .n 8 0 9 11 192, .n 8 0 9 12 72, .p 8 0 9 13 96, .n 8 0 9 14 24, .n 8 0 10 2 24, .p 8 0 10 3 96,
   .n 8 0 10 4 72, .n 8 0 10 5 192, .p 8 0 10 6 336, .n 8 0 10 8 336, .p 8 0 10 9 192, .p 8 0 10 10 72,
   .n 8 0 10 11 96, .p 8 0 10 12 24]

private def g2Mid5_0_a : List FM :=
  [.n 0 8 5 6 32, .p 0 8 5 7 32, .p 0 8 6 6 96, .n 0 8 6 7 96, .n 0 8 7 6 32, .p 0 8 7 7 32,
   .p 0 8 7 8 32, .n 0 8 7 9 32, .n 0 8 8 6 160, .p 0 8 8 7 160, .n 0 8 8 8 96, .p 0 8 8 9 96,
   .p 0 8 9 6 160, .n 0 8 9 7 160, .p 0 8 9 8 32, .n 0 8 9 9 32, .p 0 8 10 6 32, .n 0 8 10 7 32,
   .p 0 8 10 8 160, .n 0 8 10 9 160, .n 0 8 11 6 96, .p 0 8 11 7 96, .n 0 8 11 8 160, .p 0 8 11 9 160,
   .p 0 8 12 6 32, .n 0 8 12 7 32, .n 0 8 12 8 32, .p 0 8 12 9 32, .p 0 8 13 8 96, .n 0 8 13 9 96,
   .n 0 8 14 8 32, .p 0 8 14 9 32, .n 1 7 5 6 32, .p 1 7 5 7 16, .p 1 7 5 9 16, .p 1 7 6 4 16,
   .p 1 7 6 5 16, .p 1 7 6 6 96, .n 1 7 6 7 128, .p 1 7 6 8 48, .n 1 7 6 10 64, .p 1 7 6 11 16,
   .p 1 7 7 3 16, .n 1 7 7 4 48, .n 1 7 7 5 16, .n 1 7 7 6 96, .p 1 7 7 7 144, .p 1 7 7 8 16,
   .n 1 7 7 9 112, .p 1 7 7 10 128, .n 1 7 7 11 32, .n 1 7 8 3 48, .n 1 7 8 5 32, .n 1 7 8 6 16,
   .p 1 7 8 7 256, .n 1 7 8 8 288, .p 1 7 8 9 96, .p 1 7 8 10 48, .n 1 7 8 11 16, .p 1 7 9 3 32,
   .p 1 7 9 4 128, .p 1 7 9 6 176, .n 1 7 9 7 448, .p 1 7 9 8 96, .p 1 7 9 9 160, .n 1 7 9 10 208,
   .p 1 7 9 11 64, .p 1 7 10 3 32, .n 1 7 10 4 112, .p 1 7 10 5 80, .n 1 7 10 6 192, .n 1 7 10 7 48,
   .p 1 7 10 8 464, .n 1 7 10 9 240, .p 1 7 10 10 32, .n 1 7 10 11 16, .n 1 7 11 3 48, .n 1 7 11 4 48,
   .n 1 7 11 5 16, .p 1 7 11 7 336, .n 1 7 11 8 304, .p 1 7 11 9 16, .p 1 7 11 10 96, .n 1 7 11 11 32,
   .p 1 7 12 3 16, .p 1 7 12 4 96, .n 1 7 12 5 64, .p 1 7 12 6 112, .n 1 7 12 7 96, .n 1 7 12 8 192,
   .p 1 7 12 9 128, .n 1 7 12 10 16, .p 1 7 12 11 16, .n 1 7 13 4 32, .p 1 7 13 5 32, .n 1 7 13 6 48,
   .n 1 7 13 7 48, .p 1 7 13 8 192, .n 1 7 13 9 80, .n 1 7 13 10 16, .p 1 7 14 7 16, .n 1 7 14 8 32,
   .p 1 7 14 9 16, .p 2 6 5 6 24, .n 2 6 5 7 64, .p 2 6 5 8 8, .p 2 6 5 9 32, .p 2 6 6 4 16,
   .p 2 6 6 5 88, .n 2 6 6 6 200, .p 2 6 6 7 176, .p 2 6 6 8 24, .p 2 6 6 9 40, .n 2 6 6 10 192,
   .p 2 6 6 11 48, .n 2 6 7 2 16, .n 2 6 7 4 24, .n 2 6 7 5 104, .p 2 6 7 6 176, .n 2 6 7 7 80,
   .n 2 6 7 8 224, .p 2 6 7 9 56, .p 2 6 7 10 320, .n 2 6 7 11 128, .p 2 6 7 12 24, .p 2 6 8 2 48,
   .n 2 6 8 3 32, .n 2 6 8 4 80, .n 2 6 8 5 144, .p 2 6 8 6 504, .n 2 6 8 7 360, .p 2 6 8 8 424,
   .n 2 6 8 9 544, .p 2 6 8 10 184, .p 2 6 8 11 56, .n 2 6 8 12 56, .n 2 6 9 2 48, .p 2 6 9 3 64,
   .p 2 6 9 4 280, .p 2 6 9 5 64, .n 2 6 9 6 632, .p 2 6 9 7 504, .n 2 6 9 8 104, .p 2 6 9 9 240,
   .n 2 6 9 10 488, .p 2 6 9 11 88, .p 2 6 9 12 32, .p 2 6 10 2 16, .n 2 6 10 4 256, .p 2 6 10 5 280,
   .n 2 6 10 6 352, .p 2 6 10 7 80, .n 2 6 10 8 432, .p 2 6 10 9 664, .p 2 6 10 10 64, .n 2 6 10 11 64,
   .n 2 6 11 3 64, .n 2 6 11 4 88, .n 2 6 11 5 72, .p 2 6 11 6 672, .n 2 6 11 7 384, .p 2 6 11 8 304,
   .n 2 6 11 9 520, .p 2 6 11 10 128, .p 2 6 11 11 16, .p 2 6 11 12 8, .p 2 6 12 3 32, .p 2 6 12 4 256,
   .n 2 6 12 5 224, .n 2 6 12 6 104, .p 2 6 12 7 88, .p 2 6 12 8 104, .n 2 6 12 9 112, .p 2 6 12 10 8,
   .n 2 6 12 11 40, .n 2 6 12 12 8, .n 2 6 13 4 104, .p 2 6 13 5 112, .n 2 6 13 6 112, .p 2 6 13 7 24,
   .n 2 6 13 8 112, .p 2 6 13 9 192, .n 2 6 13 10 24, .p 2 6 13 11 24, .p 2 6 14 6 24, .p 2 6 14 7 16,
   .p 2 6 14 8 8, .n 2 6 14 9 48, .p 3 5 5 6 36, .n 3 5 5 7 52, .n 3 5 5 8 4, .p 3 5 5 9 20,
   .n 3 5 6 4 20, .p 3 5 6 5 48, .n 3 5 6 6 92, .p 3 5 6 7 144, .n 3 5 6 8 136, .p 3 5 6 9 156,
   .n 3 5 6 10 104, .p 3 5 6 11 4, .p 3 5 7 2 20, .n 3 5 7 3 104, .p 3 5 7 4 72, .n 3 5 7 5 72,
   .p 3 5 7 6 256, .n 3 5 7 7 316, .n 3 5 7 8 60, .p 3 5 7 9 320, .n 3 5 7 10 92, .n 3 5 7 11 84,
   .p 3 5 7 12 60, .n 3 5 8 2 36, .p 3 5 8 3 208, .n 3 5 8 4 72, .p 3 5 8 6 56, .n 3 5 8 7 588,
   .p 3 5 8 8 996, .n 3 5 8 9 856, .p 3 5 8 10 148, .p 3 5 8 11 212, .n 3 5 8 12 68, .p 3 5 9 2 12,
   .n 3 5 9 3 20, .n 3 5 9 4 88, .p 3 5 9 5 148, .n 3 5 9 6 840, .p 3 5 9 7 1492, .n 3 5 9 8 404,
   .n 3 5 9 9 512, .p 3 5 9 10 444, .n 3 5 9 11 160, .n 3 5 9 12 84, .p 3 5 9 13 12, .p 3 5 10 2 4,
   .n 3 5 10 3 172, .p 3 5 10 4 104, .n 3 5 10 5 92, .p 3 5 10 6 416, .p 3 5 10 7 156, .n 3 5 10 8 1468,
   .p 3 5 10 9 1208, .n 3 5 10 10 132, .n 3 5 10 11 112, .p 3 5 10 12 116, .n 3 5 10 13 28, .p 3 5 11 3 92,
   .p 3 5 11 4 44, .n 3 5 11 5 116, .p 3 5 11 6 520, .n 3 5 11 7 1228, .p 3 5 11 8 916, .n 3 5 11 9 24,
   .n 3 5 11 10 448, .p 3 5 11 11 232, .n 3 5 11 12 8, .p 3 5 11 13 20, .n 3 5 12 3 4, .p 3 5 12 4 20,
   .p 3 5 12 5 12, .n 3 5 12 6 352, .p 3 5 12 7 244, .p 3 5 12 8 548, .n 3 5 12 9 432, .p 3 5 12 10 56,
   .n 3 5 12 11 72, .n 3 5 12 12 16, .n 3 5 12 13 4, .n 3 5 13 4 60, .p 3 5 13 5 72, .n 3 5 13 6 36,
   .p 3 5 13 7 168, .n 3 5 13 8 384, .p 3 5 13 9 132, .p 3 5 13 10 128, .n 3 5 13 11 20, .p 3 5 14 6 36,
   .n 3 5 14 7 20, .n 3 5 14 8 4, .n 3 5 14 9 12, .p 4 4 5 6 4, .n 4 4 5 7 4, .n 4 4 5 8 4,
   .p 4 4 5 9 4, .n 4 4 6 4 24, .n 4 4 6 5 76, .p 4 4 6 6 256, .n 4 4 6 7 140, .n 4 4 6 8 92,
   .p 4 4 6 9 32, .p 4 4 6 10 116, .n 4 4 6 11 72, .p 4 4 7 2 32, .p 4 4 7 3 8, .n 4 4 7 4 24,
   .p 4 4 7 5 100, .n 4 4 7 6 260, .n 4 4 7 7 128, .p 4 4 7 8 424, .p 4 4 7 9 116, .n 4 4 7 10 452,
   .p 4 4 7 11 160, .p 4 4 7 12 24, .n 4 4 8 2 144, .p 4 4 8 3 64, .p 4 4 8 4 112, .p 4 4 8 5 284,
   .n 4 4 8 6 340, .p 4 4 8 7 128, .n 4 4 8 8 408, .p 4 4 8 9 468, .n 4 4 8 10 100, .n 4 4 8 11 184,
   .p 4 4 8 12 112, .p 4 4 8 13 8, .p 4 4 9 1 8, .p 4 4 9 2 192, .n 4 4 9 3 72, .n 4 4 9 4 432,
   .p 4 4 9 5 4, .p 4 4 9 6 508, .n 4 4 9 7 152, .n 4 4 9 8 168, .n 4 4 9 9 412, .p 4 4 9 10 900,
   .n 4 4 9 11 128, .n 4 4 9 12 232, .n 4 4 9 13 16, .n 4 4 10 1 8, .n 4 4 10 2 80, .n 4 4 10 3 104,
   .p 4 4 10 4 448, .n 4 4 10 5 564, .p 4 4 10 6 404, .p 4 4 10 7 328, .p 4 4 10 8 104, .n 4 4 10 9 708,
   .n 4 4 10 10 196, .p 4 4 10 11 256, .p 4 4 10 12 88, .p 4 4 10 13 32, .p 4 4 11 3 112, .p 4 4 11 4 176,
   .n 4 4 11 5 60, .n 4 4 11 6 828, .p 4 4 11 7 304, .p 4 4 11 8 184, .p 4 4 11 9 396, .n 4 4 11 10 284,
   .p 4 4 11 11 56, .n 4 4 11 12 16, .n 4 4 11 13 40, .n 4 4 12 3 8, .n 4 4 12 4 312, .p 4 4 12 5 428,
   .p 4 4 12 6 116, .n 4 4 12 7 208, .n 4 4 12 8 40, .p 4 4 12 9 76, .n 4 4 12 10 44, .n 4 4 12 11 48,
   .p 4 4 12 12 24, .p 4 4 12 13 16, .p 4 4 13 4 56, .n 4 4 13 5 116, .p 4 4 13 6 128, .n 4 4 13 7 116,
   .p 4 4 13 8 12, .p 4 4 13 9 16, .p 4 4 13 10 60, .n 4 4 13 11 40, .p 4 4 14 6 12, .n 4 4 14 7 12,
   .n 4 4 14 8 12, .p 4 4 14 9 12, .p 5 3 6 4 32, .n 5 3 6 5 64, .p 5 3 6 6 40, .n 5 3 6 7 24,
   .p 5 3 6 8 48, .n 5 3 6 9 112, .p 5 3 6 10 136, .n 5 3 6 11 56, .n 5 3 7 2 56, .p 5 3 7 3 136,
   .n 5 3 7 4 132, .p 5 3 7 5 92, .n 5 3 7 6 52, .n 5 3 7 7 12, .p 5 3 7 8 92, .n 5 3 7 9 60,
   .n 5 3 7 10 84, .p 5 3 7 11 100, .n 5 3 7 12 24, .p 5 3 8 2 104, .n 5 3 8 3 236, .n 5 3 8 4 16,
   .p 5 3 8 5 244, .p 5 3 8 6 52, .p 5 3 8 7 84, .n 5 3 8 8 964, .p 5 3 8 9 1132, .n 5 3 8 10 124,
   .n 5 3 8 11 488, .p 5 3 8 12 180, .p 5 3 8 13 32, .p 5 3 9 1 24, .p 5 3 9 2 8, .n 5 3 9 3 44,
   .n 5 3 9 4 108, .n 5 3 9 5 16, .p 5 3 9 6 968, .n 5 3 9 7 1392, .p 5 3 9 8 248, .p 5 3 9 9 568,
   .n 5 3 9 10 416, .p 5 3 9 11 204, .p 5 3 9 12 68, .n 5 3 9 13 112, .n 5 3 10 1 40, .n 5 3 10 2 16,
   .p 5 3 10 3 156, .n 5 3 10 4 12, .n 5 3 10 5 48, .n 5 3 10 6 464, .p 5 3 10 7 152, .p 5 3 10 8 1424,
   .n 5 3 10 9 1552, .p 5 3 10 10 112, .p 5 3 10 11 476, .n 5 3 10 12 276, .p 5 3 10 13 88, .p 5 3 11 2 8,
   .n 5 3 11 3 20, .p 5 3 11 4 160, .n 5 3 11 5 52, .n 5 3 11 6 804, .p 5 3 11 7 1324, .n 5 3 11 8 700,
   .n 5 3 11 9 188, .p 5 3 11 10 540, .n 5 3 11 11 312, .p 5 3 11 12 28, .p 5 3 11 13 16, .p 5 3 12 3 24,
   .n 5 3 12 4 156, .p 5 3 12 5 76, .p 5 3 12 6 356, .n 5 3 12 7 196, .n 5 3 12 8 428, .p 5 3 12 9 396,
   .n 5 3 12 10 68, .n 5 3 12 11 20, .p 5 3 12 12 40, .n 5 3 12 13 24, .p 5 3 13 4 56, .n 5 3 13 5 136,
   .p 5 3 13 6 128, .n 5 3 13 7 160, .p 5 3 13 8 184, .n 5 3 13 9 8, .n 5 3 13 10 112, .p 5 3 13 11 48,
   .n 6 2 6 4 20, .p 6 2 6 5 60, .n 6 2 6 6 52, .n 6 2 6 7 4, .p 6 2 6 8 36, .n 6 2 6 9 44,
   .p 6 2 6 10 36, .n 6 2 6 11 12, .p 6 2 7 2 16, .n 6 2 7 3 44, .n 6 2 7 4 20, .p 6 2 7 5 64,
   .p 6 2 7 6 72, .p 6 2 7 7 8, .n 6 2 7 8 224, .p 6 2 7 9 32, .p 6 2 7 10 168, .n 6 2 7 11 60,
   .n 6 2 7 12 12, .p 6 2 8 2 60, .n 6 2 8 3 68, .n 6 2 8 4 28, .n 6 2 8 5 68, .p 6 2 8 6 128,
   .n 6 2 8 7 24, .p 6 2 8 8 16, .p 6 2 8 9 104, .n 6 2 8 10 156, .p 6 2 8 11 28, .n 6 2 8 12 20,
   .p 6 2 8 13 28, .n 6 2 9 1 4, .n 6 2 9 2 72, .p 6 2 9 3 136, .n 6 2 9 4 12, .n 6 2 9 5 44,
   .p 6 2 9 6 176, .n 6 2 9 7 500, .p 6 2 9 8 260, .p 6 2 9 9 416, .n 6 2 9 10 524, .p 6 2 9 11 60,
   .p 6 2 9 12 184, .n 6 2 9 13 64, .n 6 2 9 14 12, .n 6 2 10 1 52, .p 6 2 10 2 128, .p 6 2 10 3 40,
   .n 6 2 10 4 412, .p 6 2 10 5 460, .p 6 2 10 6 32, .n 6 2 10 7 452, .p 6 2 10 8 148, .p 6 2 10 9 176,
   .p 6 2 10 10 108, .n 6 2 10 11 212, .n 6 2 10 12 8, .p 6 2 10 13 40, .p 6 2 10 14 4, .p 6 2 11 2 36,
   .n 6 2 11 3 12, .n 6 2 11 4 188, .p 6 2 11 5 60, .p 6 2 11 6 376, .n 6 2 11 7 80, .n 6 2 11 8 424,
   .p 6 2 11 9 96, .p 6 2 11 10 228, .n 6 2 11 11 68, .n 6 2 11 12 28, .p 6 2 11 13 4, .p 6 2 12 3 12,
   .p 6 2 12 4 28, .n 6 2 12 5 168, .p 6 2 12 6 128, .p 6 2 12 7 160, .n 6 2 12 8 200, .n 6 2 12 9 40,
   .p 6 2 12 10 96, .p 6 2 12 11 20, .n 6 2 12 12 52, .p 6 2 12 13 16, .p 6 2 13 4 12, .n 6 2 13 5 36,
   .p 6 2 13 6 12, .p 6 2 13 7 60, .n 6 2 13 8 60, .n 6 2 13 9 12, .p 6 2 13 10 36, .n 6 2 13 11 12,
   .p 7 1 7 2 4, .n 7 1 7 3 12, .p 7 1 7 4 32, .n 7 1 7 5 64, .p 7 1 7 6 8, .p 7 1 7 7 136,
   .n 7 1 7 8 128, .n 7 1 7 9 32, .p 7 1 7 10 84, .n 7 1 7 11 28, .n 7 1 8 2 32, .p 7 1 8 3 112,
   .n 7 1 8 4 60, .n 7 1 8 5 140, .p 7 1 8 6 64, .p 7 1 8 7 128, .p 7 1 8 8 104, .n 7 1 8 9 280,
   .p 7 1 8 11 176, .n 7 1 8 12 76, .p 7 1 8 13 4, .n 7 1 9 1 28, .p 7 1 9 2 52, .p 7 1 9 4 16,
   .n 7 1 9 5 60, .n 7 1 9 6 108, .p 7 1 9 7 224, .n 7 1 9 8 128, .n 7 1 9 9 20, .p 7 1 9 10 220,
   .n 7 1 9 11 224, .n 7 1 9 12 16, .p 7 1 9 13 108, .n 7 1 9 14 36, .p 7 1 10 1 4, .p 7 1 10 2 20,
   .n 7 1 10 3 48, .n 7 1 10 4 96, .p 7 1 10 5 100, .p 7 1 10 6 436, .n 7 1 10 7 448, .n 7 1 10 8 544,
   .p 7 1 10 9 780, .p 7 1 10 10 60, .n 7 1 10 11 400, .p 7 1 10 12 128, .p 7 1 10 13 12, .n 7 1 10 14 4,
   .p 7 1 11 2 28, .p 7 1 11 3 12, .n 7 1 11 4 272, .p 7 1 11 5 256, .p 7 1 11 6 376, .n 7 1 11 7 584,
   .n 7 1 11 8 32, .p 7 1 11 9 352, .n 7 1 11 10 116, .n 7 1 11 11 36, .p 7 1 11 12 16, .n 7 1 12 4 4,
   .p 7 1 12 5 12, .n 7 1 12 7 32, .p 7 1 12 8 24, .p 7 1 12 9 24, .n 7 1 12 10 32, .p 7 1 12 12 12,
   .n 7 1 12 13 4, .n 8 0 9 3 24, .p 8 0 9 4 72, .n 8 0 9 5 24, .n 8 0 9 6 120, .p 8 0 9 7 144,
   .n 8 0 9 8 48, .n 8 0 9 9 48, .p 8 0 9 10 144, .n 8 0 9 11 120, .n 8 0 9 12 24, .p 8 0 9 13 72,
   .n 8 0 9 14 24, .p 8 0 10 1 24, .n 8 0 10 2 72, .p 8 0 10 3 24, .p 8 0 10 4 120, .n 8 0 10 5 144,
   .p 8 0 10 6 48, .p 8 0 10 7 48, .n 8 0 10 8 144, .p 8 0 10 9 120, .p 8 0 10 10 24, .n 8 0 10 11 72,
   .p 8 0 10 12 24]

private def g2Mid5_0_b : List FM :=
  [.n 0 8 5 6 32, .p 0 8 5 7 32, .p 0 8 6 6 32, .p 0 8 6 7 32, .n 0 8 6 8 64, .p 0 8 7 6 160,
   .n 0 8 7 7 224, .n 0 8 7 8 32, .p 0 8 7 9 96, .n 0 8 8 6 288, .p 0 8 8 7 32, .p 0 8 8 8 480,
   .n 0 8 8 9 160, .n 0 8 8 10 64, .p 0 8 9 6 32, .p 0 8 9 7 352, .n 0 8 9 8 416, .n 0 8 9 9 160,
   .p 0 8 9 10 192, .p 0 8 10 6 224, .n 0 8 10 7 160, .n 0 8 10 8 288, .p 0 8 10 9 352, .n 0 8 10 10 128,
   .n 0 8 11 6 160, .n 0 8 11 7 160, .p 0 8 11 8 416, .p 0 8 11 9 32, .n 0 8 11 10 128, .p 0 8 12 6 32,
   .p 0 8 12 7 96, .n 0 8 12 8 96, .n 0 8 12 9 224, .p 0 8 12 10 192, .p 0 8 13 8 32, .p 0 8 13 9 32,
   .n 0 8 13 10 64, .n 0 8 14 8 32, .p 0 8 14 9 32, .n 1 7 5 6 32, .p 1 7 5 7 16, .p 1 7 5 9 16,
   .p 1 7 6 4 16, .p 1 7 6 5 16, .n 1 7 6 6 32, .p 1 7 6 7 96, .n 1 7 6 8 16, .n 1 7 6 9 64,
   .n 1 7 6 11 16, .p 1 7 7 3 16, .n 1 7 7 4 48, .p 1 7 7 5 16, .p 1 7 7 6 224, .n 1 7 7 7 272,
   .n 1 7 7 8 144, .p 1 7 7 9 112, .p 1 7 7 10 64, .p 1 7 7 12 32, .n 1 7 8 3 48, .n 1 7 8 5 64,
   .n 1 7 8 6 272, .p 1 7 8 7 96, .p 1 7 8 8 576, .n 1 7 8 9 128, .n 1 7 8 10 80, .p 1 7 8 11 16,
   .n 1 7 8 12 96, .p 1 7 9 3 32, .p 1 7 9 4 96, .n 1 7 9 5 32, .p 1 7 9 6 176, .p 1 7 9 7 256,
   .n 1 7 9 8 544, .n 1 7 9 9 128, .n 1 7 9 10 16, .p 1 7 9 11 64, .p 1 7 9 12 96, .p 1 7 10 3 32,
   .n 1 7 10 4 16, .p 1 7 10 5 80, .n 1 7 10 7 336, .n 1 7 10 8 176, .p 1 7 10 9 464, .p 1 7 10 10 32,
   .n 1 7 10 11 48, .n 1 7 10 12 32, .n 1 7 11 3 48, .n 1 7 11 4 144, .p 1 7 11 5 16, .n 1 7 11 6 128,
   .p 1 7 11 7 112, .p 1 7 11 8 560, .n 1 7 11 9 144, .n 1 7 11 10 160, .n 1 7 11 11 64, .p 1 7 12 3 16,
   .p 1 7 12 4 128, .n 1 7 12 5 32, .p 1 7 12 6 48, .p 1 7 12 7 128, .n 1 7 12 8 352, .n 1 7 12 9 288,
   .p 1 7 12 10 304, .p 1 7 12 11 48, .n 1 7 13 4 32, .p 1 7 13 6 16, .n 1 7 13 7 112, .p 1 7 13 8 128,
   .p 1 7 13 9 144, .n 1 7 13 10 144, .p 1 7 14 7 16, .n 1 7 14 8 32, .p 1 7 14 9 16, .p 2 6 5 6 32,
   .n 2 6 5 7 72, .p 2 6 5 9 40, .p 2 6 6 4 8, .p 2 6 6 5 104, .n 2 6 6 6 112, .n 2 6 6 7 120,
   .p 2 6 6 8 336, .n 2 6 6 9 200, .p 2 6 6 10 56, .n 2 6 6 11 72, .n 2 6 7 2 16, .n 2 6 7 3 8,
   .n 2 6 7 4 8, .n 2 6 7 5 16, .n 2 6 7 6 376, .p 2 6 7 7 696, .n 2 6 7 8 208, .n 2 6 7 9 272,
   .p 2 6 7 10 104, .n 2 6 7 11 16, .p 2 6 7 12 120, .p 2 6 8 2 48, .n 2 6 8 3 24, .n 2 6 8 4 32,
   .n 2 6 8 5 336, .p 2 6 8 6 768, .p 2 6 8 7 216, .n 2 6 8 8 1632, .p 2 6 8 9 904, .p 2 6 8 10 320,
   .p 2 6 8 11 112, .n 2 6 8 12 368, .p 2 6 8 13 24, .n 2 6 9 2 48, .p 2 6 9 3 104, .p 2 6 9 4 40,
   .p 2 6 9 5 8, .p 2 6 9 6 576, .n 2 6 9 7 1608, .p 2 6 9 8 1608, .p 2 6 9 9 416, .n 2 6 9 10 1616,
   .p 2 6 9 11 176, .p 2 6 9 12 400, .n 2 6 9 13 56, .p 2 6 10 2 16, .n 2 6 10 3 72, .p 2 6 10 4 136,
   .p 2 6 10 5 416, .n 2 6 10 6 1528, .p 2 6 10 7 216, .p 2 6 10 8 1304, .n 2 6 10 9 1400, .p 2 6 10 10 1224,
   .n 2 6 10 11 160, .n 2 6 10 12 192, .p 2 6 10 13 40, .n 2 6 11 3 32, .n 2 6 11 4 376, .n 2 6 11 5 56,
   .p 2 6 11 6 776, .p 2 6 11 7 1080, .n 2 6 11 8 1696, .p 2 6 11 9 32, .p 2 6 11 10 344, .n 2 6 11 11 120,
   .p 2 6 11 12 56, .n 2 6 11 13 8, .p 2 6 12 3 32, .p 2 6 12 4 336, .n 2 6 12 5 120, .n 2 6 12 6 304,
   .n 2 6 12 7 200, .p 2 6 12 8 112, .p 2 6 12 9 616, .n 2 6 12 10 512, .p 2 6 12 11 56, .n 2 6 12 12 16,
   .n 2 6 13 4 104, .p 2 6 13 6 144, .n 2 6 13 7 224, .p 2 6 13 8 168, .n 2 6 13 9 88, .p 2 6 13 10 80,
   .p 2 6 13 11 24, .p 2 6 14 6 24, .p 2 6 14 7 16, .p 2 6 14 8 8, .n 2 6 14 9 48, .p 3 5 5 6 32,
   .n 3 5 5 7 48, .p 3 5 5 9 16, .n 3 5 6 4 24, .p 3 5 6 5 40, .p 3 5 6 6 144, .n 3 5 6 7 252,
   .p 3 5 6 8 68, .n 3 5 6 9 12, .p 3 5 6 10 100, .n 3 5 6 11 64, .p 3 5 7 2 28, .n 3 5 7 3 100,
   .p 3 5 7 4 40, .n 3 5 7 5 68, .n 3 5 7 6 396, .p 3 5 7 7 648, .p 3 5 7 8 44, .n 3 5 7 9 44,
   .n 3 5 7 10 168, .n 3 5 7 11 52, .p 3 5 7 12 68, .n 3 5 8 2 52, .p 3 5 8 3 220, .n 3 5 8 4 16,
   .n 3 5 8 5 16, .p 3 5 8 6 364, .n 3 5 8 7 28, .n 3 5 8 8 1240, .p 3 5 8 9 396, .p 3 5 8 10 280,
   .p 3 5 8 11 264, .n 3 5 8 12 232, .p 3 5 8 13 60, .p 3 5 9 2 20, .n 3 5 9 3 32, .n 3 5 9 4 128,
   .p 3 5 9 5 80, .n 3 5 9 6 76, .n 3 5 9 7 636, .p 3 5 9 8 1556, .n 3 5 9 9 232, .n 3 5 9 10 528,
   .n 3 5 9 11 84, .p 3 5 9 12 116, .n 3 5 9 13 56, .p 3 5 10 2 4, .n 3 5 10 3 232, .p 3 5 10 4 308,
   .n 3 5 10 5 72, .n 3 5 10 6 524, .p 3 5 10 7 504, .p 3 5 10 8 440, .n 3 5 10 9 992, .p 3 5 10 10 688,
   .n 3 5 10 11 128, .p 3 5 10 12 44, .n 3 5 10 13 40, .p 3 5 11 3 148, .n 3 5 11 4 156, .n 3 5 11 5 28,
   .p 3 5 11 6 692, .p 3 5 11 7 16, .n 3 5 11 8 1364, .p 3 5 11 9 548, .n 3 5 11 10 92, .p 3 5 11 11 172,
   .p 3 5 11 12 24, .p 3 5 11 13 40, .n 3 5 12 3 4, .p 3 5 12 4 36, .p 3 5 12 5 64, .n 3 5 12 6 436,
   .n 3 5 12 7 172, .p 3 5 12 8 640, .p 3 5 12 9 588, .n 3 5 12 10 604, .n 3 5 12 11 88, .n 3 5 12 12 20,
   .n 3 5 12 13 4, .n 3 5 13 4 60, .p 3 5 13 6 164, .n 3 5 13 7 12, .n 3 5 13 8 140, .n 3 5 13 9 256,
   .p 3 5 13 10 324, .n 3 5 13 11 20, .p 3 5 14 6 36, .n 3 5 14 7 20, .n 3 5 14 8 4, .n 3 5 14 9 12,
   .p 4 4 6 4 4, .n 4 4 6 5 132, .p 4 4 6 6 200, .p 4 4 6 7 140, .n 4 4 6 8 392, .p 4 4 6 9 224,
   .n 4 4 6 10 68, .p 4 4 6 11 24, .p 4 4 7 2 8, .p 4 4 7 3 60, .n 4 4 7 4 56, .n 4 4 7 5 52,
   .p 4 4 7 6 268, .n 4 4 7 7 732, .p 4 4 7 8 368, .p 4 4 7 9 412, .n 4 4 7 10 260, .p 4 4 7 11 56,
   .n 4 4 7 12 72, .n 4 4 8 2 96, .p 4 4 8 3 12, .n 4 4 8 4 20, .p 4 4 8 5 728, .n 4 4 8 6 892,
   .n 4 4 8 7 292, .p 4 4 8 8 1796, .n 4 4 8 9 1312, .n 4 4 8 10 300, .p 4 4 8 11 88, .p 4 4 8 12 280,
   .p 4 4 8 13 8, .p 4 4 9 1 8, .p 4 4 9 2 168, .n 4 4 9 3 248, .p 4 4 9 4 252, .n 4 4 9 5 148,
   .n 4 4 9 6 1044, .p 4 4 9 7 2296, .n 4 4 9 8 1984, .n 4 4 9 9 824, .p 4 4 9 10 2604, .n 4 4 9 11 424,
   .n 4 4 9 12 764, .p 4 4 9 13 108, .n 4 4 10 1 8, .n 4 4 10 2 80, .p 4 4 10 3 76, .n 4 4 10 4 144,
   .n 4 4 10 5 980, .p 4 4 10 6 2204, .n 4 4 10 7 16, .n 4 4 10 8 1700, .p 4 4 10 9 1620, .n 4 4 10 10 1628,
   .p 4 4 10 11 172, .p 4 4 10 12 580, .n 4 4 10 13 96, .p 4 4 11 3 108, .p 4 4 11 4 308, .p 4 4 11 5 280,
   .n 4 4 11 6 988, .n 4 4 11 7 1484, .p 4 4 11 8 2216, .p 4 4 11 9 36, .n 4 4 11 10 692, .p 4 4 11 11 328,
   .n 4 4 11 12 76, .n 4 4 11 13 36, .n 4 4 12 3 8, .n 4 4 12 4 400, .p 4 4 12 5 328, .p 4 4 12 6 300,
   .p 4 4 12 7 20, .n 4 4 12 8 44, .n 4 4 12 9 408, .p 4 4 12 10 348, .n 4 4 12 11 204, .p 4 4 12 12 52,
   .p 4 4 12 13 16, .p 4 4 13 4 56, .n 4 4 13 5 24, .n 4 4 13 6 60, .p 4 4 13 7 80, .n 4 4 13 8 248,
   .p 4 4 13 9 240, .n 4 4 13 10 4, .n 4 4 13 11 40, .p 4 4 14 6 12, .n 4 4 14 7 12, .n 4 4 14 8 12,
   .p 4 4 14 9 12, .p 5 3 6 4 8, .p 5 3 6 5 8, .n 5 3 6 6 76, .p 5 3 6 7 92, .n 5 3 6 8 64,
   .p 5 3 6 9 112, .n 5 3 6 10 124, .p 5 3 6 11 44, .n 5 3 7 2 32, .p 5 3 7 3 64, .n 5 3 7 4 60,
   .p 5 3 7 5 112, .p 5 3 7 6 112, .n 5 3 7 7 476, .p 5 3 7 8 244, .p 5 3 7 9 8, .p 5 3 7 10 56,
   .p 5 3 7 11 36, .n 5 3 7 12 64, .p 5 3 8 2 76, .n 5 3 8 3 224, .p 5 3 8 4 64, .p 5 3 8 5 156,
   .n 5 3 8 6 76, .n 5 3 8 7 180, .p 5 3 8 8 488, .n 5 3 8 9 72, .n 5 3 8 10 168, .n 5 3 8 11 420,
   .p 5 3 8 12 384, .n 5 3 8 13 28, .p 5 3 9 1 20, .p 5 3 9 2 20, .n 5 3 9 3 4, .n 5 3 9 4 96,
   .p 5 3 9 5 4, .p 5 3 9 6 284, .p 5 3 9 7 192, .n 5 3 9 8 1232, .p 5 3 9 9 456, .p 5 3 9 10 584,
   .p 5 3 9 11 92, .n 5 3 9 12 328, .p 5 3 9 13 8, .n 5 3 10 1 40, .n 5 3 10 2 8, .p 5 3 10 3 232,
   .n 5 3 10 4 416, .n 5 3 10 5 12, .p 5 3 10 6 484, .n 5 3 10 7 84, .n 5 3 10 8 56, .p 5 3 10 9 232,
   .n 5 3 10 10 724, .p 5 3 10 11 388, .n 5 3 10 12 48, .p 5 3 10 13 52, .p 5 3 11 2 8, .n 5 3 11 3 84,
   .p 5 3 11 4 416, .n 5 3 11 5 60, .n 5 3 11 6 848, .p 5 3 11 7 84, .p 5 3 11 8 884, .n 5 3 11 9 464,
   .p 5 3 11 10 256, .n 5 3 11 11 232, .p 5 3 11 12 52, .n 5 3 11 13 12, .p 5 3 12 3 24, .n 5 3 12 4 196,
   .n 5 3 12 5 8, .p 5 3 12 6 508, .n 5 3 12 7 52, .n 5 3 12 8 328, .n 5 3 12 9 184, .p 5 3 12 10 236,
   .n 5 3 12 11 12, .p 5 3 12 12 36, .n 5 3 12 13 24, .p 5 3 13 4 56, .n 5 3 13 5 36, .n 5 3 13 6 132,
   .p 5 3 13 7 88, .p 5 3 13 9 156, .n 5 3 13 10 180, .p 5 3 13 11 48, .n 6 2 6 4 12, .p 6 2 6 5 36,
   .n 6 2 6 6 12, .n 6 2 6 7 60, .p 6 2 6 8 60, .p 6 2 6 9 12, .n 6 2 6 10 36, .p 6 2 6 11 12,
   .p 6 2 7 2 8, .n 6 2 7 3 20, .n 6 2 7 4 44, .p 6 2 7 5 72, .p 6 2 7 6 72, .p 6 2 7 7 8,
   .n 6 2 7 8 216, .p 6 2 7 9 8, .p 6 2 7 10 192, .n 6 2 7 11 68, .n 6 2 7 12 12, .p 6 2 8 2 48,
   .n 6 2 8 3 24, .n 6 2 8 4 88, .n 6 2 8 5 176, .p 6 2 8 6 516, .n 6 2 8 7 132, .n 6 2 8 8 572,
   .p 6 2 8 9 636, .n 6 2 8 10 36, .n 6 2 8 11 308, .p 6 2 8 12 132, .p 6 2 8 13 4, .n 6 2 9 1 8,
   .n 6 2 9 2 44, .p 6 2 9 3 204, .n 6 2 9 4 332, .p 6 2 9 5 180, .p 6 2 9 6 520, .n 6 2 9 7 1236,
   .p 6 2 9 8 684, .p 6 2 9 9 796, .n 6 2 9 10 1168, .p 6 2 9 11 200, .p 6 2 9 12 352, .n 6 2 9 13 136,
   .n 6 2 9 14 12, .n 6 2 10 1 52, .p 6 2 10 2 136, .n 6 2 10 3 76, .n 6 2 10 4 220, .p 6 2 10 5 684,
   .n 6 2 10 6 648, .n 6 2 10 7 196, .p 6 2 10 8 636, .n 6 2 10 9 456, .p 6 2 10 10 364, .n 6 2 10 11 32,
   .n 6 2 10 12 272, .p 6 2 10 13 128, .p 6 2 10 14 4, .p 6 2 11 2 36, .n 6 2 11 3 40, .n 6 2 11 4 32,
   .n 6 2 11 5 224, .p 6 2 11 6 400, .p 6 2 11 7 416, .n 6 2 11 8 864, .n 6 2 11 9 24, .p 6 2 11 10 508,
   .n 6 2 11 11 136, .n 6 2 11 12 48, .p 6 2 11 13 8, .p 6 2 12 3 12, .p 6 2 12 4 28, .n 6 2 12 5 164,
   .p 6 2 12 6 116, .p 6 2 12 7 148, .n 6 2 12 8 132, .n 6 2 12 9 92, .p 6 2 12 10 60, .p 6 2 12 11 80,
   .n 6 2 12 12 72, .p 6 2 12 13 16, .p 6 2 13 4 12, .n 6 2 13 5 12, .n 6 2 13 6 60, .p 6 2 13 7 108,
   .n 6 2 13 8 12, .n 6 2 13 9 84, .p 6 2 13 10 60, .n 6 2 13 11 12, .p 7 1 7 2 4, .n 7 1 7 3 12,
   .p 7 1 7 4 32, .n 7 1 7 5 64, .p 7 1 7 6 8, .p 7 1 7 7 136, .n 7 1 7 8 128, .n 7 1 7 9 32,
   .p 7 1 7 10 84, .n 7 1 7 11 28, .n 7 1 8 2 24, .p 7 1 8 3 88, .n 7 1 8 4 52, .n 7 1 8 5 148,
   .p 7 1 8 6 168, .p 7 1 8 7 72, .n 7 1 8 8 112, .n 7 1 8 9 48, .p 7 1 8 10 48, .p 7 1 8 11 32,
   .n 7 1 8 12 28, .p 7 1 8 13 4, .n 7 1 9 1 20, .p 7 1 9 2 28, .p 7 1 9 3 40, .n 7 1 9 4 48,
   .p 7 1 9 5 4, .n 7 1 9 6 60, .n 7 1 9 7 48, .p 7 1 9 8 160, .p 7 1 9 9 84, .n 7 1 9 10 124,
   .n 7 1 9 11 120, .p 7 1 9 12 80, .p 7 1 9 13 60, .n 7 1 9 14 36, .p 7 1 10 1 4, .p 7 1 10 2 4,
   .n 7 1 10 3 56, .p 7 1 10 4 16, .p 7 1 10 5 100, .p 7 1 10 6 100, .n 7 1 10 7 192, .n 7 1 10 8 304,
   .p 7 1 10 9 348, .p 7 1 10 10 220, .n 7 1 10 11 264, .n 7 1 10 12 32, .p 7 1 10 13 60, .n 7 1 10 14 4,
   .p 7 1 11 2 28, .p 7 1 11 3 20, .n 7 1 11 4 232, .p 7 1 11 5 72, .p 7 1 11 6 472, .n 7 1 11 7 280,
   .n 7 1 11 8 368, .p 7 1 11 9 272, .p 7 1 11 10 108, .n 7 1 11 11 92, .n 7 1 11 12 8, .p 7 1 11 13 8,
   .n 7 1 12 4 4, .p 7 1 12 5 4, .p 7 1 12 6 24, .n 7 1 12 7 40, .n 7 1 12 8 16, .p 7 1 12 9 64,
   .n 7 1 12 10 24, .n 7 1 12 11 24, .p 7 1 12 12 20, .n 7 1 12 13 4, .n 8 0 9 3 24, .p 8 0 9 4 72,
   .n 8 0 9 5 24, .n 8 0 9 6 120, .p 8 0 9 7 144, .n 8 0 9 8 48, .n 8 0 9 9 48, .p 8 0 9 10 144,
   .n 8 0 9 11 120, .n 8 0 9 12 24, .p 8 0 9 13 72, .n 8 0 9 14 24, .p 8 0 10 1 24, .n 8 0 10 2 72,
   .p 8 0 10 3 24, .p 8 0 10 4 120, .n 8 0 10 5 144, .p 8 0 10 6 48, .p 8 0 10 7 48, .n 8 0 10 8 144,
   .p 8 0 10 9 120, .p 8 0 10 10 24, .n 8 0 10 11 72, .p 8 0 10 12 24]

set_option maxRecDepth 65536 in
private theorem g2_det5_0_step01 :
    fmMerge (fmMerge [] (fmMul (fmSubMat g2FM ⟨0, by decide⟩ ⟨0, by decide⟩ ⟨0, by decide⟩) g2Val4_14))
      (fmMul (fmNeg (fmSubMat g2FM ⟨0, by decide⟩ ⟨0, by decide⟩ ⟨1, by decide⟩)) g2Val4_13) =
      g2Mid5_0_a := rfl

set_option maxRecDepth 65536 in
private theorem g2_det5_0_step2 :
    fmMerge g2Mid5_0_a (fmMul (fmSubMat g2FM ⟨0, by decide⟩ ⟨0, by decide⟩ ⟨2, by decide⟩) g2Val4_12) =
      g2Mid5_0_b := rfl

set_option maxRecDepth 65536 in
private theorem g2_det5_0_step34 :
    fmMerge (fmMerge g2Mid5_0_b (fmMul (fmNeg (fmSubMat g2FM ⟨0, by decide⟩ ⟨0, by decide⟩ ⟨3, by decide⟩)) g2Val4_11))
      (fmMul (fmSubMat g2FM ⟨0, by decide⟩ ⟨0, by decide⟩ ⟨4, by decide⟩) g2Val4_10) =
      g2Val5_0 := rfl

private theorem g2_det5_0 : fmDet 5 (fmSubMat g2FM ⟨0, by decide⟩) = g2Val5_0 :=
  fmDet5_of_sub4_split _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (fin4Mat_eq_of_vals _ _ (by decide)) g2_det4_14
    (fin4Mat_eq_of_vals _ _ (by decide)) g2_det4_13
    (fin4Mat_eq_of_vals _ _ (by decide)) g2_det4_12
    (fin4Mat_eq_of_vals _ _ (by decide)) g2_det4_11
    (fin4Mat_eq_of_vals _ _ (by decide)) g2_det4_10
    g2_det5_0_step01 g2_det5_0_step2 g2_det5_0_step34

private def g2Val5_1 : List FM :=
  [.n 0 7 5 7 16, .p 0 7 5 8 16, .p 0 7 6 7 64, .n 0 7 6 8 48, .n 0 7 6 9 16, .n 0 7 7 7 64,
   .p 0 7 7 9 64, .n 0 7 8 7 64, .p 0 7 8 8 128, .n 0 7 8 9 64, .p 0 7 9 7 160, .n 0 7 9 8 96,
   .n 0 7 9 9 64, .n 0 7 10 7 64, .n 0 7 10 8 96, .p 0 7 10 9 160, .n 0 7 11 7 64, .p 0 7 11 8 128,
   .n 0 7 11 9 64, .p 0 7 12 7 64, .n 0 7 12 9 64, .n 0 7 13 7 16, .n 0 7 13 8 48, .p 0 7 13 9 64,
   .p 0 7 14 8 16, .n 0 7 14 9 16, .n 1 6 5 7 16, .p 1 6 5 9 16, .p 1 6 6 6 16, .p 1 6 6 7 32,
   .n 1 6 6 9 16, .n 1 6 6 10 16, .n 1 6 6 11 16, .p 1 6 7 5 16, .n 1 6 7 6 48, .n 1 6 7 9 80,
   .p 1 6 7 10 48, .p 1 6 7 11 64, .n 1 6 8 5 64, .p 1 6 8 6 16, .p 1 6 8 7 16, .p 1 6 8 9 128,
   .n 1 6 8 10 16, .n 1 6 8 11 80, .p 1 6 9 5 80, .p 1 6 9 6 80, .n 1 6 9 7 96, .p 1 6 9 9 16,
   .n 1 6 9 10 80, .n 1 6 10 6 80, .p 1 6 10 7 16, .n 1 6 10 9 96, .p 1 6 10 10 80, .p 1 6 10 11 80,
   .n 1 6 11 5 80, .n 1 6 11 6 16, .p 1 6 11 7 128, .p 1 6 11 9 16, .p 1 6 11 10 16, .n 1 6 11 11 64,
   .p 1 6 12 5 64, .p 1 6 12 6 48, .n 1 6 12 7 80, .n 1 6 12 10 48, .p 1 6 12 11 16, .n 1 6 13 5 16,
   .n 1 6 13 6 16, .n 1 6 13 7 16, .p 1 6 13 9 32, .p 1 6 13 10 16, .p 1 6 14 7 16, .n 1 6 14 9 16,
   .p 2 5 5 7 8, .n 2 5 5 8 16, .p 2 5 5 9 8, .p 2 5 6 5 8, .p 2 5 6 6 64, .n 2 5 6 7 160,
   .p 2 5 6 8 80, .p 2 5 6 10 32, .n 2 5 6 11 24, .n 2 5 7 3 4, .n 2 5 7 4 12, .n 2 5 7 5 24,
   .n 2 5 7 6 128, .p 2 5 7 7 288, .p 2 5 7 8 56, .n 2 5 7 9 200, .n 2 5 7 10 32, .p 2 5 7 11 68,
   .n 2 5 7 12 12, .p 2 5 8 3 16, .p 2 5 8 4 36, .n 2 5 8 5 12, .n 2 5 8 6 32, .p 2 5 8 7 168,
   .n 2 5 8 8 488, .p 2 5 8 9 368, .n 2 5 8 10 64, .n 2 5 8 11 24, .p 2 5 8 12 36, .n 2 5 8 13 4,
   .n 2 5 9 3 24, .n 2 5 9 4 24, .p 2 5 9 5 104, .p 2 5 9 6 160, .n 2 5 9 7 600, .p 2 5 9 8 368,
   .p 2 5 9 9 120, .n 2 5 9 11 96, .n 2 5 9 12 24, .p 2 5 9 13 16, .p 2 5 10 3 16, .n 2 5 10 4 24,
   .n 2 5 10 5 96, .p 2 5 10 7 120, .p 2 5 10 8 368, .n 2 5 10 9 600, .p 2 5 10 10 160, .p 2 5 10 11 104,
   .n 2 5 10 12 24, .n 2 5 10 13 24, .n 2 5 11 3 4, .p 2 5 11 4 36, .n 2 5 11 5 24, .n 2 5 11 6 64,
   .p 2 5 11 7 368, .n 2 5 11 8 488, .p 2 5 11 9 168, .n 2 5 11 10 32, .n 2 5 11 11 12, .p 2 5 11 12 36,
   .p 2 5 11 13 16, .n 2 5 12 4 12, .p 2 5 12 5 68, .n 2 5 12 6 32, .n 2 5 12 7 200, .p 2 5 12 8 56,
   .p 2 5 12 9 288, .n 2 5 12 10 128, .n 2 5 12 11 24, .n 2 5 12 12 12, .n 2 5 12 13 4, .n 2 5 13 5 24,
   .p 2 5 13 6 32, .p 2 5 13 8 80, .n 2 5 13 9 160, .p 2 5 13 10 64, .p 2 5 13 11 8, .p 2 5 14 7 8,
   .n 2 5 14 8 16, .p 2 5 14 9 8, .n 3 4 6 5 24, .p 3 4 6 6 40, .p 3 4 6 7 16, .n 3 4 6 8 48,
   .p 3 4 6 9 8, .p 3 4 6 10 8, .p 3 4 7 3 16, .p 3 4 7 4 16, .n 3 4 7 5 72, .p 3 4 7 6 104,
   .n 3 4 7 7 144, .n 3 4 7 8 32, .p 3 4 7 9 216, .n 3 4 7 10 88, .n 3 4 7 11 16, .n 3 4 8 3 40,
   .n 3 4 8 4 80, .p 3 4 8 5 264, .n 3 4 8 6 200, .p 3 4 8 7 8, .p 3 4 8 8 384, .n 3 4 8 9 368,
   .n 3 4 8 10 136, .p 3 4 8 11 144, .p 3 4 8 12 32, .n 3 4 8 13 8, .p 3 4 9 3 24, .p 3 4 9 4 144,
   .n 3 4 9 5 104, .n 3 4 9 6 360, .p 3 4 9 7 440, .n 3 4 9 8 304, .n 3 4 9 9 176, .p 3 4 9 10 632,
   .n 3 4 9 11 192, .n 3 4 9 12 112, .p 3 4 9 13 8, .p 3 4 10 3 8, .n 3 4 10 4 112, .n 3 4 10 5 192,
   .p 3 4 10 6 632, .n 3 4 10 7 176, .n 3 4 10 8 304, .p 3 4 10 9 440, .n 3 4 10 10 360, .n 3 4 10 11 104,
   .p 3 4 10 12 144, .p 3 4 10 13 24, .n 3 4 11 3 8, .p 3 4 11 4 32, .p 3 4 11 5 144, .n 3 4 11 6 136,
   .n 3 4 11 7 368, .p 3 4 11 8 384, .p 3 4 11 9 8, .n 3 4 11 10 200, .p 3 4 11 11 264, .n 3 4 11 12 80,
   .n 3 4 11 13 40, .n 3 4 12 5 16, .n 3 4 12 6 88, .p 3 4 12 7 216, .n 3 4 12 8 32, .n 3 4 12 9 144,
   .p 3 4 12 10 104, .n 3 4 12 11 72, .p 3 4 12 12 16, .p 3 4 12 13 16, .p 3 4 13 6 8, .p 3 4 13 7 8,
   .n 3 4 13 8 48, .p 3 4 13 9 16, .p 3 4 13 10 40, .n 3 4 13 11 24, .p 4 3 6 5 20, .n 4 3 6 6 64,
   .p 4 3 6 7 68, .n 4 3 6 8 32, .p 4 3 6 9 28, .n 4 3 6 10 32, .p 4 3 6 11 12, .n 4 3 7 3 24,
   .p 4 3 7 4 32, .p 4 3 7 5 12, .p 4 3 7 6 56, .n 4 3 7 7 132, .n 4 3 7 8 24, .p 4 3 7 9 100,
   .p 4 3 7 10 40, .n 4 3 7 11 84, .p 4 3 7 12 24, .p 4 3 8 3 20, .n 4 3 8 5 104, .p 4 3 8 6 104,
   .n 4 3 8 7 60, .p 4 3 8 8 184, .n 4 3 8 9 244, .p 4 3 8 10 120, .n 4 3 8 11 8, .n 4 3 8 12 24,
   .p 4 3 8 13 12, .p 4 3 9 3 44, .n 4 3 9 4 72, .n 4 3 9 5 48, .n 4 3 9 6 16, .p 4 3 9 7 284,
   .n 4 3 9 8 128, .n 4 3 9 9 44, .n 4 3 9 10 208, .p 4 3 9 11 200, .p 4 3 9 12 40, .n 4 3 9 13 52,
   .n 4 3 10 3 52, .p 4 3 10 4 40, .p 4 3 10 5 200, .n 4 3 10 6 208, .n 4 3 10 7 44, .n 4 3 10 8 128,
   .p 4 3 10 9 284, .n 4 3 10 10 16, .n 4 3 10 11 48, .n 4 3 10 12 72, .p 4 3 10 13 44, .p 4 3 11 3 12,
   .n 4 3 11 4 24, .n 4 3 11 5 8, .p 4 3 11 6 120, .n 4 3 11 7 244, .p 4 3 11 8 184, .n 4 3 11 9 60,
   .p 4 3 11 10 104, .n 4 3 11 11 104, .p 4 3 11 13 20, .p 4 3 12 4 24, .n 4 3 12 5 84, .p 4 3 12 6 40,
   .p 4 3 12 7 100, .n 4 3 12 8 24, .n 4 3 12 9 132, .p 4 3 12 10 56, .p 4 3 12 11 12, .p 4 3 12 12 32,
   .n 4 3 12 13 24, .p 4 3 13 5 12, .n 4 3 13 6 32, .p 4 3 13 7 28, .n 4 3 13 8 32, .p 4 3 13 9 68,
   .n 4 3 13 10 64, .p 4 3 13 11 20, .n 5 2 6 5 4, .p 5 2 6 6 16, .n 5 2 6 7 20, .p 5 2 6 9 20,
   .n 5 2 6 10 16, .p 5 2 6 11 4, .p 5 2 7 3 16, .n 5 2 7 4 52, .p 5 2 7 5 36, .p 5 2 7 6 32,
   .n 5 2 7 7 12, .n 5 2 7 8 56, .p 5 2 7 9 12, .p 5 2 7 10 64, .n 5 2 7 11 52, .p 5 2 7 12 12,
   .p 5 2 8 3 4, .n 5 2 8 4 12, .n 5 2 8 5 56, .p 5 2 8 6 192, .n 5 2 8 7 68, .n 5 2 8 8 264,
   .p 5 2 8 9 212, .p 5 2 8 10 96, .n 5 2 8 11 112, .n 5 2 8 12 12, .p 5 2 8 13 20, .p 5 2 9 2 4,
   .p 5 2 9 3 12, .n 5 2 9 4 48, .p 5 2 9 5 24, .p 5 2 9 6 100, .n 5 2 9 7 316, .p 5 2 9 8 320,
   .p 5 2 9 9 172, .n 5 2 9 10 484, .p 5 2 9 11 160, .p 5 2 9 12 112, .n 5 2 9 13 52, .n 5 2 9 14 4,
   .n 5 2 10 2 4, .n 5 2 10 3 52, .p 5 2 10 4 112, .p 5 2 10 5 160, .n 5 2 10 6 484, .p 5 2 10 7 172,
   .p 5 2 10 8 320, .n 5 2 10 9 316, .p 5 2 10 10 100, .p 5 2 10 11 24, .n 5 2 10 12 48, .p 5 2 10 13 12,
   .p 5 2 10 14 4, .p 5 2 11 3 20, .n 5 2 11 4 12, .n 5 2 11 5 112, .p 5 2 11 6 96, .p 5 2 11 7 212,
   .n 5 2 11 8 264, .n 5 2 11 9 68, .p 5 2 11 10 192, .n 5 2 11 11 56, .n 5 2 11 12 12, .p 5 2 11 13 4,
   .p 5 2 12 4 12, .n 5 2 12 5 52, .p 5 2 12 6 64, .p 5 2 12 7 12, .n 5 2 12 8 56, .n 5 2 12 9 12,
   .p 5 2 12 10 32, .p 5 2 12 11 36, .n 5 2 12 12 52, .p 5 2 12 13 16, .p 5 2 13 5 4, .n 5 2 13 6 16,
   .p 5 2 13 7 20, .n 5 2 13 9 20, .p 5 2 13 10 16, .n 5 2 13 11 4, .n 6 1 7 3 4, .p 6 1 7 4 16,
   .n 6 1 7 5 16, .n 6 1 7 6 16, .p 6 1 7 7 40, .n 6 1 7 8 16, .n 6 1 7 9 16, .p 6 1 7 10 16,
   .n 6 1 7 11 4, .p 6 1 8 4 8, .n 6 1 8 5 28, .p 6 1 8 6 16, .p 6 1 8 7 48, .n 6 1 8 8 64,
   .n 6 1 8 9 8, .p 6 1 8 10 48, .n 6 1 8 11 16, .n 6 1 8 12 8, .p 6 1 8 13 4, .n 6 1 9 2 4,
   .p 6 1 9 3 16, .n 6 1 9 4 8, .n 6 1 9 5 48, .p 6 1 9 6 60, .p 6 1 9 7 64, .n 6 1 9 8 144,
   .p 6 1 9 10 148, .n 6 1 9 11 80, .n 6 1 9 12 40, .p 6 1 9 13 48, .n 6 1 9 14 12, .n 6 1 10 2 12,
   .p 6 1 10 3 48, .n 6 1 10 4 40, .n 6 1 10 5 80, .p 6 1 10 6 148, .n 6 1 10 8 144, .p 6 1 10 9 64,
   .p 6 1 10 10 60, .n 6 1 10 11 48, .n 6 1 10 12 8, .p 6 1 10 13 16, .n 6 1 10 14 4, .p 6 1 11 3 4,
   .n 6 1 11 4 8, .n 6 1 11 5 16, .p 6 1 11 6 48, .n 6 1 11 7 8, .n 6 1 11 8 64, .p 6 1 11 9 48,
   .p 6 1 11 10 16, .n 6 1 11 11 28, .p 6 1 11 12 8, .n 6 1 12 5 4, .p 6 1 12 6 16, .n 6 1 12 7 16,
   .n 6 1 12 8 16, .p 6 1 12 9 40, .n 6 1 12 10 16, .n 6 1 12 11 16, .p 6 1 12 12 16, .n 6 1 12 13 4,
   .p 7 0 9 4 8, .n 7 0 9 5 32, .p 7 0 9 6 24, .p 7 0 9 7 64, .n 7 0 9 8 112, .p 7 0 9 10 112,
   .n 7 0 9 11 64, .n 7 0 9 12 24, .p 7 0 9 13 32, .n 7 0 9 14 8, .n 7 0 10 2 8, .p 7 0 10 3 32,
   .n 7 0 10 4 24, .n 7 0 10 5 64, .p 7 0 10 6 112, .n 7 0 10 8 112, .p 7 0 10 9 64, .p 7 0 10 10 24,
   .n 7 0 10 11 32, .p 7 0 10 12 8]

private def g2Mid5_1_a : List FM :=
  [.n 0 7 5 6 16, .p 0 7 5 7 16, .p 0 7 6 6 48, .n 0 7 6 7 48, .n 0 7 7 6 16, .p 0 7 7 7 16,
   .p 0 7 7 8 16, .n 0 7 7 9 16, .n 0 7 8 6 80, .p 0 7 8 7 80, .n 0 7 8 8 48, .p 0 7 8 9 48,
   .p 0 7 9 6 80, .n 0 7 9 7 80, .p 0 7 9 8 16, .n 0 7 9 9 16, .p 0 7 10 6 16, .n 0 7 10 7 16,
   .p 0 7 10 8 80, .n 0 7 10 9 80, .n 0 7 11 6 48, .p 0 7 11 7 48, .n 0 7 11 8 80, .p 0 7 11 9 80,
   .p 0 7 12 6 16, .n 0 7 12 7 16, .n 0 7 12 8 16, .p 0 7 12 9 16, .p 0 7 13 8 48, .n 0 7 13 9 48,
   .n 0 7 14 8 16, .p 0 7 14 9 16, .n 1 6 5 6 8, .n 1 6 5 7 8, .p 1 6 5 8 8, .p 1 6 5 9 8,
   .p 1 6 6 4 8, .p 1 6 6 5 16, .p 1 6 6 6 8, .n 1 6 6 7 16, .p 1 6 6 8 32, .n 1 6 6 9 8,
   .n 1 6 6 10 48, .p 1 6 6 11 8, .p 1 6 7 3 8, .n 1 6 7 4 16, .n 1 6 7 5 32, .n 1 6 7 6 16,
   .p 1 6 7 7 56, .n 1 6 7 8 72, .n 1 6 7 9 16, .p 1 6 7 10 96, .n 1 6 7 11 16, .p 1 6 7 12 8,
   .n 1 6 8 3 24, .n 1 6 8 4 32, .p 1 6 8 6 80, .p 1 6 8 7 40, .n 1 6 8 8 56, .n 1 6 8 9 16,
   .p 1 6 8 10 32, .n 1 6 8 12 24, .p 1 6 9 3 16, .p 1 6 9 4 104, .p 1 6 9 5 16, .n 1 6 9 6 48,
   .n 1 6 9 7 120, .p 1 6 9 8 72, .p 1 6 9 9 80, .n 1 6 9 10 144, .p 1 6 9 11 8, .p 1 6 9 12 16,
   .p 1 6 10 3 16, .n 1 6 10 4 56, .p 1 6 10 5 16, .n 1 6 10 6 112, .n 1 6 10 7 24, .p 1 6 10 8 136,
   .n 1 6 10 9 16, .p 1 6 10 10 16, .p 1 6 10 11 8, .p 1 6 10 12 16, .n 1 6 11 3 24, .n 1 6 11 4 64,
   .p 1 6 11 6 112, .p 1 6 11 7 104, .n 1 6 11 8 88, .n 1 6 11 9 80, .p 1 6 11 10 64, .n 1 6 11 12 24,
   .p 1 6 12 3 8, .p 1 6 12 4 80, .n 1 6 12 5 32, .p 1 6 12 6 16, .n 1 6 12 7 8, .n 1 6 12 8 104,
   .p 1 6 12 9 48, .n 1 6 12 11 16, .p 1 6 12 12 8, .n 1 6 13 4 24, .p 1 6 13 5 16, .n 1 6 13 6 40,
   .n 1 6 13 7 32, .p 1 6 13 8 80, .p 1 6 13 9 8, .n 1 6 13 10 16, .p 1 6 13 11 8, .p 1 6 14 6 8,
   .p 1 6 14 7 8, .n 1 6 14 8 8, .n 1 6 14 9 8, .p 2 5 5 6 20, .n 2 5 5 7 28, .n 2 5 5 8 4,
   .p 2 5 5 9 12, .p 2 5 6 4 4, .p 2 5 6 5 40, .n 2 5 6 6 108, .p 2 5 6 7 80, .n 2 5 6 8 24,
   .p 2 5 6 9 52, .n 2 5 6 10 48, .p 2 5 6 11 4, .n 2 5 7 2 12, .n 2 5 7 3 8, .n 2 5 7 4 8,
   .n 2 5 7 5 40, .p 2 5 7 6 112, .n 2 5 7 7 60, .n 2 5 7 8 20, .p 2 5 7 9 32, .p 2 5 7 10 36,
   .n 2 5 7 11 52, .p 2 5 7 12 20, .p 2 5 8 2 36, .p 2 5 8 3 16, .n 2 5 8 4 8, .n 2 5 8 5 80,
   .p 2 5 8 6 152, .n 2 5 8 7 212, .p 2 5 8 8 276, .n 2 5 8 9 312, .p 2 5 8 10 76, .p 2 5 8 11 76,
   .n 2 5 8 12 20, .n 2 5 9 2 36, .n 2 5 9 3 4, .p 2 5 9 4 64, .p 2 5 9 5 52, .n 2 5 9 6 256,
   .p 2 5 9 7 380, .n 2 5 9 8 180, .p 2 5 9 9 24, .n 2 5 9 10 44, .p 2 5 9 11 24, .n 2 5 9 12 28,
   .p 2 5 9 13 4, .p 2 5 10 2 12, .n 2 5 10 3 4, .n 2 5 10 4 96, .p 2 5 10 5 92, .n 2 5 10 6 72,
   .p 2 5 10 7 60, .n 2 5 10 8 340, .p 2 5 10 9 416, .p 2 5 10 10 12, .n 2 5 10 11 72, .p 2 5 10 12 4,
   .n 2 5 10 13 12, .n 2 5 11 3 4, .p 2 5 11 4 20, .n 2 5 11 5 28, .p 2 5 11 6 248, .n 2 5 11 7 332,
   .p 2 5 11 8 252, .n 2 5 11 9 168, .n 2 5 11 10 64, .p 2 5 11 11 8, .p 2 5 11 12 56, .p 2 5 11 13 12,
   .p 2 5 12 3 4, .p 2 5 12 4 52, .n 2 5 12 5 68, .n 2 5 12 6 80, .p 2 5 12 7 44, .p 2 5 12 8 180,
   .n 2 5 12 9 112, .p 2 5 12 10 8, .p 2 5 12 11 8, .n 2 5 12 12 32, .n 2 5 12 13 4, .n 2 5 13 4 28,
   .p 2 5 13 5 32, .n 2 5 13 6 28, .p 2 5 13 7 72, .n 2 5 13 8 144, .p 2 5 13 9 68, .p 2 5 13 10 24,
   .p 2 5 13 11 4, .p 2 5 14 6 12, .n 2 5 14 7 4, .p 2 5 14 8 4, .n 2 5 14 9 12, .p 3 4 5 6 4,
   .n 3 4 5 7 4, .n 3 4 5 8 4, .p 3 4 5 9 4, .n 3 4 6 4 24, .n 3 4 6 5 4, .p 3 4 6 6 72,
   .n 3 4 6 7 12, .n 3 4 6 8 68, .p 3 4 6 9 32, .p 3 4 6 10 20, .n 3 4 6 11 16, .p 3 4 7 2 32,
   .n 3 4 7 3 48, .p 3 4 7 4 24, .p 3 4 7 5 60, .n 3 4 7 6 76, .n 3 4 7 7 128, .p 3 4 7 8 136,
   .p 3 4 7 9 92, .n 3 4 7 10 124, .p 3 4 7 11 24, .p 3 4 7 12 8, .n 3 4 8 2 80, .p 3 4 8 3 64,
   .p 3 4 8 4 88, .p 3 4 8 5 4, .n 3 4 8 6 100, .n 3 4 8 7 16, .p 3 4 8 8 88, .n 3 4 8 9 28,
   .n 3 4 8 10 36, .n 3 4 8 11 24, .p 3 4 8 12 40, .p 3 4 9 2 64, .p 3 4 9 3 48, .n 3 4 9 4 216,
   .n 3 4 9 5 44, .p 3 4 9 6 20, .p 3 4 9 7 272, .n 3 4 9 8 104, .n 3 4 9 9 244, .p 3 4 9 10 332,
   .n 3 4 9 11 32, .n 3 4 9 12 96, .n 3 4 10 2 16, .n 3 4 10 3 96, .p 3 4 10 4 120, .n 3 4 10 5 76,
   .p 3 4 10 6 244, .p 3 4 10 7 96, .n 3 4 10 8 328, .p 3 4 10 9 28, .n 3 4 10 10 68, .p 3 4 10 11 32,
   .p 3 4 10 12 48, .p 3 4 10 13 16, .p 3 4 11 3 32, .p 3 4 11 4 88, .n 3 4 11 5 28, .n 3 4 11 6 180,
   .n 3 4 11 7 208, .p 3 4 11 8 264, .p 3 4 11 9 164, .n 3 4 11 10 164, .p 3 4 11 11 72, .n 3 4 11 12 8,
   .n 3 4 11 13 32, .n 3 4 12 4 88, .p 3 4 12 5 108, .n 3 4 12 6 28, .p 3 4 12 8 120, .n 3 4 12 9 100,
   .n 3 4 12 10 12, .n 3 4 12 11 24, .p 3 4 12 12 8, .p 3 4 12 13 16, .p 3 4 13 4 8, .n 3 4 13 5 20,
   .p 3 4 13 6 40, .p 3 4 13 7 4, .n 3 4 13 8 100, .p 3 4 13 9 48, .p 3 4 13 10 52, .n 3 4 13 11 32,
   .p 3 4 14 6 4, .n 3 4 14 7 4, .n 3 4 14 8 4, .p 3 4 14 9 4, .p 4 3 6 4 24, .n 4 3 6 5 64,
   .p 4 3 6 6 56, .n 4 3 6 7 16, .p 4 3 6 8 8, .n 4 3 6 9 32, .p 4 3 6 10 40, .n 4 3 6 11 16,
   .n 4 3 7 2 24, .p 4 3 7 3 56, .n 4 3 7 4 36, .n 4 3 7 5 4, .p 4 3 7 6 4, .p 4 3 7 7 12,
   .n 4 3 7 8 4, .p 4 3 7 9 20, .n 4 3 7 10 60, .p 4 3 7 11 44, .n 4 3 7 12 8, .p 4 3 8 2 16,
   .n 4 3 8 3 28, .n 4 3 8 4 80, .p 4 3 8 5 180, .n 4 3 8 6 44, .p 4 3 8 7 20, .n 4 3 8 8 316,
   .p 4 3 8 9 372, .n 4 3 8 10 20, .n 4 3 8 11 168, .p 4 3 8 12 60, .p 4 3 8 13 8, .p 4 3 9 1 8,
   .p 4 3 9 2 40, .n 4 3 9 3 76, .n 4 3 9 4 28, .p 4 3 9 5 32, .p 4 3 9 6 232, .n 4 3 9 7 376,
   .p 4 3 9 8 128, .p 4 3 9 9 56, .n 4 3 9 10 16, .p 4 3 9 11 4, .p 4 3 9 12 28, .n 4 3 9 13 32,
   .n 4 3 10 1 8, .n 4 3 10 2 32, .p 4 3 10 3 20, .p 4 3 10 4 140, .n 4 3 10 5 160, .n 4 3 10 6 64,
   .p 4 3 10 7 48, .p 4 3 10 8 440, .n 4 3 10 9 528, .p 4 3 10 11 220, .n 4 3 10 12 100, .p 4 3 10 13 24,
   .p 4 3 11 3 20, .p 4 3 11 4 32, .n 4 3 11 5 12, .n 4 3 11 6 316, .p 4 3 11 7 452, .n 4 3 11 8 204,
   .n 4 3 11 9 28, .p 4 3 11 10 140, .n 4 3 11 11 72, .n 4 3 11 12 36, .p 4 3 11 13 24, .p 4 3 12 3 8,
   .n 4 3 12 4 68, .p 4 3 12 5 68, .p 4 3 12 6 84, .n 4 3 12 7 52, .n 4 3 12 8 164, .p 4 3 12 9 164,
   .n 4 3 12 10 36, .n 4 3 12 11 36, .p 4 3 12 12 56, .n 4 3 12 13 24, .p 4 3 13 4 16, .n 4 3 13 5 40,
   .p 4 3 13 6 48, .n 4 3 13 7 88, .p 4 3 13 8 112, .n 4 3 13 9 24, .n 4 3 13 10 48, .p 4 3 13 11 24,
   .n 5 2 6 4 12, .p 5 2 6 5 36, .n 5 2 6 6 28, .n 5 2 6 7 12, .p 5 2 6 8 28, .n 5 2 6 9 20,
   .p 5 2 6 10 12, .n 5 2 6 11 4, .p 5 2 7 3 4, .n 5 2 7 4 28, .p 5 2 7 5 32, .p 5 2 7 6 24,
   .n 5 2 7 7 24, .n 5 2 7 8 32, .p 5 2 7 10 40, .n 5 2 7 11 12, .n 5 2 7 12 4, .p 5 2 8 2 44,
   .n 5 2 8 3 76, .n 5 2 8 4 4, .p 5 2 8 5 20, .p 5 2 8 6 56, .n 5 2 8 7 48, .n 5 2 8 8 24,
   .p 5 2 8 9 96, .n 5 2 8 10 68, .n 5 2 8 11 4, .n 5 2 8 12 4, .p 5 2 8 13 12, .p 5 2 9 1 4,
   .n 5 2 9 2 40, .p 5 2 9 3 24, .p 5 2 9 4 44, .p 5 2 9 5 12, .p 5 2 9 6 64, .n 5 2 9 7 268,
   .p 5 2 9 8 92, .p 5 2 9 9 224, .n 5 2 9 10 228, .p 5 2 9 11 36, .p 5 2 9 12 72, .n 5 2 9 13 32,
   .n 5 2 9 14 4, .n 5 2 10 1 20, .p 5 2 10 2 32, .p 5 2 10 3 56, .n 5 2 10 4 132, .p 5 2 10 5 116,
   .n 5 2 10 6 104, .n 5 2 10 7 44, .p 5 2 10 8 172, .n 5 2 10 9 56, .p 5 2 10 10 20, .n 5 2 10 11 60,
   .p 5 2 10 12 8, .p 5 2 10 13 8, .p 5 2 10 14 4, .p 5 2 11 2 12, .p 5 2 11 3 4, .n 5 2 11 4 52,
   .n 5 2 11 5 44, .p 5 2 11 6 120, .p 5 2 11 7 112, .n 5 2 11 8 200, .n 5 2 11 9 48, .p 5 2 11 10 124,
   .n 5 2 11 11 20, .n 5 2 11 12 4, .n 5 2 11 13 4, .p 5 2 12 3 4, .p 5 2 12 4 4, .n 5 2 12 5 64,
   .p 5 2 12 6 88, .p 5 2 12 7 40, .n 5 2 12 8 112, .n 5 2 12 9 16, .p 5 2 12 10 72, .p 5 2 12 11 20,
   .n 5 2 12 12 52, .p 5 2 12 13 16, .p 5 2 13 4 4, .n 5 2 13 5 12, .p 5 2 13 6 4, .p 5 2 13 7 20,
   .n 5 2 13 8 20, .n 5 2 13 9 4, .p 5 2 13 10 12, .n 5 2 13 11 4, .p 6 1 7 2 4, .n 6 1 7 3 12,
   .p 6 1 7 4 16, .n 6 1 7 5 16, .n 6 1 7 6 8, .p 6 1 7 7 56, .n 6 1 7 8 48, .n 6 1 7 9 16,
   .p 6 1 7 10 36, .n 6 1 7 11 12, .n 6 1 8 2 16, .p 6 1 8 3 48, .n 6 1 8 4 12, .n 6 1 8 5 76,
   .p 6 1 8 6 32, .p 6 1 8 7 64, .p 6 1 8 8 8, .n 6 1 8 9 88, .p 6 1 8 10 16, .p 6 1 8 11 48,
   .n 6 1 8 12 28, .p 6 1 8 13 4, .n 6 1 9 1 12, .p 6 1 9 2 20, .p 6 1 9 3 24, .n 6 1 9 4 40,
   .n 6 1 9 5 36, .p 6 1 9 6 44, .p 6 1 9 7 48, .n 6 1 9 8 80, .p 6 1 9 9 12, .p 6 1 9 10 76,
   .n 6 1 9 11 72, .n 6 1 9 12 8, .p 6 1 9 13 36, .n 6 1 9 14 12, .n 6 1 10 1 4, .p 6 1 10 2 28,
   .n 6 1 10 3 24, .n 6 1 10 4 88, .p 6 1 10 5 84, .p 6 1 10 6 196, .n 6 1 10 7 208, .n 6 1 10 8 208,
   .p 6 1 10 9 292, .p 6 1 10 10 36, .n 6 1 10 11 152, .p 6 1 10 12 40, .p 6 1 10 13 12, .n 6 1 10 14 4,
   .p 6 1 11 2 12, .n 6 1 11 3 4, .n 6 1 11 4 96, .p 6 1 11 5 112, .p 6 1 11 6 136, .n 6 1 11 7 248,
   .n 6 1 11 8 16, .p 6 1 11 9 176, .n 6 1 11 10 52, .n 6 1 11 11 36, .p 6 1 11 12 16, .n 6 1 12 4 4,
   .p 6 1 12 5 12, .n 6 1 12 7 32, .p 6 1 12 8 24, .p 6 1 12 9 24, .n 6 1 12 10 32, .p 6 1 12 12 12,
   .n 6 1 12 13 4, .n 7 0 9 3 8, .p 7 0 9 4 24, .n 7 0 9 5 8, .n 7 0 9 6 40, .p 7 0 9 7 48,
   .n 7 0 9 8 16, .n 7 0 9 9 16, .p 7 0 9 10 48, .n 7 0 9 11 40, .n 7 0 9 12 8, .p 7 0 9 13 24,
   .n 7 0 9 14 8, .p 7 0 10 1 8, .n 7 0 10 2 24, .p 7 0 10 3 8, .p 7 0 10 4 40, .n 7 0 10 5 48,
   .p 7 0 10 6 16, .p 7 0 10 7 16, .n 7 0 10 8 48, .p 7 0 10 9 40, .p 7 0 10 10 8, .n 7 0 10 11 24,
   .p 7 0 10 12 8]

private def g2Mid5_1_b : List FM :=
  [.n 0 7 5 6 16, .p 0 7 5 7 16, .p 0 7 6 6 16, .p 0 7 6 7 16, .n 0 7 6 8 32, .p 0 7 7 6 80,
   .n 0 7 7 7 112, .n 0 7 7 8 16, .p 0 7 7 9 48, .n 0 7 8 6 144, .p 0 7 8 7 16, .p 0 7 8 8 240,
   .n 0 7 8 9 80, .n 0 7 8 10 32, .p 0 7 9 6 16, .p 0 7 9 7 176, .n 0 7 9 8 208, .n 0 7 9 9 80,
   .p 0 7 9 10 96, .p 0 7 10 6 112, .n 0 7 10 7 80, .n 0 7 10 8 144, .p 0 7 10 9 176, .n 0 7 10 10 64,
   .n 0 7 11 6 80, .n 0 7 11 7 80, .p 0 7 11 8 208, .p 0 7 11 9 16, .n 0 7 11 10 64, .p 0 7 12 6 16,
   .p 0 7 12 7 48, .n 0 7 12 8 48, .n 0 7 12 9 112, .p 0 7 12 10 96, .p 0 7 13 8 16, .p 0 7 13 9 16,
   .n 0 7 13 10 32, .n 0 7 14 8 16, .p 0 7 14 9 16, .n 1 6 5 7 16, .p 1 6 5 9 16, .p 1 6 6 5 32,
   .n 1 6 6 6 48, .p 1 6 6 7 40, .p 1 6 6 8 56, .n 1 6 6 9 56, .n 1 6 6 10 8, .n 1 6 6 11 16,
   .n 1 6 7 5 8, .p 1 6 7 6 24, .n 1 6 7 7 16, .n 1 6 7 8 104, .p 1 6 7 9 8, .p 1 6 7 10 56,
   .p 1 6 7 11 16, .p 1 6 7 12 24, .n 1 6 8 3 16, .n 1 6 8 5 96, .p 1 6 8 6 40, .p 1 6 8 7 72,
   .p 1 6 8 8 16, .p 1 6 8 9 40, .p 1 6 8 10 24, .n 1 6 8 11 8, .n 1 6 8 12 80, .p 1 6 8 13 8,
   .p 1 6 9 3 40, .n 1 6 9 4 8, .p 1 6 9 5 24, .p 1 6 9 6 152, .n 1 6 9 7 120, .n 1 6 9 8 8,
   .p 1 6 9 9 32, .n 1 6 9 10 232, .p 1 6 9 11 48, .p 1 6 9 12 96, .n 1 6 9 13 24, .n 1 6 10 3 24,
   .p 1 6 10 4 48, .p 1 6 10 5 104, .n 1 6 10 6 248, .n 1 6 10 7 112, .p 1 6 10 8 80, .p 1 6 10 9 32,
   .p 1 6 10 10 168, .n 1 6 10 11 24, .n 1 6 10 12 48, .p 1 6 10 13 24, .n 1 6 11 3 8, .n 1 6 11 4 96,
   .n 1 6 11 5 48, .p 1 6 11 6 72, .p 1 6 11 7 176, .p 1 6 11 8 40, .n 1 6 11 9 72, .n 1 6 11 10 24,
   .n 1 6 11 11 40, .p 1 6 11 12 8, .n 1 6 11 13 8, .p 1 6 12 3 8, .p 1 6 12 4 80, .n 1 6 12 5 8,
   .n 1 6 12 6 8, .p 1 6 12 7 56, .n 1 6 12 8 144, .n 1 6 12 9 72, .p 1 6 12 10 72, .p 1 6 12 11 16,
   .n 1 6 13 4 24, .p 1 6 13 6 8, .n 1 6 13 7 88, .p 1 6 13 8 72, .p 1 6 13 9 80, .n 1 6 13 10 56,
   .p 1 6 13 11 8, .p 1 6 14 6 8, .p 1 6 14 7 8, .n 1 6 14 8 8, .n 1 6 14 9 8, .p 2 5 5 6 16,
   .n 2 5 5 7 24, .p 2 5 5 9 8, .p 2 5 6 5 32, .p 2 5 6 6 8, .n 2 5 6 7 116, .p 2 5 6 8 100,
   .n 2 5 6 9 36, .p 2 5 6 10 36, .n 2 5 6 11 24, .n 2 5 7 2 4, .n 2 5 7 3 4, .n 2 5 7 4 40,
   .p 2 5 7 5 4, .n 2 5 7 6 180, .p 2 5 7 7 344, .p 2 5 7 8 4, .n 2 5 7 9 132, .n 2 5 7 11 20,
   .p 2 5 7 12 28, .p 2 5 8 2 20, .p 2 5 8 3 28, .p 2 5 8 4 8, .n 2 5 8 5 88, .p 2 5 8 6 276,
   .p 2 5 8 7 36, .n 2 5 8 8 760, .p 2 5 8 9 380, .p 2 5 8 10 120, .p 2 5 8 11 72, .n 2 5 8 12 112,
   .p 2 5 8 13 20, .n 2 5 9 2 28, .n 2 5 9 3 24, .p 2 5 9 4 48, .p 2 5 9 5 8, .p 2 5 9 6 164,
   .n 2 5 9 7 612, .p 2 5 9 8 740, .p 2 5 9 9 120, .n 2 5 9 10 560, .p 2 5 9 11 44, .p 2 5 9 12 116,
   .n 2 5 9 13 16, .p 2 5 10 2 12, .n 2 5 10 3 16, .p 2 5 10 4 52, .p 2 5 10 5 56, .n 2 5 10 6 556,
   .p 2 5 10 7 224, .p 2 5 10 8 528, .n 2 5 10 9 648, .p 2 5 10 10 488, .n 2 5 10 11 64, .n 2 5 10 12 44,
   .n 2 5 10 13 32, .p 2 5 11 3 12, .n 2 5 11 4 108, .p 2 5 11 5 4, .p 2 5 11 6 332, .p 2 5 11 7 352,
   .n 2 5 11 8 828, .p 2 5 11 9 92, .p 2 5 11 10 108, .n 2 5 11 11 44, .p 2 5 11 12 48, .p 2 5 11 13 32,
   .p 2 5 12 3 4, .p 2 5 12 4 68, .n 2 5 12 5 16, .n 2 5 12 6 124, .n 2 5 12 7 172, .p 2 5 12 8 192,
   .p 2 5 12 9 348, .n 2 5 12 10 292, .p 2 5 12 11 32, .n 2 5 12 12 36, .n 2 5 12 13 4, .n 2 5 13 4 28,
   .p 2 5 13 6 52, .n 2 5 13 7 28, .p 2 5 13 8 20, .n 2 5 13 9 120, .p 2 5 13 10 100, .p 2 5 13 11 4,
   .p 2 5 14 6 12, .n 2 5 14 7 4, .p 2 5 14 8 4, .n 2 5 14 9 12, .p 3 4 6 4 4, .n 3 4 6 5 60,
   .p 3 4 6 6 112, .n 3 4 6 7 4, .n 3 4 6 8 112, .p 3 4 6 9 64, .n 3 4 6 10 4, .p 3 4 7 2 8,
   .p 3 4 7 3 4, .n 3 4 7 4 8, .n 3 4 7 5 12, .p 3 4 7 6 4, .n 3 4 7 7 108, .p 3 4 7 8 96,
   .p 3 4 7 9 116, .n 3 4 7 10 92, .n 3 4 7 12 8, .n 3 4 8 2 32, .p 3 4 8 3 12, .n 3 4 8 4 44,
   .p 3 4 8 5 288, .n 3 4 8 6 220, .n 3 4 8 7 84, .p 3 4 8 8 308, .n 3 4 8 9 304, .n 3 4 8 10 60,
   .p 3 4 8 11 88, .p 3 4 8 12 48, .p 3 4 9 2 40, .n 3 4 9 3 48, .p 3 4 9 4 148, .n 3 4 9 5 116,
   .n 3 4 9 6 460, .p 3 4 9 7 592, .n 3 4 9 8 208, .n 3 4 9 9 304, .p 3 4 9 10 708, .n 3 4 9 11 168,
   .n 3 4 9 12 228, .p 3 4 9 13 44, .n 3 4 10 2 16, .p 3 4 10 3 4, .n 3 4 10 4 72, .n 3 4 10 5 332,
   .p 3 4 10 6 716, .p 3 4 10 7 104, .n 3 4 10 8 420, .p 3 4 10 9 228, .n 3 4 10 10 428, .p 3 4 10 11 28,
   .p 3 4 10 12 220, .n 3 4 10 13 32, .p 3 4 11 3 28, .p 3 4 11 4 60, .p 3 4 11 5 152, .n 3 4 11 6 164,
   .n 3 4 11 7 492, .p 3 4 11 8 312, .p 3 4 11 9 156, .n 3 4 11 10 140, .p 3 4 11 11 184, .n 3 4 11 12 68,
   .n 3 4 11 13 28, .n 3 4 12 4 96, .p 3 4 12 5 88, .n 3 4 12 6 4, .n 3 4 12 7 44, .p 3 4 12 8 132,
   .p 3 4 12 9 40, .n 3 4 12 10 68, .n 3 4 12 11 100, .p 3 4 12 12 36, .p 3 4 12 13 16, .p 3 4 13 4 8,
   .n 3 4 13 5 8, .p 3 4 13 6 12, .p 3 4 13 7 40, .n 3 4 13 8 104, .p 3 4 13 10 84, .n 3 4 13 11 32,
   .p 3 4 14 6 4, .n 3 4 14 7 4, .n 3 4 14 8 4, .p 3 4 14 9 4, .p 4 3 6 5 8, .n 4 3 6 6 36,
   .p 4 3 6 7 60, .n 4 3 6 8 56, .p 4 3 6 9 48, .n 4 3 6 10 36, .p 4 3 6 11 12, .n 4 3 7 3 16,
   .p 4 3 7 4 36, .p 4 3 7 5 8, .p 4 3 7 6 32, .n 4 3 7 7 180, .p 4 3 7 8 100, .p 4 3 7 9 48,
   .n 4 3 7 10 24, .p 4 3 7 11 12, .n 4 3 7 12 16, .n 4 3 8 2 12, .n 4 3 8 3 16, .p 4 3 8 4 40,
   .p 4 3 8 5 20, .n 4 3 8 6 84, .n 4 3 8 7 60, .p 4 3 8 8 352, .n 4 3 8 9 208, .n 4 3 8 10 40,
   .n 4 3 8 11 108, .p 4 3 8 12 128, .n 4 3 8 13 12, .p 4 3 9 1 4, .p 4 3 9 2 52, .p 4 3 9 3 4,
   .n 4 3 9 4 168, .p 4 3 9 5 60, .p 4 3 9 6 52, .p 4 3 9 7 296, .n 4 3 9 8 568, .p 4 3 9 10 400,
   .p 4 3 9 11 12, .n 4 3 9 12 152, .p 4 3 9 13 8, .n 4 3 10 1 8, .n 4 3 10 2 24, .p 4 3 10 3 16,
   .n 4 3 10 4 48, .n 4 3 10 5 4, .p 4 3 10 6 300, .n 4 3 10 7 132, .n 4 3 10 8 256, .p 4 3 10 9 344,
   .n 4 3 10 10 332, .p 4 3 10 11 140, .n 4 3 10 12 24, .p 4 3 10 13 28, .n 4 3 11 3 4, .p 4 3 11 4 152,
   .n 4 3 11 5 28, .n 4 3 11 6 336, .n 4 3 11 7 164, .p 4 3 11 8 596, .n 4 3 11 9 120, .n 4 3 11 10 56,
   .n 4 3 11 11 64, .p 4 3 11 12 28, .n 4 3 11 13 4, .p 4 3 12 3 8, .n 4 3 12 4 76, .p 4 3 12 5 16,
   .p 4 3 12 6 132, .p 4 3 12 7 52, .n 4 3 12 8 112, .n 4 3 12 9 144, .p 4 3 12 10 132, .n 4 3 12 11 36,
   .p 4 3 12 12 52, .n 4 3 12 13 24, .p 4 3 13 4 16, .n 4 3 13 5 12, .n 4 3 13 6 28, .p 4 3 13 7 16,
   .n 4 3 13 8 24, .p 4 3 13 9 100, .n 4 3 13 10 92, .p 4 3 13 11 24, .n 5 2 6 4 4, .p 5 2 6 5 12,
   .n 5 2 6 6 4, .n 5 2 6 7 20, .p 5 2 6 8 20, .p 5 2 6 9 4, .n 5 2 6 10 12, .p 5 2 6 11 4,
   .n 5 2 7 2 8, .p 5 2 7 3 28, .n 5 2 7 4 52, .p 5 2 7 5 24, .p 5 2 7 6 72, .n 5 2 7 7 56,
   .n 5 2 7 8 56, .p 5 2 7 9 24, .p 5 2 7 10 48, .n 5 2 7 11 20, .n 5 2 7 12 4, .p 5 2 8 2 32,
   .n 5 2 8 3 32, .n 5 2 8 4 48, .n 5 2 8 5 24, .p 5 2 8 6 188, .n 5 2 8 7 92, .n 5 2 8 8 180,
   .p 5 2 8 9 260, .n 5 2 8 10 44, .n 5 2 8 11 116, .p 5 2 8 12 52, .p 5 2 8 13 4, .n 5 2 9 2 12,
   .p 5 2 9 3 28, .n 5 2 9 4 84, .p 5 2 9 5 92, .p 5 2 9 6 216, .n 5 2 9 7 476, .p 5 2 9 8 148,
   .p 5 2 9 9 348, .n 5 2 9 10 392, .p 5 2 9 11 64, .p 5 2 9 12 128, .n 5 2 9 13 56, .n 5 2 9 14 4,
   .n 5 2 10 1 20, .p 5 2 10 2 40, .n 5 2 10 3 12, .n 5 2 10 4 52, .p 5 2 10 5 228, .n 5 2 10 6 304,
   .n 5 2 10 7 44, .p 5 2 10 8 292, .n 5 2 10 9 160, .p 5 2 10 10 84, .n 5 2 10 11 24, .n 5 2 10 12 64,
   .p 5 2 10 13 32, .p 5 2 10 14 4, .p 5 2 11 2 12, .n 5 2 11 3 8, .p 5 2 11 4 8, .n 5 2 11 5 104,
   .p 5 2 11 6 48, .p 5 2 11 7 240, .n 5 2 11 8 208, .n 5 2 11 9 104, .p 5 2 11 10 148, .n 5 2 11 11 24,
   .n 5 2 11 12 8, .p 5 2 12 3 4, .p 5 2 12 4 4, .n 5 2 12 5 60, .p 5 2 12 6 60, .p 5 2 12 7 76,
   .n 5 2 12 8 76, .n 5 2 12 9 100, .p 5 2 12 10 84, .p 5 2 12 11 64, .n 5 2 12 12 72, .p 5 2 12 13 16,
   .p 5 2 13 4 4, .n 5 2 13 5 4, .n 5 2 13 6 20, .p 5 2 13 7 36, .n 5 2 13 8 4, .n 5 2 13 9 28,
   .p 5 2 13 10 20, .n 5 2 13 11 4, .p 6 1 7 2 4, .n 6 1 7 3 12, .p 6 1 7 4 16, .n 6 1 7 5 16,
   .n 6 1 7 6 8, .p 6 1 7 7 56, .n 6 1 7 8 48, .n 6 1 7 9 16, .p 6 1 7 10 36, .n 6 1 7 11 12,
   .n 6 1 8 2 8, .p 6 1 8 3 24, .n 6 1 8 4 4, .n 6 1 8 5 52, .p 6 1 8 6 40, .p 6 1 8 7 40,
   .n 6 1 8 8 48, .n 6 1 8 9 16, .p 6 1 8 10 32, .n 6 1 8 12 12, .p 6 1 8 13 4, .n 6 1 9 1 4,
   .n 6 1 9 2 4, .p 6 1 9 3 32, .n 6 1 9 4 8, .n 6 1 9 5 36, .n 6 1 9 6 4, .p 6 1 9 8 48,
   .p 6 1 9 9 20, .n 6 1 9 10 44, .n 6 1 9 11 32, .p 6 1 9 12 24, .p 6 1 9 13 20, .n 6 1 9 14 12,
   .n 6 1 10 1 4, .p 6 1 10 2 12, .n 6 1 10 4 40, .p 6 1 10 5 20, .p 6 1 10 6 84, .n 6 1 10 7 48,
   .n 6 1 10 8 128, .p 6 1 10 9 84, .p 6 1 10 10 100, .n 6 1 10 11 80, .n 6 1 10 12 24, .p 6 1 10 13 28,
   .n 6 1 10 14 4, .p 6 1 11 2 12, .p 6 1 11 3 4, .n 6 1 11 4 88, .p 6 1 11 5 24, .p 6 1 11 6 200,
   .n 6 1 11 7 104, .n 6 1 11 8 192, .p 6 1 11 9 128, .p 6 1 11 10 76, .n 6 1 11 11 60, .n 6 1 11 12 8,
   .p 6 1 11 13 8, .n 6 1 12 4 4, .p 6 1 12 5 4, .p 6 1 12 6 24, .n 6 1 12 7 40, .n 6 1 12 8 16,
   .p 6 1 12 9 64, .n 6 1 12 10 24, .n 6 1 12 11 24, .p 6 1 12 12 20, .n 6 1 12 13 4, .n 7 0 9 3 8,
   .p 7 0 9 4 24, .n 7 0 9 5 8, .n 7 0 9 6 40, .p 7 0 9 7 48, .n 7 0 9 8 16, .n 7 0 9 9 16,
   .p 7 0 9 10 48, .n 7 0 9 11 40, .n 7 0 9 12 8, .p 7 0 9 13 24, .n 7 0 9 14 8, .p 7 0 10 1 8,
   .n 7 0 10 2 24, .p 7 0 10 3 8, .p 7 0 10 4 40, .n 7 0 10 5 48, .p 7 0 10 6 16, .p 7 0 10 7 16,
   .n 7 0 10 8 48, .p 7 0 10 9 40, .p 7 0 10 10 8, .n 7 0 10 11 24, .p 7 0 10 12 8]

set_option maxRecDepth 65536 in
private theorem g2_det5_1_step01 :
    fmMerge (fmMerge [] (fmMul (fmSubMat g2FM ⟨1, by decide⟩ ⟨0, by decide⟩ ⟨0, by decide⟩) g2Val4_14))
      (fmMul (fmNeg (fmSubMat g2FM ⟨1, by decide⟩ ⟨0, by decide⟩ ⟨1, by decide⟩)) g2Val4_9) =
      g2Mid5_1_a := rfl

set_option maxRecDepth 65536 in
private theorem g2_det5_1_step2 :
    fmMerge g2Mid5_1_a (fmMul (fmSubMat g2FM ⟨1, by decide⟩ ⟨0, by decide⟩ ⟨2, by decide⟩) g2Val4_8) =
      g2Mid5_1_b := rfl

set_option maxRecDepth 65536 in
private theorem g2_det5_1_step34 :
    fmMerge (fmMerge g2Mid5_1_b (fmMul (fmNeg (fmSubMat g2FM ⟨1, by decide⟩ ⟨0, by decide⟩ ⟨3, by decide⟩)) g2Val4_7))
      (fmMul (fmSubMat g2FM ⟨1, by decide⟩ ⟨0, by decide⟩ ⟨4, by decide⟩) g2Val4_6) =
      g2Val5_1 := rfl

private theorem g2_det5_1 : fmDet 5 (fmSubMat g2FM ⟨1, by decide⟩) = g2Val5_1 :=
  fmDet5_of_sub4_split _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (fin4Mat_eq_of_vals _ _ (by decide)) g2_det4_14
    (fin4Mat_eq_of_vals _ _ (by decide)) g2_det4_9
    (fin4Mat_eq_of_vals _ _ (by decide)) g2_det4_8
    (fin4Mat_eq_of_vals _ _ (by decide)) g2_det4_7
    (fin4Mat_eq_of_vals _ _ (by decide)) g2_det4_6
    g2_det5_1_step01 g2_det5_1_step2 g2_det5_1_step34

private def g2Val5_2 : List FM :=
  [.p 0 7 5 8 32, .n 0 7 6 8 128, .p 0 7 7 8 96, .p 0 7 8 8 256, .n 0 7 9 8 448, .p 0 7 11 8 448,
   .n 0 7 12 8 256, .n 0 7 13 8 96, .p 0 7 14 8 128, .n 0 7 15 8 32, .n 1 6 5 7 32, .p 1 6 5 9 32,
   .p 1 6 6 7 64, .n 1 6 6 9 64, .p 1 6 7 7 96, .n 1 6 7 9 96, .n 1 6 8 7 256, .p 1 6 8 9 256,
   .n 1 6 9 7 64, .p 1 6 9 9 64, .p 1 6 10 7 384, .n 1 6 10 9 384, .n 1 6 11 7 64, .p 1 6 11 9 64,
   .n 1 6 12 7 256, .p 1 6 12 9 256, .p 1 6 13 7 96, .n 1 6 13 9 96, .p 1 6 14 7 64, .n 1 6 14 9 64,
   .n 1 6 15 7 32, .p 1 6 15 9 32, .p 2 5 5 7 16, .n 2 5 5 8 32, .p 2 5 5 9 16, .p 2 5 6 5 16,
   .p 2 5 6 6 48, .n 2 5 6 7 112, .p 2 5 6 8 96, .n 2 5 6 9 112, .p 2 5 6 10 48, .p 2 5 6 11 16,
   .n 2 5 7 4 8, .n 2 5 7 5 32, .n 2 5 7 6 160, .p 2 5 7 7 144, .p 2 5 7 8 112, .p 2 5 7 9 144,
   .n 2 5 7 10 160, .n 2 5 7 11 32, .n 2 5 7 12 8, .p 2 5 8 4 32, .n 2 5 8 5 32, .p 2 5 8 6 160,
   .p 2 5 8 7 224, .n 2 5 8 8 768, .p 2 5 8 9 224, .p 2 5 8 10 160, .n 2 5 8 11 32, .p 2 5 8 12 32,
   .n 2 5 9 4 40, .p 2 5 9 5 96, .n 2 5 9 6 32, .n 2 5 9 7 512, .p 2 5 9 8 976, .n 2 5 9 9 512,
   .n 2 5 9 10 32, .p 2 5 9 11 96, .n 2 5 9 12 40, .p 2 5 11 4 40, .n 2 5 11 5 96, .p 2 5 11 6 32,
   .p 2 5 11 7 512, .n 2 5 11 8 976, .p 2 5 11 9 512, .p 2 5 11 10 32, .n 2 5 11 11 96, .p 2 5 11 12 40,
   .n 2 5 12 4 32, .p 2 5 12 5 32, .n 2 5 12 6 160, .n 2 5 12 7 224, .p 2 5 12 8 768, .n 2 5 12 9 224,
   .n 2 5 12 10 160, .p 2 5 12 11 32, .n 2 5 12 12 32, .p 2 5 13 4 8, .p 2 5 13 5 32, .p 2 5 13 6 160,
   .n 2 5 13 7 144, .n 2 5 13 8 112, .n 2 5 13 9 144, .p 2 5 13 10 160, .p 2 5 13 11 32, .p 2 5 13 12 8,
   .n 2 5 14 5 16, .n 2 5 14 6 48, .p 2 5 14 7 112, .n 2 5 14 8 96, .p 2 5 14 9 112, .n 2 5 14 10 48,
   .n 2 5 14 11 16, .n 2 5 15 7 16, .p 2 5 15 8 32, .n 2 5 15 9 16, .n 3 4 6 5 40, .p 3 4 6 6 64,
   .n 3 4 6 7 8, .p 3 4 6 9 8, .n 3 4 6 10 64, .p 3 4 6 11 40, .p 3 4 7 4 8, .p 3 4 7 5 32,
   .p 3 4 7 6 80, .n 3 4 7 7 288, .p 3 4 7 9 288, .n 3 4 7 10 80, .n 3 4 7 11 32, .n 3 4 7 12 8,
   .n 3 4 8 4 48, .p 3 4 8 5 96, .n 3 4 8 6 352, .p 3 4 8 7 608, .n 3 4 8 9 608, .p 3 4 8 10 352,
   .n 3 4 8 11 96, .p 3 4 8 12 48, .p 3 4 9 4 120, .n 3 4 9 5 32, .n 3 4 9 6 336, .p 3 4 9 7 288,
   .n 3 4 9 9 288, .p 3 4 9 10 336, .p 3 4 9 11 32, .n 3 4 9 12 120, .n 3 4 10 4 160, .n 3 4 10 5 112,
   .p 3 4 10 6 1088, .n 3 4 10 7 1200, .p 3 4 10 9 1200, .n 3 4 10 10 1088, .p 3 4 10 11 112, .p 3 4 10 12 160,
   .p 3 4 11 4 120, .n 3 4 11 5 32, .n 3 4 11 6 336, .p 3 4 11 7 288, .n 3 4 11 9 288, .p 3 4 11 10 336,
   .p 3 4 11 11 32, .n 3 4 11 12 120, .n 3 4 12 4 48, .p 3 4 12 5 96, .n 3 4 12 6 352, .p 3 4 12 7 608,
   .n 3 4 12 9 608, .p 3 4 12 10 352, .n 3 4 12 11 96, .p 3 4 12 12 48, .p 3 4 13 4 8, .p 3 4 13 5 32,
   .p 3 4 13 6 80, .n 3 4 13 7 288, .p 3 4 13 9 288, .n 3 4 13 10 80, .n 3 4 13 11 32, .n 3 4 13 12 8,
   .n 3 4 14 5 40, .p 3 4 14 6 64, .n 3 4 14 7 8, .p 3 4 14 9 8, .n 3 4 14 10 64, .p 3 4 14 11 40,
   .p 4 3 6 5 32, .n 4 3 6 6 96, .p 4 3 6 7 96, .n 4 3 6 8 64, .p 4 3 6 9 96, .n 4 3 6 10 96,
   .p 4 3 6 11 32, .p 4 3 7 4 8, .n 4 3 7 5 48, .p 4 3 7 6 64, .p 4 3 7 7 48, .n 4 3 7 8 144,
   .p 4 3 7 9 48, .p 4 3 7 10 64, .n 4 3 7 11 48, .p 4 3 7 12 8, .p 4 3 8 3 8, .n 4 3 8 4 32,
   .p 4 3 8 5 8, .p 4 3 8 6 128, .n 4 3 8 7 272, .p 4 3 8 8 320, .n 4 3 8 9 272, .p 4 3 8 10 128,
   .p 4 3 8 11 8, .n 4 3 8 12 32, .p 4 3 8 13 8, .n 4 3 9 3 16, .p 4 3 9 4 40, .n 4 3 9 6 64,
   .p 4 3 9 7 16, .p 4 3 9 8 48, .p 4 3 9 9 16, .n 4 3 9 10 64, .p 4 3 9 12 40, .n 4 3 9 13 16,
   .p 4 3 11 3 16, .n 4 3 11 4 40, .p 4 3 11 6 64, .n 4 3 11 7 16, .n 4 3 11 8 48, .n 4 3 11 9 16,
   .p 4 3 11 10 64, .n 4 3 11 12 40, .p 4 3 11 13 16, .n 4 3 12 3 8, .p 4 3 12 4 32, .n 4 3 12 5 8,
   .n 4 3 12 6 128, .p 4 3 12 7 272, .n 4 3 12 8 320, .p 4 3 12 9 272, .n 4 3 12 10 128, .n 4 3 12 11 8,
   .p 4 3 12 12 32, .n 4 3 12 13 8, .n 4 3 13 4 8, .p 4 3 13 5 48, .n 4 3 13 6 64, .n 4 3 13 7 48,
   .p 4 3 13 8 144, .n 4 3 13 9 48, .n 4 3 13 10 64, .p 4 3 13 11 48, .n 4 3 13 12 8, .n 4 3 14 5 32,
   .p 4 3 14 6 96, .n 4 3 14 7 96, .p 4 3 14 8 64, .n 4 3 14 9 96, .p 4 3 14 10 96, .n 4 3 14 11 32,
   .n 5 2 6 5 8, .p 5 2 6 6 32, .n 5 2 6 7 40, .p 5 2 6 9 40, .n 5 2 6 10 32, .p 5 2 6 11 8,
   .n 5 2 7 4 8, .p 5 2 7 5 16, .p 5 2 7 6 16, .n 5 2 7 7 48, .p 5 2 7 9 48, .n 5 2 7 10 16,
   .n 5 2 7 11 16, .p 5 2 7 12 8, .n 5 2 8 3 16, .p 5 2 8 4 32, .n 5 2 8 5 48, .p 5 2 8 6 192,
   .n 5 2 8 7 288, .p 5 2 8 9 288, .n 5 2 8 10 192, .p 5 2 8 11 48, .n 5 2 8 12 32, .p 5 2 8 13 16,
   .p 5 2 9 3 48, .n 5 2 9 4 88, .n 5 2 9 5 64, .p 5 2 9 6 176, .n 5 2 9 7 48, .p 5 2 9 9 48,
   .n 5 2 9 10 176, .p 5 2 9 11 64, .p 5 2 9 12 88, .n 5 2 9 13 48, .n 5 2 10 3 64, .p 5 2 10 4 128,
   .p 5 2 10 5 208, .n 5 2 10 6 832, .p 5 2 10 7 848, .n 5 2 10 9 848, .p 5 2 10 10 832, .n 5 2 10 11 208,
   .n 5 2 10 12 128, .p 5 2 10 13 64, .p 5 2 11 3 48, .n 5 2 11 4 88, .n 5 2 11 5 64, .p 5 2 11 6 176,
   .n 5 2 11 7 48, .p 5 2 11 9 48, .n 5 2 11 10 176, .p 5 2 11 11 64, .p 5 2 11 12 88, .n 5 2 11 13 48,
   .n 5 2 12 3 16, .p 5 2 12 4 32, .n 5 2 12 5 48, .p 5 2 12 6 192, .n 5 2 12 7 288, .p 5 2 12 9 288,
   .n 5 2 12 10 192, .p 5 2 12 11 48, .n 5 2 12 12 32, .p 5 2 12 13 16, .n 5 2 13 4 8, .p 5 2 13 5 16,
   .p 5 2 13 6 16, .n 5 2 13 7 48, .p 5 2 13 9 48, .n 5 2 13 10 16, .n 5 2 13 11 16, .p 5 2 13 12 8,
   .n 5 2 14 5 8, .p 5 2 14 6 32, .n 5 2 14 7 40, .p 5 2 14 9 40, .n 5 2 14 10 32, .p 5 2 14 11 8,
   .p 6 1 8 3 8, .n 6 1 8 4 16, .n 6 1 8 5 24, .p 6 1 8 6 64, .p 6 1 8 7 16, .n 6 1 8 8 96,
   .p 6 1 8 9 16, .p 6 1 8 10 64, .n 6 1 8 11 24, .n 6 1 8 12 16, .p 6 1 8 13 8, .p 6 1 9 3 16,
   .n 6 1 9 4 32, .n 6 1 9 5 48, .p 6 1 9 6 128, .p 6 1 9 7 32, .n 6 1 9 8 192, .p 6 1 9 9 32,
   .p 6 1 9 10 128, .n 6 1 9 11 48, .n 6 1 9 12 32, .p 6 1 9 13 16, .n 6 1 11 3 16, .p 6 1 11 4 32,
   .p 6 1 11 5 48, .n 6 1 11 6 128, .n 6 1 11 7 32, .p 6 1 11 8 192, .n 6 1 11 9 32, .n 6 1 11 10 128,
   .p 6 1 11 11 48, .p 6 1 11 12 32, .n 6 1 11 13 16, .n 6 1 12 3 8, .p 6 1 12 4 16, .p 6 1 12 5 24,
   .n 6 1 12 6 64, .n 6 1 12 7 16, .p 6 1 12 8 96, .n 6 1 12 9 16, .n 6 1 12 10 64, .p 6 1 12 11 24,
   .p 6 1 12 12 16, .n 6 1 12 13 8, .n 7 0 10 2 16, .p 7 0 10 3 64, .n 7 0 10 4 64, .n 7 0 10 5 64,
   .p 7 0 10 6 176, .n 7 0 10 7 128, .p 7 0 10 9 128, .n 7 0 10 10 176, .p 7 0 10 11 64, .p 7 0 10 12 64,
   .n 7 0 10 13 64, .p 7 0 10 14 16]

private def g2Mid5_2_a : List FM :=
  [.p 0 7 5 7 32, .n 0 7 6 7 128, .p 0 7 7 7 128, .n 0 7 7 9 32, .p 0 7 8 7 128, .p 0 7 8 9 128,
   .n 0 7 9 7 320, .n 0 7 9 9 128, .p 0 7 10 7 128, .n 0 7 10 9 128, .p 0 7 11 7 128, .p 0 7 11 9 320,
   .n 0 7 12 7 128, .n 0 7 12 9 128, .p 0 7 13 7 32, .n 0 7 13 9 128, .p 0 7 14 9 128, .n 0 7 15 9 32,
   .n 1 6 5 6 32, .p 1 6 5 8 16, .p 1 6 5 9 16, .p 1 6 6 6 48, .n 1 6 6 7 16, .p 1 6 6 8 32,
   .n 1 6 6 9 32, .n 1 6 6 10 48, .p 1 6 6 11 16, .p 1 6 7 6 80, .p 1 6 7 7 80, .n 1 6 7 8 160,
   .n 1 6 7 9 64, .p 1 6 7 10 128, .n 1 6 7 11 64, .n 1 6 8 4 16, .p 1 6 8 5 16, .n 1 6 8 6 80,
   .n 1 6 8 7 112, .n 1 6 8 8 16, .p 1 6 8 9 144, .n 1 6 8 10 16, .p 1 6 8 11 80, .p 1 6 9 4 64,
   .n 1 6 9 5 64, .n 1 6 9 6 224, .n 1 6 9 7 32, .p 1 6 9 8 320, .p 1 6 9 9 128, .n 1 6 9 10 192,
   .n 1 6 10 4 80, .p 1 6 10 5 80, .p 1 6 10 6 208, .p 1 6 10 7 176, .n 1 6 10 8 16, .n 1 6 10 9 368,
   .p 1 6 10 10 80, .n 1 6 10 11 80, .p 1 6 11 6 192, .n 1 6 11 7 64, .n 1 6 11 8 352, .p 1 6 11 9 32,
   .p 1 6 11 10 128, .p 1 6 11 11 64, .p 1 6 12 4 80, .n 1 6 12 5 80, .n 1 6 12 6 240, .n 1 6 12 7 80,
   .p 1 6 12 8 80, .p 1 6 12 9 304, .n 1 6 12 10 48, .n 1 6 12 11 16, .n 1 6 13 4 64, .p 1 6 13 5 64,
   .p 1 6 13 7 32, .p 1 6 13 8 176, .n 1 6 13 9 144, .n 1 6 13 10 64, .p 1 6 14 4 16, .n 1 6 14 5 16,
   .p 1 6 14 6 64, .p 1 6 14 7 32, .n 1 6 14 8 80, .n 1 6 14 9 48, .p 1 6 14 10 32, .n 1 6 15 6 16,
   .n 1 6 15 7 16, .p 1 6 15 9 32, .p 2 5 5 6 24, .n 2 5 5 7 40, .n 2 5 5 8 8, .p 2 5 5 9 24,
   .p 2 5 6 4 16, .p 2 5 6 5 32, .n 2 5 6 6 88, .p 2 5 6 7 104, .n 2 5 6 8 64, .p 2 5 6 9 16,
   .n 2 5 6 10 56, .p 2 5 6 11 40, .n 2 5 7 2 8, .p 2 5 7 3 16, .n 2 5 7 4 32, .n 2 5 7 5 64,
   .p 2 5 7 6 40, .n 2 5 7 7 168, .p 2 5 7 8 232, .p 2 5 7 9 72, .p 2 5 7 10 72, .n 2 5 7 11 160,
   .p 2 5 8 2 32, .n 2 5 8 3 32, .n 2 5 8 4 24, .p 2 5 8 5 8, .p 2 5 8 6 152, .p 2 5 8 7 56,
   .p 2 5 8 8 88, .n 2 5 8 9 584, .p 2 5 8 10 136, .p 2 5 8 11 168, .n 2 5 9 2 48, .n 2 5 9 3 16,
   .p 2 5 9 4 88, .n 2 5 9 5 16, .n 2 5 9 6 112, .p 2 5 9 7 528, .n 2 5 9 8 720, .p 2 5 9 9 416,
   .n 2 5 9 10 208, .p 2 5 9 11 80, .p 2 5 9 12 8, .p 2 5 10 2 32, .p 2 5 10 3 64, .n 2 5 10 4 40,
   .p 2 5 10 5 120, .n 2 5 10 6 168, .n 2 5 10 7 712, .p 2 5 10 8 232, .p 2 5 10 9 744, .n 2 5 10 10 24,
   .n 2 5 10 11 216, .n 2 5 10 12 32, .n 2 5 11 2 8, .n 2 5 11 3 16, .n 2 5 11 4 16, .n 2 5 11 5 32,
   .p 2 5 11 6 240, .n 2 5 11 7 128, .p 2 5 11 8 656, .n 2 5 11 9 880, .p 2 5 11 10 72, .p 2 5 11 11 64,
   .p 2 5 11 12 48, .n 2 5 12 3 32, .n 2 5 12 4 8, .n 2 5 12 5 136, .n 2 5 12 6 88, .p 2 5 12 7 584,
   .n 2 5 12 8 280, .n 2 5 12 9 56, .p 2 5 12 10 24, .p 2 5 12 11 24, .n 2 5 12 12 32, .p 2 5 13 3 16,
   .p 2 5 13 4 24, .p 2 5 13 5 112, .n 2 5 13 6 40, .n 2 5 13 7 200, .n 2 5 13 8 296, .p 2 5 13 9 360,
   .p 2 5 13 11 16, .p 2 5 13 12 8, .n 2 5 14 4 8, .n 2 5 14 5 24, .p 2 5 14 6 64, .n 2 5 14 7 32,
   .p 2 5 14 8 152, .n 2 5 14 9 120, .n 2 5 14 10 16, .n 2 5 14 11 16, .n 2 5 15 6 24, .p 2 5 15 7 8,
   .p 2 5 15 8 8, .p 2 5 15 9 8, .p 3 4 5 6 8, .n 3 4 5 7 8, .n 3 4 5 8 8, .p 3 4 5 9 8,
   .n 3 4 6 4 32, .p 3 4 6 5 32, .p 3 4 6 6 16, .p 3 4 6 7 48, .n 3 4 6 8 80, .p 3 4 6 9 16,
   .n 3 4 6 10 32, .p 3 4 6 11 32, .p 3 4 7 2 16, .n 3 4 7 3 48, .p 3 4 7 4 72, .p 3 4 7 5 72,
   .n 3 4 7 6 144, .n 3 4 7 7 192, .p 3 4 7 8 192, .p 3 4 7 9 176, .n 3 4 7 10 136, .n 3 4 7 11 8,
   .n 3 4 8 2 64, .p 3 4 8 3 64, .p 3 4 8 4 56, .n 3 4 8 5 152, .p 3 4 8 6 120, .p 3 4 8 7 24,
   .p 3 4 8 8 56, .n 3 4 8 9 328, .p 3 4 8 10 360, .n 3 4 8 11 120, .n 3 4 8 12 16, .p 3 4 9 2 96,
   .p 3 4 9 3 56, .n 3 4 9 4 272, .n 3 4 9 5 184, .p 3 4 9 6 232, .p 3 4 9 7 440, .n 3 4 9 8 232,
   .n 3 4 9 9 344, .p 3 4 9 10 168, .p 3 4 9 11 32, .p 3 4 9 12 8, .n 3 4 10 2 64, .n 3 4 10 3 80,
   .p 3 4 10 4 264, .p 3 4 10 5 184, .n 3 4 10 6 216, .n 3 4 10 7 184, .n 3 4 10 8 216, .p 3 4 10 9 712,
   .n 3 4 10 10 616, .p 3 4 10 11 136, .p 3 4 10 12 80, .p 3 4 11 2 16, .n 3 4 11 3 16, .n 3 4 11 4 72,
   .p 3 4 11 5 248, .n 3 4 11 6 296, .n 3 4 11 7 264, .p 3 4 11 8 440, .p 3 4 11 9 24, .p 3 4 11 10 40,
   .p 3 4 11 11 8, .n 3 4 11 12 128, .p 3 4 12 3 16, .n 3 4 12 4 104, .n 3 4 12 5 136, .p 3 4 12 6 360,
   .p 3 4 12 7 104, .n 3 4 12 8 56, .n 3 4 12 9 408, .p 3 4 12 10 248, .n 3 4 12 11 88, .p 3 4 12 12 64,
   .p 3 4 13 3 8, .p 3 4 13 4 144, .n 3 4 13 5 136, .n 3 4 13 6 48, .p 3 4 13 7 16, .n 3 4 13 8 144,
   .p 3 4 13 9 144, .p 3 4 13 10 56, .n 3 4 13 11 32, .n 3 4 13 12 8, .n 3 4 14 4 56, .p 3 4 14 5 72,
   .n 3 4 14 6 24, .p 3 4 14 7 8, .p 3 4 14 8 40, .p 3 4 14 9 8, .n 3 4 14 10 88, .p 3 4 14 11 40,
   .n 3 4 15 6 8, .p 3 4 15 7 8, .p 3 4 15 8 8, .n 3 4 15 9 8, .p 4 3 6 4 32, .n 4 3 6 5 96,
   .p 4 3 6 6 88, .n 4 3 6 7 24, .p 4 3 6 8 16, .n 4 3 6 9 16, .n 4 3 6 10 8, .p 4 3 6 11 8,
   .p 4 3 7 3 8, .n 4 3 7 4 64, .p 4 3 7 6 112, .p 4 3 7 7 64, .n 4 3 7 8 160, .p 4 3 7 9 96,
   .n 4 3 7 10 144, .p 4 3 7 11 88, .n 4 3 8 4 48, .p 4 3 8 5 272, .n 4 3 8 6 168, .n 4 3 8 7 232,
   .n 4 3 8 8 152, .p 4 3 8 9 424, .p 4 3 8 10 104, .n 4 3 8 11 216, .p 4 3 8 12 8, .p 4 3 8 13 8,
   .p 4 3 9 1 8, .p 4 3 9 2 16, .p 4 3 9 3 16, .n 4 3 9 4 24, .p 4 3 9 5 24, .n 4 3 9 6 144,
   .n 4 3 9 7 240, .p 4 3 9 8 784, .n 4 3 9 9 616, .p 4 3 9 10 160, .p 4 3 9 11 64, .n 4 3 9 12 24,
   .n 4 3 9 13 24, .n 4 3 10 1 16, .n 4 3 10 2 32, .n 4 3 10 3 48, .p 4 3 10 4 184, .n 4 3 10 5 232,
   .n 4 3 10 6 120, .p 4 3 10 7 840, .n 4 3 10 8 104, .n 4 3 10 9 760, .p 4 3 10 10 56, .p 4 3 10 11 200,
   .p 4 3 10 12 16, .p 4 3 10 13 16, .p 4 3 11 1 8, .p 4 3 11 2 16, .n 4 3 11 3 8, .n 4 3 11 5 8,
   .p 4 3 11 6 48, .p 4 3 11 7 64, .n 4 3 11 8 800, .p 4 3 11 9 920, .n 4 3 11 10 32, .n 4 3 11 11 216,
   .p 4 3 11 13 8, .p 4 3 12 3 48, .n 4 3 12 4 96, .p 4 3 12 5 16, .p 4 3 12 6 328, .n 4 3 12 7 664,
   .p 4 3 12 8 280, .p 4 3 12 9 312, .n 4 3 12 10 264, .p 4 3 12 11 40, .p 4 3 12 12 8, .n 4 3 12 13 8,
   .n 4 3 13 3 16, .p 4 3 13 4 56, .n 4 3 13 5 64, .n 4 3 13 6 80, .p 4 3 13 7 112, .p 4 3 13 8 240,
   .n 4 3 13 9 352, .p 4 3 13 10 48, .p 4 3 13 11 64, .n 4 3 13 12 8, .n 4 3 14 4 40, .p 4 3 14 5 88,
   .n 4 3 14 6 64, .p 4 3 14 7 80, .n 4 3 14 8 104, .n 4 3 14 9 8, .p 4 3 14 10 80, .n 4 3 14 11 32,
   .n 5 2 6 4 16, .p 5 2 6 5 48, .n 5 2 6 6 32, .n 5 2 6 7 32, .p 5 2 6 8 48, .n 5 2 6 9 16,
   .n 5 2 7 2 16, .p 5 2 7 3 48, .n 5 2 7 4 24, .n 5 2 7 5 24, .n 5 2 7 6 8, .n 5 2 7 7 8,
   .p 5 2 7 8 88, .n 5 2 7 9 40, .n 5 2 7 10 40, .p 5 2 7 11 24, .p 5 2 8 2 48, .n 5 2 8 3 64,
   .n 5 2 8 4 8, .n 5 2 8 5 8, .p 5 2 8 6 24, .n 5 2 8 7 72, .p 5 2 8 8 120, .p 5 2 8 9 120,
   .n 5 2 8 10 200, .p 5 2 8 11 8, .p 5 2 8 12 16, .p 5 2 8 13 16, .n 5 2 9 2 56, .n 5 2 9 3 32,
   .p 5 2 9 4 104, .p 5 2 9 5 192, .p 5 2 9 6 40, .n 5 2 9 7 360, .n 5 2 9 8 136, .p 5 2 9 9 168,
   .p 5 2 9 10 80, .p 5 2 9 11 72, .n 5 2 9 12 32, .n 5 2 9 13 40, .n 5 2 10 1 16, .p 5 2 10 2 64,
   .p 5 2 10 3 16, .n 5 2 10 4 120, .n 5 2 10 5 24, .n 5 2 10 6 120, .p 5 2 10 7 456, .n 5 2 10 8 152,
   .n 5 2 10 9 328, .p 5 2 10 10 376, .n 5 2 10 11 152, .n 5 2 10 12 48, .p 5 2 10 13 48, .p 5 2 11 1 16,
   .n 5 2 11 2 24, .p 5 2 11 3 56, .p 5 2 11 4 48, .n 5 2 11 5 400, .p 5 2 11 6 184, .p 5 2 11 7 408,
   .n 5 2 11 8 232, .n 5 2 11 9 24, .n 5 2 11 10 96, .n 5 2 11 11 16, .p 5 2 11 12 120, .n 5 2 11 13 40,
   .n 5 2 12 2 16, .n 5 2 12 3 16, .p 5 2 12 4 56, .p 5 2 12 5 72, .n 5 2 12 6 56, .n 5 2 12 7 184,
   .p 5 2 12 8 136, .p 5 2 12 9 40, .n 5 2 12 10 56, .p 5 2 12 11 72, .n 5 2 12 12 64, .p 5 2 12 13 16,
   .n 5 2 13 3 8, .n 5 2 13 4 32, .p 5 2 13 5 120, .n 5 2 13 6 24, .n 5 2 13 7 168, .p 5 2 13 8 88,
   .p 5 2 13 9 72, .n 5 2 13 10 40, .n 5 2 13 11 16, .p 5 2 13 12 8, .n 5 2 14 4 8, .p 5 2 14 5 24,
   .n 5 2 14 6 8, .n 5 2 14 7 40, .p 5 2 14 8 40, .p 5 2 14 9 8, .n 5 2 14 10 24, .p 5 2 14 11 8,
   .p 6 1 7 2 8, .n 6 1 7 3 24, .p 6 1 7 4 16, .p 6 1 7 5 16, .n 6 1 7 6 32, .p 6 1 7 7 32,
   .n 6 1 7 8 16, .n 6 1 7 9 16, .p 6 1 7 10 24, .n 6 1 7 11 8, .n 6 1 8 2 16, .p 6 1 8 3 32,
   .p 6 1 8 4 8, .n 6 1 8 5 40, .p 6 1 8 6 16, .n 6 1 8 7 16, .p 6 1 8 9 32, .n 6 1 8 11 16,
   .n 6 1 8 12 8, .p 6 1 8 13 8, .n 6 1 9 1 8, .p 6 1 9 2 24, .n 6 1 9 3 8, .n 6 1 9 4 56,
   .p 6 1 9 5 32, .p 6 1 9 6 144, .n 6 1 9 7 112, .n 6 1 9 8 208, .p 6 1 9 9 216, .p 6 1 9 10 88,
   .n 6 1 9 11 136, .p 6 1 9 12 8, .p 6 1 9 13 16, .p 6 1 10 1 16, .n 6 1 10 3 16, .n 6 1 10 4 144,
   .p 6 1 10 5 112, .p 6 1 10 6 288, .n 6 1 10 7 256, .n 6 1 10 8 128, .p 6 1 10 9 144, .n 6 1 10 10 32,
   .p 6 1 10 11 16, .p 6 1 10 12 16, .n 6 1 10 13 16, .n 6 1 11 1 8, .p 6 1 11 3 32, .p 6 1 11 4 8,
   .n 6 1 11 6 176, .p 6 1 11 7 80, .p 6 1 11 8 288, .n 6 1 11 9 248, .n 6 1 11 10 80, .p 6 1 11 11 144,
   .n 6 1 11 12 40, .n 6 1 12 2 16, .n 6 1 12 3 16, .p 6 1 12 4 168, .n 6 1 12 5 120, .n 6 1 12 6 240,
   .p 6 1 12 7 272, .p 6 1 12 8 64, .n 6 1 12 9 128, .p 6 1 12 12 24, .n 6 1 12 13 8, .p 7 0 10 3 16,
   .n 7 0 10 4 48, .p 7 0 10 5 16, .p 7 0 10 6 80, .n 7 0 10 7 96, .p 7 0 10 8 32, .p 7 0 10 9 32,
   .n 7 0 10 10 96, .p 7 0 10 11 80, .p 7 0 10 12 16, .n 7 0 10 13 48, .p 7 0 10 14 16, .n 7 0 11 1 16,
   .p 7 0 11 2 48, .n 7 0 11 3 16, .n 7 0 11 4 80, .p 7 0 11 5 96, .n 7 0 11 6 32, .n 7 0 11 7 32,
   .p 7 0 11 8 96, .n 7 0 11 9 80, .n 7 0 11 10 16, .p 7 0 11 11 48, .n 7 0 11 12 16]

private def g2Mid5_2_b : List FM :=
  [.n 0 7 5 6 32, .p 0 7 5 7 64, .p 0 7 6 6 64, .n 0 7 6 7 160, .n 0 7 6 8 32, .p 0 7 7 6 96,
   .n 0 7 7 7 32, .p 0 7 7 8 32, .n 0 7 8 6 320, .p 0 7 8 7 352, .p 0 7 8 8 224, .p 0 7 8 9 32,
   .n 0 7 8 10 32, .p 0 7 9 6 160, .n 0 7 9 7 160, .n 0 7 9 8 480, .n 0 7 9 9 96, .p 0 7 9 10 128,
   .p 0 7 10 6 192, .n 0 7 10 7 224, .p 0 7 10 8 160, .p 0 7 10 9 32, .n 0 7 10 10 160, .n 0 7 11 6 224,
   .p 0 7 11 7 160, .p 0 7 11 8 352, .p 0 7 11 9 160, .p 0 7 12 6 64, .p 0 7 12 7 32, .n 0 7 12 8 352,
   .n 0 7 12 9 160, .p 0 7 12 10 160, .n 0 7 13 7 32, .p 0 7 13 8 96, .n 0 7 13 9 32, .n 0 7 13 10 128,
   .p 0 7 14 9 96, .p 0 7 14 10 32, .n 0 7 15 9 32, .n 1 6 5 7 32, .p 1 6 5 9 32, .p 1 6 6 5 32,
   .n 1 6 6 6 64, .p 1 6 6 7 32, .p 1 6 6 8 96, .n 1 6 6 9 80, .n 1 6 6 10 16, .p 1 6 7 6 64,
   .p 1 6 7 7 112, .n 1 6 7 8 160, .n 1 6 7 9 48, .p 1 6 7 10 64, .n 1 6 7 11 48, .p 1 6 7 12 16,
   .n 1 6 8 4 32, .n 1 6 8 5 128, .p 1 6 8 6 144, .n 1 6 8 7 64, .n 1 6 8 8 112, .p 1 6 8 9 144,
   .p 1 6 8 11 112, .n 1 6 8 12 64, .p 1 6 9 4 96, .n 1 6 9 5 16, .n 1 6 9 6 96, .n 1 6 9 7 240,
   .p 1 6 9 8 176, .p 1 6 9 9 192, .n 1 6 9 10 208, .p 1 6 9 12 96, .n 1 6 10 4 48, .p 1 6 10 5 240,
   .n 1 6 10 6 192, .p 1 6 10 7 80, .p 1 6 10 8 224, .n 1 6 10 9 256, .p 1 6 10 10 176, .n 1 6 10 11 160,
   .n 1 6 10 12 64, .n 1 6 11 4 128, .n 1 6 11 5 32, .p 1 6 11 6 176, .p 1 6 11 7 320, .n 1 6 11 8 192,
   .n 1 6 11 9 272, .p 1 6 11 10 32, .p 1 6 11 11 80, .p 1 6 11 12 16, .p 1 6 12 4 192, .n 1 6 12 5 160,
   .n 1 6 12 6 112, .n 1 6 12 7 160, .n 1 6 12 8 176, .p 1 6 12 9 336, .p 1 6 12 10 32, .p 1 6 12 11 48,
   .n 1 6 13 4 96, .p 1 6 13 5 48, .p 1 6 13 6 128, .n 1 6 13 7 144, .p 1 6 13 8 176, .p 1 6 13 9 64,
   .n 1 6 13 10 144, .n 1 6 13 11 32, .p 1 6 14 4 16, .p 1 6 14 5 16, .n 1 6 14 6 32, .p 1 6 14 7 112,
   .n 1 6 14 8 32, .n 1 6 14 9 144, .p 1 6 14 10 64, .n 1 6 15 6 16, .n 1 6 15 7 16, .p 1 6 15 9 32,
   .p 2 5 5 6 32, .n 2 5 5 7 48, .p 2 5 5 9 16, .p 2 5 6 5 48, .n 2 5 6 6 96, .p 2 5 6 7 104,
   .n 2 5 6 8 24, .n 2 5 6 9 88, .p 2 5 6 10 40, .p 2 5 6 11 16, .n 2 5 7 2 8, .p 2 5 7 3 16,
   .n 2 5 7 4 16, .n 2 5 7 5 64, .n 2 5 7 6 152, .p 2 5 7 7 112, .p 2 5 7 8 176, .p 2 5 7 9 88,
   .n 2 5 7 10 40, .n 2 5 7 11 136, .p 2 5 7 12 24, .p 2 5 8 2 32, .n 2 5 8 3 32, .n 2 5 8 4 16,
   .n 2 5 8 5 80, .p 2 5 8 6 856, .n 2 5 8 7 584, .n 2 5 8 8 528, .p 2 5 8 9 64, .p 2 5 8 10 216,
   .p 2 5 8 11 184, .n 2 5 8 12 112, .n 2 5 9 2 48, .n 2 5 9 3 16, .p 2 5 9 4 104, .n 2 5 9 5 8,
   .n 2 5 9 6 520, .p 2 5 9 7 192, .p 2 5 9 8 960, .n 2 5 9 9 136, .n 2 5 9 10 824, .p 2 5 9 11 96,
   .p 2 5 9 12 200, .p 2 5 10 2 32, .p 2 5 10 3 64, .p 2 5 10 4 8, .p 2 5 10 5 248, .n 2 5 10 6 1008,
   .p 2 5 10 7 784, .n 2 5 10 8 632, .p 2 5 10 9 8, .p 2 5 10 10 912, .n 2 5 10 11 240, .n 2 5 10 12 176,
   .n 2 5 11 2 8, .n 2 5 11 3 16, .n 2 5 11 4 240, .p 2 5 11 5 16, .p 2 5 11 6 1152, .n 2 5 11 7 328,
   .n 2 5 11 8 744, .p 2 5 11 9 144, .n 2 5 11 10 88, .p 2 5 11 11 24, .p 2 5 11 12 88, .n 2 5 12 3 32,
   .p 2 5 12 4 208, .n 2 5 12 5 256, .n 2 5 12 6 296, .n 2 5 12 7 424, .p 2 5 12 8 1312, .n 2 5 12 9 48,
   .n 2 5 12 10 488, .p 2 5 12 11 56, .n 2 5 12 12 32, .p 2 5 13 3 16, .n 2 5 13 4 40, .p 2 5 13 5 56,
   .p 2 5 13 6 152, .p 2 5 13 7 64, .n 2 5 13 8 528, .n 2 5 13 9 120, .p 2 5 13 10 376, .p 2 5 13 11 16,
   .p 2 5 13 12 8, .n 2 5 14 4 8, .p 2 5 14 5 40, .n 2 5 14 6 96, .p 2 5 14 7 120, .p 2 5 14 9 64,
   .n 2 5 14 10 104, .n 2 5 14 11 16, .n 2 5 15 6 24, .p 2 5 15 7 8, .p 2 5 15 8 8, .p 2 5 15 9 8,
   .p 3 4 6 4 8, .n 3 4 6 5 96, .p 3 4 6 6 160, .n 3 4 6 8 112, .p 3 4 6 9 56, .n 3 4 6 10 56,
   .p 3 4 6 11 40, .p 3 4 7 2 16, .n 3 4 7 3 48, .p 3 4 7 4 24, .p 3 4 7 5 80, .p 3 4 7 6 8,
   .n 3 4 7 7 328, .p 3 4 7 8 200, .p 3 4 7 9 184, .n 3 4 7 10 112, .n 3 4 7 11 16, .n 3 4 7 12 8,
   .n 3 4 8 2 56, .p 3 4 8 3 56, .p 3 4 8 4 8, .p 3 4 8 5 368, .n 3 4 8 6 656, .p 3 4 8 7 192,
   .p 3 4 8 8 384, .n 3 4 8 9 608, .p 3 4 8 10 408, .n 3 4 8 11 136, .p 3 4 8 12 40, .p 3 4 9 2 80,
   .p 3 4 9 3 64, .n 3 4 9 4 256, .n 3 4 9 5 272, .p 3 4 9 7 992, .n 3 4 9 8 512, .n 3 4 9 9 368,
   .p 3 4 9 10 384, .n 3 4 9 11 16, .n 3 4 9 12 80, .n 3 4 9 13 16, .n 3 4 10 2 56, .n 3 4 10 3 88,
   .p 3 4 10 4 304, .n 3 4 10 5 352, .p 3 4 10 6 736, .n 3 4 10 7 464, .n 3 4 10 8 512, .p 3 4 10 9 1024,
   .n 3 4 10 10 968, .p 3 4 10 11 232, .p 3 4 10 12 112, .p 3 4 10 13 32, .p 3 4 11 2 16, .p 3 4 11 3 8,
   .p 3 4 11 4 32, .p 3 4 11 5 240, .n 3 4 11 6 112, .n 3 4 11 7 960, .p 3 4 11 8 624, .p 3 4 11 9 288,
   .n 3 4 11 10 64, .p 3 4 11 11 56, .n 3 4 11 12 112, .n 3 4 11 13 16, .n 3 4 12 4 248, .p 3 4 12 5 64,
   .p 3 4 12 6 144, .p 3 4 12 7 352, .p 3 4 12 8 16, .n 3 4 12 9 592, .p 3 4 12 10 416, .n 3 4 12 11 208,
   .p 3 4 12 12 56, .p 3 4 13 3 8, .p 3 4 13 4 184, .n 3 4 13 5 80, .n 3 4 13 6 304, .p 3 4 13 7 224,
   .n 3 4 13 8 96, .n 3 4 13 9 32, .p 3 4 13 10 96, .p 3 4 13 11 8, .n 3 4 13 12 8, .n 3 4 14 4 56,
   .p 3 4 14 5 48, .p 3 4 14 6 32, .n 3 4 14 7 16, .p 3 4 14 9 56, .n 3 4 14 10 104, .p 3 4 14 11 40,
   .n 3 4 15 6 8, .p 3 4 15 7 8, .p 3 4 15 8 8, .n 3 4 15 9 8, .p 4 3 6 5 8, .n 4 3 6 6 24,
   .p 4 3 6 7 16, .n 4 3 6 8 16, .p 4 3 6 9 72, .n 4 3 6 10 88, .p 4 3 6 11 32, .p 4 3 7 3 8,
   .n 4 3 7 4 16, .n 4 3 7 5 16, .p 4 3 7 6 16, .p 4 3 7 7 72, .n 4 3 7 8 72, .n 4 3 7 10 32,
   .p 4 3 7 11 64, .n 4 3 7 12 24, .n 4 3 8 2 16, .p 4 3 8 3 16, .n 4 3 8 4 8, .p 4 3 8 5 120,
   .n 4 3 8 6 264, .p 4 3 8 7 88, .p 4 3 8 8 208, .n 4 3 8 9 144, .p 4 3 8 10 104, .n 4 3 8 11 216,
   .p 4 3 8 12 104, .p 4 3 8 13 8, .p 4 3 9 1 8, .p 4 3 9 2 56, .n 4 3 9 3 8, .n 4 3 9 4 192,
   .p 4 3 9 5 72, .p 4 3 9 6 472, .n 4 3 9 7 416, .n 4 3 9 8 400, .p 4 3 9 9 16, .p 4 3 9 10 640,
   .n 4 3 9 11 40, .n 4 3 9 12 192, .n 4 3 9 13 16, .n 4 3 10 1 16, .n 4 3 10 2 48, .n 4 3 10 3 48,
   .p 4 3 10 4 152, .n 4 3 10 5 168, .p 4 3 10 6 336, .n 4 3 10 7 384, .p 4 3 10 8 632, .n 4 3 10 9 8,
   .n 4 3 10 10 912, .p 4 3 10 11 256, .p 4 3 10 12 224, .n 4 3 10 13 16, .p 4 3 11 1 8, .p 4 3 11 2 8,
   .n 4 3 11 3 16, .p 4 3 11 4 296, .n 4 3 11 5 80, .n 4 3 11 6 880, .p 4 3 11 7 504, .p 4 3 11 8 168,
   .p 4 3 11 9 56, .p 4 3 11 10 120, .n 4 3 11 11 120, .n 4 3 11 12 96, .p 4 3 11 13 32, .p 4 3 12 3 64,
   .n 4 3 12 4 296, .p 4 3 12 5 24, .p 4 3 12 6 504, .p 4 3 12 7 312, .n 4 3 12 8 1024, .p 4 3 12 9 256,
   .p 4 3 12 10 184, .n 4 3 12 11 8, .n 4 3 12 12 8, .n 4 3 12 13 8, .n 4 3 13 3 16, .p 4 3 13 4 104,
   .p 4 3 13 5 8, .n 4 3 13 6 248, .n 4 3 13 7 96, .p 4 3 13 8 432, .n 4 3 13 9 88, .n 4 3 13 10 152,
   .p 4 3 13 11 64, .n 4 3 13 12 8, .n 4 3 14 4 40, .p 4 3 14 5 32, .p 4 3 14 6 88, .n 4 3 14 7 96,
   .p 4 3 14 8 72, .n 4 3 14 9 160, .p 4 3 14 10 136, .n 4 3 14 11 32, .n 5 2 6 4 8, .p 5 2 6 5 24,
   .n 5 2 6 6 8, .n 5 2 6 7 40, .p 5 2 6 8 40, .p 5 2 6 9 8, .n 5 2 6 10 24, .p 5 2 6 11 8,
   .n 5 2 7 2 16, .p 5 2 7 3 48, .n 5 2 7 4 40, .n 5 2 7 5 16, .p 5 2 7 6 48, .n 5 2 7 7 32,
   .p 5 2 7 8 16, .n 5 2 7 9 16, .p 5 2 7 11 16, .n 5 2 7 12 8, .p 5 2 8 2 56, .n 5 2 8 3 72,
   .p 5 2 8 4 8, .n 5 2 8 5 144, .p 5 2 8 6 288, .n 5 2 8 7 192, .n 5 2 8 8 80, .p 5 2 8 9 416,
   .n 5 2 8 10 312, .n 5 2 8 11 24, .p 5 2 8 12 40, .p 5 2 8 13 16, .n 5 2 9 2 64, .n 5 2 9 3 32,
   .p 5 2 9 4 144, .p 5 2 9 5 208, .n 5 2 9 6 32, .n 5 2 9 7 480, .p 5 2 9 8 48, .p 5 2 9 9 240,
   .n 5 2 9 10 64, .p 5 2 9 11 96, .n 5 2 9 12 32, .n 5 2 9 13 32, .n 5 2 10 1 24, .p 5 2 10 2 96,
   .p 5 2 10 3 32, .n 5 2 10 4 328, .p 5 2 10 5 336, .n 5 2 10 6 464, .p 5 2 10 7 576, .p 5 2 10 8 176,
   .n 5 2 10 9 808, .p 5 2 10 10 528, .n 5 2 10 11 128, .n 5 2 10 12 8, .p 5 2 10 13 16, .p 5 2 11 1 16,
   .n 5 2 11 2 24, .p 5 2 11 4 136, .n 5 2 11 5 296, .n 5 2 11 6 112, .p 5 2 11 7 656, .n 5 2 11 8 256,
   .n 5 2 11 9 320, .p 5 2 11 10 232, .n 5 2 11 11 48, .p 5 2 11 12 24, .n 5 2 11 13 8, .n 5 2 12 2 16,
   .p 5 2 12 4 88, .n 5 2 12 5 96, .p 5 2 12 6 96, .n 5 2 12 7 224, .p 5 2 12 8 128, .p 5 2 12 9 176,
   .n 5 2 12 10 240, .p 5 2 12 11 128, .n 5 2 12 12 56, .p 5 2 12 13 16, .n 5 2 13 3 8, .n 5 2 13 4 24,
   .p 5 2 13 5 64, .p 5 2 13 6 80, .n 5 2 13 7 192, .n 5 2 13 8 16, .p 5 2 13 9 160, .n 5 2 13 10 48,
   .n 5 2 13 11 24, .p 5 2 13 12 8, .n 5 2 14 4 8, .p 5 2 14 5 8, .p 5 2 14 6 40, .n 5 2 14 7 72,
   .p 5 2 14 8 8, .p 5 2 14 9 56, .n 5 2 14 10 40, .p 5 2 14 11 8, .p 6 1 7 2 8, .n 6 1 7 3 24,
   .p 6 1 7 4 16, .p 6 1 7 5 16, .n 6 1 7 6 32, .p 6 1 7 7 32, .n 6 1 7 8 16, .n 6 1 7 9 16,
   .p 6 1 7 10 24, .n 6 1 7 11 8, .n 6 1 8 2 16, .p 6 1 8 3 32, .p 6 1 8 4 8, .n 6 1 8 5 40,
   .p 6 1 8 6 16, .n 6 1 8 7 16, .p 6 1 8 9 32, .n 6 1 8 11 16, .n 6 1 8 12 8, .p 6 1 8 13 8,
   .n 6 1 9 1 8, .p 6 1 9 2 8, .p 6 1 9 3 8, .p 6 1 9 4 8, .n 6 1 9 6 48, .p 6 1 9 7 16,
   .p 6 1 9 8 16, .n 6 1 9 9 8, .p 6 1 9 10 40, .n 6 1 9 11 24, .n 6 1 9 12 24, .p 6 1 9 13 16,
   .p 6 1 10 1 8, .p 6 1 10 2 24, .n 6 1 10 3 40, .n 6 1 10 4 104, .p 6 1 10 5 32, .p 6 1 10 6 240,
   .p 6 1 10 7 48, .n 6 1 10 8 336, .n 6 1 10 9 56, .p 6 1 10 10 248, .n 6 1 10 11 8, .n 6 1 10 12 72,
   .p 6 1 10 13 16, .n 6 1 11 1 8, .p 6 1 11 2 24, .p 6 1 11 3 24, .n 6 1 11 4 112, .p 6 1 11 5 40,
   .p 6 1 11 6 96, .n 6 1 11 7 96, .p 6 1 11 8 80, .n 6 1 11 9 8, .n 6 1 11 10 120, .p 6 1 11 11 72,
   .p 6 1 11 12 32, .n 6 1 11 13 24, .n 6 1 12 2 16, .n 6 1 12 3 32, .p 6 1 12 4 152, .p 6 1 12 5 40,
   .n 6 1 12 6 336, .p 6 1 12 7 16, .p 6 1 12 8 320, .n 6 1 12 9 32, .n 6 1 12 10 160, .p 6 1 12 11 16,
   .p 6 1 12 12 40, .n 6 1 12 13 8, .p 7 0 10 1 16, .n 7 0 10 2 48, .p 7 0 10 3 32, .p 7 0 10 4 32,
   .n 7 0 10 5 80, .p 7 0 10 6 112, .n 7 0 10 7 64, .n 7 0 10 8 64, .p 7 0 10 9 112, .n 7 0 10 10 80,
   .p 7 0 10 11 32, .p 7 0 10 12 32, .n 7 0 10 13 48, .p 7 0 10 14 16, .n 7 0 11 1 16, .p 7 0 11 2 32,
   .p 7 0 11 3 32, .n 7 0 11 4 96, .p 7 0 11 5 16, .p 7 0 11 6 64, .n 7 0 11 7 64, .p 7 0 11 8 64,
   .p 7 0 11 9 16, .n 7 0 11 10 96, .p 7 0 11 11 32, .p 7 0 11 12 32, .n 7 0 11 13 16]

set_option maxRecDepth 65536 in
private theorem g2_det5_2_step01 :
    fmMerge (fmMerge [] (fmMul (fmSubMat g2FM ⟨2, by decide⟩ ⟨0, by decide⟩ ⟨0, by decide⟩) g2Val4_13))
      (fmMul (fmNeg (fmSubMat g2FM ⟨2, by decide⟩ ⟨0, by decide⟩ ⟨1, by decide⟩)) g2Val4_9) =
      g2Mid5_2_a := rfl

set_option maxRecDepth 65536 in
private theorem g2_det5_2_step2 :
    fmMerge g2Mid5_2_a (fmMul (fmSubMat g2FM ⟨2, by decide⟩ ⟨0, by decide⟩ ⟨2, by decide⟩) g2Val4_5) =
      g2Mid5_2_b := rfl

set_option maxRecDepth 65536 in
private theorem g2_det5_2_step34 :
    fmMerge (fmMerge g2Mid5_2_b (fmMul (fmNeg (fmSubMat g2FM ⟨2, by decide⟩ ⟨0, by decide⟩ ⟨3, by decide⟩)) g2Val4_4))
      (fmMul (fmSubMat g2FM ⟨2, by decide⟩ ⟨0, by decide⟩ ⟨4, by decide⟩) g2Val4_3) =
      g2Val5_2 := rfl

private theorem g2_det5_2 : fmDet 5 (fmSubMat g2FM ⟨2, by decide⟩) = g2Val5_2 :=
  fmDet5_of_sub4_split _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (fin4Mat_eq_of_vals _ _ (by decide)) g2_det4_13
    (fin4Mat_eq_of_vals _ _ (by decide)) g2_det4_9
    (fin4Mat_eq_of_vals _ _ (by decide)) g2_det4_5
    (fin4Mat_eq_of_vals _ _ (by decide)) g2_det4_4
    (fin4Mat_eq_of_vals _ _ (by decide)) g2_det4_3
    g2_det5_2_step01 g2_det5_2_step2 g2_det5_2_step34

private def g2Val5_3 : List FM :=
  [.n 0 8 5 7 32, .p 0 8 5 8 32, .p 0 8 6 7 96, .n 0 8 6 8 128, .p 0 8 6 9 32, .p 0 8 7 7 32,
   .p 0 8 7 8 128, .n 0 8 7 9 160, .n 0 8 8 7 416, .p 0 8 8 8 128, .p 0 8 8 9 288, .p 0 8 9 7 480,
   .n 0 8 9 8 320, .n 0 8 9 9 160, .p 0 8 10 7 32, .p 0 8 10 8 128, .n 0 8 10 9 160, .n 0 8 11 7 416,
   .p 0 8 11 8 128, .p 0 8 11 9 288, .p 0 8 12 7 288, .n 0 8 12 8 128, .n 0 8 12 9 160, .n 0 8 13 7 64,
   .p 0 8 13 8 32, .p 0 8 13 9 32, .n 1 7 5 7 32, .p 1 7 5 8 16, .p 1 7 5 9 16, .p 1 7 6 6 16,
   .p 1 7 6 7 64, .n 1 7 6 8 128, .p 1 7 6 9 16, .p 1 7 6 10 16, .p 1 7 6 11 16, .p 1 7 7 5 16,
   .n 1 7 7 6 32, .p 1 7 7 7 160, .p 1 7 7 8 256, .n 1 7 7 9 256, .n 1 7 7 10 64, .n 1 7 7 11 80,
   .n 1 7 8 5 48, .n 1 7 8 6 48, .n 1 7 8 7 592, .p 1 7 8 9 448, .p 1 7 8 10 80, .p 1 7 8 11 160,
   .p 1 7 9 6 160, .p 1 7 9 7 560, .n 1 7 9 8 480, .n 1 7 9 9 80, .n 1 7 9 11 160, .p 1 7 10 5 160,
   .n 1 7 10 6 80, .p 1 7 10 7 32, .p 1 7 10 8 384, .n 1 7 10 9 496, .n 1 7 10 10 80, .p 1 7 10 11 80,
   .n 1 7 11 5 240, .n 1 7 11 6 96, .n 1 7 11 7 384, .p 1 7 11 8 128, .p 1 7 11 9 544, .p 1 7 11 10 64,
   .n 1 7 11 11 16, .p 1 7 12 5 144, .p 1 7 12 6 112, .p 1 7 12 7 240, .n 1 7 12 8 256, .n 1 7 12 9 224,
   .n 1 7 12 10 16, .n 1 7 13 5 32, .n 1 7 13 6 32, .n 1 7 13 7 48, .p 1 7 13 8 80, .p 1 7 13 9 32,
   .p 2 6 5 7 8, .n 2 6 5 8 32, .p 2 6 5 9 24, .p 2 6 6 5 16, .p 2 6 6 6 120, .n 2 6 6 7 232,
   .p 2 6 6 8 160, .n 2 6 6 9 176, .p 2 6 6 10 40, .p 2 6 6 11 72, .n 2 6 7 4 16, .n 2 6 7 5 24,
   .n 2 6 7 6 208, .p 2 6 7 7 264, .p 2 6 7 8 32, .p 2 6 7 9 488, .n 2 6 7 10 256, .n 2 6 7 11 280,
   .p 2 6 8 4 48, .n 2 6 8 5 104, .n 2 6 8 6 168, .p 2 6 8 7 848, .n 2 6 8 8 880, .n 2 6 8 9 696,
   .p 2 6 8 10 552, .p 2 6 8 11 400, .n 2 6 9 4 32, .p 2 6 9 5 208, .p 2 6 9 6 336, .n 2 6 9 7 1488,
   .p 2 6 9 8 1168, .p 2 6 9 9 496, .n 2 6 9 10 448, .n 2 6 9 11 240, .n 2 6 10 4 32, .p 2 6 10 5 128,
   .p 2 6 10 6 296, .n 2 6 10 7 136, .n 2 6 10 8 320, .p 2 6 10 9 32, .n 2 6 10 10 8, .p 2 6 10 11 40,
   .p 2 6 11 4 48, .n 2 6 11 5 568, .n 2 6 11 6 624, .p 2 6 11 7 1544, .n 2 6 11 8 192, .n 2 6 11 9 408,
   .p 2 6 11 10 192, .p 2 6 11 11 8, .n 2 6 12 4 16, .p 2 6 12 5 472, .p 2 6 12 6 264, .n 2 6 12 7 992,
   .p 2 6 12 8 16, .p 2 6 12 9 328, .n 2 6 12 10 72, .n 2 6 13 5 128, .n 2 6 13 6 16, .p 2 6 13 7 184,
   .p 2 6 13 8 48, .n 2 6 13 9 88, .p 3 5 5 7 8, .n 3 5 5 8 16, .p 3 5 5 9 8, .n 3 5 6 5 24,
   .p 3 5 6 6 112, .n 3 5 6 7 96, .p 3 5 6 8 128, .n 3 5 6 9 168, .n 3 5 6 10 80, .p 3 5 6 11 128,
   .p 3 5 7 4 16, .n 3 5 7 5 96, .p 3 5 7 6 16, .n 3 5 7 7 104, .n 3 5 7 8 336, .p 3 5 7 9 992,
   .n 3 5 7 10 176, .n 3 5 7 11 312, .p 3 5 8 3 8, .n 3 5 8 4 56, .p 3 5 8 5 184, .n 3 5 8 6 376,
   .p 3 5 8 7 1168, .n 3 5 8 8 520, .n 3 5 8 9 1496, .p 3 5 8 10 984, .p 3 5 8 11 104, .n 3 5 9 3 24,
   .p 3 5 9 4 112, .p 3 5 9 5 344, .n 3 5 9 6 592, .n 3 5 9 7 1584, .p 3 5 9 8 2608, .n 3 5 9 9 40,
   .n 3 5 9 10 1104, .p 3 5 9 11 280, .p 3 5 10 3 24, .n 3 5 10 4 160, .n 3 5 10 5 648, .p 3 5 10 6 2032,
   .n 3 5 10 7 112, .n 3 5 10 8 2784, .p 3 5 10 9 1544, .p 3 5 10 10 368, .n 3 5 10 11 264, .n 3 5 11 3 8,
   .p 3 5 11 4 128, .n 3 5 11 5 16, .n 3 5 11 6 1376, .p 3 5 11 7 1512, .p 3 5 11 8 704, .n 3 5 11 9 1008,
   .p 3 5 11 11 64, .n 3 5 12 4 40, .p 3 5 12 5 424, .p 3 5 12 6 24, .n 3 5 12 7 960, .p 3 5 12 8 360,
   .p 3 5 12 9 184, .p 3 5 12 10 8, .n 3 5 13 5 168, .p 3 5 13 6 160, .p 3 5 13 7 168, .n 3 5 13 8 144,
   .n 3 5 13 9 16, .n 4 4 6 5 8, .n 4 4 6 6 80, .p 4 4 6 7 176, .n 4 4 6 8 80, .p 4 4 6 9 104,
   .n 4 4 6 10 224, .p 4 4 6 11 112, .p 4 4 7 4 16, .n 4 4 7 5 24, .p 4 4 7 6 208, .n 4 4 7 7 320,
   .n 4 4 7 8 160, .p 4 4 7 9 344, .p 4 4 7 10 64, .n 4 4 7 11 128, .n 4 4 8 3 8, .n 4 4 8 4 96,
   .p 4 4 8 5 216, .p 4 4 8 6 16, .n 4 4 8 7 304, .p 4 4 8 8 416, .n 4 4 8 9 600, .p 4 4 8 10 544,
   .n 4 4 8 11 200, .p 4 4 8 12 16, .p 4 4 9 3 8, .p 4 4 9 4 160, .n 4 4 9 5 104, .n 4 4 9 6 688,
   .p 4 4 9 7 496, .p 4 4 9 8 848, .n 4 4 9 9 632, .n 4 4 9 10 416, .p 4 4 9 11 360, .n 4 4 9 12 32,
   .p 4 4 10 3 8, .n 4 4 10 4 80, .n 4 4 10 5 472, .p 4 4 10 6 1168, .p 4 4 10 7 256, .n 4 4 10 8 1904,
   .p 4 4 10 9 1016, .p 4 4 10 10 160, .n 4 4 10 11 168, .p 4 4 10 12 16, .n 4 4 11 3 8, .n 4 4 11 4 16,
   .p 4 4 11 5 472, .n 4 4 11 6 688, .n 4 4 11 7 336, .p 4 4 11 8 800, .n 4 4 11 9 24, .n 4 4 11 10 224,
   .p 4 4 11 11 24, .p 4 4 12 4 16, .p 4 4 12 5 8, .n 4 4 12 6 144, .p 4 4 12 7 128, .p 4 4 12 8 160,
   .n 4 4 12 9 264, .p 4 4 12 10 96, .n 4 4 13 5 88, .p 4 4 13 6 208, .n 4 4 13 7 96, .n 4 4 13 8 80,
   .p 4 4 13 9 56, .p 5 3 6 5 24, .n 5 3 6 6 56, .p 5 3 6 7 32, .n 5 3 6 8 48, .p 5 3 6 9 152,
   .n 5 3 6 10 152, .p 5 3 6 11 48, .n 5 3 7 4 16, .p 5 3 7 5 32, .p 5 3 7 6 16, .n 5 3 7 7 80,
   .p 5 3 7 8 80, .n 5 3 7 9 64, .p 5 3 7 10 48, .n 5 3 7 11 16, .n 5 3 8 3 8, .p 5 3 8 4 8,
   .n 5 3 8 5 136, .p 5 3 8 6 520, .n 5 3 8 7 576, .p 5 3 8 8 16, .p 5 3 8 9 280, .n 5 3 8 10 56,
   .n 5 3 8 11 72, .p 5 3 8 12 24, .p 5 3 9 3 96, .n 5 3 9 4 112, .n 5 3 9 5 368, .p 5 3 9 6 432,
   .p 5 3 9 7 640, .n 5 3 9 8 976, .n 5 3 9 9 48, .p 5 3 9 10 528, .n 5 3 9 11 192, .n 5 3 10 3 120,
   .p 5 3 10 4 184, .p 5 3 10 5 680, .n 5 3 10 6 1592, .p 5 3 10 7 272, .p 5 3 10 8 1488, .n 5 3 10 9 856,
   .n 5 3 10 10 312, .p 5 3 10 11 280, .n 5 3 10 12 24, .p 5 3 11 3 32, .n 5 3 11 4 128, .n 5 3 11 5 32,
   .p 5 3 11 6 512, .n 5 3 11 7 336, .n 5 3 11 8 448, .p 5 3 11 9 512, .n 5 3 11 10 64, .n 5 3 11 11 48,
   .p 5 3 12 4 64, .n 5 3 12 5 184, .p 5 3 12 6 104, .p 5 3 12 7 144, .n 5 3 12 8 176, .p 5 3 12 9 40,
   .p 5 3 12 10 8, .n 5 3 13 5 16, .p 5 3 13 6 64, .n 5 3 13 7 96, .p 5 3 13 8 64, .n 5 3 13 9 16,
   .n 6 2 6 5 8, .p 6 2 6 6 32, .n 6 2 6 7 40, .p 6 2 6 9 40, .n 6 2 6 10 32, .p 6 2 6 11 8,
   .p 6 2 8 3 8, .n 6 2 8 5 112, .p 6 2 8 6 248, .n 6 2 8 7 128, .n 6 2 8 8 168, .p 6 2 8 9 240,
   .n 6 2 8 10 88, .n 6 2 8 11 8, .p 6 2 8 12 8, .p 6 2 9 3 64, .n 6 2 9 4 128, .n 6 2 9 5 128,
   .p 6 2 9 6 352, .p 6 2 9 7 128, .n 6 2 9 8 544, .p 6 2 9 9 128, .p 6 2 9 10 288, .n 6 2 9 11 192,
   .p 6 2 9 12 32, .n 6 2 10 2 8, .n 6 2 10 3 72, .p 6 2 10 4 112, .p 6 2 10 5 472, .n 6 2 10 6 992,
   .p 6 2 10 7 40, .p 6 2 10 8 1072, .n 6 2 10 9 632, .n 6 2 10 10 152, .p 6 2 10 11 192, .n 6 2 10 12 32,
   .p 6 2 11 3 32, .n 6 2 11 4 32, .n 6 2 11 5 192, .p 6 2 11 6 352, .n 6 2 11 8 352, .p 6 2 11 9 192,
   .p 6 2 11 10 32, .n 6 2 11 11 32, .p 6 2 12 4 24, .n 6 2 12 5 96, .p 6 2 12 6 120, .n 6 2 12 8 120,
   .p 6 2 12 9 96, .n 6 2 12 10 24, .n 7 1 10 2 24, .p 7 1 10 3 96, .n 7 1 10 4 72, .n 7 1 10 5 192,
   .p 7 1 10 6 336, .n 7 1 10 8 336, .p 7 1 10 9 192, .p 7 1 10 10 72, .n 7 1 10 11 96, .p 7 1 10 12 24,
   .n 8 0 10 2 16, .p 8 0 10 3 64, .n 8 0 10 4 48, .n 8 0 10 5 128, .p 8 0 10 6 224, .n 8 0 10 8 224,
   .p 8 0 10 9 128, .p 8 0 10 10 48, .n 8 0 10 11 64, .p 8 0 10 12 16]

private def g2Mid5_3_a : List FM :=
  [.n 0 8 6 7 64, .p 0 8 6 8 64, .p 0 8 7 7 256, .n 0 8 7 8 192, .n 0 8 7 9 64, .n 0 8 8 7 320,
   .p 0 8 8 8 64, .p 0 8 8 9 256, .p 0 8 9 8 320, .n 0 8 9 9 320, .p 0 8 10 7 320, .n 0 8 10 8 320,
   .n 0 8 11 7 256, .n 0 8 11 8 64, .p 0 8 11 9 320, .p 0 8 12 7 64, .p 0 8 12 8 192, .n 0 8 12 9 256,
   .n 0 8 13 8 64, .p 0 8 13 9 64, .n 1 7 5 6 16, .p 1 7 5 8 16, .p 1 7 6 4 16, .n 1 7 6 5 16,
   .p 1 7 6 6 80, .n 1 7 6 7 192, .p 1 7 6 8 80, .p 1 7 6 9 48, .n 1 7 6 10 48, .p 1 7 6 11 32,
   .p 1 7 7 3 16, .n 1 7 7 4 32, .n 1 7 7 6 64, .p 1 7 7 7 608, .n 1 7 7 8 288, .n 1 7 7 9 224,
   .p 1 7 7 10 128, .n 1 7 7 11 144, .n 1 7 8 3 32, .n 1 7 8 4 48, .p 1 7 8 5 80, .n 1 7 8 6 80,
   .n 1 7 8 7 576, .p 1 7 8 8 80, .p 1 7 8 9 400, .n 1 7 8 10 80, .p 1 7 8 11 256, .n 1 7 9 3 32,
   .p 1 7 9 4 192, .n 1 7 9 5 64, .n 1 7 9 6 32, .p 1 7 9 7 32, .p 1 7 9 8 352, .n 1 7 9 9 224,
   .n 1 7 9 11 224, .p 1 7 10 3 128, .n 1 7 10 4 208, .p 1 7 10 5 16, .p 1 7 10 6 304, .p 1 7 10 7 192,
   .n 1 7 10 8 144, .n 1 7 10 9 304, .n 1 7 10 10 80, .p 1 7 10 11 96, .n 1 7 11 3 112, .p 1 7 11 4 96,
   .n 1 7 11 5 128, .n 1 7 11 6 192, .n 1 7 11 7 96, .n 1 7 11 8 288, .p 1 7 11 9 608, .p 1 7 11 10 128,
   .n 1 7 11 11 16, .p 1 7 12 3 32, .n 1 7 12 4 16, .p 1 7 12 5 176, .n 1 7 12 6 48, .p 1 7 12 7 64,
   .p 1 7 12 8 240, .n 1 7 12 9 400, .n 1 7 12 10 48, .n 1 7 13 5 64, .p 1 7 13 6 48, .n 1 7 13 7 32,
   .n 1 7 13 8 48, .p 1 7 13 9 96, .n 2 6 5 6 8, .n 2 6 5 7 16, .p 2 6 5 8 8, .p 2 6 5 9 16,
   .p 2 6 6 4 24, .p 2 6 6 5 24, .p 2 6 6 6 40, .n 2 6 6 8 184, .p 2 6 6 9 120, .n 2 6 6 10 136,
   .p 2 6 6 11 112, .n 2 6 7 2 16, .n 2 6 7 3 8, .n 2 6 7 5 32, .p 2 6 7 6 16, .n 2 6 7 7 288,
   .p 2 6 7 8 624, .n 2 6 7 9 112, .p 2 6 7 10 272, .n 2 6 7 11 456, .p 2 6 8 2 48, .n 2 6 8 3 32,
   .n 2 6 8 4 120, .p 2 6 8 5 8, .n 2 6 8 6 200, .p 2 6 8 7 672, .n 2 6 8 8 264, .n 2 6 8 9 824,
   .p 2 6 8 10 24, .p 2 6 8 11 688, .n 2 6 9 2 48, .p 2 6 9 3 64, .p 2 6 9 4 224, .n 2 6 9 5 80,
   .n 2 6 9 6 64, .p 2 6 9 7 304, .n 2 6 9 8 1280, .p 2 6 9 9 1568, .n 2 6 9 10 240, .n 2 6 9 11 448,
   .p 2 6 10 2 16, .p 2 6 10 3 80, .n 2 6 10 4 280, .p 2 6 10 5 296, .p 2 6 10 6 632, .n 2 6 10 7 1632,
   .p 2 6 10 8 1528, .n 2 6 10 9 632, .n 2 6 10 10 104, .p 2 6 10 11 96, .n 2 6 11 3 184, .p 2 6 11 4 192,
   .n 2 6 11 5 512, .n 2 6 11 6 368, .p 2 6 11 7 1120, .p 2 6 11 8 16, .n 2 6 11 9 560, .p 2 6 11 10 288,
   .p 2 6 11 11 8, .p 2 6 12 3 80, .n 2 6 12 4 8, .p 2 6 12 5 440, .n 2 6 12 6 216, .n 2 6 12 7 64,
   .n 2 6 12 8 696, .p 2 6 12 9 568, .n 2 6 12 10 104, .n 2 6 13 4 32, .n 2 6 13 5 144, .p 2 6 13 6 168,
   .n 2 6 13 7 96, .p 2 6 13 8 248, .n 2 6 13 9 144, .p 3 5 5 6 16, .n 3 5 5 7 24, .n 3 5 5 8 16,
   .p 3 5 5 9 24, .n 3 5 6 4 48, .p 3 5 6 5 120, .n 3 5 6 6 112, .p 3 5 6 7 280, .n 3 5 6 8 264,
   .p 3 5 6 9 32, .n 3 5 6 10 152, .p 3 5 6 11 144, .p 3 5 7 2 32, .n 3 5 7 3 96, .p 3 5 7 4 64,
   .n 3 5 7 5 48, .p 3 5 7 6 256, .n 3 5 7 7 1016, .p 3 5 7 8 760, .p 3 5 7 9 328, .p 3 5 7 10 104,
   .n 3 5 7 11 384, .n 3 5 8 2 80, .p 3 5 8 3 152, .p 3 5 8 4 112, .n 3 5 8 5 400, .p 3 5 8 6 88,
   .p 3 5 8 7 712, .n 3 5 8 8 136, .n 3 5 8 9 1160, .p 3 5 8 10 480, .p 3 5 8 11 248, .n 3 5 8 12 16,
   .p 3 5 9 2 64, .p 3 5 9 3 184, .n 3 5 9 4 464, .p 3 5 9 5 216, .n 3 5 9 6 296, .p 3 5 9 7 840,
   .n 3 5 9 8 1032, .p 3 5 9 9 992, .n 3 5 9 10 672, .p 3 5 9 11 136, .p 3 5 9 12 32, .n 3 5 10 2 16,
   .n 3 5 10 3 392, .p 3 5 10 4 496, .p 3 5 10 5 552, .n 3 5 10 6 272, .n 3 5 10 7 984, .p 3 5 10 8 344,
   .p 3 5 10 9 192, .p 3 5 10 10 296, .n 3 5 10 11 200, .n 3 5 10 12 16, .p 3 5 11 3 104, .n 3 5 11 4 208,
   .n 3 5 11 5 592, .p 3 5 11 6 480, .p 3 5 11 7 184, .p 3 5 11 8 920, .n 3 5 11 9 840, .n 3 5 11 10 104,
   .p 3 5 11 11 56, .p 3 5 12 3 48, .p 3 5 12 4 176, .p 3 5 12 5 112, .n 3 5 12 6 280, .n 3 5 12 7 8,
   .n 3 5 12 8 648, .p 3 5 12 9 552, .p 3 5 12 10 48, .n 3 5 13 4 128, .p 3 5 13 5 40, .p 3 5 13 6 120,
   .p 3 5 13 7 16, .p 3 5 13 8 72, .n 3 5 13 9 120, .p 4 4 5 6 8, .n 4 4 5 7 8, .n 4 4 5 8 8,
   .p 4 4 5 9 8, .n 4 4 6 4 8, .n 4 4 6 5 48, .p 4 4 6 6 40, .p 4 4 6 7 72, .p 4 4 6 8 48,
   .n 4 4 6 9 104, .n 4 4 6 10 80, .p 4 4 6 11 80, .p 4 4 7 3 56, .n 4 4 7 4 96, .p 4 4 7 5 16,
   .p 4 4 7 6 88, .n 4 4 7 7 32, .n 4 4 7 8 296, .p 4 4 7 9 456, .n 4 4 7 10 208, .p 4 4 7 11 16,
   .n 4 4 8 2 56, .p 4 4 8 3 40, .p 4 4 8 4 96, .p 4 4 8 5 16, .p 4 4 8 6 208, .n 4 4 8 7 752,
   .p 4 4 8 8 176, .p 4 4 8 9 136, .p 4 4 8 10 592, .n 4 4 8 11 464, .p 4 4 8 12 8, .p 4 4 9 1 8,
   .p 4 4 9 2 104, .n 4 4 9 3 88, .n 4 4 9 4 184, .p 4 4 9 5 128, .n 4 4 9 6 280, .p 4 4 9 7 248,
   .p 4 4 9 8 1264, .n 4 4 9 9 1424, .n 4 4 9 10 360, .p 4 4 9 11 616, .n 4 4 9 12 32, .n 4 4 10 1 8,
   .n 4 4 10 2 56, .n 4 4 10 3 248, .p 4 4 10 4 640, .p 4 4 10 5 64, .n 4 4 10 6 1096, .p 4 4 10 7 1752,
   .n 4 4 10 8 1856, .p 4 4 10 9 736, .p 4 4 10 10 296, .n 4 4 10 11 248, .p 4 4 10 12 24, .p 4 4 11 2 8,
   .p 4 4 11 3 280, .n 4 4 11 4 640, .n 4 4 11 5 64, .p 4 4 11 6 1128, .n 4 4 11 7 1216, .p 4 4 11 8 392,
   .p 4 4 11 9 488, .n 4 4 11 10 376, .n 4 4 12 3 40, .p 4 4 12 4 360, .n 4 4 12 5 400, .p 4 4 12 6 16,
   .n 4 4 12 7 192, .p 4 4 12 8 512, .n 4 4 12 9 392, .p 4 4 12 10 136, .n 4 4 13 4 168, .p 4 4 13 5 288,
   .n 4 4 13 6 112, .p 4 4 13 7 128, .n 4 4 13 8 232, .p 4 4 13 9 96, .p 5 3 6 4 32, .n 5 3 6 5 80,
   .p 5 3 6 6 80, .n 5 3 6 7 112, .p 5 3 6 8 160, .n 5 3 6 9 80, .n 5 3 6 10 16, .p 5 3 6 11 16,
   .n 5 3 7 2 32, .p 5 3 7 3 80, .n 5 3 7 4 80, .p 5 3 7 5 48, .n 5 3 7 6 168, .p 5 3 7 7 360,
   .n 5 3 7 8 256, .p 5 3 7 9 160, .n 5 3 7 10 232, .p 5 3 7 11 120, .p 5 3 8 2 96, .n 5 3 8 3 168,
   .n 5 3 8 4 96, .p 5 3 8 5 448, .n 5 3 8 6 40, .n 5 3 8 7 608, .p 5 3 8 8 56, .p 5 3 8 9 384,
   .p 5 3 8 10 200, .n 5 3 8 11 312, .p 5 3 8 12 40, .p 5 3 9 1 16, .n 5 3 9 2 64, .n 5 3 9 3 128,
   .p 5 3 9 4 336, .n 5 3 9 5 144, .p 5 3 9 6 168, .n 5 3 9 7 456, .p 5 3 9 8 704, .n 5 3 9 9 720,
   .p 5 3 9 10 200, .p 5 3 9 11 152, .n 5 3 9 12 64, .n 5 3 10 1 24, .p 5 3 10 3 240, .n 5 3 10 4 184,
   .n 5 3 10 5 280, .n 5 3 10 6 264, .p 5 3 10 7 1176, .n 5 3 10 8 712, .p 5 3 10 9 112, .n 5 3 10 10 152,
   .p 5 3 10 11 56, .p 5 3 10 12 32, .p 5 3 11 2 24, .p 5 3 11 3 40, .n 5 3 11 4 232, .p 5 3 11 5 104,
   .p 5 3 11 6 320, .n 5 3 11 7 192, .n 5 3 11 8 360, .p 5 3 11 9 360, .n 5 3 11 10 8, .n 5 3 11 11 56,
   .n 5 3 12 3 56, .p 5 3 12 4 224, .n 5 3 12 5 264, .p 5 3 12 6 160, .n 5 3 12 7 296, .p 5 3 12 8 384,
   .n 5 3 12 9 152, .n 5 3 13 4 88, .p 5 3 13 5 216, .n 5 3 13 6 144, .p 5 3 13 7 16, .n 5 3 13 8 24,
   .p 5 3 13 9 24, .n 6 2 6 4 16, .p 6 2 6 5 48, .n 6 2 6 6 32, .n 6 2 6 7 32, .p 6 2 6 8 48,
   .n 6 2 6 9 16, .p 6 2 7 2 16, .n 6 2 7 3 48, .p 6 2 7 4 48, .p 6 2 7 5 16, .n 6 2 7 6 80,
   .p 6 2 7 7 16, .p 6 2 7 8 80, .n 6 2 7 9 16, .n 6 2 7 10 64, .p 6 2 7 11 32, .p 6 2 8 2 8,
   .n 6 2 8 3 8, .n 6 2 8 4 24, .p 6 2 8 5 24, .p 6 2 8 6 40, .n 6 2 8 7 56, .n 6 2 8 8 24,
   .p 6 2 8 9 72, .n 6 2 8 10 16, .n 6 2 8 11 32, .p 6 2 8 12 16, .n 6 2 9 1 8, .n 6 2 9 2 8,
   .p 6 2 9 3 48, .n 6 2 9 4 88, .n 6 2 9 5 24, .p 6 2 9 6 392, .n 6 2 9 7 216, .n 6 2 9 8 520,
   .p 6 2 9 9 416, .p 6 2 9 10 192, .n 6 2 9 11 216, .p 6 2 9 12 32, .n 6 2 10 1 16, .p 6 2 10 2 40,
   .p 6 2 10 3 144, .n 6 2 10 4 384, .p 6 2 10 5 72, .p 6 2 10 6 344, .n 6 2 10 7 296, .p 6 2 10 8 216,
   .n 6 2 10 9 56, .n 6 2 10 10 192, .p 6 2 10 11 152, .n 6 2 10 12 24, .p 6 2 11 2 16, .n 6 2 11 3 96,
   .p 6 2 11 4 184, .n 6 2 11 5 24, .n 6 2 11 6 328, .p 6 2 11 7 328, .p 6 2 11 8 40, .n 6 2 11 9 200,
   .p 6 2 11 10 88, .n 6 2 11 11 8, .n 6 2 12 3 16, .p 6 2 12 4 32, .n 6 2 12 5 16, .p 6 2 12 6 32,
   .n 6 2 12 7 48, .n 6 2 12 8 32, .p 6 2 12 9 80, .n 6 2 12 10 32, .n 6 2 13 4 16, .p 6 2 13 5 48,
   .n 6 2 13 6 32, .n 6 2 13 7 32, .p 6 2 13 8 48, .n 6 2 13 9 16, .n 7 1 8 2 16, .p 7 1 8 3 48,
   .n 7 1 8 4 16, .n 7 1 8 5 80, .p 7 1 8 6 80, .p 7 1 8 7 16, .n 7 1 8 8 48, .p 7 1 8 9 16,
   .n 7 1 9 1 16, .p 7 1 9 2 48, .n 7 1 9 4 112, .p 7 1 9 5 16, .p 7 1 9 6 208, .n 7 1 9 7 80,
   .n 7 1 9 8 240, .p 7 1 9 9 192, .p 7 1 9 10 64, .n 7 1 9 11 112, .p 7 1 9 12 32, .p 7 1 10 2 16,
   .n 7 1 10 4 128, .p 7 1 10 5 144, .p 7 1 10 6 112, .n 7 1 10 7 240, .p 7 1 10 8 80, .p 7 1 10 9 48,
   .n 7 1 10 10 64, .p 7 1 10 11 48, .n 7 1 10 12 16, .n 7 1 11 3 32, .p 7 1 11 4 80, .p 7 1 11 5 16,
   .n 7 1 11 6 176, .p 7 1 11 7 80, .p 7 1 11 8 112, .n 7 1 11 9 80, .n 7 1 11 10 16, .p 7 1 11 11 16]

private def g2Mid5_3_b : List FM :=
  [.n 0 8 5 6 32, .p 0 8 5 7 32, .p 0 8 6 6 64, .n 0 8 6 7 128, .p 0 8 6 8 64, .p 0 8 7 6 96,
   .p 0 8 7 7 160, .n 0 8 7 8 224, .n 0 8 7 9 32, .n 0 8 8 6 320, .p 0 8 8 8 192, .p 0 8 8 9 128,
   .p 0 8 9 6 160, .n 0 8 9 7 160, .p 0 8 9 8 160, .n 0 8 9 9 160, .p 0 8 10 6 192, .p 0 8 10 7 128,
   .n 0 8 10 8 320, .n 0 8 11 6 224, .n 0 8 11 7 32, .p 0 8 11 8 96, .p 0 8 11 9 160, .p 0 8 12 6 64,
   .p 0 8 12 8 64, .n 0 8 12 9 128, .n 0 8 13 8 32, .p 0 8 13 9 32, .n 1 7 5 6 16, .p 1 7 5 9 16,
   .p 1 7 6 4 16, .p 1 7 6 5 16, .p 1 7 6 6 32, .n 1 7 6 7 176, .p 1 7 6 8 112, .n 1 7 6 9 16,
   .p 1 7 6 11 16, .p 1 7 7 3 16, .n 1 7 7 4 32, .p 1 7 7 6 48, .p 1 7 7 7 432, .n 1 7 7 8 240,
   .n 1 7 7 9 144, .n 1 7 7 11 80, .n 1 7 8 3 32, .n 1 7 8 4 64, .n 1 7 8 5 64, .n 1 7 8 6 176,
   .n 1 7 8 7 192, .p 1 7 8 8 32, .p 1 7 8 9 352, .n 1 7 8 10 16, .p 1 7 8 11 160, .n 1 7 9 3 32,
   .p 1 7 9 4 224, .n 1 7 9 5 32, .p 1 7 9 6 112, .n 1 7 9 7 112, .p 1 7 9 8 112, .n 1 7 9 9 176,
   .p 1 7 9 10 64, .n 1 7 9 11 160, .p 1 7 10 3 128, .n 1 7 10 4 176, .p 1 7 10 5 208, .p 1 7 10 6 128,
   .n 1 7 10 7 112, .p 1 7 10 8 112, .n 1 7 10 9 272, .n 1 7 10 10 96, .p 1 7 10 11 80, .n 1 7 11 3 112,
   .n 1 7 11 4 32, .n 1 7 11 5 128, .n 1 7 11 6 240, .p 1 7 11 7 144, .n 1 7 11 8 80, .p 1 7 11 9 400,
   .p 1 7 11 10 64, .n 1 7 11 11 16, .p 1 7 12 3 32, .p 1 7 12 4 96, .n 1 7 12 5 32, .p 1 7 12 6 144,
   .p 1 7 12 7 96, .n 1 7 12 8 128, .n 1 7 12 9 192, .n 1 7 12 10 16, .n 1 7 13 4 32, .p 1 7 13 5 32,
   .n 1 7 13 6 32, .n 1 7 13 7 80, .p 1 7 13 8 80, .p 1 7 13 9 32, .p 2 6 5 6 32, .n 2 6 5 7 56,
   .p 2 6 5 9 24, .p 2 6 6 4 8, .p 2 6 6 5 72, .n 2 6 6 6 80, .p 2 6 6 7 88, .n 2 6 6 8 120,
   .n 2 6 6 9 40, .p 2 6 6 11 72, .n 2 6 7 2 16, .n 2 6 7 3 8, .p 2 6 7 4 16, .n 2 6 7 5 48,
   .n 2 6 7 6 144, .n 2 6 7 7 96, .p 2 6 7 8 656, .n 2 6 7 9 16, .n 2 6 7 10 64, .n 2 6 7 11 280,
   .p 2 6 8 2 48, .n 2 6 8 3 32, .n 2 6 8 4 128, .n 2 6 8 5 208, .p 2 6 8 6 712, .n 2 6 8 7 80,
   .n 2 6 8 8 784, .n 2 6 8 9 144, .p 2 6 8 10 216, .p 2 6 8 11 400, .n 2 6 9 2 48, .p 2 6 9 3 64,
   .p 2 6 9 4 272, .n 2 6 9 5 32, .n 2 6 9 6 560, .p 2 6 9 7 672, .n 2 6 9 8 496, .p 2 6 9 9 560,
   .n 2 6 9 10 192, .n 2 6 9 11 240, .p 2 6 10 2 16, .p 2 6 10 3 80, .n 2 6 10 4 200, .p 2 6 10 5 632,
   .n 2 6 10 6 560, .n 2 6 10 7 728, .p 2 6 10 8 1272, .n 2 6 10 9 472, .n 2 6 10 10 80, .p 2 6 10 11 40,
   .n 2 6 11 3 184, .n 2 6 11 4 160, .n 2 6 11 5 416, .p 2 6 11 6 864, .p 2 6 11 7 112, .n 2 6 11 8 320,
   .n 2 6 11 9 96, .p 2 6 11 10 192, .p 2 6 11 11 8, .p 2 6 12 3 80, .p 2 6 12 4 320, .n 2 6 12 5 112,
   .n 2 6 12 6 200, .p 2 6 12 7 80, .n 2 6 12 8 368, .p 2 6 12 9 272, .n 2 6 12 10 72, .n 2 6 13 4 128,
   .p 2 6 13 5 112, .n 2 6 13 6 64, .p 2 6 13 7 8, .p 2 6 13 8 160, .n 2 6 13 9 88, .p 3 5 5 6 16,
   .n 3 5 5 7 24, .p 3 5 5 9 8, .n 3 5 6 4 24, .p 3 5 6 5 8, .p 3 5 6 6 24, .p 3 5 6 7 232,
   .n 3 5 6 8 256, .n 3 5 6 9 16, .n 3 5 6 10 96, .p 3 5 6 11 128, .p 3 5 7 2 32, .n 3 5 7 3 96,
   .p 3 5 7 4 32, .n 3 5 7 5 16, .p 3 5 7 6 104, .n 3 5 7 7 736, .p 3 5 7 8 664, .p 3 5 7 9 360,
   .n 3 5 7 10 32, .n 3 5 7 11 312, .n 3 5 8 2 72, .p 3 5 8 3 144, .p 3 5 8 4 72, .p 3 5 8 6 48,
   .p 3 5 8 7 88, .n 3 5 8 8 144, .n 3 5 8 9 888, .p 3 5 8 10 640, .p 3 5 8 11 112, .p 3 5 9 2 48,
   .p 3 5 9 3 200, .n 3 5 9 4 440, .p 3 5 9 5 96, .n 3 5 9 6 536, .p 3 5 9 7 1016, .n 3 5 9 8 256,
   .p 3 5 9 9 408, .n 3 5 9 10 800, .p 3 5 9 11 264, .n 3 5 10 2 8, .n 3 5 10 3 416, .p 3 5 10 4 600,
   .p 3 5 10 5 168, .n 3 5 10 6 280, .n 3 5 10 7 8, .n 3 5 10 8 640, .p 3 5 10 9 544, .p 3 5 10 10 296,
   .n 3 5 10 11 256, .p 3 5 11 3 136, .n 3 5 11 4 352, .n 3 5 11 5 448, .p 3 5 11 6 1192, .n 3 5 11 7 720,
   .p 3 5 11 8 680, .n 3 5 11 9 536, .n 3 5 11 10 16, .p 3 5 11 11 64, .p 3 5 12 3 32, .p 3 5 12 4 280,
   .p 3 5 12 5 48, .n 3 5 12 6 560, .n 3 5 12 7 56, .p 3 5 12 8 112, .p 3 5 12 9 136, .p 3 5 12 10 8,
   .n 3 5 13 4 168, .p 3 5 13 5 144, .n 3 5 13 6 8, .p 3 5 13 7 208, .n 3 5 13 8 160, .n 3 5 13 9 16,
   .n 4 4 6 5 72, .p 4 4 6 6 72, .p 4 4 6 7 56, .n 4 4 6 8 8, .p 4 4 6 9 32, .n 4 4 6 10 192,
   .p 4 4 6 11 112, .p 4 4 7 3 56, .n 4 4 7 4 96, .p 4 4 7 5 16, .p 4 4 7 6 120, .n 4 4 7 7 128,
   .n 4 4 7 8 216, .p 4 4 7 9 312, .p 4 4 7 10 64, .n 4 4 7 11 128, .n 4 4 8 2 64, .p 4 4 8 3 48,
   .p 4 4 8 4 88, .p 4 4 8 5 384, .n 4 4 8 6 664, .n 4 4 8 7 232, .p 4 4 8 8 768, .n 4 4 8 9 632,
   .p 4 4 8 10 496, .n 4 4 8 11 208, .p 4 4 8 12 16, .p 4 4 9 1 8, .p 4 4 9 2 128, .n 4 4 9 3 112,
   .n 4 4 9 4 328, .p 4 4 9 5 80, .p 4 4 9 6 472, .n 4 4 9 7 248, .p 4 4 9 8 320, .n 4 4 9 9 224,
   .n 4 4 9 10 432, .p 4 4 9 11 368, .n 4 4 9 12 32, .n 4 4 10 1 8, .n 4 4 10 2 64, .n 4 4 10 3 232,
   .p 4 4 10 4 624, .n 4 4 10 5 552, .p 4 4 10 6 264, .p 4 4 10 7 1000, .n 4 4 10 8 1912, .p 4 4 10 9 856,
   .p 4 4 10 10 176, .n 4 4 10 11 168, .p 4 4 10 12 16, .p 4 4 11 3 288, .n 4 4 11 4 224, .n 4 4 11 5 160,
   .n 4 4 11 6 232, .n 4 4 11 7 112, .p 4 4 11 8 792, .n 4 4 11 9 168, .n 4 4 11 10 208, .p 4 4 11 11 24,
   .n 4 4 12 3 48, .p 4 4 12 4 24, .p 4 4 12 5 224, .n 4 4 12 6 120, .n 4 4 12 7 328, .p 4 4 12 8 384,
   .n 4 4 12 9 232, .p 4 4 12 10 96, .n 4 4 13 4 88, .p 4 4 13 5 80, .p 4 4 13 6 88, .n 4 4 13 7 8,
   .n 4 4 13 8 128, .p 4 4 13 9 56, .p 5 3 6 4 8, .n 5 3 6 6 8, .n 5 3 6 7 80, .p 5 3 6 8 120,
   .p 5 3 6 9 32, .n 5 3 6 10 120, .p 5 3 6 11 48, .n 5 3 7 2 32, .p 5 3 7 3 80, .n 5 3 7 4 48,
   .p 5 3 7 5 16, .n 5 3 7 6 128, .p 5 3 7 7 256, .n 5 3 7 8 208, .p 5 3 7 9 48, .p 5 3 7 10 32,
   .n 5 3 7 11 16, .p 5 3 8 2 88, .n 5 3 8 3 160, .n 5 3 8 4 40, .p 5 3 8 5 192, .p 5 3 8 6 96,
   .n 5 3 8 7 368, .p 5 3 8 8 112, .p 5 3 8 9 160, .n 5 3 8 10 24, .n 5 3 8 11 80, .p 5 3 8 12 24,
   .p 5 3 9 1 16, .n 5 3 9 2 32, .n 5 3 9 3 160, .p 5 3 9 4 216, .n 5 3 9 5 24, .p 5 3 9 6 456,
   .n 5 3 9 7 616, .n 5 3 9 8 56, .p 5 3 9 9 40, .p 5 3 9 10 312, .n 5 3 9 11 152, .n 5 3 10 1 32,
   .p 5 3 10 2 16, .p 5 3 10 3 288, .n 5 3 10 4 456, .p 5 3 10 5 24, .n 5 3 10 6 32, .p 5 3 10 7 360,
   .p 5 3 10 8 192, .n 5 3 10 9 376, .n 5 3 10 10 208, .p 5 3 10 11 248, .n 5 3 10 12 24, .p 5 3 11 2 8,
   .n 5 3 11 3 8, .p 5 3 11 4 200, .n 5 3 11 5 136, .n 5 3 11 6 600, .p 5 3 11 7 728, .n 5 3 11 8 232,
   .p 5 3 11 9 104, .n 5 3 11 10 16, .n 5 3 11 11 48, .n 5 3 12 3 40, .p 5 3 12 4 8, .p 5 3 12 5 8,
   .p 5 3 12 6 248, .n 5 3 12 7 280, .n 5 3 12 8 8, .p 5 3 12 9 56, .p 5 3 12 10 8, .n 5 3 13 4 16,
   .p 5 3 13 5 16, .p 5 3 13 6 64, .n 5 3 13 7 128, .p 5 3 13 8 80, .n 5 3 13 9 16, .n 6 2 6 4 8,
   .p 6 2 6 5 24, .n 6 2 6 6 8, .n 6 2 6 7 40, .p 6 2 6 8 40, .p 6 2 6 9 8, .n 6 2 6 10 24,
   .p 6 2 6 11 8, .p 6 2 7 2 16, .n 6 2 7 3 48, .p 6 2 7 4 32, .p 6 2 7 5 32, .n 6 2 7 6 48,
   .p 6 2 7 7 16, .p 6 2 8 2 16, .n 6 2 8 3 16, .n 6 2 8 4 8, .n 6 2 8 5 128, .p 6 2 8 6 320,
   .n 6 2 8 7 144, .n 6 2 8 8 224, .p 6 2 8 9 288, .n 6 2 8 10 112, .p 6 2 8 12 8, .n 6 2 9 1 8,
   .n 6 2 9 2 32, .p 6 2 9 3 72, .p 6 2 9 4 8, .n 6 2 9 5 24, .n 6 2 9 6 24, .p 6 2 9 7 72,
   .n 6 2 9 8 200, .p 6 2 9 9 64, .p 6 2 9 10 216, .n 6 2 9 11 176, .p 6 2 9 12 32, .n 6 2 10 1 32,
   .p 6 2 10 2 96, .p 6 2 10 3 112, .n 6 2 10 4 528, .p 6 2 10 5 448, .n 6 2 10 6 48, .n 6 2 10 7 288,
   .p 6 2 10 8 624, .n 6 2 10 9 416, .n 6 2 10 10 112, .p 6 2 10 11 176, .n 6 2 10 12 32, .p 6 2 11 2 24,
   .n 6 2 11 3 104, .p 6 2 11 4 120, .n 6 2 11 5 24, .p 6 2 11 6 24, .p 6 2 11 7 8, .n 6 2 11 8 184,
   .p 6 2 11 9 152, .p 6 2 11 10 16, .n 6 2 11 11 32, .n 6 2 12 3 8, .p 6 2 12 4 40, .n 6 2 12 5 88,
   .p 6 2 12 6 88, .p 6 2 12 7 8, .n 6 2 12 8 104, .p 6 2 12 9 88, .n 6 2 12 10 24, .n 7 1 8 2 16,
   .p 7 1 8 3 48, .n 7 1 8 4 16, .n 7 1 8 5 80, .p 7 1 8 6 80, .p 7 1 8 7 16, .n 7 1 8 8 48,
   .p 7 1 8 9 16, .n 7 1 9 1 16, .p 7 1 9 2 32, .p 7 1 9 3 16, .n 7 1 9 4 48, .n 7 1 9 5 16,
   .p 7 1 9 6 16, .p 7 1 9 7 48, .n 7 1 9 8 16, .n 7 1 9 9 32, .p 7 1 9 10 16, .p 7 1 10 1 8,
   .n 7 1 10 2 8, .n 7 1 10 3 24, .p 7 1 10 4 8, .p 7 1 10 5 32, .p 7 1 10 6 64, .n 7 1 10 7 96,
   .n 7 1 10 8 96, .p 7 1 10 9 152, .p 7 1 10 10 8, .n 7 1 10 11 72, .p 7 1 10 12 24, .p 7 1 11 2 16,
   .n 7 1 11 3 16, .n 7 1 11 4 80, .p 7 1 11 5 112, .p 7 1 11 6 80, .n 7 1 11 7 176, .p 7 1 11 8 16,
   .p 7 1 11 9 80, .n 7 1 11 10 32, .p 8 0 10 1 16, .n 8 0 10 2 48, .p 8 0 10 3 16, .p 8 0 10 4 80,
   .n 8 0 10 5 96, .p 8 0 10 6 32, .p 8 0 10 7 32, .n 8 0 10 8 96, .p 8 0 10 9 80, .p 8 0 10 10 16,
   .n 8 0 10 11 48, .p 8 0 10 12 16]

set_option maxRecDepth 65536 in
private theorem g2_det5_3_step01 :
    fmMerge (fmMerge [] (fmMul (fmSubMat g2FM ⟨3, by decide⟩ ⟨0, by decide⟩ ⟨0, by decide⟩) g2Val4_12))
      (fmMul (fmNeg (fmSubMat g2FM ⟨3, by decide⟩ ⟨0, by decide⟩ ⟨1, by decide⟩)) g2Val4_8) =
      g2Mid5_3_a := rfl

set_option maxRecDepth 65536 in
private theorem g2_det5_3_step2 :
    fmMerge g2Mid5_3_a (fmMul (fmSubMat g2FM ⟨3, by decide⟩ ⟨0, by decide⟩ ⟨2, by decide⟩) g2Val4_5) =
      g2Mid5_3_b := rfl

set_option maxRecDepth 65536 in
private theorem g2_det5_3_step34 :
    fmMerge (fmMerge g2Mid5_3_b (fmMul (fmNeg (fmSubMat g2FM ⟨3, by decide⟩ ⟨0, by decide⟩ ⟨3, by decide⟩)) g2Val4_2))
      (fmMul (fmSubMat g2FM ⟨3, by decide⟩ ⟨0, by decide⟩ ⟨4, by decide⟩) g2Val4_1) =
      g2Val5_3 := rfl

private theorem g2_det5_3 : fmDet 5 (fmSubMat g2FM ⟨3, by decide⟩) = g2Val5_3 :=
  fmDet5_of_sub4_split _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (fin4Mat_eq_of_vals _ _ (by decide)) g2_det4_12
    (fin4Mat_eq_of_vals _ _ (by decide)) g2_det4_8
    (fin4Mat_eq_of_vals _ _ (by decide)) g2_det4_5
    (fin4Mat_eq_of_vals _ _ (by decide)) g2_det4_2
    (fin4Mat_eq_of_vals _ _ (by decide)) g2_det4_1
    g2_det5_3_step01 g2_det5_3_step2 g2_det5_3_step34

private def g2Val5_4 : List FM :=
  [.p 0 8 4 7 64, .n 0 8 5 7 288, .n 0 8 5 8 32, .p 0 8 6 7 416, .p 0 8 6 8 128, .n 0 8 6 9 32,
   .n 0 8 7 7 32, .n 0 8 7 8 128, .p 0 8 7 9 160, .n 0 8 8 7 480, .n 0 8 8 8 128, .n 0 8 8 9 288,
   .p 0 8 9 7 416, .p 0 8 9 8 320, .p 0 8 9 9 160, .n 0 8 10 7 32, .n 0 8 10 8 128, .p 0 8 10 9 160,
   .n 0 8 11 7 96, .n 0 8 11 8 128, .n 0 8 11 9 288, .p 0 8 12 7 32, .p 0 8 12 8 128, .p 0 8 12 9 160,
   .n 0 8 13 8 32, .n 0 8 13 9 32, .n 1 7 5 6 32, .n 1 7 5 7 32, .p 1 7 5 8 80, .n 1 7 5 9 16,
   .n 1 7 6 5 32, .p 1 7 6 6 112, .p 1 7 6 7 128, .n 1 7 6 8 256, .p 1 7 6 9 80, .n 1 7 6 10 16,
   .n 1 7 6 11 16, .p 1 7 7 5 144, .n 1 7 7 6 96, .n 1 7 7 7 96, .p 1 7 7 8 128, .n 1 7 7 9 224,
   .p 1 7 7 10 64, .p 1 7 7 11 80, .n 1 7 8 5 240, .n 1 7 8 6 80, .n 1 7 8 7 240, .p 1 7 8 8 384,
   .p 1 7 8 9 416, .n 1 7 8 10 80, .n 1 7 8 11 160, .p 1 7 9 5 160, .p 1 7 9 6 160, .p 1 7 9 7 400,
   .n 1 7 9 8 480, .n 1 7 9 9 400, .p 1 7 9 11 160, .n 1 7 10 6 48, .p 1 7 10 7 32, .p 1 7 10 9 16,
   .p 1 7 10 10 80, .n 1 7 10 11 80, .n 1 7 11 5 48, .n 1 7 11 6 32, .n 1 7 11 7 448, .p 1 7 11 8 256,
   .p 1 7 11 9 320, .n 1 7 11 10 64, .p 1 7 11 11 16, .p 1 7 12 5 16, .p 1 7 12 6 16, .p 1 7 12 7 336,
   .n 1 7 12 8 128, .n 1 7 12 9 256, .p 1 7 12 10 16, .n 1 7 13 7 80, .p 1 7 13 8 16, .p 1 7 13 9 64,
   .n 2 6 5 5 16, .n 2 6 5 6 176, .p 2 6 5 7 312, .n 2 6 5 8 112, .n 2 6 5 9 8, .p 2 6 6 4 16,
   .p 2 6 6 5 32, .p 2 6 6 6 440, .n 2 6 6 7 824, .p 2 6 6 8 112, .p 2 6 6 9 256, .p 2 6 6 10 8,
   .n 2 6 6 11 40, .n 2 6 7 4 48, .p 2 6 7 5 168, .n 2 6 7 6 16, .p 2 6 7 7 280, .p 2 6 7 8 320,
   .n 2 6 7 9 888, .p 2 6 7 10 64, .p 2 6 7 11 120, .p 2 6 8 4 32, .n 2 6 8 5 584, .n 2 6 8 6 872,
   .p 2 6 8 7 880, .n 2 6 8 8 64, .p 2 6 8 9 1000, .n 2 6 8 10 312, .n 2 6 8 11 80, .p 2 6 9 4 32,
   .p 2 6 9 5 512, .p 2 6 9 6 944, .n 2 6 9 7 752, .n 2 6 9 8 1168, .p 2 6 9 9 64, .p 2 6 9 10 448,
   .n 2 6 9 11 80, .n 2 6 10 4 48, .p 2 6 10 5 208, .n 2 6 10 6 280, .n 2 6 10 7 24, .p 2 6 10 8 1264,
   .n 2 6 10 9 1008, .n 2 6 10 10 232, .p 2 6 10 11 120, .p 2 6 11 4 16, .n 2 6 11 5 600, .n 2 6 11 6 176,
   .p 2 6 11 7 152, .n 2 6 11 8 160, .p 2 6 11 9 808, .n 2 6 11 11 40, .p 2 6 12 5 344, .p 2 6 12 6 200,
   .n 2 6 12 7 32, .n 2 6 12 8 288, .n 2 6 12 9 248, .p 2 6 12 10 24, .n 2 6 13 5 64, .n 2 6 13 6 64,
   .p 2 6 13 7 8, .p 2 6 13 8 96, .p 2 6 13 9 24, .p 3 5 5 5 40, .n 3 5 5 6 64, .p 3 5 5 7 8,
   .p 3 5 5 8 16, .p 3 5 6 3 8, .n 3 5 6 4 8, .p 3 5 6 5 120, .p 3 5 6 6 56, .n 3 5 6 7 368,
   .p 3 5 6 8 264, .n 3 5 6 9 248, .p 3 5 6 10 168, .p 3 5 6 11 8, .n 3 5 7 3 56, .n 3 5 7 5 560,
   .p 3 5 7 6 288, .p 3 5 7 7 632, .n 3 5 7 8 320, .p 3 5 7 9 592, .n 3 5 7 10 384, .n 3 5 7 11 192,
   .p 3 5 8 3 136, .p 3 5 8 5 360, .n 3 5 8 6 368, .p 3 5 8 7 528, .n 3 5 8 8 832, .n 3 5 8 9 648,
   .p 3 5 8 10 272, .p 3 5 8 11 552, .n 3 5 9 3 152, .p 3 5 9 4 112, .p 3 5 9 5 424, .n 3 5 9 6 400,
   .n 3 5 9 7 1392, .p 3 5 9 8 1392, .p 3 5 9 9 680, .n 3 5 9 10 80, .n 3 5 9 11 584, .p 3 5 10 3 80,
   .n 3 5 10 4 216, .n 3 5 10 5 344, .p 3 5 10 6 1000, .n 3 5 10 7 160, .n 3 5 10 8 296, .n 3 5 10 9 232,
   .n 3 5 10 10 72, .p 3 5 10 11 240, .n 3 5 11 3 16, .p 3 5 11 4 144, .n 3 5 11 5 352, .n 3 5 11 6 624,
   .p 3 5 11 7 1576, .n 3 5 11 8 336, .n 3 5 11 9 576, .p 3 5 11 10 208, .n 3 5 11 11 24, .n 3 5 12 4 32,
   .p 3 5 12 5 440, .p 3 5 12 6 80, .n 3 5 12 7 1024, .p 3 5 12 8 96, .p 3 5 12 9 552, .n 3 5 12 10 112,
   .n 3 5 13 5 128, .p 3 5 13 6 32, .p 3 5 13 7 200, .p 3 5 13 8 16, .n 3 5 13 9 120, .n 4 4 5 5 24,
   .p 4 4 5 6 80, .n 4 4 5 7 96, .p 4 4 5 8 48, .n 4 4 5 9 8, .n 4 4 6 3 32, .n 4 4 6 4 32,
   .p 4 4 6 5 88, .n 4 4 6 6 208, .p 4 4 6 7 528, .n 4 4 6 8 176, .n 4 4 6 9 312, .p 4 4 6 10 32,
   .p 4 4 6 11 112, .p 4 4 7 3 152, .p 4 4 7 4 240, .n 4 4 7 5 552, .p 4 4 7 6 80, .n 4 4 7 7 384,
   .n 4 4 7 8 256, .p 4 4 7 9 1256, .n 4 4 7 10 192, .n 4 4 7 11 344, .n 4 4 8 3 216, .n 4 4 8 4 576,
   .p 4 4 8 5 1016, .p 4 4 8 6 656, .n 4 4 8 7 336, .n 4 4 8 8 32, .n 4 4 8 9 1528, .p 4 4 8 10 864,
   .p 4 4 8 11 168, .n 4 4 8 12 16, .p 4 4 9 3 72, .p 4 4 9 4 608, .n 4 4 9 5 120, .n 4 4 9 6 2192,
   .p 4 4 9 7 208, .p 4 4 9 8 2672, .n 4 4 9 9 360, .n 4 4 9 10 1248, .p 4 4 9 11 328, .p 4 4 9 12 32,
   .p 4 4 10 3 56, .n 4 4 10 4 272, .n 4 4 10 5 1016, .p 4 4 10 6 2832, .p 4 4 10 7 64, .n 4 4 10 8 3728,
   .p 4 4 10 9 1880, .p 4 4 10 10 544, .n 4 4 10 11 344, .n 4 4 10 12 16, .n 4 4 11 3 32, .p 4 4 11 4 16,
   .p 4 4 11 5 648, .n 4 4 11 6 1264, .p 4 4 11 7 16, .p 4 4 11 8 1408, .n 4 4 11 9 840, .n 4 4 11 10 32,
   .p 4 4 11 11 80, .p 4 4 12 4 16, .p 4 4 12 5 40, .n 4 4 12 6 144, .p 4 4 12 8 224, .n 4 4 12 9 168,
   .p 4 4 12 10 32, .n 4 4 13 5 80, .p 4 4 13 6 160, .n 4 4 13 8 160, .p 4 4 13 9 80, .p 5 3 6 3 48,
   .n 5 3 6 4 32, .n 5 3 6 5 56, .n 5 3 6 6 168, .p 5 3 6 7 320, .n 5 3 6 8 48, .p 5 3 6 9 72,
   .n 5 3 6 10 264, .p 5 3 6 11 128, .n 5 3 7 3 112, .p 5 3 7 5 512, .n 5 3 7 6 192, .n 5 3 7 7 560,
   .p 5 3 7 8 192, .p 5 3 7 9 160, .p 5 3 7 10 128, .n 5 3 7 11 128, .n 5 3 8 3 136, .p 5 3 8 4 424,
   .n 5 3 8 5 504, .p 5 3 8 6 296, .n 5 3 8 7 32, .p 5 3 8 8 32, .n 5 3 8 9 408, .p 5 3 8 10 520,
   .n 5 3 8 11 200, .p 5 3 8 12 8, .p 5 3 9 3 400, .n 5 3 9 4 560, .n 5 3 9 5 624, .p 5 3 9 6 816,
   .p 5 3 9 7 352, .p 5 3 9 8 48, .n 5 3 9 9 432, .n 5 3 9 10 368, .p 5 3 9 11 432, .n 5 3 9 12 64,
   .n 5 3 10 3 232, .p 5 3 10 4 232, .p 5 3 10 5 760, .n 5 3 10 6 1096, .p 5 3 10 7 240, .n 5 3 10 8 272,
   .p 5 3 10 9 504, .p 5 3 10 10 56, .n 5 3 10 11 248, .p 5 3 10 12 56, .p 5 3 11 3 32, .n 5 3 11 4 144,
   .p 5 3 11 5 128, .p 5 3 11 6 208, .n 5 3 11 7 336, .n 5 3 11 8 48, .p 5 3 11 9 288, .n 5 3 11 10 144,
   .p 5 3 11 11 16, .p 5 3 12 4 80, .n 5 3 12 5 200, .p 5 3 12 6 72, .p 5 3 12 7 112, .p 5 3 12 8 32,
   .n 5 3 12 9 168, .p 5 3 12 10 72, .n 5 3 13 5 16, .p 5 3 13 6 64, .n 5 3 13 7 96, .p 5 3 13 8 64,
   .n 5 3 13 9 16, .n 6 2 6 3 32, .p 6 2 6 4 88, .n 6 2 6 5 56, .p 6 2 6 6 24, .n 6 2 6 7 120,
   .p 6 2 6 8 72, .p 6 2 6 9 152, .n 6 2 6 10 184, .p 6 2 6 11 56, .p 6 2 7 3 16, .n 6 2 7 4 64,
   .p 6 2 7 5 96, .n 6 2 7 6 64, .p 6 2 7 8 64, .n 6 2 7 9 96, .p 6 2 7 10 64, .n 6 2 7 11 16,
   .n 6 2 8 2 8, .p 6 2 8 3 24, .p 6 2 8 4 16, .n 6 2 8 5 176, .p 6 2 8 6 288, .n 6 2 8 7 64,
   .n 6 2 8 8 304, .p 6 2 8 9 304, .n 6 2 8 10 24, .n 6 2 8 11 88, .p 6 2 8 12 32, .p 6 2 9 2 32,
   .p 6 2 9 3 96, .n 6 2 9 4 352, .n 6 2 9 5 192, .p 6 2 9 6 864, .p 6 2 9 7 128, .n 6 2 9 8 1056,
   .p 6 2 9 9 192, .p 6 2 9 10 512, .n 6 2 9 11 224, .n 6 2 10 2 16, .n 6 2 10 3 184, .p 6 2 10 4 336,
   .p 6 2 10 5 872, .n 6 2 10 6 1992, .p 6 2 10 7 56, .p 6 2 10 8 2104, .n 6 2 10 9 1096, .n 6 2 10 10 392,
   .p 6 2 10 11 352, .n 6 2 10 12 40, .p 6 2 11 3 48, .n 6 2 11 4 32, .n 6 2 11 5 352, .p 6 2 11 6 608,
   .n 6 2 11 8 608, .p 6 2 11 9 352, .p 6 2 11 10 32, .n 6 2 11 11 48, .p 6 2 12 4 32, .n 6 2 12 5 128,
   .p 6 2 12 6 160, .n 6 2 12 8 160, .p 6 2 12 9 128, .n 6 2 12 10 32, .p 7 1 6 3 8, .n 7 1 6 4 32,
   .p 7 1 6 5 32, .p 7 1 6 6 32, .n 7 1 6 7 80, .p 7 1 6 8 32, .p 7 1 6 9 32, .n 7 1 6 10 32,
   .p 7 1 6 11 8, .p 7 1 8 2 8, .n 7 1 8 4 88, .p 7 1 8 5 128, .p 7 1 8 6 80, .n 7 1 8 7 256,
   .p 7 1 8 8 80, .p 7 1 8 9 128, .n 7 1 8 10 88, .p 7 1 8 12 8, .p 7 1 9 2 32, .n 7 1 9 3 128,
   .p 7 1 9 4 160, .n 7 1 9 6 192, .p 7 1 9 7 256, .n 7 1 9 8 192, .p 7 1 9 10 160, .n 7 1 9 11 128,
   .p 7 1 9 12 32, .n 7 1 10 2 48, .p 7 1 10 3 152, .n 7 1 10 4 64, .n 7 1 10 5 224, .p 7 1 10 6 192,
   .p 7 1 10 7 80, .n 7 1 10 8 32, .n 7 1 10 9 96, .n 7 1 10 10 16, .p 7 1 10 11 88, .n 7 1 10 12 32,
   .n 8 0 10 2 32, .p 8 0 10 3 128, .n 8 0 10 4 96, .n 8 0 10 5 256, .p 8 0 10 6 448, .n 8 0 10 8 448,
   .p 8 0 10 9 256, .p 8 0 10 10 96, .n 8 0 10 11 128, .p 8 0 10 12 32]

private def g2Mid5_4_a : List FM :=
  [.p 0 8 4 7 64, .n 0 8 5 7 256, .n 0 8 5 8 64, .p 0 8 6 7 320, .p 0 8 6 8 192, .n 0 8 7 8 64,
   .p 0 8 7 9 64, .n 0 8 8 7 320, .n 0 8 8 8 320, .n 0 8 8 9 256, .p 0 8 9 7 256, .p 0 8 9 8 320,
   .p 0 8 9 9 320, .n 0 8 10 7 64, .p 0 8 10 8 64, .n 0 8 11 8 192, .n 0 8 11 9 320, .p 0 8 12 8 64,
   .p 0 8 12 9 256, .n 0 8 13 9 64, .n 1 7 4 6 32, .p 1 7 4 7 32, .n 1 7 5 4 32, .p 1 7 5 5 32,
   .p 1 7 5 6 48, .n 1 7 5 7 32, .p 1 7 5 8 16, .n 1 7 5 9 32, .n 1 7 6 3 32, .p 1 7 6 4 112,
   .n 1 7 6 5 48, .p 1 7 6 6 48, .n 1 7 6 7 96, .n 1 7 6 8 80, .p 1 7 6 9 80, .p 1 7 6 10 48,
   .n 1 7 6 11 32, .p 1 7 7 3 112, .n 1 7 7 4 128, .n 1 7 7 5 32, .n 1 7 7 6 64, .p 1 7 7 7 160,
   .p 1 7 7 8 64, .n 1 7 7 9 128, .n 1 7 7 10 128, .p 1 7 7 11 144, .n 1 7 8 3 128, .p 1 7 8 4 48,
   .n 1 7 8 5 16, .n 1 7 8 6 112, .n 1 7 8 7 32, .p 1 7 8 8 48, .p 1 7 8 9 368, .p 1 7 8 10 80,
   .n 1 7 8 11 256, .p 1 7 9 3 32, .n 1 7 9 4 32, .p 1 7 9 5 224, .p 1 7 9 6 224, .n 1 7 9 7 224,
   .p 1 7 9 8 128, .n 1 7 9 9 576, .p 1 7 9 11 224, .p 1 7 10 3 32, .p 1 7 10 4 80, .n 1 7 10 5 208,
   .n 1 7 10 6 176, .p 1 7 10 7 480, .n 1 7 10 8 368, .p 1 7 10 9 176, .p 1 7 10 10 80, .n 1 7 10 11 96,
   .n 1 7 11 3 16, .n 1 7 11 4 64, .p 1 7 11 5 32, .p 1 7 11 6 64, .n 1 7 11 7 416, .p 1 7 11 8 128,
   .p 1 7 11 9 384, .n 1 7 11 10 128, .p 1 7 11 11 16, .p 1 7 12 4 16, .p 1 7 12 5 16, .p 1 7 12 6 16,
   .p 1 7 12 7 128, .p 1 7 12 8 144, .n 1 7 12 9 368, .p 1 7 12 10 48, .n 1 7 13 6 16, .n 1 7 13 8 80,
   .p 1 7 13 9 96, .p 2 6 4 6 32, .n 2 6 4 7 32, .n 2 6 5 4 16, .n 2 6 5 5 64, .n 2 6 5 6 152,
   .p 2 6 5 7 224, .p 2 6 5 8 72, .n 2 6 5 9 64, .p 2 6 6 2 16, .p 2 6 6 3 48, .n 2 6 6 4 24,
   .p 2 6 6 5 120, .p 2 6 6 6 232, .n 2 6 6 7 464, .n 2 6 6 8 136, .p 2 6 6 9 216, .p 2 6 6 10 40,
   .n 2 6 6 11 48, .n 2 6 7 2 48, .n 2 6 7 3 56, .p 2 6 7 4 144, .p 2 6 7 5 16, .p 2 6 7 6 144,
   .p 2 6 7 7 416, .n 2 6 7 8 224, .n 2 6 7 9 544, .n 2 6 7 10 16, .p 2 6 7 11 168, .p 2 6 8 2 48,
   .n 2 6 8 3 80, .n 2 6 8 4 232, .n 2 6 8 5 312, .n 2 6 8 6 552, .n 2 6 8 7 80, .p 2 6 8 8 616,
   .p 2 6 8 9 968, .n 2 6 8 10 200, .n 2 6 8 11 176, .n 2 6 9 2 16, .p 2 6 9 3 64, .p 2 6 9 4 272,
   .p 2 6 9 5 576, .p 2 6 9 6 32, .n 2 6 9 7 304, .n 2 6 9 8 272, .n 2 6 9 9 656, .p 2 6 9 10 304,
   .p 2 6 10 3 128, .n 2 6 10 4 168, .n 2 6 10 5 376, .p 2 6 10 6 568, .p 2 6 10 7 432, .n 2 6 10 8 120,
   .n 2 6 10 9 408, .n 2 6 10 10 152, .p 2 6 10 11 96, .n 2 6 11 3 136, .n 2 6 11 4 16, .n 2 6 11 5 176,
   .n 2 6 11 6 304, .n 2 6 11 7 288, .p 2 6 11 8 32, .p 2 6 11 9 896, .p 2 6 11 10 32, .n 2 6 11 11 40,
   .p 2 6 12 3 32, .p 2 6 12 4 40, .p 2 6 12 5 312, .n 2 6 12 6 24, .p 2 6 12 7 144, .p 2 6 12 8 24,
   .n 2 6 12 9 520, .n 2 6 12 10 8, .n 2 6 13 5 96, .p 2 6 13 6 24, .n 2 6 13 7 48, .p 2 6 13 8 8,
   .p 2 6 13 9 112, .p 3 5 5 4 80, .n 3 5 5 5 72, .n 3 5 5 6 104, .p 3 5 5 7 64, .p 3 5 5 8 24,
   .p 3 5 5 9 8, .n 3 5 6 2 32, .p 3 5 6 3 128, .n 3 5 6 4 144, .p 3 5 6 5 176, .n 3 5 6 6 24,
   .n 3 5 6 7 104, .n 3 5 6 8 24, .p 3 5 6 9 56, .n 3 5 6 10 96, .p 3 5 6 11 64, .p 3 5 7 2 64,
   .n 3 5 7 3 456, .p 3 5 7 4 112, .p 3 5 7 5 48, .p 3 5 7 6 272, .n 3 5 7 7 40, .p 3 5 7 8 136,
   .n 3 5 7 9 88, .p 3 5 7 10 376, .n 3 5 7 11 424, .n 3 5 8 2 16, .p 3 5 8 3 408, .n 3 5 8 4 32,
   .n 3 5 8 5 376, .n 3 5 8 6 16, .p 3 5 8 7 280, .p 3 5 8 8 88, .n 3 5 8 9 880, .n 3 5 8 10 360,
   .p 3 5 8 11 888, .p 3 5 8 12 16, .n 3 5 9 2 32, .p 3 5 9 3 40, .p 3 5 9 4 224, .n 3 5 9 5 8,
   .n 3 5 9 6 664, .p 3 5 9 7 440, .n 3 5 9 8 1128, .p 3 5 9 9 1904, .p 3 5 9 10 32, .n 3 5 9 11 776,
   .n 3 5 9 12 32, .p 3 5 10 2 16, .n 3 5 10 3 40, .n 3 5 10 4 624, .p 3 5 10 5 592, .p 3 5 10 6 1080,
   .n 3 5 10 7 1720, .p 3 5 10 8 1288, .n 3 5 10 9 696, .n 3 5 10 10 176, .p 3 5 10 11 264, .p 3 5 10 12 16,
   .n 3 5 11 3 160, .p 3 5 11 4 384, .n 3 5 11 5 528, .n 3 5 11 6 464, .p 3 5 11 7 1352, .p 3 5 11 8 8,
   .n 3 5 11 9 968, .p 3 5 11 10 392, .n 3 5 11 11 16, .p 3 5 12 3 80, .p 3 5 12 4 64, .p 3 5 12 5 248,
   .n 3 5 12 6 208, .n 3 5 12 7 248, .n 3 5 12 8 648, .p 3 5 12 9 880, .n 3 5 12 10 168, .n 3 5 13 4 64,
   .n 3 5 13 5 80, .p 3 5 13 6 128, .n 3 5 13 7 24, .p 3 5 13 8 256, .n 3 5 13 9 216, .n 4 4 5 4 24,
   .p 4 4 5 5 32, .p 4 4 5 6 64, .n 4 4 5 7 80, .n 4 4 5 8 40, .p 4 4 5 9 48, .n 4 4 6 2 16,
   .n 4 4 6 3 152, .p 4 4 6 4 200, .p 4 4 6 5 32, .n 4 4 6 6 112, .p 4 4 6 7 272, .n 4 4 6 8 160,
   .n 4 4 6 9 56, .n 4 4 6 10 168, .p 4 4 6 11 160, .p 4 4 7 2 136, .p 4 4 7 3 248, .n 4 4 7 4 432,
   .p 4 4 7 5 80, .n 4 4 7 6 152, .n 4 4 7 7 672, .p 4 4 7 8 408, .p 4 4 7 9 632, .p 4 4 7 10 296,
   .n 4 4 7 11 544, .n 4 4 8 1 8, .n 4 4 8 2 216, .n 4 4 8 3 88, .p 4 4 8 4 256, .n 4 4 8 5 208,
   .p 4 4 8 6 600, .p 4 4 8 7 616, .n 4 4 8 8 128, .n 4 4 8 9 1616, .p 4 4 8 10 296, .p 4 4 8 11 536,
   .n 4 4 8 12 40, .p 4 4 9 1 8, .p 4 4 9 2 104, .p 4 4 9 3 264, .n 4 4 9 4 72, .n 4 4 9 5 784,
   .p 4 4 9 6 40, .p 4 4 9 7 312, .n 4 4 9 8 192, .p 4 4 9 9 1024, .n 4 4 9 10 744, .n 4 4 9 11 56,
   .p 4 4 9 12 96, .n 4 4 10 2 8, .n 4 4 10 3 424, .p 4 4 10 4 64, .p 4 4 10 5 1568, .n 4 4 10 6 816,
   .n 4 4 10 7 704, .n 4 4 10 8 304, .p 4 4 10 9 504, .p 4 4 10 10 352, .n 4 4 10 11 176, .n 4 4 10 12 56,
   .p 4 4 11 3 120, .n 4 4 11 4 48, .n 4 4 11 5 640, .p 4 4 11 6 344, .p 4 4 11 7 256, .p 4 4 11 8 584,
   .n 4 4 11 9 584, .n 4 4 11 10 112, .p 4 4 11 11 80, .p 4 4 12 3 32, .p 4 4 12 4 184, .n 4 4 12 5 224,
   .p 4 4 12 6 8, .n 4 4 12 7 72, .n 4 4 12 8 16, .p 4 4 12 9 8, .p 4 4 12 10 80, .n 4 4 13 4 128,
   .p 4 4 13 5 144, .p 4 4 13 6 24, .p 4 4 13 7 72, .n 4 4 13 8 152, .p 4 4 13 9 40, .n 5 3 5 4 8,
   .p 5 3 5 5 8, .p 5 3 5 6 16, .n 5 3 5 7 16, .n 5 3 5 8 8, .p 5 3 5 9 8, .p 5 3 6 2 80,
   .n 5 3 6 3 120, .p 5 3 6 4 80, .n 5 3 6 5 232, .p 5 3 6 6 112, .p 5 3 6 7 184, .p 5 3 6 8 80,
   .n 5 3 6 9 184, .n 5 3 6 10 96, .p 5 3 6 11 96, .n 5 3 7 2 232, .p 5 3 7 3 376, .n 5 3 7 4 24,
   .n 5 3 7 5 8, .n 5 3 7 6 80, .n 5 3 7 7 80, .n 5 3 7 8 248, .p 5 3 7 9 472, .n 5 3 7 10 184,
   .p 5 3 7 11 8, .n 5 3 8 1 8, .p 5 3 8 2 112, .n 5 3 8 3 80, .n 5 3 8 4 328, .p 5 3 8 5 584,
   .p 5 3 8 6 56, .n 5 3 8 7 552, .n 5 3 8 8 264, .p 5 3 8 9 256, .p 5 3 8 10 696, .n 5 3 8 11 456,
   .n 5 3 8 12 16, .p 5 3 9 1 16, .p 5 3 9 2 128, .n 5 3 9 3 256, .p 5 3 9 4 32, .n 5 3 9 5 224,
   .p 5 3 9 6 88, .p 5 3 9 7 136, .p 5 3 9 8 1488, .n 5 3 9 9 1600, .n 5 3 9 10 424, .p 5 3 9 11 648,
   .n 5 3 9 12 32, .n 5 3 10 2 128, .n 5 3 10 3 136, .p 5 3 10 4 960, .n 5 3 10 5 400, .n 5 3 10 6 1224,
   .p 5 3 10 7 1552, .n 5 3 10 8 1128, .p 5 3 10 9 528, .p 5 3 10 10 200, .n 5 3 10 11 264, .p 5 3 10 12 40,
   .p 5 3 11 2 16, .p 5 3 11 3 240, .n 5 3 11 4 720, .p 5 3 11 5 272, .p 5 3 11 6 984, .n 5 3 11 7 1016,
   .n 5 3 11 8 256, .p 5 3 11 9 768, .n 5 3 11 10 280, .n 5 3 11 11 8, .n 5 3 12 3 32, .p 5 3 12 4 176,
   .n 5 3 12 5 224, .p 5 3 12 6 32, .n 5 3 12 7 128, .p 5 3 12 8 464, .n 5 3 12 9 384, .p 5 3 12 10 96,
   .n 5 3 13 4 80, .p 5 3 13 5 176, .n 5 3 13 6 96, .p 5 3 13 7 32, .n 5 3 13 8 80, .p 5 3 13 9 48,
   .n 6 2 6 2 64, .p 6 2 6 3 176, .n 6 2 6 4 112, .n 6 2 6 5 32, .p 6 2 6 6 16, .n 6 2 6 7 64,
   .p 6 2 6 8 176, .n 6 2 6 9 96, .n 6 2 6 10 16, .p 6 2 6 11 16, .p 6 2 7 2 80, .n 6 2 7 3 192,
   .p 6 2 7 4 200, .n 6 2 7 5 168, .n 6 2 7 6 24, .p 6 2 7 7 152, .p 6 2 7 8 24, .p 6 2 7 9 72,
   .n 6 2 7 10 280, .p 6 2 7 11 136, .p 6 2 8 2 8, .n 6 2 8 3 128, .n 6 2 8 4 32, .p 6 2 8 5 504,
   .p 6 2 8 6 40, .n 6 2 8 7 632, .n 6 2 8 8 280, .p 6 2 8 9 584, .p 6 2 8 10 208, .n 6 2 8 11 328,
   .p 6 2 8 12 56, .p 6 2 9 1 24, .p 6 2 9 2 24, .n 6 2 9 3 112, .n 6 2 9 4 120, .p 6 2 9 5 392,
   .n 6 2 9 6 344, .p 6 2 9 7 200, .p 6 2 9 8 280, .n 6 2 9 9 672, .p 6 2 9 10 256, .p 6 2 9 11 168,
   .n 6 2 9 12 96, .n 6 2 10 1 16, .n 6 2 10 2 88, .p 6 2 10 3 248, .p 6 2 10 4 328, .n 6 2 10 5 952,
   .n 6 2 10 6 8, .p 6 2 10 7 792, .n 6 2 10 8 72, .n 6 2 10 9 152, .n 6 2 10 10 192, .p 6 2 10 11 80,
   .p 6 2 10 12 32, .p 6 2 11 2 16, .p 6 2 11 3 16, .n 6 2 11 4 192, .p 6 2 11 5 192, .p 6 2 11 6 160,
   .n 6 2 11 7 224, .n 6 2 11 8 64, .p 6 2 11 9 64, .p 6 2 11 10 80, .n 6 2 11 11 48, .n 6 2 12 3 16,
   .p 6 2 12 4 32, .n 6 2 12 5 32, .p 6 2 12 6 80, .n 6 2 12 7 80, .n 6 2 12 8 64, .p 6 2 12 9 128,
   .n 6 2 12 10 48, .n 6 2 13 4 16, .p 6 2 13 5 48, .n 6 2 13 6 32, .n 6 2 13 7 32, .p 6 2 13 8 48,
   .n 6 2 13 9 16, .p 7 1 6 2 16, .n 7 1 6 3 48, .p 7 1 6 4 16, .p 7 1 6 5 80, .n 7 1 6 6 80,
   .n 7 1 6 7 16, .p 7 1 6 8 48, .n 7 1 6 9 16, .n 7 1 7 3 32, .p 7 1 7 4 64, .p 7 1 7 5 64,
   .n 7 1 7 6 192, .p 7 1 7 8 192, .n 7 1 7 9 64, .n 7 1 7 10 64, .p 7 1 7 11 32, .p 7 1 8 1 16,
   .n 7 1 8 2 64, .p 7 1 8 3 32, .p 7 1 8 4 128, .n 7 1 8 5 112, .n 7 1 8 6 80, .p 7 1 8 7 48,
   .p 7 1 8 8 48, .p 7 1 8 9 32, .n 7 1 8 10 48, .n 7 1 8 11 16, .p 7 1 8 12 16, .p 7 1 9 1 16,
   .n 7 1 9 2 16, .p 7 1 9 3 32, .n 7 1 9 4 144, .n 7 1 9 5 80, .p 7 1 9 6 560, .n 7 1 9 7 176,
   .n 7 1 9 8 592, .p 7 1 9 9 384, .p 7 1 9 10 160, .n 7 1 9 11 176, .p 7 1 9 12 32, .n 7 1 10 1 48,
   .p 7 1 10 2 112, .p 7 1 10 3 96, .n 7 1 10 4 416, .p 7 1 10 5 160, .p 7 1 10 6 352, .n 7 1 10 7 320,
   .p 7 1 10 8 64, .p 7 1 10 9 16, .n 7 1 10 10 80, .p 7 1 10 11 96, .n 7 1 10 12 32, .n 7 1 11 3 64,
   .p 7 1 11 4 176, .n 7 1 11 5 16, .n 7 1 11 6 336, .p 7 1 11 7 240, .p 7 1 11 8 144, .n 7 1 11 9 176,
   .p 7 1 11 10 16, .p 7 1 11 11 16, .p 8 0 9 3 32, .n 8 0 9 4 96, .p 8 0 9 6 256, .n 8 0 9 7 192,
   .n 8 0 9 8 192, .p 8 0 9 9 256, .n 8 0 9 11 96, .p 8 0 9 12 32, .n 8 0 10 1 32, .p 8 0 10 2 96,
   .n 8 0 10 4 256, .p 8 0 10 5 192, .p 8 0 10 6 192, .n 8 0 10 7 256, .p 8 0 10 9 96, .n 8 0 10 10 32]

private def g2Mid5_4_b : List FM :=
  [.p 0 8 4 6 64, .n 0 8 5 6 224, .n 0 8 5 7 32, .n 0 8 5 8 64, .p 0 8 6 6 192, .p 0 8 6 7 128,
   .p 0 8 6 8 192, .p 0 8 7 6 160, .n 0 8 7 7 160, .n 0 8 7 8 32, .p 0 8 7 9 32, .n 0 8 8 6 320,
   .n 0 8 8 8 448, .n 0 8 8 9 128, .p 0 8 9 6 96, .p 0 8 9 7 160, .p 0 8 9 8 480, .p 0 8 9 9 160,
   .p 0 8 10 6 64, .n 0 8 10 7 128, .p 0 8 10 8 64, .n 0 8 11 6 32, .p 0 8 11 7 32, .n 0 8 11 8 352,
   .n 0 8 11 9 160, .p 0 8 12 8 192, .p 0 8 12 9 128, .n 0 8 13 8 32, .n 0 8 13 9 32, .n 1 7 4 6 32,
   .p 1 7 4 7 32, .n 1 7 5 4 32, .n 1 7 5 5 32, .p 1 7 5 6 48, .p 1 7 5 7 96, .n 1 7 5 8 32,
   .n 1 7 5 9 48, .n 1 7 6 3 32, .p 1 7 6 4 112, .p 1 7 6 5 48, .p 1 7 6 6 96, .n 1 7 6 7 368,
   .p 1 7 6 8 16, .p 1 7 6 9 144, .n 1 7 6 11 16, .p 1 7 7 3 112, .n 1 7 7 4 96, .p 1 7 7 5 64,
   .n 1 7 7 6 112, .p 1 7 7 7 16, .p 1 7 7 8 48, .n 1 7 7 9 112, .p 1 7 7 11 80, .n 1 7 8 3 128,
   .n 1 7 8 4 64, .n 1 7 8 5 128, .n 1 7 8 6 272, .p 1 7 8 7 608, .p 1 7 8 8 96, .p 1 7 8 9 32,
   .p 1 7 8 10 16, .n 1 7 8 11 160, .p 1 7 9 3 32, .p 1 7 9 4 96, .p 1 7 9 5 32, .p 1 7 9 6 400,
   .n 1 7 9 7 400, .n 1 7 9 8 112, .n 1 7 9 9 144, .n 1 7 9 10 64, .p 1 7 9 11 160, .p 1 7 10 3 32,
   .p 1 7 10 4 48, .n 1 7 10 5 16, .p 1 7 10 7 16, .n 1 7 10 8 240, .p 1 7 10 9 144, .p 1 7 10 10 96,
   .n 1 7 10 11 80, .n 1 7 11 3 16, .n 1 7 11 4 96, .p 1 7 11 5 64, .n 1 7 11 6 208, .n 1 7 11 7 80,
   .p 1 7 11 8 272, .p 1 7 11 9 112, .n 1 7 11 10 64, .p 1 7 11 11 16, .p 1 7 12 4 32, .n 1 7 12 5 32,
   .p 1 7 12 6 80, .p 1 7 12 7 96, .n 1 7 12 9 192, .p 1 7 12 10 16, .n 1 7 13 7 16, .n 1 7 13 8 48,
   .p 1 7 13 9 64, .n 2 6 4 6 32, .p 2 6 4 7 32, .n 2 6 5 5 112, .p 2 6 5 6 160, .n 2 6 5 7 88,
   .p 2 6 5 8 96, .n 2 6 5 9 56, .p 2 6 6 2 16, .p 2 6 6 3 48, .n 2 6 6 4 40, .p 2 6 6 5 232,
   .n 2 6 6 6 192, .n 2 6 6 7 72, .n 2 6 6 8 232, .p 2 6 6 9 280, .n 2 6 6 11 40, .n 2 6 7 2 48,
   .n 2 6 7 3 56, .p 2 6 7 4 208, .p 2 6 7 5 80, .n 2 6 7 6 336, .p 2 6 7 7 736, .n 2 6 7 8 208,
   .n 2 6 7 9 560, .p 2 6 7 10 64, .p 2 6 7 11 120, .p 2 6 8 2 48, .n 2 6 8 3 80, .n 2 6 8 4 576,
   .n 2 6 8 5 384, .p 2 6 8 6 776, .n 2 6 8 7 992, .p 2 6 8 8 1040, .p 2 6 8 9 512, .n 2 6 8 10 264,
   .n 2 6 8 11 80, .n 2 6 9 2 16, .p 2 6 9 3 64, .p 2 6 9 4 752, .p 2 6 9 5 64, .n 2 6 9 6 176,
   .p 2 6 9 7 32, .n 2 6 9 8 1008, .n 2 6 9 9 16, .p 2 6 9 10 384, .n 2 6 9 11 80, .p 2 6 10 3 128,
   .n 2 6 10 4 216, .p 2 6 10 5 152, .n 2 6 10 6 320, .p 2 6 10 7 648, .p 2 6 10 8 168, .n 2 6 10 9 472,
   .n 2 6 10 10 208, .p 2 6 10 11 120, .n 2 6 11 3 136, .n 2 6 11 4 384, .p 2 6 11 5 64, .n 2 6 11 7 432,
   .p 2 6 11 8 448, .p 2 6 11 9 480, .n 2 6 11 11 40, .p 2 6 12 3 32, .p 2 6 12 4 320, .n 2 6 12 5 128,
   .p 2 6 12 6 152, .p 2 6 12 7 256, .n 2 6 12 8 464, .n 2 6 12 9 192, .p 2 6 12 10 24, .n 2 6 13 4 64,
   .p 2 6 13 5 32, .n 2 6 13 6 32, .n 2 6 13 7 120, .p 2 6 13 8 160, .p 2 6 13 9 24, .p 3 5 5 4 56,
   .p 3 5 5 5 48, .n 3 5 5 6 120, .n 3 5 5 7 112, .p 3 5 5 8 112, .p 3 5 5 9 16, .n 3 5 6 2 24,
   .p 3 5 6 3 104, .n 3 5 6 4 104, .p 3 5 6 5 32, .n 3 5 6 6 128, .p 3 5 6 7 392, .n 3 5 6 8 256,
   .n 3 5 6 9 120, .p 3 5 6 10 96, .p 3 5 6 11 8, .p 3 5 7 2 16, .n 3 5 7 3 376, .p 3 5 7 4 128,
   .n 3 5 7 5 224, .p 3 5 7 6 328, .p 3 5 7 7 288, .p 3 5 7 8 88, .p 3 5 7 9 24, .n 3 5 7 10 80,
   .n 3 5 7 11 192, .p 3 5 8 2 72, .p 3 5 8 3 368, .n 3 5 8 4 120, .n 3 5 8 5 200, .p 3 5 8 6 904,
   .n 3 5 8 7 1544, .p 3 5 8 8 64, .p 3 5 8 9 96, .n 3 5 8 10 184, .p 3 5 8 11 544, .n 3 5 9 2 96,
   .n 3 5 9 3 24, .p 3 5 9 4 328, .p 3 5 9 5 240, .n 3 5 9 6 1352, .p 3 5 9 7 1064, .n 3 5 9 8 304,
   .p 3 5 9 9 504, .p 3 5 9 10 208, .n 3 5 9 11 568, .p 3 5 10 2 32, .n 3 5 10 3 24, .n 3 5 10 4 536,
   .p 3 5 10 5 592, .n 3 5 10 6 288, .p 3 5 10 7 120, .p 3 5 10 8 704, .n 3 5 10 9 696, .n 3 5 10 10 136,
   .p 3 5 10 11 232, .n 3 5 11 3 96, .p 3 5 11 4 32, .n 3 5 11 5 432, .p 3 5 11 6 936, .n 3 5 11 7 112,
   .n 3 5 11 8 376, .n 3 5 11 9 136, .p 3 5 11 10 208, .n 3 5 11 11 24, .p 3 5 12 3 48, .p 3 5 12 4 344,
   .n 3 5 12 5 136, .n 3 5 12 6 232, .n 3 5 12 7 248, .n 3 5 12 8 96, .p 3 5 12 9 432, .n 3 5 12 10 112,
   .n 3 5 13 4 128, .p 3 5 13 5 80, .n 3 5 13 6 48, .p 3 5 13 7 152, .p 3 5 13 8 64, .n 3 5 13 9 120,
   .n 4 4 5 4 40, .p 4 4 5 5 80, .n 4 4 5 6 24, .p 4 4 5 7 8, .n 4 4 5 8 64, .p 4 4 5 9 40,
   .n 4 4 6 2 32, .n 4 4 6 3 96, .p 4 4 6 4 168, .n 4 4 6 5 112, .p 4 4 6 6 136, .p 4 4 6 7 184,
   .n 4 4 6 8 144, .n 4 4 6 9 216, .p 4 4 6 11 112, .p 4 4 7 2 224, .p 4 4 7 3 96, .n 4 4 7 4 432,
   .n 4 4 7 5 112, .p 4 4 7 6 296, .n 4 4 7 7 800, .p 4 4 7 8 392, .p 4 4 7 9 776, .n 4 4 7 10 96,
   .n 4 4 7 11 344, .n 4 4 8 1 8, .n 4 4 8 2 384, .p 4 4 8 3 8, .p 4 4 8 4 992, .n 4 4 8 5 120,
   .n 4 4 8 6 920, .p 4 4 8 7 1160, .n 4 4 8 8 392, .n 4 4 8 9 1112, .p 4 4 8 10 592, .p 4 4 8 11 200,
   .n 4 4 8 12 16, .p 4 4 9 1 8, .p 4 4 9 2 224, .p 4 4 9 3 272, .n 4 4 9 4 1224, .p 4 4 9 5 368,
   .p 4 4 9 6 248, .n 4 4 9 7 280, .p 4 4 9 8 960, .n 4 4 9 10 880, .p 4 4 9 11 272, .p 4 4 9 12 32,
   .n 4 4 10 2 32, .n 4 4 10 3 416, .p 4 4 10 4 360, .p 4 4 10 5 464, .p 4 4 10 6 424, .n 4 4 10 7 616,
   .n 4 4 10 8 1264, .p 4 4 10 9 1016, .p 4 4 10 10 400, .n 4 4 10 11 320, .n 4 4 10 12 16, .p 4 4 11 3 120,
   .p 4 4 11 4 336, .n 4 4 11 5 896, .p 4 4 11 6 8, .p 4 4 11 7 464, .p 4 4 11 8 344, .n 4 4 11 9 408,
   .n 4 4 11 10 48, .p 4 4 11 11 80, .p 4 4 12 3 16, .n 4 4 12 4 80, .p 4 4 12 5 264, .n 4 4 12 6 216,
   .n 4 4 12 7 232, .p 4 4 12 8 392, .n 4 4 12 9 176, .p 4 4 12 10 32, .n 4 4 13 4 80, .p 4 4 13 5 64,
   .p 4 4 13 6 48, .p 4 4 13 7 112, .n 4 4 13 8 224, .p 4 4 13 9 80, .p 5 3 5 4 16, .n 5 3 5 5 48,
   .p 5 3 5 6 32, .p 5 3 5 7 32, .n 5 3 5 8 48, .p 5 3 5 9 16, .p 5 3 6 2 80, .n 5 3 6 3 120,
   .p 5 3 6 4 56, .n 5 3 6 5 168, .p 5 3 6 6 136, .n 5 3 6 7 8, .p 5 3 6 8 200, .n 5 3 6 9 88,
   .n 5 3 6 10 216, .p 5 3 6 11 128, .n 5 3 7 2 216, .p 5 3 7 3 360, .n 5 3 7 4 40, .p 5 3 7 5 72,
   .n 5 3 7 6 120, .n 5 3 7 7 232, .n 5 3 7 8 88, .p 5 3 7 9 312, .p 5 3 7 10 80, .n 5 3 7 11 128,
   .n 5 3 8 1 16, .p 5 3 8 2 48, .n 5 3 8 3 128, .p 5 3 8 4 72, .p 5 3 8 5 472, .n 5 3 8 6 1072,
   .p 5 3 8 7 1000, .n 5 3 8 8 240, .n 5 3 8 9 584, .p 5 3 8 10 672, .n 5 3 8 11 232, .p 5 3 8 12 8,
   .p 5 3 9 1 48, .p 5 3 9 2 144, .n 5 3 9 3 144, .n 5 3 9 4 424, .n 5 3 9 5 184, .p 5 3 9 6 1176,
   .n 5 3 9 7 824, .p 5 3 9 8 616, .n 5 3 9 9 248, .n 5 3 9 10 552, .p 5 3 9 11 456, .n 5 3 9 12 64,
   .n 5 3 10 1 16, .n 5 3 10 2 104, .n 5 3 10 3 96, .p 5 3 10 4 664, .n 5 3 10 5 480, .p 5 3 10 6 256,
   .n 5 3 10 7 144, .n 5 3 10 8 688, .p 5 3 10 9 720, .p 5 3 10 10 72, .n 5 3 10 11 240, .p 5 3 10 12 56,
   .p 5 3 11 3 128, .n 5 3 11 4 80, .p 5 3 11 5 16, .n 5 3 11 6 560, .p 5 3 11 7 528, .p 5 3 11 8 112,
   .n 5 3 11 9 48, .n 5 3 11 10 112, .p 5 3 11 11 16, .n 5 3 12 4 120, .p 5 3 12 5 208, .n 5 3 12 6 8,
   .n 5 3 12 7 96, .p 5 3 12 8 56, .n 5 3 12 9 112, .p 5 3 12 10 72, .n 5 3 13 4 16, .p 5 3 13 5 16,
   .p 5 3 13 6 64, .n 5 3 13 7 128, .p 5 3 13 8 80, .n 5 3 13 9 16, .n 6 2 6 2 48, .p 6 2 6 3 120,
   .n 6 2 6 4 64, .n 6 2 6 7 176, .p 6 2 6 8 256, .n 6 2 6 10 144, .p 6 2 6 11 56, .n 6 2 7 2 8,
   .n 6 2 7 3 40, .p 6 2 7 4 136, .n 6 2 7 5 40, .n 6 2 7 6 152, .p 6 2 7 7 120, .n 6 2 7 8 8,
   .n 6 2 7 9 24, .p 6 2 7 10 32, .n 6 2 7 11 16, .p 6 2 8 2 176, .n 6 2 8 3 224, .n 6 2 8 4 424,
   .p 6 2 8 5 488, .p 6 2 8 6 552, .n 6 2 8 7 584, .n 6 2 8 8 312, .p 6 2 8 9 408, .n 6 2 8 10 24,
   .n 6 2 8 11 88, .p 6 2 8 12 32, .p 6 2 9 1 56, .n 6 2 9 2 192, .n 6 2 9 3 88, .p 6 2 9 4 712,
   .n 6 2 9 5 440, .n 6 2 9 6 376, .p 6 2 9 7 616, .n 6 2 9 8 488, .p 6 2 9 9 32, .p 6 2 9 10 344,
   .n 6 2 9 11 176, .n 6 2 10 1 48, .p 6 2 10 2 32, .p 6 2 10 3 208, .n 6 2 10 4 80, .n 6 2 10 5 184,
   .n 6 2 10 6 488, .p 6 2 10 7 488, .p 6 2 10 8 792, .n 6 2 10 9 760, .n 6 2 10 10 216, .p 6 2 10 11 296,
   .n 6 2 10 12 40, .p 6 2 11 2 16, .p 6 2 11 3 16, .n 6 2 11 4 208, .p 6 2 11 5 208, .p 6 2 11 6 224,
   .n 6 2 11 7 320, .n 6 2 11 8 80, .p 6 2 11 9 144, .p 6 2 11 10 48, .n 6 2 11 11 48, .p 6 2 12 4 16,
   .n 6 2 12 5 80, .p 6 2 12 6 128, .n 6 2 12 7 32, .n 6 2 12 8 112, .p 6 2 12 9 112, .n 6 2 12 10 32,
   .p 7 1 6 2 8, .n 7 1 6 3 24, .p 7 1 6 5 64, .n 7 1 6 6 48, .n 7 1 6 7 48, .p 7 1 6 8 64,
   .n 7 1 6 10 24, .p 7 1 6 11 8, .p 7 1 7 2 32, .n 7 1 7 3 96, .p 7 1 7 4 32, .p 7 1 7 5 160,
   .n 7 1 7 6 160, .n 7 1 7 7 32, .p 7 1 7 8 96, .n 7 1 7 9 32, .p 7 1 8 1 24, .n 7 1 8 2 88,
   .p 7 1 8 3 120, .n 7 1 8 4 72, .n 7 1 8 5 64, .p 7 1 8 6 288, .n 7 1 8 7 320, .p 7 1 8 9 232,
   .n 7 1 8 10 136, .p 7 1 8 11 8, .p 7 1 8 12 8, .n 7 1 9 1 16, .p 7 1 9 2 32, .n 7 1 9 3 16,
   .p 7 1 9 4 80, .n 7 1 9 5 176, .n 7 1 9 6 16, .p 7 1 9 7 336, .n 7 1 9 8 304, .p 7 1 9 10 176,
   .n 7 1 9 11 128, .p 7 1 9 12 32, .n 7 1 10 1 32, .p 7 1 10 2 72, .p 7 1 10 3 40, .n 7 1 10 4 176,
   .p 7 1 10 5 48, .p 7 1 10 6 64, .p 7 1 10 8 80, .n 7 1 10 9 144, .n 7 1 10 10 8, .p 7 1 10 11 88,
   .n 7 1 10 12 32, .p 7 1 11 2 16, .n 7 1 11 3 16, .n 7 1 11 4 80, .p 7 1 11 5 112, .p 7 1 11 6 80,
   .n 7 1 11 7 176, .p 7 1 11 8 16, .p 7 1 11 9 80, .n 7 1 11 10 32, .n 8 0 9 1 32, .p 8 0 9 2 96,
   .n 8 0 9 4 256, .p 8 0 9 5 192, .p 8 0 9 6 192, .n 8 0 9 7 256, .p 8 0 9 9 96, .n 8 0 9 10 32,
   .p 8 0 10 3 32, .n 8 0 10 4 96, .p 8 0 10 6 256, .n 8 0 10 7 192, .n 8 0 10 8 192, .p 8 0 10 9 256,
   .n 8 0 10 11 96, .p 8 0 10 12 32]

set_option maxRecDepth 65536 in
private theorem g2_det5_4_step01 :
    fmMerge (fmMerge [] (fmMul (fmSubMat g2FM ⟨4, by decide⟩ ⟨0, by decide⟩ ⟨0, by decide⟩) g2Val4_11))
      (fmMul (fmNeg (fmSubMat g2FM ⟨4, by decide⟩ ⟨0, by decide⟩ ⟨1, by decide⟩)) g2Val4_7) =
      g2Mid5_4_a := rfl

set_option maxRecDepth 65536 in
private theorem g2_det5_4_step2 :
    fmMerge g2Mid5_4_a (fmMul (fmSubMat g2FM ⟨4, by decide⟩ ⟨0, by decide⟩ ⟨2, by decide⟩) g2Val4_4) =
      g2Mid5_4_b := rfl

set_option maxRecDepth 65536 in
private theorem g2_det5_4_step34 :
    fmMerge (fmMerge g2Mid5_4_b (fmMul (fmNeg (fmSubMat g2FM ⟨4, by decide⟩ ⟨0, by decide⟩ ⟨3, by decide⟩)) g2Val4_2))
      (fmMul (fmSubMat g2FM ⟨4, by decide⟩ ⟨0, by decide⟩ ⟨4, by decide⟩) g2Val4_0) =
      g2Val5_4 := rfl

private theorem g2_det5_4 : fmDet 5 (fmSubMat g2FM ⟨4, by decide⟩) = g2Val5_4 :=
  fmDet5_of_sub4_split _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (fin4Mat_eq_of_vals _ _ (by decide)) g2_det4_11
    (fin4Mat_eq_of_vals _ _ (by decide)) g2_det4_7
    (fin4Mat_eq_of_vals _ _ (by decide)) g2_det4_4
    (fin4Mat_eq_of_vals _ _ (by decide)) g2_det4_2
    (fin4Mat_eq_of_vals _ _ (by decide)) g2_det4_0
    g2_det5_4_step01 g2_det5_4_step2 g2_det5_4_step34

private def g2Val5_5 : List FM :=
  [.p 0 7 4 7 32, .n 0 7 5 7 160, .p 0 7 6 7 256, .n 0 7 8 7 448, .p 0 7 9 7 448, .n 0 7 11 7 256,
   .p 0 7 12 7 160, .n 0 7 13 7 32, .n 1 6 5 6 32, .p 1 6 5 8 32, .n 1 6 6 5 32, .p 1 6 6 6 128,
   .n 1 6 6 8 128, .p 1 6 6 9 32, .p 1 6 7 5 160, .n 1 6 7 6 128, .p 1 6 7 8 128, .n 1 6 7 9 160,
   .n 1 6 8 5 288, .n 1 6 8 6 128, .p 1 6 8 8 128, .p 1 6 8 9 288, .p 1 6 9 5 160, .p 1 6 9 6 320,
   .n 1 6 9 8 320, .n 1 6 9 9 160, .p 1 6 10 5 160, .n 1 6 10 6 128, .p 1 6 10 8 128, .n 1 6 10 9 160,
   .n 1 6 11 5 288, .n 1 6 11 6 128, .p 1 6 11 8 128, .p 1 6 11 9 288, .p 1 6 12 5 160, .p 1 6 12 6 128,
   .n 1 6 12 8 128, .n 1 6 12 9 160, .n 1 6 13 5 32, .n 1 6 13 6 32, .p 1 6 13 8 32, .p 1 6 13 9 32,
   .n 2 5 5 6 80, .p 2 5 5 7 160, .n 2 5 5 8 80, .p 2 5 6 3 8, .p 2 5 6 4 16, .p 2 5 6 5 32,
   .p 2 5 6 6 208, .n 2 5 6 7 528, .p 2 5 6 8 208, .p 2 5 6 9 32, .p 2 5 6 10 16, .p 2 5 6 11 8,
   .n 2 5 7 3 40, .n 2 5 7 4 64, .n 2 5 7 5 64, .p 2 5 7 6 32, .p 2 5 7 7 272, .p 2 5 7 8 32,
   .n 2 5 7 9 64, .n 2 5 7 10 64, .n 2 5 7 11 40, .p 2 5 8 3 80, .p 2 5 8 4 80, .n 2 5 8 5 96,
   .n 2 5 8 6 496, .p 2 5 8 7 864, .n 2 5 8 8 496, .n 2 5 8 9 96, .p 2 5 8 10 80, .p 2 5 8 11 80,
   .n 2 5 9 3 80, .p 2 5 9 5 320, .p 2 5 9 6 320, .n 2 5 9 7 1120, .p 2 5 9 8 320, .p 2 5 9 9 320,
   .n 2 5 9 11 80, .p 2 5 10 3 40, .n 2 5 10 4 80, .n 2 5 10 5 160, .p 2 5 10 6 240, .n 2 5 10 7 80,
   .p 2 5 10 8 240, .n 2 5 10 9 160, .n 2 5 10 10 80, .p 2 5 10 11 40, .n 2 5 11 3 8, .p 2 5 11 4 64,
   .n 2 5 11 5 192, .n 2 5 11 6 288, .p 2 5 11 7 848, .n 2 5 11 8 288, .n 2 5 11 9 192, .p 2 5 11 10 64,
   .n 2 5 11 11 8, .n 2 5 12 4 16, .p 2 5 12 5 224, .p 2 5 12 6 48, .n 2 5 12 7 512, .p 2 5 12 8 48,
   .p 2 5 12 9 224, .n 2 5 12 10 16, .n 2 5 13 5 64, .p 2 5 13 6 16, .p 2 5 13 7 96, .p 2 5 13 8 16,
   .n 2 5 13 9 64, .p 3 4 5 5 8, .n 3 4 5 6 16, .p 3 4 5 8 16, .n 3 4 5 9 8, .n 3 4 6 3 32,
   .n 3 4 6 4 24, .p 3 4 6 5 128, .n 3 4 6 6 56, .p 3 4 6 8 56, .n 3 4 6 9 128, .p 3 4 6 10 24,
   .p 3 4 6 11 32, .p 3 4 7 3 112, .p 3 4 7 4 144, .n 3 4 7 5 560, .p 3 4 7 6 240, .n 3 4 7 8 240,
   .p 3 4 7 9 560, .n 3 4 7 10 144, .n 3 4 7 11 112, .n 3 4 8 3 128, .n 3 4 8 4 328, .p 3 4 8 5 672,
   .p 3 4 8 6 152, .n 3 4 8 8 152, .n 3 4 8 9 672, .p 3 4 8 10 328, .p 3 4 8 11 128, .p 3 4 9 3 32,
   .p 3 4 9 4 352, .p 3 4 9 5 32, .n 3 4 9 6 1248, .p 3 4 9 8 1248, .n 3 4 9 9 32, .n 3 4 9 10 352,
   .n 3 4 9 11 32, .p 3 4 10 3 32, .n 3 4 10 4 168, .n 3 4 10 5 576, .p 3 4 10 6 1528, .n 3 4 10 8 1528,
   .p 3 4 10 9 576, .p 3 4 10 10 168, .n 3 4 10 11 32, .n 3 4 11 3 16, .p 3 4 11 4 16, .p 3 4 11 5 304,
   .n 3 4 11 6 592, .p 3 4 11 8 592, .n 3 4 11 9 304, .n 3 4 11 10 16, .p 3 4 11 11 16, .p 3 4 12 4 8,
   .p 3 4 12 5 32, .n 3 4 12 6 88, .p 3 4 12 8 88, .n 3 4 12 9 32, .n 3 4 12 10 8, .n 3 4 13 5 40,
   .p 3 4 13 6 80, .n 3 4 13 8 80, .p 3 4 13 9 40, .n 4 3 5 5 8, .p 4 3 5 6 32, .n 4 3 5 7 48,
   .p 4 3 5 8 32, .n 4 3 5 9 8, .p 4 3 6 3 48, .n 4 3 6 4 56, .n 4 3 6 5 32, .n 4 3 6 6 136,
   .p 4 3 6 7 352, .n 4 3 6 8 136, .n 4 3 6 9 32, .n 4 3 6 10 56, .p 4 3 6 11 48, .n 4 3 7 3 80,
   .p 4 3 7 4 32, .p 4 3 7 5 256, .n 4 3 7 6 32, .n 4 3 7 7 352, .n 4 3 7 8 32, .p 4 3 7 9 256,
   .p 4 3 7 10 32, .n 4 3 7 11 80, .n 4 3 8 3 64, .p 4 3 8 4 184, .n 4 3 8 5 224, .p 4 3 8 6 264,
   .n 4 3 8 7 320, .p 4 3 8 8 264, .n 4 3 8 9 224, .p 4 3 8 10 184, .n 4 3 8 11 64, .p 4 3 9 3 192,
   .n 4 3 9 4 224, .n 4 3 9 5 304, .p 4 3 9 6 160, .p 4 3 9 7 352, .p 4 3 9 8 160, .n 4 3 9 9 304,
   .n 4 3 9 10 224, .p 4 3 9 11 192, .n 4 3 10 3 112, .p 4 3 10 4 88, .p 4 3 10 5 352, .n 4 3 10 6 408,
   .p 4 3 10 7 160, .n 4 3 10 8 408, .p 4 3 10 9 352, .p 4 3 10 10 88, .n 4 3 10 11 112, .p 4 3 11 3 16,
   .n 4 3 11 4 64, .p 4 3 11 5 64, .p 4 3 11 6 64, .n 4 3 11 7 160, .p 4 3 11 8 64, .p 4 3 11 9 64,
   .n 4 3 11 10 64, .p 4 3 11 11 16, .p 4 3 12 4 40, .n 4 3 12 5 96, .p 4 3 12 6 24, .p 4 3 12 7 64,
   .p 4 3 12 8 24, .n 4 3 12 9 96, .p 4 3 12 10 40, .n 4 3 13 5 8, .p 4 3 13 6 32, .n 4 3 13 7 48,
   .p 4 3 13 8 32, .n 4 3 13 9 8, .n 5 2 6 3 32, .p 5 2 6 4 96, .n 5 2 6 5 64, .n 5 2 6 6 32,
   .p 5 2 6 8 32, .p 5 2 6 9 64, .n 5 2 6 10 96, .p 5 2 6 11 32, .p 5 2 7 3 8, .n 5 2 7 4 48,
   .p 5 2 7 5 112, .n 5 2 7 6 112, .p 5 2 7 8 112, .n 5 2 7 9 112, .p 5 2 7 10 48, .n 5 2 7 11 8,
   .n 5 2 8 2 8, .p 5 2 8 3 32, .n 5 2 8 4 8, .n 5 2 8 5 128, .p 5 2 8 6 192, .n 5 2 8 8 192,
   .p 5 2 8 9 128, .p 5 2 8 10 8, .n 5 2 8 11 32, .p 5 2 8 12 8, .p 5 2 9 2 16, .p 5 2 9 3 64,
   .n 5 2 9 4 208, .n 5 2 9 5 128, .p 5 2 9 6 544, .n 5 2 9 8 544, .p 5 2 9 9 128, .p 5 2 9 10 208,
   .n 5 2 9 11 64, .n 5 2 9 12 16, .n 5 2 10 2 8, .n 5 2 10 3 96, .p 5 2 10 4 168, .p 5 2 10 5 448,
   .n 5 2 10 6 976, .p 5 2 10 8 976, .n 5 2 10 9 448, .n 5 2 10 10 168, .p 5 2 10 11 96, .p 5 2 10 12 8,
   .p 5 2 11 3 24, .n 5 2 11 4 16, .n 5 2 11 5 176, .p 5 2 11 6 304, .n 5 2 11 8 304, .p 5 2 11 9 176,
   .p 5 2 11 10 16, .n 5 2 11 11 24, .p 5 2 12 4 16, .n 5 2 12 5 64, .p 5 2 12 6 80, .n 5 2 12 8 80,
   .p 5 2 12 9 64, .n 5 2 12 10 16, .p 6 1 6 3 8, .n 6 1 6 4 32, .p 6 1 6 5 32, .p 6 1 6 6 32,
   .n 6 1 6 7 80, .p 6 1 6 8 32, .p 6 1 6 9 32, .n 6 1 6 10 32, .p 6 1 6 11 8, .p 6 1 8 2 8,
   .n 6 1 8 3 16, .n 6 1 8 4 24, .p 6 1 8 5 64, .p 6 1 8 6 16, .n 6 1 8 7 96, .p 6 1 8 8 16,
   .p 6 1 8 9 64, .n 6 1 8 10 24, .n 6 1 8 11 16, .p 6 1 8 12 8, .p 6 1 9 2 16, .n 6 1 9 3 64,
   .p 6 1 9 4 80, .n 6 1 9 6 96, .p 6 1 9 7 128, .n 6 1 9 8 96, .p 6 1 9 10 80, .n 6 1 9 11 64,
   .p 6 1 9 12 16, .n 6 1 10 2 24, .p 6 1 10 3 72, .n 6 1 10 4 24, .n 6 1 10 5 96, .p 6 1 10 6 48,
   .p 6 1 10 7 48, .p 6 1 10 8 48, .n 6 1 10 9 96, .n 6 1 10 10 24, .p 6 1 10 11 72, .n 6 1 10 12 24,
   .n 7 0 10 2 16, .p 7 0 10 3 64, .n 7 0 10 4 48, .n 7 0 10 5 128, .p 7 0 10 6 224, .n 7 0 10 8 224,
   .p 7 0 10 9 128, .p 7 0 10 10 48, .n 7 0 10 11 64, .p 7 0 10 12 16]

private def g2Mid5_5_a : List FM :=
  [.p 0 7 4 7 32, .n 0 7 5 7 128, .n 0 7 5 8 32, .p 0 7 6 7 128, .p 0 7 6 8 128, .p 0 7 7 7 128,
   .n 0 7 7 8 128, .n 0 7 8 7 320, .n 0 7 8 8 128, .p 0 7 9 7 128, .p 0 7 9 8 320, .p 0 7 10 7 128,
   .n 0 7 10 8 128, .n 0 7 11 7 128, .n 0 7 11 8 128, .p 0 7 12 7 32, .p 0 7 12 8 128, .n 0 7 13 8 32,
   .n 1 6 4 6 16, .p 1 6 4 7 16, .n 1 6 5 4 16, .p 1 6 5 6 16, .p 1 6 5 8 16, .n 1 6 5 9 16,
   .n 1 6 6 3 16, .p 1 6 6 4 48, .p 1 6 6 5 32, .p 1 6 6 6 64, .n 1 6 6 7 144, .n 1 6 6 8 48,
   .p 1 6 6 9 64, .p 1 6 7 3 64, .n 1 6 7 4 16, .n 1 6 7 5 80, .n 1 6 7 6 64, .p 1 6 7 7 224,
   .p 1 6 7 8 16, .n 1 6 7 9 144, .n 1 6 8 3 80, .n 1 6 8 4 80, .n 1 6 8 5 32, .n 1 6 8 6 96,
   .n 1 6 8 7 48, .p 1 6 8 8 80, .p 1 6 8 9 256, .p 1 6 9 4 80, .p 1 6 9 5 240, .p 1 6 9 6 96,
   .n 1 6 9 7 96, .n 1 6 9 8 80, .n 1 6 9 9 240, .p 1 6 10 3 80, .p 1 6 10 4 16, .n 1 6 10 5 160,
   .p 1 6 10 6 64, .p 1 6 10 7 80, .n 1 6 10 8 16, .n 1 6 10 9 64, .n 1 6 11 3 64, .n 1 6 11 4 48,
   .n 1 6 11 5 112, .n 1 6 11 6 64, .n 1 6 11 7 96, .p 1 6 11 8 48, .p 1 6 11 9 336, .p 1 6 12 3 16,
   .p 1 6 12 4 16, .p 1 6 12 5 160, .n 1 6 12 6 16, .p 1 6 12 7 96, .n 1 6 12 8 16, .n 1 6 12 9 256,
   .n 1 6 13 5 48, .p 1 6 13 6 16, .n 1 6 13 7 32, .p 1 6 13 9 64, .p 2 5 4 6 16, .n 2 5 4 7 16,
   .p 2 5 5 4 8, .n 2 5 5 5 32, .n 2 5 5 6 88, .p 2 5 5 7 104, .p 2 5 5 8 32, .n 2 5 5 9 24,
   .p 2 5 6 2 8, .p 2 5 6 3 56, .n 2 5 6 4 40, .p 2 5 6 5 48, .p 2 5 6 6 96, .n 2 5 6 7 120,
   .n 2 5 6 8 168, .p 2 5 6 9 128, .n 2 5 6 10 24, .p 2 5 6 11 16, .n 2 5 7 2 32, .n 2 5 7 3 152,
   .p 2 5 7 4 40, .p 2 5 7 5 88, .p 2 5 7 6 176, .n 2 5 7 7 208, .p 2 5 7 8 264, .n 2 5 7 9 168,
   .p 2 5 7 10 64, .n 2 5 7 11 72, .p 2 5 8 2 48, .p 2 5 8 3 88, .n 2 5 8 4 8, .n 2 5 8 5 224,
   .n 2 5 8 6 336, .p 2 5 8 7 408, .p 2 5 8 8 120, .n 2 5 8 9 176, .n 2 5 8 10 48, .p 2 5 8 11 128,
   .n 2 5 9 2 32, .p 2 5 9 3 48, .p 2 5 9 4 120, .p 2 5 9 5 136, .n 2 5 9 6 96, .p 2 5 9 7 96,
   .n 2 5 9 8 760, .p 2 5 9 9 568, .p 2 5 9 10 32, .n 2 5 9 11 112, .p 2 5 10 2 8, .p 2 5 10 3 8,
   .n 2 5 10 4 248, .p 2 5 10 5 48, .p 2 5 10 6 448, .n 2 5 10 7 584, .p 2 5 10 8 648, .n 2 5 10 9 288,
   .n 2 5 10 10 88, .p 2 5 10 11 48, .n 2 5 11 3 88, .p 2 5 11 4 120, .n 2 5 11 5 152, .n 2 5 11 6 176,
   .p 2 5 11 7 400, .p 2 5 11 8 88, .n 2 5 11 9 280, .p 2 5 11 10 96, .n 2 5 11 11 8, .p 2 5 12 3 40,
   .p 2 5 12 4 40, .p 2 5 12 5 128, .n 2 5 12 6 96, .n 2 5 12 7 72, .n 2 5 12 8 344, .p 2 5 12 9 336,
   .n 2 5 12 10 32, .n 2 5 13 4 32, .n 2 5 13 5 40, .p 2 5 13 6 56, .n 2 5 13 7 8, .p 2 5 13 8 120,
   .n 2 5 13 9 96, .p 3 4 5 4 24, .n 3 4 5 5 16, .n 3 4 5 6 24, .p 3 4 5 7 8, .p 3 4 5 9 8,
   .n 3 4 6 2 32, .n 3 4 6 3 8, .p 3 4 6 4 40, .p 3 4 6 5 24, .n 3 4 6 6 56, .p 3 4 6 7 104,
   .n 3 4 6 8 24, .n 3 4 6 9 40, .n 3 4 6 10 56, .p 3 4 6 11 48, .p 3 4 7 2 96, .n 3 4 7 3 8,
   .n 3 4 7 4 192, .p 3 4 7 5 128, .p 3 4 7 6 56, .n 3 4 7 7 328, .p 3 4 7 8 64, .p 3 4 7 9 256,
   .p 3 4 7 10 104, .n 3 4 7 11 176, .n 3 4 8 2 96, .n 3 4 8 3 32, .p 3 4 8 4 176, .n 3 4 8 5 160,
   .p 3 4 8 6 224, .p 3 4 8 7 208, .p 3 4 8 8 32, .n 3 4 8 9 624, .p 3 4 8 10 48, .p 3 4 8 11 224,
   .p 3 4 9 2 32, .p 3 4 9 3 208, .n 3 4 9 4 40, .n 3 4 9 5 392, .n 3 4 9 6 128, .p 3 4 9 7 160,
   .n 3 4 9 8 40, .p 3 4 9 9 504, .n 3 4 9 10 208, .n 3 4 9 11 96, .n 3 4 10 3 232, .n 3 4 10 4 56,
   .p 3 4 10 5 760, .n 3 4 10 6 184, .n 3 4 10 7 216, .n 3 4 10 8 280, .p 3 4 10 9 88, .p 3 4 10 10 136,
   .n 3 4 10 11 16, .p 3 4 11 3 56, .p 3 4 11 4 16, .n 3 4 11 5 304, .p 3 4 11 6 88, .p 3 4 11 7 120,
   .p 3 4 11 8 304, .n 3 4 11 9 272, .n 3 4 11 10 24, .p 3 4 11 11 16, .p 3 4 12 3 16, .p 3 4 12 4 96,
   .n 3 4 12 5 112, .p 3 4 12 6 16, .n 3 4 12 7 96, .p 3 4 12 8 16, .p 3 4 12 9 64, .n 3 4 13 4 64,
   .p 3 4 13 5 72, .p 3 4 13 6 8, .p 3 4 13 7 40, .n 3 4 13 8 72, .p 3 4 13 9 16, .n 4 3 5 4 16,
   .p 4 3 5 5 16, .p 4 3 5 6 32, .n 4 3 5 7 32, .n 4 3 5 8 16, .p 4 3 5 9 16, .p 4 3 6 2 48,
   .n 4 3 6 3 104, .p 4 3 6 4 64, .n 4 3 6 5 40, .p 4 3 6 7 56, .p 4 3 6 8 64, .n 4 3 6 9 88,
   .n 4 3 6 10 48, .p 4 3 6 11 48, .n 4 3 7 2 88, .p 4 3 7 3 168, .p 4 3 7 4 24, .n 4 3 7 5 72,
   .n 4 3 7 6 112, .p 4 3 7 7 80, .n 4 3 7 8 200, .p 4 3 7 9 280, .n 4 3 7 10 8, .n 4 3 7 11 72,
   .n 4 3 8 2 8, .p 4 3 8 3 80, .n 4 3 8 4 272, .p 4 3 8 5 224, .p 4 3 8 6 248, .n 4 3 8 7 320,
   .n 4 3 8 8 40, .n 4 3 8 9 32, .p 4 3 8 10 208, .n 4 3 8 11 80, .n 4 3 8 12 8, .p 4 3 9 2 96,
   .n 4 3 9 3 160, .p 4 3 9 4 40, .n 4 3 9 5 72, .n 4 3 9 6 16, .n 4 3 9 7 16, .p 4 3 9 8 696,
   .n 4 3 9 9 584, .n 4 3 9 10 192, .p 4 3 9 11 192, .p 4 3 9 12 16, .n 4 3 10 2 56, .n 4 3 10 3 88,
   .p 4 3 10 4 424, .n 4 3 10 5 72, .n 4 3 10 6 544, .p 4 3 10 7 568, .n 4 3 10 8 544, .p 4 3 10 9 328,
   .p 4 3 10 10 88, .n 4 3 10 11 96, .n 4 3 10 12 8, .p 4 3 11 2 8, .p 4 3 11 3 120, .n 4 3 11 4 312,
   .p 4 3 11 5 40, .p 4 3 11 6 432, .n 4 3 11 7 304, .n 4 3 11 8 152, .p 4 3 11 9 264, .n 4 3 11 10 104,
   .p 4 3 11 11 8, .n 4 3 12 3 16, .p 4 3 12 4 88, .n 4 3 12 5 112, .p 4 3 12 6 8, .n 4 3 12 7 48,
   .p 4 3 12 8 232, .n 4 3 12 9 208, .p 4 3 12 10 56, .n 4 3 13 4 40, .p 4 3 13 5 88, .n 4 3 13 6 48,
   .p 4 3 13 7 16, .n 4 3 13 8 40, .p 4 3 13 9 24, .n 5 2 6 2 32, .p 5 2 6 3 96, .n 5 2 6 4 56,
   .n 5 2 6 5 56, .p 5 2 6 6 32, .p 5 2 6 8 72, .n 5 2 6 9 56, .n 5 2 6 10 16, .p 5 2 6 11 16,
   .p 5 2 7 2 24, .n 5 2 7 3 56, .p 5 2 7 4 88, .n 5 2 7 5 120, .p 5 2 7 7 112, .n 5 2 7 8 8,
   .p 5 2 7 9 8, .n 5 2 7 10 104, .p 5 2 7 11 56, .n 5 2 8 1 8, .p 5 2 8 2 16, .n 5 2 8 3 72,
   .n 5 2 8 4 8, .p 5 2 8 5 256, .p 5 2 8 6 24, .n 5 2 8 7 312, .n 5 2 8 8 176, .p 5 2 8 9 280,
   .p 5 2 8 10 136, .n 5 2 8 11 144, .p 5 2 8 12 8, .p 5 2 9 1 16, .p 5 2 9 2 32, .n 5 2 9 3 96,
   .n 5 2 9 4 72, .p 5 2 9 5 216, .n 5 2 9 6 160, .p 5 2 9 7 96, .p 5 2 9 8 152, .n 5 2 9 9 312,
   .p 5 2 9 10 80, .p 5 2 9 11 80, .n 5 2 9 12 32, .n 5 2 10 1 8, .n 5 2 10 2 48, .p 5 2 10 3 128,
   .p 5 2 10 4 144, .n 5 2 10 5 408, .n 5 2 10 6 32, .p 5 2 10 7 320, .p 5 2 10 8 8, .n 5 2 10 9 48,
   .n 5 2 10 10 96, .p 5 2 10 11 16, .p 5 2 10 12 24, .p 5 2 11 2 8, .p 5 2 11 3 8, .n 5 2 11 4 104,
   .p 5 2 11 5 104, .p 5 2 11 6 112, .n 5 2 11 7 160, .n 5 2 11 8 40, .p 5 2 11 9 72, .p 5 2 11 10 24,
   .n 5 2 11 11 24, .n 5 2 12 3 8, .p 5 2 12 4 16, .n 5 2 12 5 16, .p 5 2 12 6 40, .n 5 2 12 7 40,
   .n 5 2 12 8 32, .p 5 2 12 9 64, .n 5 2 12 10 24, .n 5 2 13 4 8, .p 5 2 13 5 24, .n 5 2 13 6 16,
   .n 5 2 13 7 16, .p 5 2 13 8 24, .n 5 2 13 9 8, .p 6 1 6 2 8, .n 6 1 6 3 24, .p 6 1 6 4 8,
   .p 6 1 6 5 40, .n 6 1 6 6 40, .n 6 1 6 7 8, .p 6 1 6 8 24, .n 6 1 6 9 8, .n 6 1 7 3 16,
   .p 6 1 7 4 24, .p 6 1 7 5 56, .n 6 1 7 6 104, .n 6 1 7 7 40, .p 6 1 7 8 136, .n 6 1 7 9 24,
   .n 6 1 7 10 56, .p 6 1 7 11 24, .p 6 1 8 1 8, .n 6 1 8 2 24, .n 6 1 8 3 16, .p 6 1 8 4 96,
   .n 6 1 8 5 32, .n 6 1 8 6 96, .p 6 1 8 7 48, .p 6 1 8 8 16, .p 6 1 8 9 24, .n 6 1 8 10 8,
   .n 6 1 8 11 32, .p 6 1 8 12 16, .p 6 1 9 1 16, .n 6 1 9 2 32, .p 6 1 9 3 32, .n 6 1 9 4 48,
   .n 6 1 9 5 80, .p 6 1 9 6 272, .n 6 1 9 7 48, .n 6 1 9 8 272, .p 6 1 9 9 128, .p 6 1 9 10 80,
   .n 6 1 9 11 48, .n 6 1 10 1 24, .p 6 1 10 2 48, .p 6 1 10 3 56, .n 6 1 10 4 168, .p 6 1 10 5 24,
   .p 6 1 10 6 136, .n 6 1 10 7 72, .p 6 1 10 8 24, .n 6 1 10 9 32, .n 6 1 10 10 24, .p 6 1 10 11 48,
   .n 6 1 10 12 16, .n 6 1 11 3 32, .p 6 1 11 4 88, .n 6 1 11 5 8, .n 6 1 11 6 168, .p 6 1 11 7 120,
   .p 6 1 11 8 72, .n 6 1 11 9 88, .p 6 1 11 10 8, .p 6 1 11 11 8, .p 7 0 9 3 16, .n 7 0 9 4 48,
   .p 7 0 9 6 128, .n 7 0 9 7 96, .n 7 0 9 8 96, .p 7 0 9 9 128, .n 7 0 9 11 48, .p 7 0 9 12 16,
   .n 7 0 10 1 16, .p 7 0 10 2 48, .n 7 0 10 4 128, .p 7 0 10 5 96, .p 7 0 10 6 96, .n 7 0 10 7 128,
   .p 7 0 10 9 48, .n 7 0 10 10 16]

private def g2Mid5_5_b : List FM :=
  [.p 0 7 4 6 32, .n 0 7 5 6 128, .n 0 7 5 8 32, .p 0 7 6 6 128, .p 0 7 6 8 128, .p 0 7 7 6 128,
   .n 0 7 7 8 128, .n 0 7 8 6 320, .n 0 7 8 8 128, .p 0 7 9 6 128, .p 0 7 9 8 320, .p 0 7 10 6 128,
   .n 0 7 10 8 128, .n 0 7 11 6 128, .n 0 7 11 8 128, .p 0 7 12 6 32, .p 0 7 12 8 128, .n 0 7 13 8 32,
   .n 1 6 4 6 16, .p 1 6 4 7 16, .n 1 6 5 4 16, .n 1 6 5 5 32, .p 1 6 5 6 48, .p 1 6 5 7 32,
   .n 1 6 5 8 16, .n 1 6 5 9 16, .n 1 6 6 3 16, .p 1 6 6 4 48, .p 1 6 6 5 96, .n 1 6 6 7 208,
   .p 1 6 6 8 16, .p 1 6 6 9 64, .p 1 6 7 3 64, .p 1 6 7 4 16, .n 1 6 7 5 48, .n 1 6 7 6 128,
   .p 1 6 7 7 160, .p 1 6 7 8 48, .n 1 6 7 9 112, .n 1 6 8 3 80, .n 1 6 8 4 208, .n 1 6 8 5 96,
   .p 1 6 8 6 96, .p 1 6 8 7 144, .p 1 6 8 8 16, .p 1 6 8 9 128, .p 1 6 9 4 240, .p 1 6 9 5 80,
   .p 1 6 9 6 96, .n 1 6 9 7 96, .n 1 6 9 8 240, .n 1 6 9 9 80, .p 1 6 10 3 80, .p 1 6 10 4 16,
   .p 1 6 10 5 32, .n 1 6 10 6 128, .n 1 6 10 7 112, .p 1 6 10 8 176, .n 1 6 10 9 64, .n 1 6 11 3 64,
   .n 1 6 11 4 208, .n 1 6 11 5 16, .n 1 6 11 7 32, .p 1 6 11 8 144, .p 1 6 11 9 176, .p 1 6 12 3 16,
   .p 1 6 12 4 144, .n 1 6 12 5 32, .p 1 6 12 6 48, .p 1 6 12 7 160, .n 1 6 12 8 208, .n 1 6 12 9 128,
   .n 1 6 13 4 32, .p 1 6 13 5 16, .n 1 6 13 6 16, .n 1 6 13 7 64, .p 1 6 13 8 64, .p 1 6 13 9 32,
   .n 2 5 4 6 16, .p 2 5 4 7 16, .p 2 5 5 4 8, .n 2 5 5 5 48, .p 2 5 5 6 88, .n 2 5 5 7 72,
   .p 2 5 5 8 48, .n 2 5 5 9 24, .p 2 5 6 2 16, .p 2 5 6 3 32, .n 2 5 6 4 24, .p 2 5 6 5 96,
   .n 2 5 6 6 160, .p 2 5 6 7 136, .n 2 5 6 8 216, .p 2 5 6 9 112, .p 2 5 6 11 8, .n 2 5 7 2 64,
   .n 2 5 7 3 88, .p 2 5 7 4 40, .p 2 5 7 5 88, .n 2 5 7 6 112, .p 2 5 7 7 80, .p 2 5 7 8 264,
   .n 2 5 7 9 168, .n 2 5 7 11 40, .p 2 5 8 2 96, .p 2 5 8 3 56, .n 2 5 8 4 152, .n 2 5 8 5 272,
   .p 2 5 8 6 640, .n 2 5 8 7 568, .p 2 5 8 8 168, .n 2 5 8 9 32, .n 2 5 8 10 16, .p 2 5 8 11 80,
   .n 2 5 9 2 64, .p 2 5 9 3 16, .p 2 5 9 4 344, .p 2 5 9 5 8, .n 2 5 9 6 448, .p 2 5 9 7 448,
   .n 2 5 9 8 632, .p 2 5 9 9 344, .p 2 5 9 10 64, .n 2 5 9 11 80, .p 2 5 10 2 16, .p 2 5 10 3 16,
   .n 2 5 10 4 264, .p 2 5 10 5 256, .n 2 5 10 6 352, .p 2 5 10 7 216, .p 2 5 10 8 440, .n 2 5 10 9 272,
   .n 2 5 10 10 96, .p 2 5 10 11 40, .n 2 5 11 3 56, .n 2 5 11 4 72, .n 2 5 11 5 88, .p 2 5 11 6 496,
   .n 2 5 11 7 272, .p 2 5 11 8 24, .n 2 5 11 9 88, .p 2 5 11 10 64, .n 2 5 11 11 8, .p 2 5 12 3 24,
   .p 2 5 12 4 184, .n 2 5 12 5 80, .n 2 5 12 6 112, .n 2 5 12 7 56, .n 2 5 12 8 136, .p 2 5 12 9 192,
   .n 2 5 12 10 16, .n 2 5 13 4 64, .p 2 5 13 5 40, .n 2 5 13 6 24, .p 2 5 13 7 72, .p 2 5 13 8 40,
   .n 2 5 13 9 64, .p 3 4 5 4 16, .p 3 4 5 5 40, .n 3 4 5 6 72, .n 3 4 5 7 40, .p 3 4 5 8 56,
   .n 3 4 6 2 48, .p 3 4 6 3 48, .n 3 4 6 5 96, .p 3 4 6 6 64, .p 3 4 6 7 224, .n 3 4 6 8 144,
   .n 3 4 6 9 80, .p 3 4 6 11 32, .p 3 4 7 2 160, .n 3 4 7 3 136, .n 3 4 7 4 160, .p 3 4 7 5 32,
   .p 3 4 7 6 184, .n 3 4 7 7 200, .n 3 4 7 8 32, .p 3 4 7 9 288, .n 3 4 7 10 24, .n 3 4 7 11 112,
   .n 3 4 8 2 192, .p 3 4 8 3 40, .p 3 4 8 4 456, .n 3 4 8 5 24, .n 3 4 8 6 168, .n 3 4 8 7 184,
   .p 3 4 8 8 168, .n 3 4 8 9 344, .p 3 4 8 10 120, .p 3 4 8 11 128, .p 3 4 9 2 96, .p 3 4 9 3 208,
   .n 3 4 9 4 504, .p 3 4 9 5 40, .n 3 4 9 6 160, .p 3 4 9 7 128, .p 3 4 9 8 392, .p 3 4 9 9 40,
   .n 3 4 9 10 208, .n 3 4 9 11 32, .n 3 4 10 2 16, .n 3 4 10 3 224, .p 3 4 10 4 80, .p 3 4 10 5 272,
   .p 3 4 10 6 176, .p 3 4 10 7 144, .n 3 4 10 8 768, .p 3 4 10 9 224, .p 3 4 10 10 144, .n 3 4 10 11 32,
   .p 3 4 11 3 56, .p 3 4 11 4 176, .n 3 4 11 5 400, .p 3 4 11 6 24, .p 3 4 11 7 56, .p 3 4 11 8 208,
   .n 3 4 11 9 112, .n 3 4 11 10 24, .p 3 4 11 11 16, .p 3 4 12 3 8, .n 3 4 12 4 24, .p 3 4 12 5 104,
   .n 3 4 12 6 72, .n 3 4 12 7 184, .p 3 4 12 8 232, .n 3 4 12 9 56, .n 3 4 12 10 8, .n 3 4 13 4 40,
   .p 3 4 13 5 32, .p 3 4 13 6 24, .p 3 4 13 7 56, .n 3 4 13 8 112, .p 3 4 13 9 40, .n 4 3 5 4 16,
   .p 4 3 5 5 32, .n 4 3 5 6 16, .p 4 3 5 7 16, .n 4 3 5 8 32, .p 4 3 5 9 16, .p 4 3 6 2 48,
   .n 4 3 6 3 104, .p 4 3 6 4 64, .n 4 3 6 5 72, .p 4 3 6 6 96, .n 4 3 6 7 40, .p 4 3 6 8 96,
   .n 4 3 6 9 88, .n 4 3 6 10 48, .p 4 3 6 11 48, .n 4 3 7 2 80, .p 4 3 7 3 160, .p 4 3 7 4 24,
   .n 4 3 7 5 136, .p 4 3 7 6 64, .n 4 3 7 7 96, .n 4 3 7 8 136, .p 4 3 7 9 280, .n 4 3 7 11 80,
   .n 4 3 8 1 8, .n 4 3 8 2 32, .p 4 3 8 3 56, .n 4 3 8 4 24, .p 4 3 8 5 256, .n 4 3 8 6 616,
   .p 4 3 8 7 544, .n 4 3 8 8 72, .n 4 3 8 9 280, .p 4 3 8 10 232, .n 4 3 8 11 56, .p 4 3 9 1 16,
   .p 4 3 9 2 112, .n 4 3 9 3 112, .n 4 3 9 4 328, .p 4 3 9 5 152, .p 4 3 9 6 496, .n 4 3 9 7 528,
   .p 4 3 9 8 472, .n 4 3 9 9 216, .n 4 3 9 10 240, .p 4 3 9 11 176, .n 4 3 10 1 8, .n 4 3 10 2 48,
   .n 4 3 10 3 64, .p 4 3 10 4 336, .n 4 3 10 5 248, .p 4 3 10 6 272, .n 4 3 10 7 248, .n 4 3 10 8 368,
   .p 4 3 10 9 416, .p 4 3 10 10 64, .n 4 3 10 11 104, .p 4 3 11 3 64, .p 4 3 11 4 8, .n 4 3 11 5 88,
   .n 4 3 11 6 320, .p 4 3 11 7 448, .n 4 3 11 8 24, .n 4 3 11 9 56, .n 4 3 11 10 48, .p 4 3 11 11 16,
   .n 4 3 12 4 56, .p 4 3 12 5 96, .n 4 3 12 6 8, .n 4 3 12 7 32, .p 4 3 12 8 24, .n 4 3 12 9 64,
   .p 4 3 12 10 40, .n 4 3 13 4 8, .p 4 3 13 5 8, .p 4 3 13 6 32, .n 4 3 13 7 64, .p 4 3 13 8 40,
   .n 4 3 13 9 8, .p 5 2 5 4 8, .n 5 2 5 5 24, .p 5 2 5 6 16, .p 5 2 5 7 16, .n 5 2 5 8 24,
   .p 5 2 5 9 8, .n 5 2 6 2 16, .p 5 2 6 3 40, .n 5 2 6 4 16, .n 5 2 6 6 24, .n 5 2 6 7 56,
   .p 5 2 6 8 128, .n 5 2 6 9 16, .n 5 2 6 10 72, .p 5 2 6 11 32, .n 5 2 7 2 40, .p 5 2 7 3 72,
   .p 5 2 7 4 24, .n 5 2 7 5 56, .n 5 2 7 6 64, .p 5 2 7 7 48, .p 5 2 7 8 56, .n 5 2 7 9 56,
   .p 5 2 7 10 24, .n 5 2 7 11 8, .n 5 2 8 1 8, .p 5 2 8 2 112, .n 5 2 8 3 144, .n 5 2 8 4 160,
   .p 5 2 8 5 184, .p 5 2 8 6 224, .n 5 2 8 7 112, .n 5 2 8 8 248, .p 5 2 8 9 128, .p 5 2 8 10 64,
   .n 5 2 8 11 48, .p 5 2 8 12 8, .p 5 2 9 1 32, .n 5 2 9 2 80, .n 5 2 9 3 80, .p 5 2 9 4 312,
   .n 5 2 9 5 152, .n 5 2 9 6 96, .p 5 2 9 7 160, .n 5 2 9 8 216, .p 5 2 9 9 72, .p 5 2 9 10 96,
   .n 5 2 9 11 32, .n 5 2 9 12 16, .n 5 2 10 1 24, .p 5 2 10 2 16, .p 5 2 10 3 104, .n 5 2 10 4 72,
   .n 5 2 10 5 16, .n 5 2 10 6 232, .p 5 2 10 7 120, .p 5 2 10 8 400, .n 5 2 10 9 264, .n 5 2 10 10 120,
   .p 5 2 10 11 80, .p 5 2 10 12 8, .p 5 2 11 2 8, .p 5 2 11 3 8, .n 5 2 11 4 104, .p 5 2 11 5 104,
   .p 5 2 11 6 112, .n 5 2 11 7 160, .n 5 2 11 8 40, .p 5 2 11 9 72, .p 5 2 11 10 24, .n 5 2 11 11 24,
   .p 5 2 12 4 8, .n 5 2 12 5 40, .p 5 2 12 6 64, .n 5 2 12 7 16, .n 5 2 12 8 56, .p 5 2 12 9 56,
   .n 5 2 12 10 16, .n 6 1 6 4 8, .p 6 1 6 5 24, .n 6 1 6 6 8, .n 6 1 6 7 40, .p 6 1 6 8 40,
   .p 6 1 6 9 8, .n 6 1 6 10 24, .p 6 1 6 11 8, .p 6 1 7 2 24, .n 6 1 7 3 72, .p 6 1 7 4 24,
   .p 6 1 7 5 120, .n 6 1 7 6 120, .n 6 1 7 7 24, .p 6 1 7 8 72, .n 6 1 7 9 24, .p 6 1 8 1 16,
   .n 6 1 8 2 48, .p 6 1 8 3 40, .n 6 1 8 4 8, .n 6 1 8 5 16, .p 6 1 8 6 112, .n 6 1 8 7 160,
   .p 6 1 8 9 128, .n 6 1 8 10 64, .n 6 1 8 11 8, .p 6 1 8 12 8, .n 6 1 9 2 16, .p 6 1 9 3 16,
   .p 6 1 9 4 96, .n 6 1 9 5 176, .n 6 1 9 6 16, .p 6 1 9 7 240, .n 6 1 9 8 176, .n 6 1 9 9 16,
   .p 6 1 9 10 96, .n 6 1 9 11 64, .p 6 1 9 12 16, .n 6 1 10 1 16, .p 6 1 10 2 32, .p 6 1 10 3 24,
   .n 6 1 10 4 64, .n 6 1 10 5 8, .n 6 1 10 6 8, .p 6 1 10 7 72, .p 6 1 10 8 56, .n 6 1 10 9 136,
   .p 6 1 10 10 8, .p 6 1 10 11 64, .n 6 1 10 12 24, .p 6 1 11 2 8, .n 6 1 11 3 8, .n 6 1 11 4 40,
   .p 6 1 11 5 56, .p 6 1 11 6 40, .n 6 1 11 7 88, .p 6 1 11 8 8, .p 6 1 11 9 40, .n 6 1 11 10 16,
   .n 7 0 9 1 16, .p 7 0 9 2 48, .n 7 0 9 4 128, .p 7 0 9 5 96, .p 7 0 9 6 96, .n 7 0 9 7 128,
   .p 7 0 9 9 48, .n 7 0 9 10 16, .p 7 0 10 3 16, .n 7 0 10 4 48, .p 7 0 10 6 128, .n 7 0 10 7 96,
   .n 7 0 10 8 96, .p 7 0 10 9 128, .n 7 0 10 11 48, .p 7 0 10 12 16]

set_option maxRecDepth 65536 in
private theorem g2_det5_5_step01 :
    fmMerge (fmMerge [] (fmMul (fmSubMat g2FM ⟨5, by decide⟩ ⟨0, by decide⟩ ⟨0, by decide⟩) g2Val4_10))
      (fmMul (fmNeg (fmSubMat g2FM ⟨5, by decide⟩ ⟨0, by decide⟩ ⟨1, by decide⟩)) g2Val4_6) =
      g2Mid5_5_a := rfl

set_option maxRecDepth 65536 in
private theorem g2_det5_5_step2 :
    fmMerge g2Mid5_5_a (fmMul (fmSubMat g2FM ⟨5, by decide⟩ ⟨0, by decide⟩ ⟨2, by decide⟩) g2Val4_3) =
      g2Mid5_5_b := rfl

set_option maxRecDepth 65536 in
private theorem g2_det5_5_step34 :
    fmMerge (fmMerge g2Mid5_5_b (fmMul (fmNeg (fmSubMat g2FM ⟨5, by decide⟩ ⟨0, by decide⟩ ⟨3, by decide⟩)) g2Val4_1))
      (fmMul (fmSubMat g2FM ⟨5, by decide⟩ ⟨0, by decide⟩ ⟨4, by decide⟩) g2Val4_0) =
      g2Val5_5 := rfl

private theorem g2_det5_5 : fmDet 5 (fmSubMat g2FM ⟨5, by decide⟩) = g2Val5_5 :=
  fmDet5_of_sub4_split _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (fin4Mat_eq_of_vals _ _ (by decide)) g2_det4_10
    (fin4Mat_eq_of_vals _ _ (by decide)) g2_det4_6
    (fin4Mat_eq_of_vals _ _ (by decide)) g2_det4_3
    (fin4Mat_eq_of_vals _ _ (by decide)) g2_det4_1
    (fin4Mat_eq_of_vals _ _ (by decide)) g2_det4_0
    g2_det5_5_step01 g2_det5_5_step2 g2_det5_5_step34

private def g2Comb6_0 : List FM :=
  [.p 0 9 5 8 32, .n 0 9 5 9 32, .p 0 9 6 7 32, .n 0 9 6 8 192, .p 0 9 6 9 128, .p 0 9 6 10 32,
   .n 0 9 7 7 160, .p 0 9 7 8 384, .n 0 9 7 9 64, .n 0 9 7 10 160, .p 0 9 8 7 256, .n 0 9 8 8 96,
   .n 0 9 8 9 416, .p 0 9 8 10 256, .n 0 9 9 8 704, .p 0 9 9 9 704, .n 0 9 10 7 448, .p 0 9 10 8 896,
   .n 0 9 10 10 448, .p 0 9 11 7 448, .n 0 9 11 9 896, .p 0 9 11 10 448, .n 0 9 12 8 704, .p 0 9 12 9 704,
   .n 0 9 13 7 256, .p 0 9 13 8 416, .p 0 9 13 9 96, .n 0 9 13 10 256, .p 0 9 14 7 160, .p 0 9 14 8 64,
   .n 0 9 14 9 384, .p 0 9 14 10 160, .n 0 9 15 7 32, .n 0 9 15 8 128, .p 0 9 15 9 192, .n 0 9 15 10 32,
   .p 0 9 16 8 32, .n 0 9 16 9 32, .p 1 8 5 8 48, .n 1 8 5 9 32, .n 1 8 5 10 16, .n 1 8 6 7 32,
   .n 1 8 6 8 112, .p 1 8 6 9 48, .p 1 8 6 10 64, .p 1 8 6 11 16, .p 1 8 6 12 16, .n 1 8 7 6 32,
   .p 1 8 7 7 112, .n 1 8 7 8 32, .p 1 8 7 9 96, .n 1 8 7 10 16, .n 1 8 7 11 48, .n 1 8 7 12 80,
   .n 1 8 8 5 16, .p 1 8 8 6 144, .n 1 8 8 7 32, .p 1 8 8 8 144, .n 1 8 8 9 96, .n 1 8 8 10 272,
   .n 1 8 8 11 16, .p 1 8 8 12 144, .p 1 8 9 5 80, .n 1 8 9 6 208, .n 1 8 9 7 336, .p 1 8 9 8 176,
   .n 1 8 9 9 272, .p 1 8 9 10 432, .p 1 8 9 11 208, .n 1 8 9 12 80, .n 1 8 10 5 144, .p 1 8 10 6 16,
   .p 1 8 10 7 464, .n 1 8 10 8 240, .p 1 8 10 9 240, .n 1 8 10 10 16, .n 1 8 10 11 240, .n 1 8 10 12 80,
   .p 1 8 11 5 80, .p 1 8 11 6 240, .p 1 8 11 7 16, .n 1 8 11 8 240, .p 1 8 11 9 240, .n 1 8 11 10 464,
   .n 1 8 11 11 16, .p 1 8 11 12 144, .p 1 8 12 5 80, .n 1 8 12 6 208, .n 1 8 12 7 432, .p 1 8 12 8 272,
   .n 1 8 12 9 176, .p 1 8 12 10 336, .p 1 8 12 11 208, .n 1 8 12 12 80, .n 1 8 13 5 144, .p 1 8 13 6 16,
   .p 1 8 13 7 272, .p 1 8 13 8 96, .n 1 8 13 9 144, .p 1 8 13 10 32, .n 1 8 13 11 144, .p 1 8 13 12 16,
   .p 1 8 14 5 80, .p 1 8 14 6 48, .p 1 8 14 7 16, .n 1 8 14 8 96, .p 1 8 14 9 32, .n 1 8 14 10 112,
   .p 1 8 14 11 32, .n 1 8 15 5 16, .n 1 8 15 6 16, .n 1 8 15 7 64, .n 1 8 15 8 48, .p 1 8 15 9 112,
   .p 1 8 15 10 32, .p 1 8 16 7 16, .p 1 8 16 8 32, .n 1 8 16 9 48, .p 2 7 5 8 8, .p 2 7 5 9 32,
   .n 2 7 5 10 40, .n 2 7 6 6 16, .n 2 7 6 7 224, .p 2 7 6 8 472, .n 2 7 6 9 312, .p 2 7 6 10 16,
   .n 2 7 6 11 8, .p 2 7 6 12 72, .n 2 7 7 6 80, .p 2 7 7 7 1032, .n 2 7 7 8 1632, .p 2 7 7 9 304,
   .p 2 7 7 10 632, .p 2 7 7 11 24, .n 2 7 7 12 296, .p 2 7 7 13 16, .p 2 7 8 4 16, .n 2 7 8 5 8,
   .p 2 7 8 6 488, .n 2 7 8 7 1408, .p 2 7 8 8 552, .p 2 7 8 9 1792, .n 2 7 8 10 1608, .n 2 7 8 11 152,
   .p 2 7 8 12 392, .n 2 7 8 13 64, .n 2 7 9 4 64, .p 2 7 9 5 104, .n 2 7 9 6 696, .n 2 7 9 7 488,
   .p 2 7 9 8 3864, .n 2 7 9 9 3992, .p 2 7 9 10 712, .p 2 7 9 11 520, .n 2 7 9 12 40, .p 2 7 9 13 80,
   .p 2 7 10 4 80, .n 2 7 10 5 328, .p 2 7 10 6 72, .p 2 7 10 7 2936, .n 2 7 10 8 4680, .p 2 7 10 9 760,
   .p 2 7 10 10 2136, .n 2 7 10 11 616, .n 2 7 10 12 360, .p 2 7 11 5 360, .p 2 7 11 6 616, .n 2 7 11 7 2136,
   .n 2 7 11 8 760, .p 2 7 11 9 4680, .n 2 7 11 10 2936, .n 2 7 11 11 72, .p 2 7 11 12 328, .n 2 7 11 13 80,
   .n 2 7 12 4 80, .p 2 7 12 5 40, .n 2 7 12 6 520, .n 2 7 12 7 712, .p 2 7 12 8 3992, .n 2 7 12 9 3864,
   .p 2 7 12 10 488, .p 2 7 12 11 696, .n 2 7 12 12 104, .p 2 7 12 13 64, .p 2 7 13 4 64, .n 2 7 13 5 392,
   .p 2 7 13 6 152, .p 2 7 13 7 1608, .n 2 7 13 8 1792, .n 2 7 13 9 552, .p 2 7 13 10 1408, .n 2 7 13 11 488,
   .p 2 7 13 12 8, .n 2 7 13 13 16, .n 2 7 14 4 16, .p 2 7 14 5 296, .n 2 7 14 6 24, .n 2 7 14 7 632,
   .n 2 7 14 8 304, .p 2 7 14 9 1632, .n 2 7 14 10 1032, .p 2 7 14 11 80, .n 2 7 15 5 72, .p 2 7 15 6 8,
   .n 2 7 15 7 16, .p 2 7 15 8 312, .n 2 7 15 9 472, .p 2 7 15 10 224, .p 2 7 15 11 16, .p 2 7 16 7 40,
   .n 2 7 16 8 32, .n 2 7 16 9 8, .n 3 6 5 8 16, .p 3 6 5 9 32, .n 3 6 5 10 16, .p 3 6 6 6 16,
   .n 3 6 6 7 208, .p 3 6 6 8 272, .p 3 6 6 9 32, .n 3 6 6 10 64, .n 3 6 6 11 112, .p 3 6 6 12 64,
   .p 3 6 7 4 4, .p 3 6 7 5 44, .p 3 6 7 6 168, .n 3 6 7 7 280, .p 3 6 7 8 256, .n 3 6 7 9 432,
   .p 3 6 7 10 88, .p 3 6 7 11 200, .n 3 6 7 12 100, .p 3 6 7 13 52, .p 3 6 8 3 4, .n 3 6 8 4 64,
   .p 3 6 8 5 144, .n 3 6 8 6 716, .p 3 6 8 7 1504, .n 3 6 8 8 1064, .n 3 6 8 9 712, .p 3 6 8 10 1024,
   .p 3 6 8 11 428, .n 3 6 8 12 376, .n 3 6 8 13 184, .p 3 6 8 14 12, .n 3 6 9 3 28, .p 3 6 9 4 192,
   .n 3 6 9 5 880, .p 3 6 9 6 756, .p 3 6 9 7 528, .n 3 6 9 8 1704, .p 3 6 9 9 3048, .n 3 6 9 10 1440,
   .n 3 6 9 11 1588, .p 3 6 9 12 904, .p 3 6 9 13 264, .n 3 6 9 14 52, .p 3 6 10 3 72, .n 3 6 10 4 260,
   .p 3 6 10 5 1044, .p 3 6 10 6 464, .n 3 6 10 7 3944, .p 3 6 10 8 3696, .n 3 6 10 9 528, .n 3 6 10 10 1992,
   .p 3 6 10 11 1760, .n 3 6 10 12 140, .n 3 6 10 13 260, .p 3 6 10 14 88, .n 3 6 11 3 88, .p 3 6 11 4 260,
   .p 3 6 11 5 140, .n 3 6 11 6 1760, .p 3 6 11 7 1992, .p 3 6 11 8 528, .n 3 6 11 9 3696, .p 3 6 11 10 3944,
   .n 3 6 11 11 464, .n 3 6 11 12 1044, .p 3 6 11 13 260, .n 3 6 11 14 72, .p 3 6 12 3 52, .n 3 6 12 4 264,
   .n 3 6 12 5 904, .p 3 6 12 6 1588, .p 3 6 12 7 1440, .n 3 6 12 8 3048, .p 3 6 12 9 1704, .n 3 6 12 10 528,
   .n 3 6 12 11 756, .p 3 6 12 12 880, .n 3 6 12 13 192, .p 3 6 12 14 28, .n 3 6 13 3 12, .p 3 6 13 4 184,
   .p 3 6 13 5 376, .n 3 6 13 6 428, .n 3 6 13 7 1024, .p 3 6 13 8 712, .p 3 6 13 9 1064, .n 3 6 13 10 1504,
   .p 3 6 13 11 716, .n 3 6 13 12 144, .p 3 6 13 13 64, .n 3 6 13 14 4, .n 3 6 14 4 52, .p 3 6 14 5 100,
   .n 3 6 14 6 200, .n 3 6 14 7 88, .p 3 6 14 8 432, .n 3 6 14 9 256, .p 3 6 14 10 280, .n 3 6 14 11 168,
   .n 3 6 14 12 44, .n 3 6 14 13 4, .n 3 6 15 5 64, .p 3 6 15 6 112, .p 3 6 15 7 64, .n 3 6 15 8 32,
   .n 3 6 15 9 272, .p 3 6 15 10 208, .n 3 6 15 11 16, .p 3 6 16 7 16, .n 3 6 16 8 32, .p 3 6 16 9 16,
   .p 4 5 6 6 32, .p 4 5 6 7 72, .n 4 5 6 8 344, .p 4 5 6 9 304, .n 4 5 6 10 48, .p 4 5 6 11 8,
   .n 4 5 6 12 24, .n 4 5 7 4 16, .n 4 5 7 5 32, .p 4 5 7 6 488, .n 4 5 7 7 1592, .p 4 5 7 8 1856,
   .n 4 5 7 9 320, .n 4 5 7 10 440, .n 4 5 7 11 216, .p 4 5 7 12 288, .n 4 5 7 13 16, .n 4 5 8 3 24,
   .p 4 5 8 4 48, .p 4 5 8 5 24, .n 4 5 8 6 1016, .p 4 5 8 7 2736, .n 4 5 8 8 1160, .n 4 5 8 9 2800,
   .p 4 5 8 10 2120, .p 4 5 8 11 1000, .n 4 5 8 12 1032, .p 4 5 8 13 88, .p 4 5 8 14 16, .p 4 5 9 3 112,
   .p 4 5 9 4 40, .n 4 5 9 5 584, .p 4 5 9 6 408, .p 4 5 9 7 1544, .n 4 5 9 8 5168, .p 4 5 9 9 6328,
   .n 4 5 9 10 2320, .n 4 5 9 11 1176, .p 4 5 9 12 904, .n 4 5 9 13 80, .n 4 5 9 14 8, .n 4 5 10 3 176,
   .n 4 5 10 4 208, .p 4 5 10 5 1616, .n 4 5 10 6 88, .n 4 5 10 7 5696, .p 4 5 10 8 7128, .n 4 5 10 9 1200,
   .n 4 5 10 10 2248, .p 4 5 10 11 208, .p 4 5 10 12 888, .n 4 5 10 13 128, .n 4 5 10 14 96, .p 4 5 11 3 96,
   .p 4 5 11 4 128, .n 4 5 11 5 888, .n 4 5 11 6 208, .p 4 5 11 7 2248, .p 4 5 11 8 1200, .n 4 5 11 9 7128,
   .p 4 5 11 10 5696, .p 4 5 11 11 88, .n 4 5 11 12 1616, .p 4 5 11 13 208, .p 4 5 11 14 176, .p 4 5 12 3 8,
   .p 4 5 12 4 80, .n 4 5 12 5 904, .p 4 5 12 6 1176, .p 4 5 12 7 2320, .n 4 5 12 8 6328, .p 4 5 12 9 5168,
   .n 4 5 12 10 1544, .n 4 5 12 11 408, .p 4 5 12 12 584, .n 4 5 12 13 40, .n 4 5 12 14 112, .n 4 5 13 3 16,
   .n 4 5 13 4 88, .p 4 5 13 5 1032, .n 4 5 13 6 1000, .n 4 5 13 7 2120, .p 4 5 13 8 2800, .p 4 5 13 9 1160,
   .n 4 5 13 10 2736, .p 4 5 13 11 1016, .n 4 5 13 12 24, .n 4 5 13 13 48, .p 4 5 13 14 24, .p 4 5 14 4 16,
   .n 4 5 14 5 288, .p 4 5 14 6 216, .p 4 5 14 7 440, .p 4 5 14 8 320, .n 4 5 14 9 1856, .p 4 5 14 10 1592,
   .n 4 5 14 11 488, .p 4 5 14 12 32, .p 4 5 14 13 16, .p 4 5 15 5 24, .n 4 5 15 6 8, .p 4 5 15 7 48,
   .n 4 5 15 8 304, .p 4 5 15 9 344, .n 4 5 15 10 72, .n 4 5 15 11 32, .n 5 4 6 6 44, .p 5 4 6 7 120,
   .n 5 4 6 8 84, .p 5 4 6 9 16, .n 5 4 6 10 84, .p 5 4 6 11 120, .n 5 4 6 12 44, .p 5 4 7 4 24,
   .n 5 4 7 5 124, .p 5 4 7 6 104, .p 5 4 7 7 292, .n 5 4 7 8 640, .p 5 4 7 9 468, .n 5 4 7 10 24,
   .n 5 4 7 11 292, .p 5 4 7 12 280, .n 5 4 7 13 88, .p 5 4 8 3 56, .n 5 4 8 4 20, .n 5 4 8 5 248,
   .p 5 4 8 6 1140, .n 5 4 8 7 2496, .p 5 4 8 8 1448, .p 5 4 8 9 1472, .n 5 4 8 10 1544, .p 5 4 8 11 8,
   .p 5 4 8 12 44, .p 5 4 8 13 184, .n 5 4 8 14 44, .n 5 4 9 3 132, .n 5 4 9 4 376, .p 5 4 9 5 1908,
   .n 5 4 9 6 2456, .p 5 4 9 7 584, .p 5 4 9 8 3776, .n 5 4 9 9 5960, .p 5 4 9 10 1184, .p 5 4 9 11 3068,
   .n 5 4 9 12 1352, .n 5 4 9 13 492, .p 5 4 9 14 248, .n 5 4 10 3 64, .p 5 4 10 4 1104, .n 5 4 10 5 1976,
   .n 5 4 10 6 1392, .p 5 4 10 7 6864, .n 5 4 10 8 7368, .p 5 4 10 9 1136, .p 5 4 10 10 5832, .n 5 4 10 11 5552,
   .p 5 4 10 12 632, .p 5 4 10 13 1128, .n 5 4 10 14 344, .p 5 4 11 3 344, .n 5 4 11 4 1128, .n 5 4 11 5 632,
   .p 5 4 11 6 5552, .n 5 4 11 7 5832, .n 5 4 11 8 1136, .p 5 4 11 9 7368, .n 5 4 11 10 6864, .p 5 4 11 11 1392,
   .p 5 4 11 12 1976, .n 5 4 11 13 1104, .p 5 4 11 14 64, .n 5 4 12 3 248, .p 5 4 12 4 492, .p 5 4 12 5 1352,
   .n 5 4 12 6 3068, .n 5 4 12 7 1184, .p 5 4 12 8 5960, .n 5 4 12 9 3776, .n 5 4 12 10 584, .p 5 4 12 11 2456,
   .n 5 4 12 12 1908, .p 5 4 12 13 376, .p 5 4 12 14 132, .p 5 4 13 3 44, .n 5 4 13 4 184, .n 5 4 13 5 44,
   .n 5 4 13 6 8, .p 5 4 13 7 1544, .n 5 4 13 8 1472, .n 5 4 13 9 1448, .p 5 4 13 10 2496, .n 5 4 13 11 1140,
   .p 5 4 13 12 248, .p 5 4 13 13 20, .n 5 4 13 14 56, .p 5 4 14 4 88, .n 5 4 14 5 280, .p 5 4 14 6 292,
   .p 5 4 14 7 24, .n 5 4 14 8 468, .p 5 4 14 9 640, .n 5 4 14 10 292, .n 5 4 14 11 104, .p 5 4 14 12 124,
   .n 5 4 14 13 24, .p 5 4 15 5 44, .n 5 4 15 6 120, .p 5 4 15 7 84, .n 5 4 15 8 16, .p 5 4 15 9 84,
   .n 5 4 15 10 120, .p 5 4 15 11 44, .p 6 3 6 6 12, .n 6 3 6 7 48, .p 6 3 6 8 60, .n 6 3 6 10 60,
   .p 6 3 6 11 48, .n 6 3 6 12 12, .n 6 3 7 4 16, .p 6 3 7 5 152, .n 6 3 7 6 424, .p 6 3 7 7 508,
   .n 6 3 7 8 344, .p 6 3 7 9 316, .n 6 3 7 10 312, .p 6 3 7 11 84, .p 6 3 7 12 72, .n 6 3 7 13 36,
   .n 6 3 8 3 64, .p 6 3 8 4 136, .n 6 3 8 5 32, .p 6 3 8 6 348, .n 6 3 8 7 1112, .p 6 3 8 8 368,
   .p 6 3 8 9 1256, .n 6 3 8 10 648, .n 6 3 8 11 968, .p 6 3 8 12 872, .n 6 3 8 13 104, .n 6 3 8 14 52,
   .p 6 3 9 3 24, .n 6 3 9 4 112, .n 6 3 9 5 160, .p 6 3 9 6 944, .n 6 3 9 7 1108, .p 6 3 9 8 1176,
   .n 6 3 9 9 2176, .p 6 3 9 10 1688, .p 6 3 9 11 336, .n 6 3 9 12 712, .p 6 3 9 14 88, .p 6 3 9 15 12,
   .n 6 3 10 2 4, .p 6 3 10 3 232, .n 6 3 10 4 300, .n 6 3 10 5 608, .p 6 3 10 6 300, .p 6 3 10 7 2232,
   .n 6 3 10 8 2160, .n 6 3 10 9 296, .n 6 3 10 10 196, .p 6 3 10 11 1680, .n 6 3 10 12 868, .n 6 3 10 13 152,
   .p 6 3 10 14 156, .n 6 3 10 15 16, .p 6 3 11 2 16, .n 6 3 11 3 156, .p 6 3 11 4 152, .p 6 3 11 5 868,
   .n 6 3 11 6 1680, .p 6 3 11 7 196, .p 6 3 11 8 296, .p 6 3 11 9 2160, .n 6 3 11 10 2232, .n 6 3 11 11 300,
   .p 6 3 11 12 608, .p 6 3 11 13 300, .n 6 3 11 14 232, .p 6 3 11 15 4, .n 6 3 12 2 12, .n 6 3 12 3 88,
   .p 6 3 12 5 712, .n 6 3 12 6 336, .n 6 3 12 7 1688, .p 6 3 12 8 2176, .n 6 3 12 9 1176, .p 6 3 12 10 1108,
   .n 6 3 12 11 944, .p 6 3 12 12 160, .p 6 3 12 13 112, .n 6 3 12 14 24, .p 6 3 13 3 52, .p 6 3 13 4 104,
   .n 6 3 13 5 872, .p 6 3 13 6 968, .p 6 3 13 7 648, .n 6 3 13 8 1256, .n 6 3 13 9 368, .p 6 3 13 10 1112,
   .n 6 3 13 11 348, .p 6 3 13 12 32, .n 6 3 13 13 136, .p 6 3 13 14 64, .p 6 3 14 4 36, .n 6 3 14 5 72,
   .n 6 3 14 6 84, .p 6 3 14 7 312, .n 6 3 14 8 316, .p 6 3 14 9 344, .n 6 3 14 10 508, .p 6 3 14 11 424,
   .n 6 3 14 12 152, .p 6 3 14 13 16, .p 6 3 15 5 12, .n 6 3 15 6 48, .p 6 3 15 7 60, .n 6 3 15 9 60,
   .p 6 3 15 10 48, .n 6 3 15 11 12, .p 7 2 7 4 4, .n 7 2 7 5 40, .p 7 2 7 6 136, .n 7 2 7 7 200,
   .p 7 2 7 8 80, .p 7 2 7 9 136, .n 7 2 7 10 200, .p 7 2 7 11 104, .n 7 2 7 12 20, .p 7 2 8 3 36,
   .n 7 2 8 4 156, .p 7 2 8 5 200, .n 7 2 8 6 28, .p 7 2 8 7 80, .n 7 2 8 8 512, .p 7 2 8 9 440,
   .p 7 2 8 10 320, .n 7 2 8 11 692, .p 7 2 8 12 380, .n 7 2 8 13 64, .n 7 2 8 14 4, .p 7 2 9 3 24,
   .n 7 2 9 4 56, .n 7 2 9 5 372, .p 7 2 9 6 1428, .n 7 2 9 7 1076, .n 7 2 9 8 1720, .p 7 2 9 9 2880,
   .n 7 2 9 10 224, .n 7 2 9 11 1768, .p 7 2 9 12 816, .p 7 2 9 13 276, .n 7 2 9 14 244, .p 7 2 9 15 36,
   .p 7 2 10 2 12, .p 7 2 10 3 160, .n 7 2 10 4 704, .p 7 2 10 5 836, .p 7 2 10 6 436, .n 7 2 10 7 2800,
   .p 7 2 10 8 4008, .n 7 2 10 9 1024, .n 7 2 10 10 3748, .p 7 2 10 11 3864, .n 7 2 10 12 392, .n 7 2 10 13 1028,
   .p 7 2 10 14 388, .n 7 2 10 15 8, .p 7 2 11 2 8, .n 7 2 11 3 388, .p 7 2 11 4 1028, .p 7 2 11 5 392,
   .n 7 2 11 6 3864, .p 7 2 11 7 3748, .p 7 2 11 8 1024, .n 7 2 11 9 4008, .p 7 2 11 10 2800, .n 7 2 11 11 436,
   .n 7 2 11 12 836, .p 7 2 11 13 704, .n 7 2 11 14 160, .n 7 2 11 15 12, .n 7 2 12 2 36, .p 7 2 12 3 244,
   .n 7 2 12 4 276, .n 7 2 12 5 816, .p 7 2 12 6 1768, .p 7 2 12 7 224, .n 7 2 12 8 2880, .p 7 2 12 9 1720,
   .p 7 2 12 10 1076, .n 7 2 12 11 1428, .p 7 2 12 12 372, .p 7 2 12 13 56, .n 7 2 12 14 24, .p 7 2 13 3 4,
   .p 7 2 13 4 64, .n 7 2 13 5 380, .p 7 2 13 6 692, .n 7 2 13 7 320, .n 7 2 13 8 440, .p 7 2 13 9 512,
   .n 7 2 13 10 80, .p 7 2 13 11 28, .n 7 2 13 12 200, .p 7 2 13 13 156, .n 7 2 13 14 36, .p 7 2 14 5 20,
   .n 7 2 14 6 104, .p 7 2 14 7 200, .n 7 2 14 8 136, .n 7 2 14 9 80, .p 7 2 14 10 200, .n 7 2 14 11 136,
   .p 7 2 14 12 40, .n 7 2 14 13 4, .n 8 1 8 3 8, .p 8 1 8 4 40, .n 8 1 8 5 64, .p 8 1 8 7 112,
   .n 8 1 8 8 112, .p 8 1 8 10 64, .n 8 1 8 11 40, .p 8 1 8 12 8, .p 8 1 9 4 16, .n 8 1 9 5 96,
   .p 8 1 9 6 184, .n 8 1 9 7 8, .n 8 1 9 8 416, .p 8 1 9 9 448, .p 8 1 9 10 112, .n 8 1 9 11 464,
   .p 8 1 9 12 208, .p 8 1 9 13 96, .n 8 1 9 14 104, .p 8 1 9 15 24, .n 8 1 10 2 8, .p 8 1 10 3 64,
   .n 8 1 10 4 120, .n 8 1 10 5 128, .p 8 1 10 6 576, .n 8 1 10 7 208, .n 8 1 10 8 944, .p 8 1 10 9 960,
   .p 8 1 10 10 440, .n 8 1 10 11 1056, .p 8 1 10 12 296, .p 8 1 10 13 320, .n 8 1 10 14 240, .p 8 1 10 15 48,
   .n 8 1 11 2 48, .p 8 1 11 3 240, .n 8 1 11 4 320, .n 8 1 11 5 296, .p 8 1 11 6 1056, .n 8 1 11 7 440,
   .n 8 1 11 8 960, .p 8 1 11 9 944, .p 8 1 11 10 208, .n 8 1 11 11 576, .p 8 1 11 12 128, .p 8 1 11 13 120,
   .n 8 1 11 14 64, .p 8 1 11 15 8, .n 8 1 12 2 24, .p 8 1 12 3 104, .n 8 1 12 4 96, .n 8 1 12 5 208,
   .p 8 1 12 6 464, .n 8 1 12 7 112, .n 8 1 12 8 448, .p 8 1 12 9 416, .p 8 1 12 10 8, .n 8 1 12 11 184,
   .p 8 1 12 12 96, .n 8 1 12 13 16, .n 8 1 13 5 8, .p 8 1 13 6 40, .n 8 1 13 7 64, .p 8 1 13 9 112,
   .n 8 1 13 10 112, .p 8 1 13 12 64, .n 8 1 13 13 40, .p 8 1 13 14 8, .p 9 0 10 4 48, .n 9 0 10 5 240,
   .p 9 0 10 6 336, .p 9 0 10 7 240, .n 9 0 10 8 1056, .p 9 0 10 9 672, .p 9 0 10 10 672, .n 9 0 10 11 1056,
   .p 9 0 10 12 240, .p 9 0 10 13 336, .n 9 0 10 14 240, .p 9 0 10 15 48, .n 9 0 11 2 48, .p 9 0 11 3 240,
   .n 9 0 11 4 336, .n 9 0 11 5 240, .p 9 0 11 6 1056, .n 9 0 11 7 672, .n 9 0 11 8 672, .p 9 0 11 9 1056,
   .n 9 0 11 10 240, .n 9 0 11 11 336, .p 9 0 11 12 240, .n 9 0 11 13 48]

set_option maxRecDepth 65536 in
private theorem g2_comb6_step0 :
    fmMerge [] (fmMul (g2FM ⟨0, by decide⟩ ⟨0, by decide⟩) g2Val5_0) = g2Comb6_0 := rfl

private def g2Comb6_1 : List FM :=
  [.p 0 9 5 8 32, .n 0 9 5 9 32, .n 0 9 6 8 160, .p 0 9 6 9 128, .p 0 9 6 10 32, .p 0 9 7 8 256,
   .n 0 9 7 9 96, .n 0 9 7 10 160, .n 0 9 8 9 256, .p 0 9 8 10 256, .n 0 9 9 8 448, .p 0 9 9 9 448,
   .p 0 9 10 8 448, .n 0 9 10 10 448, .n 0 9 11 9 448, .p 0 9 11 10 448, .n 0 9 12 8 256, .p 0 9 12 9 256,
   .p 0 9 13 8 160, .p 0 9 13 9 96, .n 0 9 13 10 256, .n 0 9 14 8 32, .n 0 9 14 9 128, .p 0 9 14 10 160,
   .p 0 9 15 9 32, .n 0 9 15 10 32, .p 1 8 5 9 16, .n 1 8 5 10 16, .n 1 8 6 7 16, .p 1 8 6 8 48,
   .n 1 8 6 9 80, .p 1 8 6 10 16, .p 1 8 6 11 16, .p 1 8 6 12 16, .n 1 8 7 8 128, .p 1 8 7 9 128,
   .p 1 8 7 10 160, .n 1 8 7 11 80, .n 1 8 7 12 80, .p 1 8 8 5 16, .p 1 8 8 6 16, .p 1 8 8 7 160,
   .n 1 8 8 8 32, .n 1 8 8 9 48, .n 1 8 8 10 400, .p 1 8 8 11 144, .p 1 8 8 12 144, .n 1 8 9 5 80,
   .n 1 8 9 6 80, .n 1 8 9 7 176, .p 1 8 9 8 336, .n 1 8 9 9 16, .p 1 8 9 10 176, .n 1 8 9 11 80,
   .n 1 8 9 12 80, .p 1 8 10 5 144, .p 1 8 10 6 144, .n 1 8 10 7 304, .n 1 8 10 8 176, .n 1 8 10 9 48,
   .p 1 8 10 10 400, .n 1 8 10 11 80, .n 1 8 10 12 80, .n 1 8 11 5 80, .n 1 8 11 6 80, .p 1 8 11 7 592,
   .n 1 8 11 8 176, .n 1 8 11 9 48, .n 1 8 11 10 496, .p 1 8 11 11 144, .p 1 8 11 12 144, .n 1 8 12 5 80,
   .n 1 8 12 6 80, .n 1 8 12 7 80, .p 1 8 12 8 48, .p 1 8 12 9 272, .p 1 8 12 10 80, .n 1 8 12 11 80,
   .n 1 8 12 12 80, .p 1 8 13 5 144, .p 1 8 13 6 144, .n 1 8 13 7 400, .p 1 8 13 8 112, .n 1 8 13 9 192,
   .p 1 8 13 10 160, .p 1 8 13 11 16, .p 1 8 13 12 16, .n 1 8 14 5 80, .n 1 8 14 6 80, .p 1 8 14 7 256,
   .p 1 8 14 8 64, .n 1 8 14 9 64, .n 1 8 14 10 96, .p 1 8 15 5 16, .p 1 8 15 6 16, .n 1 8 15 7 16,
   .n 1 8 15 8 144, .p 1 8 15 9 112, .p 1 8 15 10 16, .n 1 8 16 7 16, .p 1 8 16 8 48, .n 1 8 16 9 32,
   .n 2 7 5 8 40, .p 2 7 5 9 32, .p 2 7 5 10 8, .n 2 7 6 6 16, .n 2 7 6 7 80, .p 2 7 6 8 488,
   .n 2 7 6 9 312, .n 2 7 6 10 48, .n 2 7 6 11 56, .p 2 7 6 12 24, .p 2 7 7 5 16, .p 2 7 7 6 48,
   .p 2 7 7 7 296, .n 2 7 7 8 1248, .p 2 7 7 9 288, .p 2 7 7 10 488, .p 2 7 7 11 184, .n 2 7 7 12 88,
   .p 2 7 7 13 16, .n 2 7 8 3 8, .n 2 7 8 4 8, .n 2 7 8 5 120, .p 2 7 8 6 56, .n 2 7 8 7 256,
   .p 2 7 8 8 424, .p 2 7 8 9 1488, .n 2 7 8 10 1304, .n 2 7 8 11 272, .p 2 7 8 12 64, .n 2 7 8 13 64,
   .p 2 7 9 3 40, .p 2 7 9 4 32, .p 2 7 9 5 336, .n 2 7 9 6 296, .n 2 7 9 7 424, .p 2 7 9 8 2088,
   .n 2 7 9 9 2936, .p 2 7 9 10 536, .p 2 7 9 11 416, .p 2 7 9 12 136, .p 2 7 9 13 72, .n 2 7 10 3 80,
   .n 2 7 10 4 40, .n 2 7 10 5 400, .p 2 7 10 6 152, .p 2 7 10 7 1064, .n 2 7 10 8 2312, .p 2 7 10 9 280,
   .p 2 7 10 10 2056, .n 2 7 10 11 520, .n 2 7 10 12 240, .p 2 7 10 13 40, .p 2 7 11 3 80, .p 2 7 11 5 40,
   .p 2 7 11 6 376, .n 2 7 11 7 680, .n 2 7 11 8 328, .p 2 7 11 9 3032, .n 2 7 11 10 2472, .p 2 7 11 11 56,
   .p 2 7 11 12 56, .n 2 7 11 13 160, .n 2 7 12 3 40, .p 2 7 12 4 40, .p 2 7 12 5 424, .n 2 7 12 6 408,
   .n 2 7 12 7 296, .p 2 7 12 8 1528, .n 2 7 12 9 2088, .n 2 7 12 10 8, .p 2 7 12 11 576, .p 2 7 12 12 128,
   .p 2 7 12 13 144, .p 2 7 13 3 8, .n 2 7 13 4 32, .n 2 7 13 5 480, .n 2 7 13 6 56, .p 2 7 13 7 616,
   .n 2 7 13 8 544, .n 2 7 13 9 168, .p 2 7 13 10 1344, .n 2 7 13 11 528, .n 2 7 13 12 104, .n 2 7 13 13 56,
   .p 2 7 14 4 8, .p 2 7 14 5 224, .p 2 7 14 6 216, .n 2 7 14 7 216, .n 2 7 14 8 128, .p 2 7 14 9 416,
   .n 2 7 14 10 696, .p 2 7 14 11 144, .p 2 7 14 12 24, .p 2 7 14 13 8, .n 2 7 15 5 40, .n 2 7 15 6 72,
   .n 2 7 15 7 64, .p 2 7 15 8 72, .p 2 7 15 9 8, .p 2 7 15 10 96, .p 2 7 16 7 40, .n 2 7 16 9 40,
   .p 3 6 5 8 8, .n 3 6 5 9 16, .p 3 6 5 10 8, .p 3 6 6 6 40, .n 3 6 6 7 8, .n 3 6 6 8 200,
   .p 3 6 6 9 232, .n 3 6 6 10 40, .n 3 6 6 11 16, .n 3 6 6 12 8, .n 3 6 7 4 8, .n 3 6 7 5 64,
   .n 3 6 7 6 56, .n 3 6 7 7 240, .p 3 6 7 8 992, .n 3 6 7 9 288, .n 3 6 7 10 592, .p 3 6 7 11 144,
   .p 3 6 7 12 96, .p 3 6 7 13 16, .p 3 6 8 3 48, .p 3 6 8 4 56, .p 3 6 8 5 216, .n 3 6 8 6 24,
   .p 3 6 8 7 96, .n 3 6 8 8 904, .n 3 6 8 9 1056, .p 3 6 8 10 2008, .n 3 6 8 11 24, .n 3 6 8 12 352,
   .n 3 6 8 13 64, .n 3 6 9 3 192, .n 3 6 9 4 208, .n 3 6 9 5 176, .p 3 6 9 6 280, .p 3 6 9 7 1128,
   .n 3 6 9 8 1288, .p 3 6 9 9 1912, .n 3 6 9 10 1096, .n 3 6 9 11 936, .p 3 6 9 12 424, .p 3 6 9 13 152,
   .p 3 6 10 3 288, .p 3 6 10 4 368, .n 3 6 10 5 224, .n 3 6 10 6 760, .n 3 6 10 7 920, .p 3 6 10 8 1496,
   .p 3 6 10 9 568, .n 3 6 10 10 2248, .p 3 6 10 11 1672, .p 3 6 10 12 88, .n 3 6 10 13 328, .n 3 6 11 3 192,
   .n 3 6 11 4 232, .p 3 6 11 5 488, .p 3 6 11 6 568, .n 3 6 11 7 584, .p 3 6 11 8 808, .n 3 6 11 9 2184,
   .p 3 6 11 10 2232, .n 3 6 11 11 952, .n 3 6 11 12 464, .p 3 6 11 13 512, .p 3 6 12 3 48, .n 3 6 12 4 104,
   .n 3 6 12 5 168, .p 3 6 12 6 344, .n 3 6 12 7 248, .n 3 6 12 8 552, .p 3 6 12 9 360, .p 3 6 12 10 744,
   .n 3 6 12 11 72, .p 3 6 12 12 112, .n 3 6 12 13 464, .p 3 6 13 4 192, .n 3 6 13 5 288, .n 3 6 13 6 408,
   .p 3 6 13 7 1496, .n 3 6 13 8 736, .p 3 6 13 9 248, .n 3 6 13 10 1216, .p 3 6 13 11 296, .p 3 6 13 12 200,
   .p 3 6 13 13 216, .n 3 6 14 4 64, .p 3 6 14 5 304, .n 3 6 14 6 112, .n 3 6 14 7 736, .p 3 6 14 8 208,
   .p 3 6 14 9 640, .p 3 6 14 10 48, .n 3 6 14 11 152, .n 3 6 14 12 96, .n 3 6 14 13 40, .n 3 6 15 5 88,
   .p 3 6 15 6 128, .n 3 6 15 7 8, .p 3 6 15 8 216, .n 3 6 15 9 440, .p 3 6 15 10 152, .p 3 6 15 11 40,
   .p 3 6 16 7 24, .n 3 6 16 8 48, .p 3 6 16 9 24, .n 4 5 6 6 40, .p 4 5 6 7 176, .n 4 5 6 8 248,
   .p 4 5 6 9 112, .n 4 5 6 10 8, .p 4 5 6 11 32, .n 4 5 6 12 24, .p 4 5 7 4 32, .p 4 5 7 5 112,
   .n 4 5 7 6 64, .n 4 5 7 7 784, .p 4 5 7 8 1008, .n 4 5 7 9 176, .p 4 5 7 10 48, .n 4 5 7 11 352,
   .p 4 5 7 12 192, .n 4 5 7 13 16, .n 4 5 8 3 112, .n 4 5 8 4 56, .n 4 5 8 5 32, .p 4 5 8 6 24,
   .p 4 5 8 7 1248, .n 4 5 8 8 464, .n 4 5 8 9 1600, .p 4 5 8 10 880, .p 4 5 8 11 336, .n 4 5 8 12 376,
   .p 4 5 8 13 160, .n 4 5 8 14 8, .p 4 5 9 3 304, .p 4 5 9 4 304, .n 4 5 9 5 1072, .p 4 5 9 6 672,
   .p 4 5 9 7 240, .n 4 5 9 8 3312, .p 4 5 9 9 3952, .n 4 5 9 10 1136, .p 4 5 9 11 480, .n 4 5 9 12 128,
   .n 4 5 9 13 320, .p 4 5 9 14 16, .n 4 5 10 3 192, .n 4 5 10 4 864, .p 4 5 10 5 1568, .n 4 5 10 6 32,
   .n 4 5 10 7 2544, .p 4 5 10 8 4896, .n 4 5 10 9 752, .n 4 5 10 10 3200, .n 4 5 10 11 176, .p 4 5 10 12 1120,
   .p 4 5 10 13 176, .n 4 5 11 3 128, .p 4 5 11 4 880, .p 4 5 11 5 432, .n 4 5 11 6 2416, .p 4 5 11 7 1280,
   .p 4 5 11 8 384, .n 4 5 11 9 4576, .p 4 5 11 10 5856, .n 4 5 11 11 416, .n 4 5 11 12 1232, .n 4 5 11 13 48,
   .n 4 5 11 14 16, .p 4 5 12 3 176, .n 4 5 12 4 328, .n 4 5 12 5 1856, .p 4 5 12 6 2760, .p 4 5 12 7 1856,
   .n 4 5 12 8 4432, .p 4 5 12 9 3104, .n 4 5 12 10 1104, .n 4 5 12 11 944, .p 4 5 12 12 536, .p 4 5 12 13 224,
   .p 4 5 12 14 8, .n 4 5 13 3 48, .p 4 5 13 4 64, .p 4 5 13 5 912, .n 4 5 13 6 816, .n 4 5 13 7 2000,
   .p 4 5 13 8 2160, .p 4 5 13 9 880, .n 4 5 13 10 2320, .p 4 5 13 11 1536, .n 4 5 13 12 112, .n 4 5 13 13 256,
   .n 4 5 14 4 32, .n 4 5 14 5 64, .n 4 5 14 6 152, .p 4 5 14 7 544, .p 4 5 14 8 248, .n 4 5 14 9 1120,
   .p 4 5 14 10 872, .n 4 5 14 11 400, .p 4 5 14 12 24, .p 4 5 14 13 80, .p 4 5 15 6 64, .n 4 5 15 7 16,
   .n 4 5 15 8 240, .p 4 5 15 9 176, .p 4 5 15 10 112, .n 4 5 15 11 96, .p 5 4 6 6 16, .n 5 4 6 7 72,
   .p 5 4 6 8 120, .n 5 4 6 9 80, .p 5 4 6 11 24, .n 5 4 6 12 8, .n 5 4 7 4 48, .n 5 4 7 5 48,
   .p 5 4 7 6 216, .p 5 4 7 7 328, .n 5 4 7 8 880, .p 5 4 7 9 272, .p 5 4 7 10 312, .n 5 4 7 11 152,
   .p 5 4 7 12 16, .n 5 4 7 13 16, .p 5 4 8 3 128, .n 5 4 8 4 136, .n 5 4 8 5 40, .p 5 4 8 6 264,
   .n 5 4 8 7 1264, .p 5 4 8 8 1104, .p 5 4 8 9 1264, .n 5 4 8 10 1760, .p 5 4 8 11 336, .p 5 4 8 12 24,
   .p 5 4 8 13 88, .n 5 4 8 14 8, .n 5 4 9 3 160, .n 5 4 9 4 72, .p 5 4 9 5 1144, .n 5 4 9 6 1504,
   .n 5 4 9 7 48, .p 5 4 9 8 2944, .n 5 4 9 9 3792, .p 5 4 9 10 576, .p 5 4 9 11 1584, .n 5 4 9 12 472,
   .n 5 4 9 13 264, .p 5 4 9 14 64, .p 5 4 10 2 8, .n 5 4 10 3 208, .p 5 4 10 4 808, .n 5 4 10 5 1088,
   .n 5 4 10 6 264, .p 5 4 10 7 3248, .n 5 4 10 8 4560, .p 5 4 10 9 432, .p 5 4 10 10 4696, .n 5 4 10 11 3808,
   .p 5 4 10 12 232, .p 5 4 10 13 656, .n 5 4 10 14 152, .n 5 4 11 2 16, .p 5 4 11 3 400, .n 5 4 11 4 672,
   .n 5 4 11 5 960, .p 5 4 11 6 3120, .n 5 4 11 7 2256, .n 5 4 11 8 1312, .p 5 4 11 9 4688, .n 5 4 11 10 4720,
   .p 5 4 11 11 1280, .p 5 4 11 12 1152, .n 5 4 11 13 848, .p 5 4 11 14 144, .p 5 4 12 2 8, .n 5 4 12 3 176,
   .p 5 4 12 4 264, .p 5 4 12 5 904, .n 5 4 12 6 2160, .p 5 4 12 7 48, .p 5 4 12 8 3152, .n 5 4 12 9 2320,
   .n 5 4 12 10 648, .p 5 4 12 11 1696, .n 5 4 12 12 1080, .p 5 4 12 13 360, .n 5 4 12 14 48, .p 5 4 13 3 16,
   .n 5 4 13 4 232, .p 5 4 13 5 328, .p 5 4 13 6 192, .n 5 4 13 7 144, .n 5 4 13 8 320, .n 5 4 13 9 848,
   .p 5 4 13 10 1952, .n 5 4 13 11 992, .n 5 4 13 12 56, .p 5 4 13 13 104, .p 5 4 14 4 88, .n 5 4 14 5 288,
   .p 5 4 14 6 240, .p 5 4 14 7 88, .n 5 4 14 8 200, .p 5 4 14 9 192, .n 5 4 14 10 192, .n 5 4 14 11 40,
   .p 5 4 14 12 192, .n 5 4 14 13 80, .p 5 4 15 5 48, .n 5 4 15 6 120, .p 5 4 15 7 72, .n 5 4 15 8 48,
   .p 5 4 15 9 192, .n 5 4 15 10 216, .p 5 4 15 11 72, .p 6 3 7 4 32, .n 6 3 7 5 32, .n 6 3 7 6 192,
   .p 6 3 7 7 384, .n 6 3 7 8 160, .n 6 3 7 9 32, .n 6 3 7 10 128, .p 6 3 7 11 192, .n 6 3 7 12 64,
   .n 6 3 8 3 72, .p 6 3 8 4 208, .n 6 3 8 5 120, .n 6 3 8 6 56, .n 6 3 8 7 96, .p 6 3 8 8 96,
   .p 6 3 8 9 224, .n 6 3 8 10 80, .n 6 3 8 11 344, .p 6 3 8 12 336, .n 6 3 8 13 104, .p 6 3 8 14 8,
   .p 6 3 9 3 8, .n 6 3 9 4 72, .p 6 3 9 5 96, .p 6 3 9 6 176, .n 6 3 9 7 464, .p 6 3 9 8 448,
   .n 6 3 9 9 704, .p 6 3 9 10 1104, .n 6 3 9 11 696, .n 6 3 9 12 56, .p 6 3 9 13 224, .n 6 3 9 14 64,
   .n 6 3 10 2 24, .p 6 3 10 3 128, .n 6 3 10 4 136, .n 6 3 10 5 440, .p 6 3 10 6 672, .p 6 3 10 7 992,
   .n 6 3 10 8 1888, .n 6 3 10 9 112, .p 6 3 10 10 760, .p 6 3 10 11 928, .n 6 3 10 12 1048, .p 6 3 10 13 40,
   .p 6 3 10 14 128, .p 6 3 11 2 16, .p 6 3 11 3 184, .n 6 3 11 4 368, .n 6 3 11 5 120, .p 6 3 11 6 368,
   .n 6 3 11 7 320, .p 6 3 11 8 288, .p 6 3 11 9 1472, .n 6 3 11 10 2480, .p 6 3 11 11 392, .p 6 3 11 12 784,
   .n 6 3 11 13 72, .n 6 3 11 14 144, .p 6 3 12 2 8, .n 6 3 12 3 312, .p 6 3 12 4 264, .p 6 3 12 5 1352,
   .n 6 3 12 6 1608, .n 6 3 12 7 1344, .p 6 3 12 8 2416, .n 6 3 12 9 736, .p 6 3 12 10 248, .n 6 3 12 11 392,
   .p 6 3 12 12 136, .n 6 3 12 13 104, .p 6 3 12 14 72, .p 6 3 13 3 64, .p 6 3 13 4 24, .n 6 3 13 5 600,
   .p 6 3 13 6 624, .p 6 3 13 7 576, .n 6 3 13 8 960, .n 6 3 13 9 144, .p 6 3 13 10 720, .n 6 3 13 11 384,
   .p 6 3 13 12 104, .n 6 3 13 13 24, .p 6 3 14 4 48, .n 6 3 14 5 152, .p 6 3 14 6 80, .p 6 3 14 7 192,
   .n 6 3 14 8 240, .p 6 3 14 9 112, .n 6 3 14 10 208, .p 6 3 14 11 320, .n 6 3 14 12 192, .p 6 3 14 13 40,
   .p 6 3 15 5 16, .n 6 3 15 6 64, .p 6 3 15 7 80, .n 6 3 15 9 80, .p 6 3 15 10 64, .n 6 3 15 11 16,
   .n 7 2 7 4 8, .p 7 2 7 5 16, .p 7 2 7 6 48, .n 7 2 7 7 176, .p 7 2 7 8 160, .p 7 2 7 9 48,
   .n 7 2 7 10 176, .p 7 2 7 11 112, .n 7 2 7 12 24, .p 7 2 8 3 16, .n 7 2 8 4 64, .p 7 2 8 5 80,
   .n 7 2 8 6 40, .p 7 2 8 7 112, .n 7 2 8 8 272, .p 7 2 8 9 176, .p 7 2 8 10 160, .n 7 2 8 11 320,
   .p 7 2 8 12 208, .n 7 2 8 13 64, .p 7 2 8 14 8, .p 7 2 9 4 16, .n 7 2 9 5 248, .p 7 2 9 6 752,
   .n 7 2 9 7 496, .n 7 2 9 8 1008, .p 7 2 9 9 1568, .n 7 2 9 10 112, .n 7 2 9 11 912, .p 7 2 9 12 416,
   .p 7 2 9 13 88, .n 7 2 9 14 64, .p 7 2 10 2 16, .p 7 2 10 3 64, .n 7 2 10 4 408, .p 7 2 10 5 632,
   .n 7 2 10 6 24, .n 7 2 10 7 1600, .p 7 2 10 8 2816, .n 7 2 10 9 1024, .n 7 2 10 10 2416, .p 7 2 10 11 2704,
   .n 7 2 10 12 296, .n 7 2 10 13 760, .p 7 2 10 14 312, .n 7 2 10 15 16, .p 7 2 11 2 32, .n 7 2 11 3 344,
   .p 7 2 11 4 712, .p 7 2 11 5 440, .n 7 2 11 6 2752, .p 7 2 11 7 2368, .p 7 2 11 8 992, .n 7 2 11 9 2848,
   .p 7 2 11 10 1840, .n 7 2 11 11 168, .n 7 2 11 12 680, .p 7 2 11 13 552, .n 7 2 11 14 144, .n 7 2 12 2 32,
   .p 7 2 12 3 176, .n 7 2 12 4 184, .n 7 2 12 5 512, .p 7 2 12 6 1136, .p 7 2 12 7 16, .n 7 2 12 8 1696,
   .p 7 2 12 9 1136, .p 7 2 12 10 592, .n 7 2 12 11 896, .p 7 2 12 12 216, .p 7 2 12 13 80, .n 7 2 12 14 32,
   .p 7 2 13 3 8, .p 7 2 13 4 32, .n 7 2 13 5 256, .p 7 2 13 6 464, .n 7 2 13 7 192, .n 7 2 13 8 304,
   .p 7 2 13 9 368, .n 7 2 13 10 144, .p 7 2 13 11 56, .n 7 2 13 12 48, .p 7 2 13 13 16, .p 7 2 14 5 8,
   .n 7 2 14 6 48, .p 7 2 14 7 112, .n 7 2 14 8 112, .p 7 2 14 10 112, .n 7 2 14 11 112, .p 7 2 14 12 48,
   .n 7 2 14 13 8, .n 8 1 10 5 32, .p 8 1 10 6 128, .n 8 1 10 7 96, .n 8 1 10 8 256, .p 8 1 10 9 448,
   .n 8 1 10 11 448, .p 8 1 10 12 256, .p 8 1 10 13 96, .n 8 1 10 14 128, .p 8 1 10 15 32, .p 8 1 11 3 32,
   .n 8 1 11 4 96, .n 8 1 11 5 32, .p 8 1 11 6 352, .n 8 1 11 7 192, .n 8 1 11 8 448, .p 8 1 11 9 448,
   .p 8 1 11 10 192, .n 8 1 11 11 352, .p 8 1 11 12 32, .p 8 1 11 13 96, .n 8 1 11 14 32, .n 8 1 12 2 32,
   .p 8 1 12 3 128, .n 8 1 12 4 96, .n 8 1 12 5 256, .p 8 1 12 6 448, .n 8 1 12 8 448, .p 8 1 12 9 256,
   .p 8 1 12 10 96, .n 8 1 12 11 128, .p 8 1 12 12 32, .p 9 0 10 4 32, .n 9 0 10 5 160, .p 9 0 10 6 224,
   .p 9 0 10 7 160, .n 9 0 10 8 704, .p 9 0 10 9 448, .p 9 0 10 10 448, .n 9 0 10 11 704, .p 9 0 10 12 160,
   .p 9 0 10 13 224, .n 9 0 10 14 160, .p 9 0 10 15 32, .n 9 0 11 2 32, .p 9 0 11 3 160, .n 9 0 11 4 224,
   .n 9 0 11 5 160, .p 9 0 11 6 704, .n 9 0 11 7 448, .n 9 0 11 8 448, .p 9 0 11 9 704, .n 9 0 11 10 160,
   .n 9 0 11 11 224, .p 9 0 11 12 160, .n 9 0 11 13 32]

set_option maxRecDepth 65536 in
private theorem g2_comb6_step1 :
    fmMerge g2Comb6_0 (fmMul (fmNeg (g2FM ⟨0, by decide⟩ ⟨1, by decide⟩)) g2Val5_1) = g2Comb6_1 := rfl

private def g2Comb6_2 : List FM :=
  [.p 0 9 5 8 32, .n 0 9 6 8 192, .p 0 9 6 10 32, .p 0 9 7 8 384, .n 0 9 7 10 160, .n 0 9 8 8 96,
   .p 0 9 8 10 256, .n 0 9 9 8 704, .p 0 9 10 8 896, .n 0 9 10 10 448, .p 0 9 11 10 448, .n 0 9 12 8 704,
   .p 0 9 13 8 416, .n 0 9 13 10 256, .p 0 9 14 8 64, .p 0 9 14 10 160, .n 0 9 15 8 128, .n 0 9 15 10 32,
   .p 0 9 16 8 32, .n 1 8 5 8 32, .n 1 8 5 9 48, .p 1 8 5 10 16, .p 1 8 6 7 16, .p 1 8 6 8 176,
   .p 1 8 6 9 144, .n 1 8 6 10 48, .p 1 8 6 11 16, .p 1 8 6 12 16, .n 1 8 7 7 64, .n 1 8 7 8 288,
   .p 1 8 7 10 64, .n 1 8 7 11 80, .n 1 8 7 12 80, .p 1 8 8 5 16, .p 1 8 8 6 16, .p 1 8 8 7 64,
   .n 1 8 8 8 96, .n 1 8 8 9 464, .n 1 8 8 10 144, .p 1 8 8 11 144, .p 1 8 8 12 144, .n 1 8 9 5 80,
   .n 1 8 9 6 80, .p 1 8 9 7 80, .p 1 8 9 8 784, .p 1 8 9 9 624, .p 1 8 9 10 240, .n 1 8 9 11 80,
   .n 1 8 9 12 80, .p 1 8 10 5 144, .p 1 8 10 6 144, .n 1 8 10 7 240, .n 1 8 10 8 688, .n 1 8 10 9 112,
   .p 1 8 10 10 16, .n 1 8 10 11 80, .n 1 8 10 12 80, .n 1 8 11 5 80, .n 1 8 11 6 80, .p 1 8 11 7 208,
   .n 1 8 11 8 240, .n 1 8 11 9 560, .n 1 8 11 10 432, .p 1 8 11 11 144, .p 1 8 11 12 144, .n 1 8 12 5 80,
   .n 1 8 12 6 80, .n 1 8 12 7 16, .p 1 8 12 8 688, .p 1 8 12 9 720, .p 1 8 12 10 336, .n 1 8 12 11 80,
   .n 1 8 12 12 80, .p 1 8 13 5 144, .p 1 8 13 6 144, .n 1 8 13 7 144, .n 1 8 13 8 304, .n 1 8 13 9 256,
   .p 1 8 13 10 64, .p 1 8 13 11 16, .p 1 8 13 12 16, .n 1 8 14 5 80, .n 1 8 14 6 80, .p 1 8 14 7 160,
   .n 1 8 14 8 64, .n 1 8 14 9 224, .n 1 8 14 10 160, .p 1 8 15 5 16, .p 1 8 15 6 16, .n 1 8 15 7 80,
   .p 1 8 15 8 80, .p 1 8 15 9 240, .p 1 8 15 10 48, .p 1 8 16 7 16, .n 1 8 16 8 16, .n 1 8 16 9 64,
   .p 2 7 5 8 40, .n 2 7 5 10 40, .n 2 7 6 7 112, .p 2 7 6 8 280, .n 2 7 6 9 168, .n 2 7 6 10 32,
   .n 2 7 6 11 8, .p 2 7 6 12 40, .n 2 7 7 5 8, .n 2 7 7 6 32, .p 2 7 7 7 376, .n 2 7 7 8 1392,
   .p 2 7 7 9 384, .p 2 7 7 10 776, .p 2 7 7 11 8, .n 2 7 7 12 120, .p 2 7 7 13 8, .n 2 7 8 3 8,
   .n 2 7 8 5 56, .p 2 7 8 6 184, .n 2 7 8 7 48, .p 2 7 8 8 1048, .p 2 7 8 9 384, .n 2 7 8 10 1432,
   .n 2 7 8 11 80, .p 2 7 8 12 40, .n 2 7 8 13 32, .p 2 7 9 3 40, .p 2 7 9 5 328, .n 2 7 9 6 360,
   .n 2 7 9 7 1192, .p 2 7 9 8 2472, .n 2 7 9 9 1672, .n 2 7 9 10 264, .p 2 7 9 11 416, .p 2 7 9 12 200,
   .p 2 7 9 13 32, .n 2 7 10 3 80, .n 2 7 10 5 496, .p 2 7 10 6 184, .p 2 7 10 7 1448, .n 2 7 10 8 4056,
   .p 2 7 10 9 920, .p 2 7 10 10 2856, .n 2 7 10 11 616, .n 2 7 10 12 200, .p 2 7 10 13 40, .p 2 7 11 3 80,
   .p 2 7 11 5 80, .p 2 7 11 6 280, .p 2 7 11 7 120, .p 2 7 11 8 312, .p 2 7 11 9 1288, .n 2 7 11 10 2088,
   .p 2 7 11 11 88, .n 2 7 11 12 40, .n 2 7 11 13 120, .n 2 7 12 3 40, .p 2 7 12 5 488, .n 2 7 12 6 408,
   .n 2 7 12 7 1096, .p 2 7 12 8 2792, .n 2 7 12 9 1704, .n 2 7 12 10 776, .p 2 7 12 11 512, .p 2 7 12 12 120,
   .p 2 7 12 13 112, .p 2 7 13 3 8, .n 2 7 13 5 504, .p 2 7 13 6 136, .p 2 7 13 7 488, .n 2 7 13 8 1648,
   .p 2 7 13 9 456, .p 2 7 13 10 1552, .n 2 7 13 11 400, .n 2 7 13 12 40, .n 2 7 13 13 48, .p 2 7 14 5 192,
   .p 2 7 14 6 40, .p 2 7 14 7 72, .n 2 7 14 8 32, .p 2 7 14 9 272, .n 2 7 14 10 616, .p 2 7 14 11 64,
   .p 2 7 14 13 8, .n 2 7 15 5 24, .n 2 7 15 6 24, .n 2 7 15 7 48, .p 2 7 15 8 216, .n 2 7 15 9 200,
   .p 2 7 15 10 64, .p 2 7 15 11 16, .n 2 7 16 7 8, .n 2 7 16 8 32, .p 2 7 16 9 40, .n 3 6 5 8 24,
   .p 3 6 5 9 48, .n 3 6 5 10 24, .n 3 6 6 6 32, .n 3 6 6 7 8, .n 3 6 6 8 48, .p 3 6 6 9 72,
   .p 3 6 6 10 192, .n 3 6 6 11 176, .n 3 6 7 4 8, .p 3 6 7 5 32, .p 3 6 7 6 72, .n 3 6 7 7 56,
   .p 3 6 7 8 608, .n 3 6 7 9 744, .n 3 6 7 10 432, .p 3 6 7 11 376, .p 3 6 7 12 128, .p 3 6 7 13 24,
   .p 3 6 8 3 48, .p 3 6 8 4 32, .p 3 6 8 5 8, .n 3 6 8 6 264, .n 3 6 8 8 520, .p 3 6 8 9 480,
   .p 3 6 8 10 712, .n 3 6 8 11 24, .n 3 6 8 12 392, .n 3 6 8 13 80, .n 3 6 9 3 192, .n 3 6 9 4 96,
   .n 3 6 9 5 136, .p 3 6 9 6 728, .p 3 6 9 7 696, .n 3 6 9 8 1512, .p 3 6 9 9 1016, .n 3 6 9 10 392,
   .n 3 6 9 11 504, .p 3 6 9 12 280, .p 3 6 9 13 112, .p 3 6 10 3 288, .p 3 6 10 4 168, .n 3 6 10 5 160,
   .n 3 6 10 6 600, .n 3 6 10 7 1144, .p 3 6 10 8 2248, .n 3 6 10 9 168, .n 3 6 10 10 1448, .p 3 6 10 11 744,
   .p 3 6 10 12 240, .n 3 6 10 13 168, .n 3 6 11 3 192, .n 3 6 11 4 72, .p 3 6 11 5 640, .n 3 6 11 6 360,
   .p 3 6 11 7 216, .p 3 6 11 8 72, .n 3 6 11 9 1432, .p 3 6 11 10 2008, .n 3 6 11 11 792, .n 3 6 11 12 400,
   .p 3 6 11 13 312, .p 3 6 12 3 48, .n 3 6 12 4 144, .n 3 6 12 5 312, .p 3 6 12 6 776, .p 3 6 12 7 456,
   .n 3 6 12 8 1448, .p 3 6 12 9 136, .p 3 6 12 10 312, .p 3 6 12 11 376, .p 3 6 12 12 152, .n 3 6 12 13 352,
   .p 3 6 13 4 176, .n 3 6 13 5 328, .n 3 6 13 6 408, .p 3 6 13 7 200, .p 3 6 13 8 800, .p 3 6 13 9 632,
   .n 3 6 13 10 1312, .p 3 6 13 11 56, .n 3 6 13 12 8, .p 3 6 13 13 192, .n 3 6 14 4 56, .p 3 6 14 5 336,
   .p 3 6 14 6 120, .n 3 6 14 7 576, .n 3 6 14 8 248, .p 3 6 14 9 256, .p 3 6 14 10 232, .n 3 6 14 11 24,
   .n 3 6 14 13 40, .n 3 6 15 5 80, .n 3 6 15 6 32, .p 3 6 15 7 224, .p 3 6 15 8 56, .n 3 6 15 9 288,
   .p 3 6 15 10 152, .n 3 6 15 11 32, .n 3 6 16 7 8, .p 3 6 16 8 16, .n 3 6 16 9 8, .p 4 5 6 6 72,
   .n 4 5 6 7 48, .n 4 5 6 8 136, .p 4 5 6 9 48, .p 4 5 6 10 72, .p 4 5 6 11 64, .n 4 5 6 12 72,
   .p 4 5 7 4 32, .n 4 5 7 5 8, .p 4 5 7 6 48, .n 4 5 7 7 992, .p 4 5 7 8 1696, .n 4 5 7 9 400,
   .n 4 5 7 10 512, .n 4 5 7 11 80, .p 4 5 7 12 208, .p 4 5 7 13 8, .n 4 5 8 3 112, .n 4 5 8 4 40,
   .p 4 5 8 5 144, .n 4 5 8 6 64, .p 4 5 8 7 1456, .n 4 5 8 8 1808, .n 4 5 8 9 752, .p 4 5 8 10 1600,
   .n 4 5 8 11 256, .n 4 5 8 12 200, .p 4 5 8 13 32, .p 4 5 9 3 296, .p 4 5 9 4 224, .n 4 5 9 5 1088,
   .n 4 5 9 6 96, .p 4 5 9 7 2336, .n 4 5 9 8 4192, .p 4 5 9 9 3056, .p 4 5 9 10 32, .n 4 5 9 11 456,
   .n 4 5 9 12 64, .n 4 5 9 13 48, .n 4 5 10 3 176, .n 4 5 10 4 664, .p 4 5 10 5 1824, .n 4 5 10 6 416,
   .n 4 5 10 7 4160, .p 4 5 10 8 7248, .n 4 5 10 9 1344, .n 4 5 10 10 4864, .p 4 5 10 11 2064, .p 4 5 10 12 616,
   .n 4 5 10 13 128, .n 4 5 11 3 128, .p 4 5 11 4 576, .n 4 5 11 5 72, .n 4 5 11 6 176, .n 4 5 11 7 384,
   .n 4 5 11 8 208, .n 4 5 11 9 2224, .p 4 5 11 10 4240, .n 4 5 11 11 800, .n 4 5 11 12 976, .p 4 5 11 13 152,
   .p 4 5 12 3 160, .n 4 5 12 4 56, .n 4 5 12 5 1792, .p 4 5 12 6 1824, .p 4 5 12 7 3024, .n 4 5 12 8 5328,
   .p 4 5 12 9 2224, .p 4 5 12 10 992, .n 4 5 12 11 1712, .p 4 5 12 12 520, .p 4 5 12 13 144, .n 4 5 13 3 40,
   .n 4 5 13 4 64, .p 4 5 13 5 1088, .n 4 5 13 6 1408, .n 4 5 13 7 1280, .p 4 5 13 8 3008, .n 4 5 13 9 464,
   .n 4 5 13 10 2112, .p 4 5 13 11 1448, .p 4 5 13 12 64, .n 4 5 13 13 240, .n 4 5 14 4 8, .n 4 5 14 5 48,
   .p 4 5 14 6 120, .n 4 5 14 7 16, .p 4 5 14 8 24, .n 4 5 14 9 432, .p 4 5 14 10 664, .n 4 5 14 11 288,
   .n 4 5 14 12 96, .p 4 5 14 13 80, .n 4 5 15 5 48, .p 4 5 15 6 96, .p 4 5 15 7 64, .n 4 5 15 8 304,
   .p 4 5 15 9 288, .n 4 5 15 10 112, .p 4 5 15 11 16, .n 5 4 6 6 56, .p 5 4 6 7 152, .n 5 4 6 8 112,
   .p 5 4 6 9 48, .n 5 4 6 10 152, .p 5 4 6 11 184, .n 5 4 6 12 64, .n 5 4 7 4 48, .p 5 4 7 6 104,
   .p 5 4 7 7 448, .n 5 4 7 8 1152, .p 5 4 7 9 712, .p 5 4 7 10 104, .n 5 4 7 11 240, .p 5 4 7 12 96,
   .n 5 4 7 13 24, .p 5 4 8 3 128, .n 5 4 8 4 144, .n 5 4 8 5 56, .p 5 4 8 6 312, .n 5 4 8 7 1184,
   .p 5 4 8 8 1072, .p 5 4 8 9 672, .n 5 4 8 10 784, .n 5 4 8 11 192, .p 5 4 8 12 64, .p 5 4 8 13 120,
   .n 5 4 8 14 8, .n 5 4 9 3 128, .n 5 4 9 4 88, .p 5 4 9 5 1040, .n 5 4 9 6 1504, .p 5 4 9 8 3504,
   .n 5 4 9 9 4720, .p 5 4 9 10 1040, .p 5 4 9 11 1504, .n 5 4 9 12 440, .n 5 4 9 13 256, .p 5 4 9 14 48,
   .p 5 4 10 2 8, .n 5 4 10 3 288, .p 5 4 10 4 912, .n 5 4 10 5 896, .n 5 4 10 6 360, .p 5 4 10 7 2496,
   .n 5 4 10 8 3616, .p 5 4 10 9 416, .p 5 4 10 10 3896, .n 5 4 10 11 3040, .p 5 4 10 12 16, .p 5 4 10 13 544,
   .n 5 4 10 14 88, .n 5 4 11 2 16, .p 5 4 11 3 464, .n 5 4 11 4 784, .n 5 4 11 5 1176, .p 5 4 11 6 3888,
   .n 5 4 11 7 3056, .n 5 4 11 8 1328, .p 5 4 11 9 5632, .n 5 4 11 10 5472, .p 5 4 11 11 1184, .p 5 4 11 12 1344,
   .n 5 4 11 13 744, .p 5 4 11 14 64, .p 5 4 12 2 8, .n 5 4 12 3 192, .p 5 4 12 4 272, .p 5 4 12 5 936,
   .n 5 4 12 6 2240, .p 5 4 12 7 512, .p 5 4 12 8 2224, .n 5 4 12 9 1760, .n 5 4 12 10 600, .p 5 4 12 11 1696,
   .n 5 4 12 12 1184, .p 5 4 12 13 344, .n 5 4 12 14 16, .p 5 4 13 3 16, .n 5 4 13 4 200, .p 5 4 13 5 368,
   .n 5 4 13 6 336, .p 5 4 13 7 832, .n 5 4 13 8 912, .n 5 4 13 9 880, .p 5 4 13 10 2032, .n 5 4 13 11 944,
   .n 5 4 13 12 72, .p 5 4 13 13 96, .p 5 4 14 4 80, .n 5 4 14 5 208, .p 5 4 14 6 152, .n 5 4 14 7 120,
   .p 5 4 14 8 240, .n 5 4 14 9 80, .n 5 4 14 10 72, .n 5 4 14 11 152, .p 5 4 14 12 240, .n 5 4 14 13 80,
   .n 5 4 15 5 8, .p 5 4 15 6 40, .n 5 4 15 7 80, .p 5 4 15 8 80, .n 5 4 15 9 40, .p 5 4 15 10 8,
   .p 6 3 6 6 16, .n 6 3 6 7 64, .p 6 3 6 8 80, .n 6 3 6 10 80, .p 6 3 6 11 64, .n 6 3 6 12 16,
   .p 6 3 7 4 32, .n 6 3 7 5 32, .n 6 3 7 6 160, .p 6 3 7 7 272, .n 6 3 7 8 64, .p 6 3 7 9 48,
   .n 6 3 7 10 288, .p 6 3 7 11 240, .n 6 3 7 12 32, .n 6 3 7 13 16, .n 6 3 8 3 72, .p 6 3 8 4 232,
   .n 6 3 8 5 168, .p 6 3 8 6 48, .n 6 3 8 7 512, .p 6 3 8 8 688, .p 6 3 8 9 224, .n 6 3 8 10 672,
   .p 6 3 8 11 72, .p 6 3 8 12 232, .n 6 3 8 13 56, .n 6 3 8 14 16, .n 6 3 9 3 32, .n 6 3 9 4 72,
   .p 6 3 9 5 168, .p 6 3 9 6 576, .n 6 3 9 7 1280, .p 6 3 9 8 672, .n 6 3 9 9 336, .p 6 3 9 10 592,
   .n 6 3 9 11 96, .n 6 3 9 12 280, .p 6 3 9 13 40, .p 6 3 9 14 48, .n 6 3 10 2 24, .p 6 3 10 3 208,
   .n 6 3 10 4 152, .n 6 3 10 5 776, .p 6 3 10 6 480, .p 6 3 10 7 2528, .n 6 3 10 8 3392, .n 6 3 10 9 48,
   .p 6 3 10 10 1976, .n 6 3 10 11 560, .n 6 3 10 12 424, .p 6 3 10 13 184, .p 6 3 11 2 16, .p 6 3 11 3 56,
   .n 6 3 11 4 224, .p 6 3 11 5 504, .n 6 3 11 6 1120, .p 6 3 11 7 896, .p 6 3 11 8 352, .n 6 3 11 9 32,
   .n 6 3 11 10 944, .p 6 3 11 11 200, .p 6 3 11 12 448, .n 6 3 11 13 88, .n 6 3 11 14 64, .p 6 3 12 2 8,
   .n 6 3 12 3 200, .p 6 3 12 4 80, .p 6 3 12 5 1128, .n 6 3 12 6 1008, .n 6 3 12 7 1856, .p 6 3 12 8 2784,
   .n 6 3 12 9 512, .n 6 3 12 10 568, .p 6 3 12 11 8, .p 6 3 12 12 208, .n 6 3 12 13 104, .p 6 3 12 14 32,
   .p 6 3 13 3 40, .p 6 3 13 4 72, .n 6 3 13 5 704, .p 6 3 13 6 1040, .n 6 3 13 7 16, .n 6 3 13 8 960,
   .p 6 3 13 9 448, .p 6 3 13 10 304, .n 6 3 13 11 280, .p 6 3 13 12 56, .p 6 3 14 4 32, .n 6 3 14 5 120,
   .p 6 3 14 6 128, .p 6 3 14 7 32, .n 6 3 14 8 160, .p 6 3 14 9 208, .n 6 3 14 10 320, .p 6 3 14 11 352,
   .n 6 3 14 12 192, .p 6 3 14 13 40, .n 7 2 7 4 8, .p 7 2 7 5 16, .p 7 2 7 6 48, .n 7 2 7 7 176,
   .p 7 2 7 8 160, .p 7 2 7 9 48, .n 7 2 7 10 176, .p 7 2 7 11 112, .n 7 2 7 12 24, .p 7 2 8 3 16,
   .n 7 2 8 4 80, .p 7 2 8 5 112, .p 7 2 8 6 8, .n 7 2 8 7 16, .n 7 2 8 8 304, .p 7 2 8 9 368,
   .p 7 2 8 10 128, .n 7 2 8 11 448, .p 7 2 8 12 256, .n 7 2 8 13 32, .n 7 2 8 14 8, .p 7 2 9 3 16,
   .n 7 2 9 4 48, .n 7 2 9 5 232, .p 7 2 9 6 976, .n 7 2 9 7 720, .n 7 2 9 8 1264, .p 7 2 9 9 1984,
   .n 7 2 9 10 48, .n 7 2 9 11 1216, .p 7 2 9 12 480, .p 7 2 9 13 168, .n 7 2 9 14 96, .p 7 2 10 2 16,
   .p 7 2 10 3 80, .n 7 2 10 4 408, .p 7 2 10 5 472, .p 7 2 10 6 168, .n 7 2 10 7 1360, .p 7 2 10 8 2304,
   .n 7 2 10 9 960, .n 7 2 10 10 2032, .p 7 2 10 11 2432, .n 7 2 10 12 296, .n 7 2 10 13 664, .p 7 2 10 14 248,
   .p 7 2 11 2 48, .n 7 2 11 3 408, .p 7 2 11 4 808, .p 7 2 11 5 440, .n 7 2 11 6 3024, .p 7 2 11 7 2752,
   .p 7 2 11 8 1056, .n 7 2 11 9 3360, .p 7 2 11 10 2080, .p 7 2 11 11 24, .n 7 2 11 12 840, .p 7 2 11 13 552,
   .n 7 2 11 14 128, .n 7 2 12 2 32, .p 7 2 12 3 144, .n 7 2 12 4 104, .n 7 2 12 5 448, .p 7 2 12 6 832,
   .p 7 2 12 7 80, .n 7 2 12 8 1280, .p 7 2 12 9 880, .p 7 2 12 10 368, .n 7 2 12 11 672, .p 7 2 12 12 232,
   .p 7 2 12 13 16, .n 7 2 12 14 16, .n 7 2 13 3 8, .p 7 2 13 4 64, .n 7 2 13 5 208, .p 7 2 13 6 336,
   .n 7 2 13 7 224, .n 7 2 13 8 112, .p 7 2 13 9 336, .n 7 2 13 10 272, .p 7 2 13 11 104, .n 7 2 13 12 16,
   .p 7 2 14 5 8, .n 7 2 14 6 48, .p 7 2 14 7 112, .n 7 2 14 8 112, .p 7 2 14 10 112, .n 7 2 14 11 112,
   .p 7 2 14 12 48, .n 7 2 14 13 8, .p 8 1 10 3 32, .n 8 1 10 4 128, .p 8 1 10 5 96, .p 8 1 10 6 256,
   .n 8 1 10 7 448, .p 8 1 10 9 448, .n 8 1 10 10 256, .n 8 1 10 11 96, .p 8 1 10 12 128, .n 8 1 10 13 32,
   .n 8 1 11 2 32, .p 8 1 11 3 160, .n 8 1 11 4 224, .n 8 1 11 5 160, .p 8 1 11 6 704, .n 8 1 11 7 448,
   .n 8 1 11 8 448, .p 8 1 11 9 704, .n 8 1 11 10 160, .n 8 1 11 11 224, .p 8 1 11 12 160, .n 8 1 11 13 32,
   .n 8 1 12 2 32, .p 8 1 12 3 128, .n 8 1 12 4 96, .n 8 1 12 5 256, .p 8 1 12 6 448, .n 8 1 12 8 448,
   .p 8 1 12 9 256, .p 8 1 12 10 96, .n 8 1 12 11 128, .p 8 1 12 12 32, .p 9 0 10 4 32, .n 9 0 10 5 160,
   .p 9 0 10 6 224, .p 9 0 10 7 160, .n 9 0 10 8 704, .p 9 0 10 9 448, .p 9 0 10 10 448, .n 9 0 10 11 704,
   .p 9 0 10 12 160, .p 9 0 10 13 224, .n 9 0 10 14 160, .p 9 0 10 15 32, .n 9 0 11 2 32, .p 9 0 11 3 160,
   .n 9 0 11 4 224, .n 9 0 11 5 160, .p 9 0 11 6 704, .n 9 0 11 7 448, .n 9 0 11 8 448, .p 9 0 11 9 704,
   .n 9 0 11 10 160, .n 9 0 11 11 224, .p 9 0 11 12 160, .n 9 0 11 13 32]

set_option maxRecDepth 65536 in
private theorem g2_comb6_step2 :
    fmMerge g2Comb6_1 (fmMul (g2FM ⟨0, by decide⟩ ⟨2, by decide⟩) g2Val5_2) = g2Comb6_2 := rfl

private def g2Comb6_3 : List FM :=
  [.p 0 9 5 8 64, .n 0 9 5 9 64, .p 0 9 5 10 32, .n 0 9 6 7 32, .n 0 9 6 8 224, .p 0 9 6 9 192,
   .n 0 9 6 10 128, .p 0 9 6 11 32, .p 0 9 7 7 96, .p 0 9 7 8 128, .p 0 9 7 9 64, .p 0 9 7 10 96,
   .n 0 9 7 11 160, .p 0 9 8 7 32, .p 0 9 8 8 416, .n 0 9 8 9 832, .p 0 9 8 10 256, .p 0 9 8 11 288,
   .n 0 9 9 7 416, .n 0 9 9 8 640, .p 0 9 9 9 960, .n 0 9 9 10 448, .n 0 9 9 11 160, .p 0 9 10 7 480,
   .p 0 9 10 8 64, .p 0 9 10 9 64, .n 0 9 10 11 160, .p 0 9 11 7 32, .p 0 9 11 8 512, .n 0 9 11 9 832,
   .p 0 9 11 10 448, .p 0 9 11 11 288, .n 0 9 12 7 416, .n 0 9 12 8 448, .p 0 9 12 9 576, .n 0 9 12 10 256,
   .n 0 9 12 11 160, .p 0 9 13 7 288, .p 0 9 13 8 64, .n 0 9 13 9 128, .n 0 9 13 10 96, .p 0 9 13 11 32,
   .n 0 9 14 7 64, .p 0 9 14 8 160, .p 0 9 14 10 128, .n 0 9 15 8 128, .n 0 9 15 10 32, .p 0 9 16 8 32,
   .n 1 8 5 8 64, .p 1 8 5 9 32, .n 1 8 5 10 48, .p 1 8 5 11 16, .p 1 8 6 7 32, .p 1 8 6 8 240,
   .n 1 8 6 9 48, .p 1 8 6 10 112, .n 1 8 6 11 48, .p 1 8 6 12 16, .p 1 8 6 13 16, .n 1 8 7 7 160,
   .n 1 8 7 8 160, .n 1 8 7 9 80, .p 1 8 7 10 64, .p 1 8 7 11 48, .n 1 8 7 12 80, .n 1 8 7 13 80,
   .p 1 8 8 5 32, .p 1 8 8 6 16, .p 1 8 8 7 192, .n 1 8 8 8 480, .p 1 8 8 9 96, .n 1 8 8 10 400,
   .n 1 8 8 11 80, .p 1 8 8 12 144, .p 1 8 8 13 160, .n 1 8 9 5 128, .n 1 8 9 6 80, .p 1 8 9 7 208,
   .p 1 8 9 8 848, .p 1 8 9 9 192, .p 1 8 9 10 368, .p 1 8 9 11 240, .n 1 8 9 12 80, .n 1 8 9 13 160,
   .p 1 8 10 5 144, .p 1 8 10 6 144, .n 1 8 10 7 560, .n 1 8 10 8 176, .n 1 8 10 9 192, .p 1 8 10 10 80,
   .n 1 8 10 11 336, .n 1 8 10 12 80, .p 1 8 10 13 80, .p 1 8 11 5 80, .n 1 8 11 6 80, .p 1 8 11 7 112,
   .n 1 8 11 8 624, .n 1 8 11 9 288, .n 1 8 11 10 432, .p 1 8 11 11 208, .p 1 8 11 12 144, .n 1 8 11 13 16,
   .n 1 8 12 5 320, .n 1 8 12 6 80, .p 1 8 12 7 560, .p 1 8 12 8 560, .p 1 8 12 9 480, .p 1 8 12 10 336,
   .n 1 8 12 11 48, .n 1 8 12 12 80, .p 1 8 13 5 288, .p 1 8 13 6 144, .n 1 8 13 7 592, .n 1 8 13 8 80,
   .n 1 8 13 9 96, .p 1 8 13 12 16, .n 1 8 14 5 112, .n 1 8 14 6 80, .p 1 8 14 7 272, .n 1 8 14 8 128,
   .n 1 8 14 9 272, .n 1 8 14 10 128, .p 1 8 15 5 16, .p 1 8 15 6 16, .n 1 8 15 7 80, .p 1 8 15 8 80,
   .p 1 8 15 9 240, .p 1 8 15 10 48, .p 1 8 16 7 16, .n 1 8 16 8 16, .n 1 8 16 9 64, .n 2 7 5 8 32,
   .p 2 7 5 9 136, .n 2 7 5 10 96, .n 2 7 5 11 8, .n 2 7 6 6 16, .n 2 7 6 7 112, .p 2 7 6 8 592,
   .n 2 7 6 9 888, .p 2 7 6 10 600, .n 2 7 6 11 224, .p 2 7 6 12 8, .p 2 7 6 13 40, .p 2 7 7 5 24,
   .p 2 7 7 6 80, .p 2 7 7 7 16, .n 2 7 7 8 704, .p 2 7 7 9 184, .n 2 7 7 10 488, .p 2 7 7 11 1168,
   .n 2 7 7 12 168, .n 2 7 7 13 112, .n 2 7 8 3 8, .n 2 7 8 4 16, .n 2 7 8 5 144, .p 2 7 8 6 152,
   .p 2 7 8 7 104, .n 2 7 8 8 1480, .p 2 7 8 9 4776, .n 2 7 8 10 1848, .n 2 7 8 11 2056, .p 2 7 8 12 472,
   .p 2 7 8 13 48, .p 2 7 9 3 40, .p 2 7 9 4 48, .p 2 7 9 5 304, .n 2 7 9 6 664, .p 2 7 9 7 1104,
   .p 2 7 9 8 2184, .n 2 7 9 9 7120, .p 2 7 9 10 3192, .p 2 7 9 11 1208, .n 2 7 9 12 408, .p 2 7 9 13 112,
   .n 2 7 10 3 80, .n 2 7 10 4 32, .n 2 7 10 5 224, .p 2 7 10 6 152, .n 2 7 10 7 1824, .p 2 7 10 8 1336,
   .p 2 7 10 9 336, .n 2 7 10 10 360, .p 2 7 10 11 784, .n 2 7 10 12 8, .n 2 7 10 13 80, .p 2 7 11 3 80,
   .n 2 7 11 4 32, .n 2 7 11 5 128, .p 2 7 11 6 1064, .n 2 7 11 7 192, .n 2 7 11 8 3320, .p 2 7 11 9 6160,
   .n 2 7 11 10 1912, .n 2 7 11 11 1744, .p 2 7 11 12 104, .n 2 7 11 13 80, .n 2 7 12 3 40, .p 2 7 12 4 48,
   .p 2 7 12 5 368, .n 2 7 12 6 952, .p 2 7 12 7 1792, .p 2 7 12 8 1544, .n 2 7 12 9 4752, .p 2 7 12 10 536,
   .p 2 7 12 11 1304, .p 2 7 12 12 40, .p 2 7 12 13 112, .p 2 7 13 3 8, .n 2 7 13 4 16, .n 2 7 13 5 304,
   .p 2 7 13 6 56, .n 2 7 13 7 1136, .p 2 7 13 8 120, .p 2 7 13 9 1096, .p 2 7 13 10 776, .n 2 7 13 11 512,
   .n 2 7 13 12 40, .n 2 7 13 13 48, .p 2 7 14 5 128, .p 2 7 14 6 152, .p 2 7 14 7 304, .n 2 7 14 8 424,
   .p 2 7 14 9 232, .n 2 7 14 10 464, .p 2 7 14 11 64, .p 2 7 14 13 8, .n 2 7 15 5 24, .n 2 7 15 6 24,
   .n 2 7 15 7 48, .p 2 7 15 8 216, .n 2 7 15 9 200, .p 2 7 15 10 64, .p 2 7 15 11 16, .n 2 7 16 7 8,
   .n 2 7 16 8 32, .p 2 7 16 9 40, .n 3 6 5 8 16, .n 3 6 5 9 8, .p 3 6 5 10 64, .n 3 6 5 11 40,
   .p 3 6 6 6 24, .p 3 6 6 7 56, .n 3 6 6 8 488, .p 3 6 6 9 544, .n 3 6 6 10 144, .p 3 6 6 11 168,
   .n 3 6 6 12 144, .n 3 6 6 13 16, .n 3 6 7 4 8, .n 3 6 7 5 72, .p 3 6 7 6 96, .n 3 6 7 7 40,
   .p 3 6 7 8 1112, .n 3 6 7 9 600, .n 3 6 7 10 1192, .p 3 6 7 11 200, .p 3 6 7 12 232, .p 3 6 7 13 272,
   .p 3 6 8 3 48, .p 3 6 8 4 72, .p 3 6 8 5 72, .n 3 6 8 6 328, .n 3 6 8 7 632, .p 3 6 8 8 200,
   .n 3 6 8 9 872, .p 3 6 8 10 2376, .n 3 6 8 11 96, .n 3 6 8 12 64, .n 3 6 8 13 776, .n 3 6 9 3 184,
   .n 3 6 9 4 232, .p 3 6 9 5 208, .p 3 6 9 6 544, .p 3 6 9 7 1400, .n 3 6 9 8 2400, .p 3 6 9 9 792,
   .p 3 6 9 10 896, .n 3 6 9 11 1904, .p 3 6 9 12 8, .p 3 6 9 13 872, .p 3 6 10 3 264, .p 3 6 10 4 344,
   .n 3 6 10 5 288, .n 3 6 10 6 984, .n 3 6 10 7 832, .p 3 6 10 8 2408, .p 3 6 10 9 832, .n 3 6 10 10 4248,
   .p 3 6 10 11 2808, .p 3 6 10 12 208, .n 3 6 10 13 512, .n 3 6 11 3 168, .n 3 6 11 4 184, .n 3 6 11 5 208,
   .p 3 6 11 6 896, .p 3 6 11 7 184, .n 3 6 11 8 784, .n 3 6 11 9 472, .p 3 6 11 10 2192, .n 3 6 11 11 1328,
   .n 3 6 11 12 488, .p 3 6 11 13 360, .p 3 6 12 3 40, .n 3 6 12 4 104, .p 3 6 12 5 784, .p 3 6 12 6 40,
   .n 3 6 12 7 1008, .n 3 6 12 8 312, .n 3 6 12 9 448, .p 3 6 12 10 920, .p 3 6 12 11 184, .p 3 6 12 12 256,
   .n 3 6 12 13 352, .p 3 6 13 4 168, .n 3 6 13 5 840, .n 3 6 13 6 480, .p 3 6 13 7 1624, .p 3 6 13 8 496,
   .n 3 6 13 9 128, .n 3 6 13 10 1088, .p 3 6 13 11 64, .n 3 6 13 12 8, .p 3 6 13 13 192, .n 3 6 14 4 56,
   .p 3 6 14 5 424, .p 3 6 14 6 224, .n 3 6 14 7 968, .n 3 6 14 8 288, .p 3 6 14 9 656, .p 3 6 14 10 72,
   .n 3 6 14 11 24, .n 3 6 14 13 40, .n 3 6 15 5 80, .n 3 6 15 6 32, .p 3 6 15 7 224, .p 3 6 15 8 56,
   .n 3 6 15 9 288, .p 3 6 15 10 152, .n 3 6 15 11 32, .n 3 6 16 7 8, .p 3 6 16 8 16, .n 3 6 16 9 8,
   .p 4 5 5 8 16, .n 4 5 5 9 48, .p 4 5 5 10 48, .n 4 5 5 11 16, .p 4 5 6 6 32, .p 4 5 6 7 280,
   .n 4 5 6 8 760, .p 4 5 6 9 704, .n 4 5 6 10 688, .p 4 5 6 11 568, .p 4 5 6 12 8, .n 4 5 6 13 144,
   .p 4 5 7 4 32, .p 4 5 7 5 48, .n 4 5 7 6 480, .n 4 5 7 7 328, .p 4 5 7 8 1280, .n 4 5 7 9 248,
   .p 4 5 7 10 1136, .n 4 5 7 11 2216, .p 4 5 7 12 272, .p 4 5 7 13 504, .n 4 5 8 3 112, .n 4 5 8 4 32,
   .p 4 5 8 5 288, .p 4 5 8 6 112, .p 4 5 8 7 248, .p 4 5 8 8 2224, .n 4 5 8 9 7000, .p 4 5 8 10 2720,
   .p 4 5 8 11 3640, .n 4 5 8 12 1712, .n 4 5 8 13 392, .p 4 5 8 14 16, .p 4 5 9 3 272, .p 4 5 9 4 208,
   .n 4 5 9 5 1136, .p 4 5 9 6 1552, .n 4 5 9 7 2360, .n 4 5 9 8 3264, .p 4 5 9 9 12024, .n 4 5 9 10 7600,
   .n 4 5 9 11 1784, .p 4 5 9 12 2352, .n 4 5 9 13 232, .n 4 5 9 14 32, .n 4 5 10 3 120, .n 4 5 10 4 744,
   .p 4 5 10 5 816, .p 4 5 10 6 288, .p 4 5 10 7 2728, .n 4 5 10 8 4160, .n 4 5 10 9 712, .p 4 5 10 10 3216,
   .n 4 5 10 11 1424, .n 4 5 10 12 152, .p 4 5 10 13 248, .p 4 5 10 14 16, .n 4 5 11 3 168, .p 4 5 11 4 848,
   .p 4 5 11 5 792, .n 4 5 11 6 4672, .p 4 5 11 7 1432, .p 4 5 11 8 8400, .n 4 5 11 9 10712, .p 4 5 11 10 3136,
   .p 4 5 11 11 2352, .n 4 5 11 12 1440, .p 4 5 11 13 32, .p 4 5 12 3 168, .n 4 5 12 4 336, .n 4 5 12 5 1112,
   .p 4 5 12 6 4320, .n 4 5 12 7 3048, .n 4 5 12 8 4816, .p 4 5 12 9 7432, .n 4 5 12 10 1152, .n 4 5 12 11 2304,
   .p 4 5 12 12 704, .p 4 5 12 13 144, .n 4 5 13 3 40, .p 4 5 13 4 32, .p 4 5 13 5 152, .n 4 5 13 6 1008,
   .p 4 5 13 7 1320, .p 4 5 13 8 720, .n 4 5 13 9 1176, .n 4 5 13 10 1280, .p 4 5 13 11 1456, .p 4 5 13 12 64,
   .n 4 5 13 13 240, .n 4 5 14 4 8, .p 4 5 14 5 200, .n 4 5 14 6 240, .n 4 5 14 7 336, .p 4 5 14 8 664,
   .n 4 5 14 9 552, .p 4 5 14 10 576, .n 4 5 14 11 288, .n 4 5 14 12 96, .p 4 5 14 13 80, .n 4 5 15 5 48,
   .p 4 5 15 6 96, .p 4 5 15 7 64, .n 4 5 15 8 304, .p 4 5 15 9 288, .n 4 5 15 10 112, .p 4 5 15 11 16,
   .n 5 4 6 6 96, .p 5 4 6 7 88, .p 5 4 6 8 312, .n 5 4 6 9 384, .p 5 4 6 10 16, .n 5 4 6 11 168,
   .p 5 4 6 12 408, .n 5 4 6 13 176, .n 5 4 7 4 48, .p 5 4 7 5 88, .p 5 4 7 6 40, .p 5 4 7 7 504,
   .n 5 4 7 8 1680, .p 5 4 7 9 704, .p 5 4 7 10 1608, .n 5 4 7 11 1384, .n 5 4 7 12 48, .p 5 4 7 13 216,
   .p 5 4 8 3 128, .n 5 4 8 4 200, .n 5 4 8 5 120, .p 5 4 8 6 600, .n 5 4 8 7 1280, .p 5 4 8 8 1368,
   .p 5 4 8 9 368, .n 5 4 8 10 2408, .p 5 4 8 11 2752, .n 5 4 8 12 1648, .p 5 4 8 13 456, .n 5 4 8 14 16,
   .n 5 4 9 3 120, .p 5 4 9 4 24, .p 5 4 9 5 784, .n 5 4 9 6 720, .n 5 4 9 7 2424, .p 5 4 9 8 4816,
   .n 5 4 9 9 104, .n 5 4 9 10 5472, .p 5 4 9 11 2832, .p 5 4 9 12 1496, .n 5 4 9 13 1224, .p 5 4 9 14 112,
   .p 5 4 10 2 8, .n 5 4 10 3 208, .p 5 4 10 4 536, .n 5 4 10 5 1104, .p 5 4 10 6 328, .p 5 4 10 7 5888,
   .n 5 4 10 8 9624, .n 5 4 10 9 1232, .p 5 4 10 10 12224, .n 5 4 10 11 7568, .n 5 4 10 12 256, .p 5 4 10 13 1152,
   .n 5 4 10 14 144, .n 5 4 11 2 16, .p 5 4 11 3 328, .n 5 4 11 4 352, .p 5 4 11 5 248, .n 5 4 11 6 784,
   .n 5 4 11 7 2232, .p 5 4 11 8 5760, .n 5 4 11 9 168, .n 5 4 11 10 5824, .p 5 4 11 11 2608, .p 5 4 11 12 1152,
   .n 5 4 11 13 784, .p 5 4 11 14 64, .p 5 4 12 2 8, .n 5 4 12 3 144, .p 5 4 12 4 128, .p 5 4 12 5 24,
   .p 5 4 12 6 856, .n 5 4 12 7 1632, .p 5 4 12 8 344, .p 5 4 12 9 1232, .n 5 4 12 10 1840, .p 5 4 12 11 1968,
   .n 5 4 12 12 1272, .p 5 4 12 13 344, .n 5 4 12 14 16, .p 5 4 13 3 16, .n 5 4 13 4 168, .p 5 4 13 5 136,
   .p 5 4 13 6 96, .p 5 4 13 7 840, .n 5 4 13 8 1744, .p 5 4 13 9 56, .p 5 4 13 10 1632, .n 5 4 13 11 888,
   .n 5 4 13 12 72, .p 5 4 13 13 96, .p 5 4 14 4 80, .n 5 4 14 5 48, .n 5 4 14 6 360, .p 5 4 14 7 328,
   .p 5 4 14 8 368, .n 5 4 14 9 432, .p 5 4 14 10 56, .n 5 4 14 11 152, .p 5 4 14 12 240, .n 5 4 14 13 80,
   .n 5 4 15 5 8, .p 5 4 15 6 40, .n 5 4 15 7 80, .p 5 4 15 8 80, .n 5 4 15 9 40, .p 5 4 15 10 8,
   .p 6 3 6 6 72, .n 6 3 6 7 264, .p 6 3 6 8 328, .n 6 3 6 9 200, .p 6 3 6 10 280, .n 6 3 6 11 472,
   .p 6 3 6 12 344, .n 6 3 6 13 88, .p 6 3 7 4 32, .n 6 3 7 5 120, .p 6 3 7 6 136, .n 6 3 7 7 8,
   .n 6 3 7 8 56, .p 6 3 7 9 8, .n 6 3 7 10 40, .p 6 3 7 11 104, .n 6 3 7 12 72, .p 6 3 7 13 16,
   .n 6 3 8 3 72, .p 6 3 8 4 240, .n 6 3 8 5 224, .n 6 3 8 6 96, .p 6 3 8 7 632, .n 6 3 8 8 1448,
   .p 6 3 8 9 1736, .n 6 3 8 10 776, .n 6 3 8 11 144, .p 6 3 8 12 88, .p 6 3 8 13 120, .n 6 3 8 14 56,
   .n 6 3 9 3 8, .p 6 3 9 4 16, .p 6 3 9 5 120, .n 6 3 9 6 888, .p 6 3 9 7 1656, .p 6 3 9 8 88,
   .n 6 3 9 9 3016, .p 6 3 9 10 2120, .p 6 3 9 11 1008, .n 6 3 9 12 1416, .p 6 3 9 13 240, .p 6 3 9 14 80,
   .n 6 3 10 2 24, .p 6 3 10 3 88, .n 6 3 10 4 104, .p 6 3 10 5 160, .n 6 3 10 6 8, .n 6 3 10 7 1192,
   .p 6 3 10 8 1864, .p 6 3 10 9 168, .n 6 3 10 10 2000, .p 6 3 10 11 1008, .p 6 3 10 12 256, .n 6 3 10 13 232,
   .p 6 3 10 14 16, .p 6 3 11 2 8, .p 6 3 11 3 232, .n 6 3 11 4 616, .n 6 3 11 5 384, .p 6 3 11 6 2312,
   .n 6 3 11 7 1256, .n 6 3 11 8 2392, .p 6 3 11 9 3080, .n 6 3 11 10 176, .n 6 3 11 11 1632, .p 6 3 11 12 928,
   .n 6 3 11 13 40, .n 6 3 11 14 64, .p 6 3 12 2 8, .n 6 3 12 3 232, .p 6 3 12 4 336, .p 6 3 12 5 880,
   .n 6 3 12 6 1928, .n 6 3 12 7 152, .p 6 3 12 8 2856, .n 6 3 12 9 2408, .p 6 3 12 10 640, .n 6 3 12 11 32,
   .p 6 3 12 12 104, .n 6 3 12 13 104, .p 6 3 12 14 32, .p 6 3 13 3 40, .n 6 3 13 4 32, .n 6 3 13 5 328,
   .p 6 3 13 6 648, .n 6 3 13 7 56, .n 6 3 13 8 760, .p 6 3 13 9 552, .p 6 3 13 10 88, .n 6 3 13 11 208,
   .p 6 3 13 12 56, .p 6 3 14 4 32, .n 6 3 14 5 88, .n 6 3 14 6 32, .p 6 3 14 7 352, .n 6 3 14 8 480,
   .p 6 3 14 9 368, .n 6 3 14 10 352, .p 6 3 14 11 352, .n 6 3 14 12 192, .p 6 3 14 13 40, .n 7 2 6 6 16,
   .p 7 2 6 7 80, .n 7 2 6 8 144, .p 7 2 6 9 80, .p 7 2 6 10 80, .n 7 2 6 11 144, .p 7 2 6 12 80,
   .n 7 2 6 13 16, .n 7 2 7 4 8, .p 7 2 7 5 32, .n 7 2 7 6 32, .n 7 2 7 7 32, .p 7 2 7 8 80,
   .n 7 2 7 9 32, .n 7 2 7 10 32, .p 7 2 7 11 32, .n 7 2 7 12 8, .p 7 2 8 3 16, .n 7 2 8 4 64,
   .p 7 2 8 5 96, .n 7 2 8 6 216, .p 7 2 8 7 704, .n 7 2 8 8 1056, .p 7 2 8 9 288, .p 7 2 8 10 944,
   .n 7 2 8 11 1104, .p 7 2 8 12 416, .n 7 2 8 14 24, .p 7 2 9 4 96, .n 7 2 9 5 392, .p 7 2 9 6 256,
   .p 7 2 9 7 992, .n 7 2 9 8 1632, .n 7 2 9 9 176, .p 7 2 9 10 1952, .n 7 2 9 11 1056, .n 7 2 9 12 512,
   .p 7 2 9 13 632, .n 7 2 9 14 160, .p 7 2 10 2 16, .n 7 2 10 3 40, .n 7 2 10 4 272, .p 7 2 10 5 1008,
   .p 7 2 10 6 48, .n 7 2 10 7 4368, .p 7 2 10 8 6048, .p 7 2 10 9 96, .n 7 2 10 10 6288, .p 7 2 10 11 4472,
   .p 7 2 10 12 112, .n 7 2 10 13 1168, .p 7 2 10 14 336, .p 7 2 11 2 40, .n 7 2 11 3 160, .p 7 2 11 4 336,
   .n 7 2 11 5 528, .p 7 2 11 6 112, .p 7 2 11 7 1440, .n 7 2 11 8 2048, .n 7 2 11 9 128, .p 7 2 11 10 2088,
   .n 7 2 11 11 1152, .n 7 2 11 12 400, .p 7 2 11 13 528, .n 7 2 11 14 128, .n 7 2 12 2 32, .p 7 2 12 3 80,
   .p 7 2 12 4 24, .n 7 2 12 5 80, .n 7 2 12 6 496, .p 7 2 12 7 1216, .n 7 2 12 8 816, .n 7 2 12 9 448,
   .p 7 2 12 10 1120, .n 7 2 12 11 784, .p 7 2 12 12 216, .p 7 2 12 13 16, .n 7 2 12 14 16, .n 7 2 13 3 8,
   .p 7 2 13 4 16, .p 7 2 13 5 32, .n 7 2 13 6 96, .p 7 2 13 7 16, .p 7 2 13 8 128, .n 7 2 13 9 96,
   .n 7 2 13 10 32, .p 7 2 13 11 56, .n 7 2 13 12 16, .p 7 2 14 5 8, .n 7 2 14 6 48, .p 7 2 14 7 112,
   .n 7 2 14 8 112, .p 7 2 14 10 112, .n 7 2 14 11 112, .p 7 2 14 12 48, .n 7 2 14 13 8, .p 8 1 10 4 32,
   .n 8 1 10 5 128, .p 8 1 10 6 96, .p 8 1 10 7 256, .n 8 1 10 8 448, .p 8 1 10 10 448, .n 8 1 10 11 256,
   .n 8 1 10 12 96, .p 8 1 10 13 128, .n 8 1 10 14 32, .n 8 1 12 2 32, .p 8 1 12 3 128, .n 8 1 12 4 96,
   .n 8 1 12 5 256, .p 8 1 12 6 448, .n 8 1 12 8 448, .p 8 1 12 9 256, .p 8 1 12 10 96, .n 8 1 12 11 128,
   .p 8 1 12 12 32, .n 9 0 10 3 32, .p 9 0 10 4 192, .n 9 0 10 5 384, .p 9 0 10 6 64, .p 9 0 10 7 864,
   .n 9 0 10 8 1152, .p 9 0 10 10 1152, .n 9 0 10 11 864, .n 9 0 10 12 64, .p 9 0 10 13 384, .n 9 0 10 14 192,
   .p 9 0 10 15 32]

set_option maxRecDepth 65536 in
private theorem g2_comb6_step3 :
    fmMerge g2Comb6_2 (fmMul (fmNeg (g2FM ⟨0, by decide⟩ ⟨3, by decide⟩)) g2Val5_3) = g2Comb6_3 := rfl

private def g2Comb6_4 : List FM :=
  [.p 0 9 4 9 64, .n 0 9 5 9 352, .n 0 9 6 7 32, .p 0 9 6 9 640, .p 0 9 7 7 160, .n 0 9 7 9 64,
   .n 0 9 8 7 256, .n 0 9 8 9 1312, .p 0 9 9 9 1600, .p 0 9 10 7 448, .n 0 9 11 7 448, .n 0 9 11 9 1408,
   .p 0 9 12 9 1024, .p 0 9 13 7 256, .p 0 9 13 9 32, .n 0 9 14 7 160, .n 0 9 14 9 384, .p 0 9 15 7 32,
   .p 0 9 15 9 192, .n 0 9 16 9 32, .n 1 8 5 8 96, .p 1 8 5 10 32, .p 1 8 6 7 32, .p 1 8 6 8 384,
   .n 1 8 6 10 128, .p 1 8 6 11 32, .p 1 8 7 6 32, .n 1 8 7 7 96, .n 1 8 7 8 352, .p 1 8 7 10 128,
   .n 1 8 7 11 160, .p 1 8 8 5 32, .n 1 8 8 6 128, .n 1 8 8 7 96, .n 1 8 8 8 512, .n 1 8 8 9 32,
   .p 1 8 8 10 128, .p 1 8 8 11 288, .n 1 8 9 5 160, .p 1 8 9 6 128, .p 1 8 9 7 672, .p 1 8 9 8 1088,
   .p 1 8 9 9 160, .n 1 8 9 10 320, .n 1 8 9 11 160, .p 1 8 10 5 288, .p 1 8 10 6 128, .n 1 8 10 7 736,
   .n 1 8 10 8 256, .n 1 8 10 9 288, .p 1 8 10 10 128, .n 1 8 10 11 160, .n 1 8 11 5 160, .n 1 8 11 6 320,
   .n 1 8 11 7 288, .n 1 8 11 8 704, .p 1 8 11 9 160, .p 1 8 11 10 128, .p 1 8 11 11 288, .n 1 8 12 5 160,
   .p 1 8 12 6 128, .p 1 8 12 7 1056, .p 1 8 12 8 512, .p 1 8 12 9 160, .n 1 8 12 10 128, .n 1 8 12 11 160,
   .p 1 8 13 5 288, .p 1 8 13 6 128, .n 1 8 13 7 544, .p 1 8 13 8 32, .n 1 8 13 9 288, .p 1 8 13 10 32,
   .p 1 8 13 11 32, .n 1 8 14 5 160, .n 1 8 14 6 128, .n 1 8 14 7 192, .n 1 8 14 8 128, .p 1 8 14 9 160,
   .p 1 8 15 5 32, .p 1 8 15 6 32, .p 1 8 15 7 256, .p 1 8 15 8 32, .n 1 8 15 9 32, .n 1 8 16 7 64,
   .n 2 7 5 7 16, .n 2 7 5 8 208, .p 2 7 5 9 448, .n 2 7 5 10 208, .n 2 7 5 11 16, .p 2 7 6 6 16,
   .p 2 7 6 7 96, .p 2 7 6 8 720, .n 2 7 6 9 1600, .p 2 7 6 10 720, .p 2 7 6 11 32, .p 2 7 6 12 16,
   .p 2 7 7 5 8, .p 2 7 7 6 16, .n 2 7 7 7 80, .n 2 7 7 8 208, .p 2 7 7 9 464, .n 2 7 7 10 416,
   .p 2 7 7 11 272, .n 2 7 7 12 64, .p 2 7 7 13 8, .n 2 7 8 3 8, .n 2 7 8 4 16, .n 2 7 8 5 128,
   .n 2 7 8 6 192, .n 2 7 8 7 592, .n 2 7 8 8 1920, .p 2 7 8 9 5216, .n 2 7 8 10 1280, .n 2 7 8 11 1128,
   .p 2 7 8 12 80, .n 2 7 8 13 32, .p 2 7 9 3 40, .p 2 7 9 4 64, .p 2 7 9 5 352, .p 2 7 9 6 224,
   .p 2 7 9 7 1680, .p 2 7 9 8 2080, .n 2 7 9 9 7872, .p 2 7 9 10 1920, .p 2 7 9 11 1480, .p 2 7 9 13 32,
   .n 2 7 10 3 80, .n 2 7 10 4 80, .n 2 7 10 5 120, .p 2 7 10 6 160, .n 2 7 10 7 1408, .p 2 7 10 8 1248,
   .p 2 7 10 9 656, .n 2 7 10 10 96, .n 2 7 10 11 240, .n 2 7 10 12 80, .p 2 7 10 13 40, .p 2 7 11 3 80,
   .n 2 7 11 5 696, .n 2 7 11 6 512, .n 2 7 11 7 576, .n 2 7 11 8 2784, .p 2 7 11 9 7216, .n 2 7 11 10 1440,
   .n 2 7 11 11 1232, .p 2 7 11 12 64, .n 2 7 11 13 120, .n 2 7 12 3 40, .p 2 7 12 4 80, .p 2 7 12 5 912,
   .p 2 7 12 6 384, .p 2 7 12 7 1840, .p 2 7 12 8 448, .n 2 7 12 9 5824, .p 2 7 12 10 896, .p 2 7 12 11 1208,
   .n 2 7 12 12 16, .p 2 7 12 13 112, .p 2 7 13 3 8, .n 2 7 13 4 64, .n 2 7 13 5 112, .p 2 7 13 6 32,
   .n 2 7 13 7 1248, .p 2 7 13 8 1200, .p 2 7 13 9 544, .p 2 7 13 10 80, .n 2 7 13 11 392, .n 2 7 13 13 48,
   .p 2 7 14 4 16, .n 2 7 14 5 472, .n 2 7 14 6 304, .p 2 7 14 7 320, .n 2 7 14 8 560, .p 2 7 14 9 1232,
   .n 2 7 14 10 240, .p 2 7 14 13 8, .p 2 7 15 5 320, .p 2 7 15 6 240, .n 2 7 15 7 16, .n 2 7 15 8 80,
   .n 2 7 15 9 544, .p 2 7 15 10 64, .p 2 7 15 11 16, .n 2 7 16 5 64, .n 2 7 16 6 64, .p 2 7 16 8 64,
   .p 2 7 16 9 64, .p 3 6 5 7 40, .n 3 6 5 8 80, .p 3 6 5 10 80, .n 3 6 5 11 40, .p 3 6 6 5 8,
   .n 3 6 6 6 24, .p 3 6 6 7 240, .n 3 6 6 8 440, .p 3 6 6 9 160, .p 3 6 6 10 120, .n 3 6 6 11 80,
   .p 3 6 6 12 24, .n 3 6 6 13 8, .n 3 6 7 4 16, .n 3 6 7 5 120, .n 3 6 7 6 64, .n 3 6 7 7 592,
   .p 3 6 7 8 1760, .n 3 6 7 9 248, .n 3 6 7 10 1264, .p 3 6 7 11 624, .n 3 6 7 12 160, .p 3 6 7 13 80,
   .p 3 6 8 3 48, .p 3 6 8 4 120, .p 3 6 8 5 256, .p 3 6 8 6 48, .n 3 6 8 7 608, .n 3 6 8 8 416,
   .n 3 6 8 9 288, .p 3 6 8 10 1200, .n 3 6 8 11 528, .p 3 6 8 12 392, .n 3 6 8 13 224, .n 3 6 9 3 176,
   .n 3 6 9 4 320, .p 3 6 9 5 176, .p 3 6 9 6 912, .p 3 6 9 7 1536, .n 3 6 9 8 3696, .p 3 6 9 9 304,
   .p 3 6 9 10 2512, .n 3 6 9 11 1104, .n 3 6 9 12 432, .p 3 6 9 13 288, .p 3 6 10 3 208, .p 3 6 10 4 360,
   .n 3 6 10 5 880, .n 3 6 10 6 1696, .p 3 6 10 7 224, .p 3 6 10 8 3952, .p 3 6 10 9 704, .n 3 6 10 10 4960,
   .p 3 6 10 11 2192, .p 3 6 10 12 168, .n 3 6 10 13 272, .n 3 6 11 3 32, .n 3 6 11 4 112, .p 3 6 11 5 240,
   .p 3 6 11 6 592, .n 3 6 11 7 240, .n 3 6 11 8 688, .n 3 6 11 9 640, .p 3 6 11 10 1680, .n 3 6 11 11 1200,
   .p 3 6 11 12 64, .p 3 6 11 13 336, .n 3 6 12 3 112, .n 3 6 12 4 56, .p 3 6 12 5 1280, .p 3 6 12 6 304,
   .n 3 6 12 7 2336, .n 3 6 12 8 256, .n 3 6 12 9 160, .p 3 6 12 10 1744, .p 3 6 12 11 16, .n 3 6 12 12 72,
   .n 3 6 12 13 352, .p 3 6 13 3 80, .n 3 6 13 4 32, .n 3 6 13 5 1296, .p 3 6 13 6 432, .p 3 6 13 7 1880,
   .n 3 6 13 8 320, .p 3 6 13 9 80, .n 3 6 13 10 1120, .p 3 6 13 11 88, .p 3 6 13 12 16, .p 3 6 13 13 192,
   .n 3 6 14 3 16, .p 3 6 14 4 88, .p 3 6 14 5 104, .n 3 6 14 6 712, .p 3 6 14 7 496, .p 3 6 14 8 200,
   .n 3 6 14 9 32, .n 3 6 14 10 152, .p 3 6 14 11 64, .n 3 6 14 13 40, .n 3 6 15 4 32, .p 3 6 15 5 360,
   .p 3 6 15 6 176, .n 3 6 15 7 832, .n 3 6 15 8 48, .p 3 6 15 9 248, .p 3 6 15 10 160, .n 3 6 15 11 32,
   .n 3 6 16 5 128, .p 3 6 16 6 32, .p 3 6 16 7 192, .p 3 6 16 8 32, .n 3 6 16 9 128, .n 4 5 5 7 24,
   .p 4 5 5 8 96, .n 4 5 5 9 144, .p 4 5 5 10 96, .n 4 5 5 11 24, .n 4 5 6 5 32, .p 4 5 6 6 24,
   .p 4 5 6 7 288, .n 4 5 6 8 872, .p 4 5 6 9 1184, .n 4 5 6 10 856, .p 4 5 6 11 256, .p 4 5 6 12 40,
   .n 4 5 6 13 32, .p 4 5 7 4 64, .p 4 5 7 5 232, .n 4 5 7 6 304, .n 4 5 7 7 752, .p 4 5 7 8 928,
   .n 4 5 7 9 504, .p 4 5 7 10 1200, .n 4 5 7 11 992, .n 4 5 7 12 32, .p 4 5 7 13 160, .n 4 5 8 3 112,
   .n 4 5 8 4 152, .n 4 5 8 5 160, .p 4 5 8 6 80, .p 4 5 8 7 1296, .p 4 5 8 8 2784, .n 4 5 8 9 6912,
   .p 4 5 8 10 1744, .p 4 5 8 11 2272, .n 4 5 8 12 616, .n 4 5 8 13 224, .p 4 5 9 3 240, .p 4 5 9 4 240,
   .n 4 5 9 5 640, .p 4 5 9 6 1488, .n 4 5 9 7 2688, .n 4 5 9 8 4912, .p 4 5 9 9 12208, .n 4 5 9 10 4624,
   .n 4 5 9 11 2704, .p 4 5 9 12 1280, .p 4 5 9 13 112, .p 4 5 10 3 32, .n 4 5 10 4 360, .p 4 5 10 5 288,
   .n 4 5 10 6 800, .p 4 5 10 7 2864, .n 4 5 10 8 1456, .n 4 5 10 9 2032, .p 4 5 10 10 1184, .p 4 5 10 11 496,
   .n 4 5 10 12 104, .n 4 5 10 13 112, .n 4 5 11 3 384, .p 4 5 11 4 144, .p 4 5 11 5 1440, .n 4 5 11 6 2864,
   .p 4 5 11 7 1104, .p 4 5 11 8 6832, .n 4 5 11 9 11168, .p 4 5 11 10 3888, .p 4 5 11 11 2384, .n 4 5 11 12 1472,
   .p 4 5 11 13 96, .p 4 5 12 3 240, .p 4 5 12 4 248, .n 4 5 12 5 976, .p 4 5 12 6 2512, .n 4 5 12 7 4368,
   .n 4 5 12 8 2368, .p 4 5 12 9 9392, .n 4 5 12 10 3216, .n 4 5 12 11 2656, .p 4 5 12 12 1032, .p 4 5 12 13 160,
   .p 4 5 13 3 16, .n 4 5 13 4 208, .n 4 5 13 5 896, .p 4 5 13 6 1136, .p 4 5 13 7 2712, .n 4 5 13 8 2864,
   .n 4 5 13 9 928, .p 4 5 13 10 112, .p 4 5 13 11 1192, .n 4 5 13 12 32, .n 4 5 13 13 240, .n 4 5 14 3 32,
   .p 4 5 14 4 8, .p 4 5 14 5 832, .n 4 5 14 6 1464, .n 4 5 14 7 336, .p 4 5 14 8 2072, .n 4 5 14 9 1456,
   .p 4 5 14 10 632, .n 4 5 14 11 240, .n 4 5 14 12 96, .p 4 5 14 13 80, .p 4 5 15 4 16, .n 4 5 15 5 8,
   .p 4 5 15 6 32, .n 4 5 15 7 96, .n 4 5 15 8 80, .p 4 5 15 9 280, .n 4 5 15 10 160, .p 4 5 15 11 16,
   .n 4 5 16 5 80, .p 4 5 16 6 160, .n 4 5 16 8 160, .p 4 5 16 9 80, .p 5 4 6 5 48, .n 5 4 6 6 128,
   .p 5 4 6 7 32, .p 5 4 6 8 144, .n 5 4 6 9 64, .n 5 4 6 10 32, .n 5 4 6 11 96, .p 5 4 6 12 144,
   .n 5 4 6 13 48, .n 5 4 7 4 96, .p 5 4 7 5 8, .p 5 4 7 6 96, .p 5 4 7 7 1184, .n 5 4 7 8 2192,
   .p 5 4 7 9 192, .p 5 4 7 10 1728, .n 5 4 7 11 960, .n 5 4 7 12 48, .p 5 4 7 13 88, .p 5 4 8 3 128,
   .n 5 4 8 4 136, .n 5 4 8 5 224, .p 5 4 8 6 568, .n 5 4 8 7 1424, .p 5 4 8 8 1904, .p 5 4 8 9 192,
   .n 5 4 8 10 2608, .p 5 4 8 11 2480, .n 5 4 8 12 1128, .p 5 4 8 13 256, .n 5 4 8 14 8, .n 5 4 9 3 72,
   .p 5 4 9 4 240, .p 5 4 9 5 704, .n 5 4 9 6 1456, .n 5 4 9 7 2832, .p 5 4 9 8 6176, .p 5 4 9 9 96,
   .n 5 4 9 10 5440, .p 5 4 9 11 1880, .p 5 4 9 12 1456, .n 5 4 9 13 800, .p 5 4 9 14 48, .p 5 4 10 2 8,
   .n 5 4 10 3 320, .p 5 4 10 4 272, .n 5 4 10 5 688, .p 5 4 10 6 1496, .p 5 4 10 7 4976, .n 5 4 10 8 10848,
   .n 5 4 10 9 912, .p 5 4 10 10 12920, .n 5 4 10 11 7344, .n 5 4 10 12 432, .p 5 4 10 13 960, .n 5 4 10 14 88,
   .n 5 4 11 2 16, .p 5 4 11 3 192, .n 5 4 11 4 96, .p 5 4 11 5 104, .n 5 4 11 6 768, .n 5 4 11 7 1856,
   .p 5 4 11 8 5408, .n 5 4 11 9 688, .n 5 4 11 10 5424, .p 5 4 11 11 3008, .p 5 4 11 12 832, .n 5 4 11 13 760,
   .p 5 4 11 14 64, .p 5 4 12 2 8, .p 5 4 12 3 256, .n 5 4 12 4 232, .n 5 4 12 5 688, .p 5 4 12 6 864,
   .n 5 4 12 7 592, .p 5 4 12 8 560, .p 5 4 12 9 1232, .n 5 4 12 10 2968, .p 5 4 12 11 2320, .n 5 4 12 12 1032,
   .p 5 4 12 13 288, .n 5 4 12 14 16, .n 5 4 13 3 216, .p 5 4 13 4 32, .p 5 4 13 5 960, .n 5 4 13 6 928,
   .p 5 4 13 7 784, .n 5 4 13 8 1728, .p 5 4 13 9 480, .p 5 4 13 10 1632, .n 5 4 13 11 1080, .n 5 4 13 12 32,
   .p 5 4 13 13 96, .p 5 4 14 3 32, .n 5 4 14 4 64, .p 5 4 14 6 64, .n 5 4 14 7 144, .p 5 4 14 8 304,
   .n 5 4 14 9 240, .p 5 4 14 10 96, .n 5 4 14 11 208, .p 5 4 14 12 240, .n 5 4 14 13 80, .p 5 4 15 4 80,
   .n 5 4 15 5 208, .p 5 4 15 6 128, .n 5 4 15 7 32, .p 5 4 15 8 208, .n 5 4 15 9 272, .p 5 4 15 10 96,
   .n 5 4 16 5 16, .p 5 4 16 6 64, .n 5 4 16 7 96, .p 5 4 16 8 64, .n 5 4 16 9 16, .n 6 3 6 5 32,
   .p 6 3 6 6 160, .n 6 3 6 7 320, .p 6 3 6 8 352, .n 6 3 6 9 320, .p 6 3 6 10 352, .n 6 3 6 11 320,
   .p 6 3 6 12 160, .n 6 3 6 13 32, .p 6 3 7 4 64, .n 6 3 7 5 192, .p 6 3 7 6 128, .p 6 3 7 7 64,
   .n 6 3 7 9 64, .n 6 3 7 10 128, .p 6 3 7 11 192, .n 6 3 7 12 64, .n 6 3 8 3 72, .p 6 3 8 4 248,
   .n 6 3 8 5 224, .n 6 3 8 6 120, .p 6 3 8 7 496, .n 6 3 8 8 1040, .p 6 3 8 9 1536, .n 6 3 8 10 1136,
   .p 6 3 8 11 280, .p 6 3 8 12 24, .p 6 3 8 13 32, .n 6 3 8 14 24, .n 6 3 9 3 32, .p 6 3 9 4 96,
   .p 6 3 9 5 208, .n 6 3 9 6 1136, .p 6 3 9 7 1120, .p 6 3 9 8 1088, .n 6 3 9 9 2496, .p 6 3 9 10 672,
   .p 6 3 9 11 1216, .n 6 3 9 12 800, .n 6 3 9 13 16, .p 6 3 9 14 80, .n 6 3 10 2 24, .p 6 3 10 3 80,
   .n 6 3 10 4 304, .p 6 3 10 5 408, .p 6 3 10 6 632, .n 6 3 10 7 1472, .n 6 3 10 8 128, .p 6 3 10 9 1488,
   .n 6 3 10 10 328, .n 6 3 10 11 592, .p 6 3 10 12 176, .p 6 3 10 13 88, .n 6 3 10 14 24, .p 6 3 11 3 240,
   .n 6 3 11 4 512, .n 6 3 11 5 496, .p 6 3 11 6 1888, .n 6 3 11 7 544, .n 6 3 11 8 2272, .p 6 3 11 9 2336,
   .p 6 3 11 10 96, .n 6 3 11 11 1488, .p 6 3 11 12 864, .n 6 3 11 13 48, .n 6 3 11 14 64, .p 6 3 12 2 40,
   .n 6 3 12 3 120, .p 6 3 12 4 120, .p 6 3 12 5 384, .n 6 3 12 6 1552, .p 6 3 12 7 1232, .p 6 3 12 8 1904,
   .n 6 3 12 9 3712, .p 6 3 12 10 1736, .p 6 3 12 11 232, .n 6 3 12 12 232, .n 6 3 12 13 64, .p 6 3 12 14 32,
   .n 6 3 13 2 16, .n 6 3 13 3 144, .p 6 3 13 4 256, .p 6 3 13 5 544, .n 6 3 13 6 864, .n 6 3 13 7 768,
   .p 6 3 13 8 1344, .p 6 3 13 9 224, .n 6 3 13 10 784, .p 6 3 13 11 144, .p 6 3 13 12 64, .p 6 3 14 3 48,
   .n 6 3 14 5 472, .p 6 3 14 6 704, .p 6 3 14 7 192, .n 6 3 14 8 1088, .p 6 3 14 9 880, .n 6 3 14 10 448,
   .p 6 3 14 11 336, .n 6 3 14 12 192, .p 6 3 14 13 40, .p 6 3 15 4 32, .n 6 3 15 5 128, .p 6 3 15 6 160,
   .n 6 3 15 8 160, .p 6 3 15 9 128, .n 6 3 15 10 32, .p 7 2 6 5 8, .n 7 2 6 6 48, .p 7 2 6 7 112,
   .n 7 2 6 8 112, .p 7 2 6 10 112, .n 7 2 6 11 112, .p 7 2 6 12 48, .n 7 2 6 13 8, .n 7 2 7 4 16,
   .p 7 2 7 5 64, .n 7 2 7 6 64, .n 7 2 7 7 64, .p 7 2 7 8 160, .n 7 2 7 9 64, .n 7 2 7 10 64,
   .p 7 2 7 11 64, .n 7 2 7 12 16, .p 7 2 8 3 16, .n 7 2 8 4 64, .p 7 2 8 5 128, .n 7 2 8 6 336,
   .p 7 2 8 7 800, .n 7 2 8 8 896, .p 7 2 8 10 992, .n 7 2 8 11 944, .p 7 2 8 12 320, .n 7 2 8 14 16,
   .p 7 2 9 4 96, .n 7 2 9 5 400, .p 7 2 9 6 320, .p 7 2 9 7 832, .n 7 2 9 8 1536, .p 7 2 9 9 32,
   .p 7 2 9 10 1600, .n 7 2 9 11 960, .n 7 2 9 12 352, .p 7 2 9 13 496, .n 7 2 9 14 128, .p 7 2 10 2 16,
   .n 7 2 10 3 80, .n 7 2 10 4 192, .p 7 2 10 5 1088, .n 7 2 10 6 144, .n 7 2 10 7 4480, .p 7 2 10 8 6240,
   .p 7 2 10 9 288, .n 7 2 10 10 6448, .p 7 2 10 11 4304, .p 7 2 10 12 224, .n 7 2 10 13 1120, .p 7 2 10 14 304,
   .p 7 2 11 2 48, .n 7 2 11 3 144, .p 7 2 11 4 224, .n 7 2 11 5 496, .p 7 2 11 6 416, .p 7 2 11 7 1184,
   .n 7 2 11 8 2304, .p 7 2 11 9 224, .p 7 2 11 10 2096, .n 7 2 11 11 1296, .n 7 2 11 12 352, .p 7 2 11 13 528,
   .n 7 2 11 14 128, .p 7 2 12 4 32, .n 7 2 12 5 16, .n 7 2 12 6 464, .p 7 2 12 7 1280, .n 7 2 12 8 1088,
   .n 7 2 12 9 416, .p 7 2 12 10 1376, .n 7 2 12 11 896, .p 7 2 12 12 160, .p 7 2 12 13 48, .n 7 2 12 14 16,
   .n 7 2 13 2 48, .p 7 2 13 3 144, .n 7 2 13 4 48, .n 7 2 13 5 192, .p 7 2 13 6 96, .p 7 2 13 7 96,
   .p 7 2 13 8 96, .n 7 2 13 9 192, .n 7 2 13 10 48, .p 7 2 13 11 144, .n 7 2 13 12 48, .p 7 2 14 5 8,
   .n 7 2 14 6 48, .p 7 2 14 7 112, .n 7 2 14 8 112, .p 7 2 14 10 112, .n 7 2 14 11 112, .p 7 2 14 12 48,
   .n 7 2 14 13 8, .p 8 1 11 3 32, .n 8 1 11 4 128, .p 8 1 11 5 96, .p 8 1 11 6 256, .n 8 1 11 7 448,
   .p 8 1 11 9 448, .n 8 1 11 10 256, .n 8 1 11 11 96, .p 8 1 11 12 128, .n 8 1 11 13 32, .n 8 1 12 2 32,
   .p 8 1 12 3 160, .n 8 1 12 4 224, .n 8 1 12 5 160, .p 8 1 12 6 704, .n 8 1 12 7 448, .n 8 1 12 8 448,
   .p 8 1 12 9 704, .n 8 1 12 10 160, .n 8 1 12 11 224, .p 8 1 12 12 160, .n 8 1 12 13 32, .n 8 1 13 2 32,
   .p 8 1 13 3 128, .n 8 1 13 4 96, .n 8 1 13 5 256, .p 8 1 13 6 448, .n 8 1 13 8 448, .p 8 1 13 9 256,
   .p 8 1 13 10 96, .n 8 1 13 11 128, .p 8 1 13 12 32, .n 9 0 10 3 32, .p 9 0 10 4 192, .n 9 0 10 5 384,
   .p 9 0 10 6 64, .p 9 0 10 7 864, .n 9 0 10 8 1152, .p 9 0 10 10 1152, .n 9 0 10 11 864, .n 9 0 10 12 64,
   .p 9 0 10 13 384, .n 9 0 10 14 192, .p 9 0 10 15 32]

set_option maxRecDepth 65536 in
private theorem g2_comb6_step4 :
    fmMerge g2Comb6_3 (fmMul (g2FM ⟨0, by decide⟩ ⟨4, by decide⟩) g2Val5_4) = g2Comb6_4 := rfl

set_option maxRecDepth 65536 in
private theorem g2_comb6_step5 :
    fmMerge g2Comb6_4 (fmMul (fmNeg (g2FM ⟨0, by decide⟩ ⟨5, by decide⟩)) g2Val5_5) =
      fmMul [.p 0 0 4 3 8] t3u3CoreFM := rfl

private theorem g2_det6_eq_core :
    fmDet 6 g2FM = fmMul [.p 0 0 4 3 8] t3u3CoreFM := by
  apply fmDet6_of_sub5 g2FM g2Val5_0 g2Val5_1 g2Val5_2 g2Val5_3 g2Val5_4 g2Val5_5 _
    g2_det5_0 g2_det5_1 g2_det5_2 g2_det5_3 g2_det5_4 g2_det5_5
  rw [g2_comb6_step0, g2_comb6_step1, g2_comb6_step2, g2_comb6_step3, g2_comb6_step4]
  exact g2_comb6_step5

private def coneBinomCoeff (k j : Fin 10) : Int :=
  match k.val, j.val with
  | 0, 0 => 19683
  | 0, 1 => 21198591
  | 0, 2 => 10147058892
  | 0, 3 => 2833284332844
  | 0, 4 => 508574537745498
  | 0, 5 => 60859419683544594
  | 0, 6 => 4855229259198335388
  | 0, 7 => 249003900578886057756
  | 0, 8 => 7449366692318341227867
  | 0, _ => 99048986760825351881639
  | 1, 0 => 32805
  | 1, 1 => 35138529
  | 1, 2 => 16727520276
  | 1, 3 => 4644972798228
  | 1, 4 => 829155413183958
  | 1, 5 => 98669739020623470
  | 1, 6 => 7827573262508241732
  | 1, 7 => 399182050045941447588
  | 1, 8 => 11874565641494964439469
  | 1, _ => 156988505478856894765049
  | 2, 0 => 54675
  | 2, 1 => 58243455
  | 2, 2 => 27574008012
  | 2, 3 => 7614584717292
  | 2, 4 => 1351710224867898
  | 2, 5 => 159958051492404690
  | 2, 6 => 12618669109834226460
  | 2, 7 => 639899075388803161436
  | 2, 8 => 18927882206345056973131
  | 2, _ => 248820221775681262176359
  | 3, 0 => 91125
  | 3, 1 => 96537825
  | 3, 2 => 45451162260
  | 3, 3 => 12481855631316
  | 3, 4 => 2203421218945398
  | 3, 5 => 259295052603486510
  | 3, 6 => 20340850987899247940
  | 3, 7 => 1025717531927953550820
  | 3, 8 => 30169796988606319659453
  | 3, _ => 394369655126358323616569
  | 4, 0 => 151875
  | 4, 1 => 160005375
  | 4, 2 => 74914634700
  | 4, 3 => 20458878541740
  | 4, 4 => 3591514850820378
  | 4, 5 => 420289368384282770
  | 4, 6 => 32786418873640849820
  | 4, 7 => 1644069165372458248860
  | 4, 8 => 48087143413774885791035
  | 4, _ => 625059425534534501776679
  | 5, 0 => 253125
  | 5, 1 => 265190625
  | 5, 2 => 123470932500
  | 5, 3 => 33531585028500
  | 5, 4 => 5853612373040150
  | 5, 5 => 681190650038931694
  | 5, 6 => 52843100538294889028
  | 5, 7 => 2635048357572023210276
  | 5, 8 => 76642903932482280022477
  | 5, _ => 990693072783147998637689
  | 6, 0 => 421875
  | 6, 1 => 439509375
  | 6, 2 => 203488087500
  | 6, 3 => 54953554107500
  | 6, 4 => 9539735940608250
  | 6, 5 => 1103964495925380690
  | 6, 6 => 85163242842138303772
  | 6, 7 => 4223120604607418951388
  | 6, 8 => 122152246022276401070379
  | 6, _ => 1570207126500309780570599
  | 7, 0 => 703125
  | 7, 1 => 728390625
  | 7, 2 => 335343012500
  | 7, 3 => 90054783612500
  | 7, 4 => 15545861557773750
  | 7, 5 => 1788989310197407150
  | 7, 6 => 137241616677121321540
  | 7, 7 => 6767915937709078390116
  | 7, 8 => 194678344165148082213341
  | 7, _ => 2488712687962886532436409
  | 8, 0 => 1171875
  | 8, 1 => 1207109375
  | 8, 2 => 552605687500
  | 8, 3 => 147566216787500
  | 8, 4 => 25331402612556250
  | 8, 5 => 2898856079817535250
  | 8, 6 => 221151222744478707100
  | 8, 7 => 10845590204186522685980
  | 8, 8 => 310256335359748123591963
  | 8, _ => 3944505625211371690686119
  | _, 0 => 1953125
  | _, 1 => 2000390625
  | _, 2 => 910577812500
  | _, 3 => 241788761812500
  | _, 4 => 41273341641393750
  | _, 5 => 4696906278790608750
  | _, 6 => 356338623017580850500
  | _, 7 => 17379143699743157480100
  | _, 8 => 494436638257692830308845
  | _, _ => 6251876603747271565460729

private def t3u3ConeSliceCDS (j : Fin 10) : List CDS :=
  match j.val with
  | 0 => [.p 0 6 7812500, .n 1 4 225000, .n 1 5 12600000, .n 1 6 24600000, .n 1 7 5850000, .n 1 8 3600000, .n 2 2 7200,
         .p 2 3 340200, .p 2 4 6374700, .p 2 5 22735800, .p 2 6 29760000, .p 2 7 27979200, .p 2 8 3831300, .p 2 9 10108800,
         .n 2 10 7372800, .n 3 2 135000, .p 3 4 4725000, .p 3 5 18090000, .n 3 6 15625000, .n 3 7 24840000, .n 3 8 21600000,
         .p 3 10 23760000, .p 4 1 48600, .n 4 2 1264500, .n 4 3 8796600, .n 4 4 57297600, .n 4 5 69615000, .n 4 6 23098500,
         .p 4 7 6579000, .p 4 8 20505600, .n 4 9 49766400, .n 4 10 27454500, .n 4 11 777600, .p 5 1 388800, .p 5 2 1639800,
         .p 5 3 22064400, .p 5 4 73103400, .p 5 5 48268800, .p 5 6 50157000, .n 5 7 12556800, .p 5 8 29406600, .p 5 9 53265600,
         .p 5 10 14443200, .p 5 11 1069200, .n 6 0 78732, .p 6 1 326592, .p 6 2 2198016, .p 6 3 157464, .p 6 4 3988764,
         .n 6 5 18402552, .p 6 7 18402552, .n 6 8 3988764, .n 6 9 157464, .n 6 10 2198016, .n 6 11 326592, .p 6 12 78732,
         .n 7 1 1069200, .n 7 2 14443200, .n 7 3 53265600, .n 7 4 29406600, .p 7 5 12556800, .n 7 6 50157000, .n 7 7 48268800,
         .n 7 8 73103400, .n 7 9 22064400, .n 7 10 1639800, .n 7 11 388800, .p 8 1 777600, .p 8 2 27454500, .p 8 3 49766400,
         .n 8 4 20505600, .n 8 5 6579000, .p 8 6 23098500, .p 8 7 69615000, .p 8 8 57297600, .p 8 9 8796600, .p 8 10 1264500,
         .n 8 11 48600, .n 9 2 23760000, .p 9 4 21600000, .p 9 5 24840000, .p 9 6 15625000, .n 9 7 18090000, .n 9 8 4725000,
         .p 9 10 135000, .p 10 2 7372800, .n 10 3 10108800, .n 10 4 3831300, .n 10 5 27979200, .n 10 6 29760000, .n 10 7 22735800,
         .n 10 8 6374700, .n 10 9 340200, .p 10 10 7200, .p 11 4 3600000, .p 11 5 5850000, .p 11 6 24600000, .p 11 7 12600000,
         .p 11 8 225000, .n 12 6 7812500]
  | 1 => [.p 0 6 8001562500, .n 1 4 229125000, .n 1 5 13048800000, .n 1 6 24969600000, .n 1 7 6016650000, .n 1 8 3745200000, .n 2 2 7141920,
         .p 2 3 349573320, .p 2 4 6677657820, .p 2 5 23349545880, .p 2 6 29985984000, .p 2 7 28812405120, .p 2 8 3920738580, .p 2 9 10648817280,
         .n 2 10 7718830080, .n 3 2 142227000, .p 3 4 4740345000, .p 3 5 18880218000, .n 3 6 16003125000, .n 3 7 25159968000, .n 3 8 23112720000,
         .p 3 10 24794352000, .p 4 1 50346360, .n 4 2 1343835300, .n 4 3 9109839960, .n 4 4 59070740160, .n 4 5 71544041400, .n 4 6 23460750900,
         .p 4 7 7324503000, .p 4 8 22654095360, .n 4 9 52219002240, .n 4 10 28500273300, .n 4 11 822648960, .p 5 1 424154880, .p 5 2 1730403480,
         .p 5 3 22927101840, .p 5 4 75141159240, .p 5 5 49430484480, .p 5 6 51825565800, .n 5 7 15472711680, .p 5 8 30287294760, .p 5 9 55737020160,
         .p 5 10 14905326720, .p 5 11 1120450320, .n 6 0 84794364, .p 6 1 332066304, .p 6 2 2225843712, .p 6 3 169588728, .p 6 4 5034359628,
         .n 6 5 20632425624, .p 6 7 20632425624, .n 6 8 5034359628, .n 6 9 169588728, .n 6 10 2225843712, .n 6 11 332066304, .p 6 12 84794364,
         .n 7 1 1120450320, .n 7 2 14905326720, .n 7 3 55737020160, .n 7 4 30287294760, .p 7 5 15472711680, .n 7 6 51825565800, .n 7 7 49430484480,
         .n 7 8 75141159240, .n 7 9 22927101840, .n 7 10 1730403480, .n 7 11 424154880, .p 8 1 822648960, .p 8 2 28500273300, .p 8 3 52219002240,
         .n 8 4 22654095360, .n 8 5 7324503000, .p 8 6 23460750900, .p 8 7 71544041400, .p 8 8 59070740160, .p 8 9 9109839960, .p 8 10 1343835300,
         .n 8 11 50346360, .n 9 2 24794352000, .p 9 4 23112720000, .p 9 5 25159968000, .p 9 6 16003125000, .n 9 7 18880218000, .n 9 8 4740345000,
         .p 9 10 142227000, .p 10 2 7718830080, .n 10 3 10648817280, .n 10 4 3920738580, .n 10 5 28812405120, .n 10 6 29985984000, .n 10 7 23349545880,
         .n 10 8 6677657820, .n 10 9 349573320, .p 10 10 7141920, .p 11 4 3745200000, .p 11 5 6016650000, .p 11 6 24969600000, .p 11 7 13048800000,
         .p 11 8 229125000, .n 12 6 8001562500]
  | 2 => [.p 0 6 3642311250000, .n 1 4 103675540000, .n 1 5 6005625440000, .n 1 6 11263170240000, .n 1 7 2749816040000, .n 1 8 1731580240000, .n 2 2 3147356288,
         .p 2 3 159595995168, .p 2 4 3108502711728, .p 2 5 10655879035232, .p 2 6 13425841267200, .p 2 7 13185467965568, .p 2 8 1781702149392, .p 2 9 4985362173312,
         .n 2 10 3591468941312, .n 3 2 66503666400, .p 3 4 2111665764000, .p 3 5 8755007937600, .n 3 6 7284622500000, .n 3 7 11314913337600, .n 3 8 10984132464000,
         .p 3 10 11498875766400, .p 4 1 23172636384, .n 4 2 634964850640, .n 4 3 4192011084384, .n 4 4 27062964592384, .n 4 5 32672686822240, .n 4 6 10609895304720,
         .p 4 7 3605881687520, .p 4 8 11086094188544, .n 4 9 24350184821376, .n 4 10 13148062852240, .n 4 11 386781934464, .p 5 1 205476348672, .p 5 2 811588527712,
         .p 5 3 10586075789376, .p 5 4 34321055391136, .p 5 5 22494793080832, .p 5 6 23832276740640, .n 5 7 8269647214592, .p 5 8 13865544972064, .p 5 9 25918483348224,
         .p 5 10 6835815768448, .p 5 11 521742247488, .n 6 0 40588235568, .p 6 1 149840741376, .p 6 2 1001128260096, .p 6 3 81176471136, .p 6 4 2738927231856,
         .n 6 5 10231571210976, .p 6 7 10231571210976, .n 6 8 2738927231856, .n 6 9 81176471136, .n 6 10 1001128260096, .n 6 11 149840741376, .p 6 12 40588235568,
         .n 7 1 521742247488, .n 7 2 6835815768448, .n 7 3 25918483348224, .n 7 4 13865544972064, .p 7 5 8269647214592, .n 7 6 23832276740640, .n 7 7 22494793080832,
         .n 7 8 34321055391136, .n 7 9 10586075789376, .n 7 10 811588527712, .n 7 11 205476348672, .p 8 1 386781934464, .p 8 2 13148062852240, .p 8 3 24350184821376,
         .n 8 4 11086094188544, .n 8 5 3605881687520, .p 8 6 10609895304720, .p 8 7 32672686822240, .p 8 8 27062964592384, .p 8 9 4192011084384, .p 8 10 634964850640,
         .n 8 11 23172636384, .n 9 2 11498875766400, .p 9 4 10984132464000, .p 9 5 11314913337600, .p 9 6 7284622500000, .n 9 7 8755007937600, .n 9 8 2111665764000,
         .p 9 10 66503666400, .p 10 2 3591468941312, .n 10 3 4985362173312, .n 10 4 1781702149392, .n 10 5 13185467965568, .n 10 6 13425841267200, .n 10 7 10655879035232,
         .n 10 8 3108502711728, .n 10 9 159595995168, .p 10 10 3147356288, .p 11 4 1731580240000, .p 11 5 2749816040000, .p 11 6 11263170240000, .p 11 7 6005625440000,
         .p 11 8 103675540000, .n 12 6 3642311250000]
  | 3 => [.p 0 6 967155047250000, .n 1 4 27358520852000, .n 1 5 1612252290432000, .n 1 6 2963337093792000, .n 1 7 732995424712000, .n 1 8 466986953712000, .n 2 2 808771381888,
         .p 2 3 42489690937632, .p 2 4 843995845479984, .p 2 5 2836230720345952, .p 2 6 3505913345963520, .p 2 7 3519518387315328, .p 2 8 471874981016208, .p 2 9 1361397420049536,
         .n 2 10 974751052726272, .n 3 2 18115588550880, .p 3 4 548185933168800, .p 3 5 2367482402905920, .n 3 6 1934310094500000, .n 3 7 2965161222865920, .n 3 8 3043059618268800,
         .p 3 10 3110668093610880, .p 4 1 6219503992800, .n 4 2 175070784129744, .n 4 3 1124988712709472, .n 4 4 7231761230103296, .n 4 5 8702345013715296, .n 4 6 2804271464999952,
         .p 4 7 1030943293157344, .p 4 8 3155133931364352, .n 4 9 6623027158978944, .n 4 10 3537944290584464, .n 4 11 106074349043328, .p 5 1 58017172193280, .p 5 2 222047204973920,
         .p 5 3 2850676291135296, .p 5 4 9142924070552736, .p 5 5 5970732083032064, .p 5 6 6401575015105824, .n 5 7 2531650036961280, .p 5 8 3703195649060384, .p 5 9 7029807008292864,
         .p 5 10 1828564725707136, .p 5 11 141692517907776, .n 6 0 11333137331376, .p 6 1 39380316666624, .p 6 2 262487767119360, .p 6 3 22666274662752, .p 6 4 850166599161072,
         .n 6 5 2947185850132704, .p 6 7 2947185850132704, .n 6 8 850166599161072, .n 6 9 22666274662752, .n 6 10 262487767119360, .n 6 11 39380316666624, .p 6 12 11333137331376,
         .n 7 1 141692517907776, .n 7 2 1828564725707136, .n 7 3 7029807008292864, .n 7 4 3703195649060384, .p 7 5 2531650036961280, .n 7 6 6401575015105824, .n 7 7 5970732083032064,
         .n 7 8 9142924070552736, .n 7 9 2850676291135296, .n 7 10 222047204973920, .n 7 11 58017172193280, .p 8 1 106074349043328, .p 8 2 3537944290584464, .p 8 3 6623027158978944,
         .n 8 4 3155133931364352, .n 8 5 1030943293157344, .p 8 6 2804271464999952, .p 8 7 8702345013715296, .p 8 8 7231761230103296, .p 8 9 1124988712709472, .p 8 10 175070784129744,
         .n 8 11 6219503992800, .n 9 2 3110668093610880, .p 9 4 3043059618268800, .p 9 5 2965161222865920, .p 9 6 1934310094500000, .n 9 7 2367482402905920, .n 9 8 548185933168800,
         .p 9 10 18115588550880, .p 10 2 974751052726272, .n 10 3 1361397420049536, .n 10 4 471874981016208, .n 10 5 3519518387315328, .n 10 6 3505913345963520, .n 10 7 2836230720345952,
         .n 10 8 843995845479984, .n 10 9 42489690937632, .p 10 10 808771381888, .p 11 4 466986953712000, .p 11 5 732995424712000, .p 11 6 2963337093792000, .p 11 7 1612252290432000,
         .p 11 8 27358520852000, .n 12 6 967155047250000]
  | 4 => [.p 0 6 165093366565575000, .n 1 4 4640004099194800, .n 1 5 278222773464924800, .n 1 6 501152531790076800, .n 1 7 125586998415192800, .n 1 8 80957891624060800, .n 2 2 133552946789312,
         .p 2 3 7269750857352624, .p 2 4 147295336316756520, .p 2 5 485212967970829328, .p 2 6 588429342227381760, .p 2 7 603866332300454912, .p 2 8 80263687274939256, .p 2 9 238981164604990080,
         .n 2 10 170064629819015168, .n 3 2 3168300246595536, .p 3 4 91389280281621360, .p 3 5 411429591507155424, .n 3 6 330186733131150000, .n 3 7 498965331523799424, .n 3 8 541620621340671360,
         .p 3 10 540935381322289536, .p 4 1 1072765275594960, .n 4 2 31039935198733720, .n 4 3 194037031958868240, .n 4 4 1242154582163715712, .n 4 5 1489791659099025616, .n 4 6 477410011506875256,
         .p 4 7 188743457658281360, .p 4 8 575691691779246080, .n 4 9 1157947828316078208, .n 4 10 611947628713192504, .n 4 11 18700135027158144, .p 5 1 10522614542886528, .p 5 2 39053782089593488,
         .p 5 3 493383338045474784, .p 5 4 1565485432573899184, .p 5 5 1018660916590566400, .p 5 6 1106865313054607472, .n 5 7 491225635343694848, .p 5 8 635887755621684976, .p 5 9 1225582720655047296,
         .p 5 10 314412833570394880, .p 5 11 24732124960239840, .n 6 0 2034298150981992, .p 6 1 6642399020492160, .p 6 2 44212384851217920, .p 6 3 4068596301963984, .p 6 4 166815208878285384,
         .n 6 5 543691952263903248, .p 6 7 543691952263903248, .n 6 8 166815208878285384, .n 6 9 4068596301963984, .n 6 10 44212384851217920, .n 6 11 6642399020492160, .p 6 12 2034298150981992,
         .n 7 1 24732124960239840, .n 7 2 314412833570394880, .n 7 3 1225582720655047296, .n 7 4 635887755621684976, .p 7 5 491225635343694848, .n 7 6 1106865313054607472, .n 7 7 1018660916590566400,
         .n 7 8 1565485432573899184, .n 7 9 493383338045474784, .n 7 10 39053782089593488, .n 7 11 10522614542886528, .p 8 1 18700135027158144, .p 8 2 611947628713192504, .p 8 3 1157947828316078208,
         .n 8 4 575691691779246080, .n 8 5 188743457658281360, .p 8 6 477410011506875256, .p 8 7 1489791659099025616, .p 8 8 1242154582163715712, .p 8 9 194037031958868240, .p 8 10 31039935198733720,
         .n 8 11 1072765275594960, .n 9 2 540935381322289536, .p 9 4 541620621340671360, .p 9 5 498965331523799424, .p 9 6 330186733131150000, .n 9 7 411429591507155424, .n 9 8 91389280281621360,
         .p 9 10 3168300246595536, .p 10 2 170064629819015168, .n 10 3 238981164604990080, .n 10 4 80263687274939256, .n 10 5 603866332300454912, .n 10 6 588429342227381760, .n 10 7 485212967970829328,
         .n 10 8 147295336316756520, .n 10 9 7269750857352624, .p 10 10 133552946789312, .p 11 4 80957891624060800, .p 11 5 125586998415192800, .p 11 6 501152531790076800, .p 11 7 278222773464924800,
         .p 11 8 4640004099194800, .n 12 6 165093366565575000]
  | 5 => [.p 0 6 18787625115162435000, .n 1 4 524501936771154928, .n 1 5 32006019730250106368, .n 1 6 56496423324335132928, .n 1 7 14342587795444015328, .n 1 8 9356217904174200448, .n 2 2 14696858642020800,
         .p 2 3 828939702467945328, .p 2 4 17135294199875171464, .p 2 5 55329343148737918672, .p 2 6 65828586923175946752, .p 2 7 69065813157645685632, .p 2 8 9092467973821097624, .p 2 9 27965798423433767808,
         .n 2 10 19780045288566292480, .n 3 2 368964960468136080, .p 3 4 10146103777460710320, .p 3 5 47651571896459651040, .n 3 6 37575250230324870000, .n 3 7 55908789666067130880, .n 3 8 64228196732558017920,
         .p 3 10 62708275685172923520, .p 4 1 123314629339428880, .n 4 2 3669872469038844280, .n 4 3 22306170278468546640, .n 4 4 142220997797513769600, .n 4 5 169999217519673977360, .n 4 6 54292524641893582680,
         .p 4 7 22956463822791164880, .p 4 8 69855219250435072000, .n 4 9 134956504468391383680, .n 4 10 70557913586803985560, .n 4 11 2197675050167320960, .p 5 1 1271374297632104960, .p 5 2 4579031022027162320,
         .p 5 3 56916460760577996768, .p 5 4 178667972123975907824, .p 5 5 115846465558316239872, .p 5 6 127752818212759042992, .n 5 7 62826892452791984128, .p 5 8 72802414345415110704, .p 5 9 142429936229535011328,
         .p 5 10 36037577504377388160, .p 5 11 2877346544023679200, .n 6 0 243437678734178376, .p 6 1 745608639289894656, .p 6 2 4961145435491731968, .p 6 3 486875357468356752, .p 6 4 21534633891735013032,
         .n 6 5 66641892721886427216, .p 6 7 66641892721886427216, .n 6 8 21534633891735013032, .n 6 9 486875357468356752, .n 6 10 4961145435491731968, .n 6 11 745608639289894656, .p 6 12 243437678734178376,
         .n 7 1 2877346544023679200, .n 7 2 36037577504377388160, .n 7 3 142429936229535011328, .n 7 4 72802414345415110704, .p 7 5 62826892452791984128, .n 7 6 127752818212759042992, .n 7 7 115846465558316239872,
         .n 7 8 178667972123975907824, .n 7 9 56916460760577996768, .n 7 10 4579031022027162320, .n 7 11 1271374297632104960, .p 8 1 2197675050167320960, .p 8 2 70557913586803985560, .p 8 3 134956504468391383680,
         .n 8 4 69855219250435072000, .n 8 5 22956463822791164880, .p 8 6 54292524641893582680, .p 8 7 169999217519673977360, .p 8 8 142220997797513769600, .p 8 9 22306170278468546640, .p 8 10 3669872469038844280,
         .n 8 11 123314629339428880, .n 9 2 62708275685172923520, .p 9 4 64228196732558017920, .p 9 5 55908789666067130880, .p 9 6 37575250230324870000, .n 9 7 47651571896459651040, .n 9 8 10146103777460710320,
         .p 9 10 368964960468136080, .p 10 2 19780045288566292480, .n 10 3 27965798423433767808, .n 10 4 9092467973821097624, .n 10 5 69065813157645685632, .n 10 6 65828586923175946752, .n 10 7 55329343148737918672,
         .n 10 8 17135294199875171464, .n 10 9 828939702467945328, .p 10 10 14696858642020800, .p 11 4 9356217904174200448, .p 11 5 14342587795444015328, .p 11 6 56496423324335132928, .p 11 7 32006019730250106368,
         .p 11 8 524501936771154928, .n 12 6 18787625115162435000]
  | 6 => [.p 0 6 1425354492070323402000, .n 1 4 39516463062279206048, .n 1 5 2454427005264688462592, .n 1 6 4245545958505111504896, .n 1 7 1091815119790475602240, .n 1 8 720822405799385636224, .n 2 2 1077804942632208000,
         .p 2 3 62993049300889765536, .p 2 4 1328764463868715439856, .p 2 5 4205429135790227603168, .p 2 6 4908639532025464886784, .p 2 7 5265635378866981808000, .p 2 8 685943887953382751440, .p 2 9 2181602211037351472256,
         .n 2 10 1533675949056500695040, .n 3 2 28612138483434888288, .p 3 4 750094170426104483616, .p 3 5 3678171181411116536640, .n 3 6 2850708984140646804000, .n 3 7 4171022253223990037760, .n 3 8 5074728531036380182656,
         .p 3 10 4846097570906584088448, .p 4 1 9446772015353160800, .n 4 2 289327932715186022032, .n 4 3 1709103124307505746400, .n 4 4 10854445557343529638656, .n 4 5 12930060843253810900960, .n 4 6 4124588707179896475600,
         .p 4 7 1855631806647295002720, .p 4 8 5638181605251997147136, .n 4 9 10485060581173685669760, .n 4 10 5423071143921215566928, .n 4 11 172173579918547144320, .p 5 1 102334162671414808320, .p 5 2 357904435659979133920,
         .p 5 3 4376299037239849832256, .p 5 4 13591839349487064113440, .p 5 5 8781876821922343833600, .p 5 6 9842349078783490928544, .n 5 7 5307512966623708854272, .p 5 8 5557452573546759412896, .p 5 9 11033647332369568048896,
         .p 5 10 2753452436339908055680, .p 5 11 223119453134973158720, .n 6 0 19420917036793341552, .p 6 1 55690440750418094592, .p 6 2 370865350308529767936, .p 6 3 38841834073586683104, .p 6 4 1833655926533718522288,
         .n 6 5 5429225458053646589280, .p 6 7 5429225458053646589280, .n 6 8 1833655926533718522288, .n 6 9 38841834073586683104, .n 6 10 370865350308529767936, .n 6 11 55690440750418094592, .p 6 12 19420917036793341552,
         .n 7 1 223119453134973158720, .n 7 2 2753452436339908055680, .n 7 3 11033647332369568048896, .n 7 4 5557452573546759412896, .p 7 5 5307512966623708854272, .n 7 6 9842349078783490928544, .n 7 7 8781876821922343833600,
         .n 7 8 13591839349487064113440, .n 7 9 4376299037239849832256, .n 7 10 357904435659979133920, .n 7 11 102334162671414808320, .p 8 1 172173579918547144320, .p 8 2 5423071143921215566928, .p 8 3 10485060581173685669760,
         .n 8 4 5638181605251997147136, .n 8 5 1855631806647295002720, .p 8 6 4124588707179896475600, .p 8 7 12930060843253810900960, .p 8 8 10854445557343529638656, .p 8 9 1709103124307505746400, .p 8 10 289327932715186022032,
         .n 8 11 9446772015353160800, .n 9 2 4846097570906584088448, .p 9 4 5074728531036380182656, .p 9 5 4171022253223990037760, .p 9 6 2850708984140646804000, .n 9 7 3678171181411116536640, .n 9 8 750094170426104483616,
         .p 9 10 28612138483434888288, .p 10 2 1533675949056500695040, .n 10 3 2181602211037351472256, .n 10 4 685943887953382751440, .n 10 5 5265635378866981808000, .n 10 6 4908639532025464886784, .n 10 7 4205429135790227603168,
         .n 10 8 1328764463868715439856, .n 10 9 62993049300889765536, .p 10 10 1077804942632208000, .p 11 4 720822405799385636224, .p 11 5 1091815119790475602240, .p 11 6 4245545958505111504896, .p 11 7 2454427005264688462592,
         .p 11 8 39516463062279206048, .n 12 6 1425354492070323402000]
  | 7 => [.p 0 6 69516574798972629920400, .n 1 4 1913446172132527395232, .n 1 5 120991232979628420170752, .n 1 6 205075055327173236001536, .n 1 7 53421303305909716948544, .n 1 8 35698411008991879006336, .n 2 2 50793420918597840000,
         .p 2 3 3076331643628597308576, .p 2 4 66231416203010774862832, .p 2 5 205448012155295010272224, .p 2 6 235255186096267582075392, .p 2 7 258053732632451037037440, .p 2 8 33228922732514983804880, .p 2 9 109399270470641730177408,
         .n 2 10 76443180925219558653952, .n 3 2 1424778141632387170656, .p 3 4 35606068337383773290016, .p 3 5 182459030699985312892992, .n 3 6 139033149597945259840800, .n 3 7 199767354902771267877888, .n 3 8 257615636841428151603072,
         .p 3 10 240742670848462720468608, .p 4 1 465066353810708617312, .n 4 2 14666668438481903460112, .n 4 3 84162578885968338074592, .n 4 4 532491209142552763279104, .n 4 5 632109575189536880070368, .n 4 6 201849936290284764233040,
         .p 4 7 96155006691942444132192, .p 4 8 291943289840208949977088, .n 4 9 523631806165046347171968, .n 4 10 267928301737117777264336, .n 4 11 8670806609234337023872, .p 5 1 5291572138664812998656, .p 5 2 17982078012716492273120,
         .p 5 3 216270036596441592160320, .p 5 4 664583354712257351811872, .p 5 5 427906951237499069202432, .p 5 6 488054404831365380172192, .n 5 7 286017139357245836013568, .p 5 8 272759119568082407068320, .p 5 9 549416325048506468388864,
         .p 5 10 135230081602544495257728, .p 5 11 11119908372182443814464, .n 6 0 996015602315544231024, .p 6 1 2668556884365850560768, .p 6 2 17809244549199745233408, .p 6 3 1992031204631088462048, .p 6 4 99493521614939395188144,
         .n 6 5 283566805848507024113760, .p 6 7 283566805848507024113760, .n 6 8 99493521614939395188144, .n 6 9 1992031204631088462048, .n 6 10 17809244549199745233408, .n 6 11 2668556884365850560768, .p 6 12 996015602315544231024,
         .n 7 1 11119908372182443814464, .n 7 2 135230081602544495257728, .n 7 3 549416325048506468388864, .n 7 4 272759119568082407068320, .p 7 5 286017139357245836013568, .n 7 6 488054404831365380172192, .n 7 7 427906951237499069202432,
         .n 7 8 664583354712257351811872, .n 7 9 216270036596441592160320, .n 7 10 17982078012716492273120, .n 7 11 5291572138664812998656, .p 8 1 8670806609234337023872, .p 8 2 267928301737117777264336, .p 8 3 523631806165046347171968,
         .n 8 4 291943289840208949977088, .n 8 5 96155006691942444132192, .p 8 6 201849936290284764233040, .p 8 7 632109575189536880070368, .p 8 8 532491209142552763279104, .p 8 9 84162578885968338074592, .p 8 10 14666668438481903460112,
         .n 8 11 465066353810708617312, .n 9 2 240742670848462720468608, .p 9 4 257615636841428151603072, .p 9 5 199767354902771267877888, .p 9 6 139033149597945259840800, .n 9 7 182459030699985312892992, .n 9 8 35606068337383773290016,
         .p 9 10 1424778141632387170656, .p 10 2 76443180925219558653952, .n 10 3 109399270470641730177408, .n 10 4 33228922732514983804880, .n 10 5 258053732632451037037440, .n 10 6 235255186096267582075392, .n 10 7 205448012155295010272224,
         .n 10 8 66231416203010774862832, .n 10 9 3076331643628597308576, .p 10 10 50793420918597840000, .p 11 4 35698411008991879006336, .p 11 5 53421303305909716948544, .p 11 6 205075055327173236001536, .p 11 7 120991232979628420170752,
         .p 11 8 1913446172132527395232, .n 12 6 69516574798972629920400]
  | 8 => [.p 0 6 1977746553030771321235380, .n 1 4 54033512106155120190120, .n 1 5 3478928243360722283796672, .n 1 6 5777773775429084328001728, .n 1 7 1524492307004299866670608, .n 1 8 1031251480284366328753152, .n 2 2 1395821977526560500000,
         .p 2 3 87608379265022116526760, .p 2 4 1925493217101354122815500, .p 2 5 5853721859396067137687544, .p 2 6 6575826986610494148587520, .p 2 7 7376395629254653434240576, .p 2 8 937853731040013908770980, .p 2 9 3199971570567655947666432,
         .n 2 10 2222516914888478400970752, .n 3 2 41342442534575361227160, .p 3 4 984685122449546931668424, .p 3 5 5278125939199155713023632, .n 3 6 3955493106061542642470760, .n 3 7 5572950035257624400109888, .n 3 8 7624575392321792032490880,
         .p 3 10 6976056808465289149135872, .p 4 1 13350863285814606890520, .n 4 2 433774452945815074860180, .n 4 3 2417010448634857291000056, .n 4 4 15236305777758077497230528, .n 4 5 18022907221985835605186136, .n 4 6 5774176672533735614676516,
         .p 4 7 2899092536997084423786744, .p 4 8 8801392625487946377753600, .n 4 9 15253211367434338242567552, .n 4 10 7720897777114346592099012, .n 4 11 254709239194665164166144, .p 5 1 159507343900172382517440, .p 5 2 526969046866250711717304,
         .p 5 3 6233143052655415844967312, .p 5 4 18952341367356856146538344, .p 5 5 12161058959926051150769664, .p 5 6 14133914275770916275011592, .n 5 7 8932324504550914262088192, .p 5 8 7810192916187276513253320, .p 5 9 15956980780152262965395136,
         .p 5 10 3873883262925951104357952, .p 5 11 323209407917528732033808, .n 6 0 29797466769273364911468, .p 6 1 74426762152516767928512, .p 6 2 498499448748801166356480, .p 6 3 59594933538546729822936, .p 6 4 3125963585835934707541884,
         .n 6 5 8618058777429657920152248, .p 6 7 8618058777429657920152248, .n 6 8 3125963585835934707541884, .n 6 9 59594933538546729822936, .n 6 10 498499448748801166356480, .n 6 11 74426762152516767928512, .p 6 12 29797466769273364911468,
         .n 7 1 323209407917528732033808, .n 7 2 3873883262925951104357952, .n 7 3 15956980780152262965395136, .n 7 4 7810192916187276513253320, .p 7 5 8932324504550914262088192, .n 7 6 14133914275770916275011592, .n 7 7 12161058959926051150769664,
         .n 7 8 18952341367356856146538344, .n 7 9 6233143052655415844967312, .n 7 10 526969046866250711717304, .n 7 11 159507343900172382517440, .p 8 1 254709239194665164166144, .p 8 2 7720897777114346592099012, .p 8 3 15253211367434338242567552,
         .n 8 4 8801392625487946377753600, .n 8 5 2899092536997084423786744, .p 8 6 5774176672533735614676516, .p 8 7 18022907221985835605186136, .p 8 8 15236305777758077497230528, .p 8 9 2417010448634857291000056, .p 8 10 433774452945815074860180,
         .n 8 11 13350863285814606890520, .n 9 2 6976056808465289149135872, .p 9 4 7624575392321792032490880, .p 9 5 5572950035257624400109888, .p 9 6 3955493106061542642470760, .n 9 7 5278125939199155713023632, .n 9 8 984685122449546931668424,
         .p 9 10 41342442534575361227160, .p 10 2 2222516914888478400970752, .n 10 3 3199971570567655947666432, .n 10 4 937853731040013908770980, .n 10 5 7376395629254653434240576, .n 10 6 6575826986610494148587520, .n 10 7 5853721859396067137687544,
         .n 10 8 1925493217101354122815500, .n 10 9 87608379265022116526760, .p 10 10 1395821977526560500000, .p 11 4 1031251480284366328753152, .p 11 5 1524492307004299866670608, .p 11 6 5777773775429084328001728, .p 11 7 3478928243360722283796672,
         .p 11 8 54033512106155120190120, .n 12 6 1977746553030771321235380]
  | _ => [.p 0 6 25007506414989086261842916, .n 1 4 677983015490829939865800, .n 1 5 44455515437143478774445824, .n 1 6 72339698596668378386999040, .n 1 7 19332201413138522285316240, .n 1 8 13239640027493308184430592, .n 2 2 17041581803582954100000,
         .p 2 3 1108484499740253124091400, .p 2 4 24876114651181930734406780, .p 2 5 74114089677112784248658520, .p 2 6 81676040503334566199500800, .p 2 7 93703181400146126043192576, .p 2 8 11749256938085192689248756, .p 2 9 41597892693120498376808448,
         .n 2 10 28717941801048733319692288, .n 3 2 532615831150089601265400, .p 3 4 12086617523109457413030120, .p 3 5 67838405189165755606924560, .n 3 6 50015012829978172523685832, .n 3 7 68988485765647343047774464, .n 3 8 100242673569171388279678464,
         .p 3 10 89838752453693607908763648, .p 4 1 170280674114998233439800, .n 4 2 5702646909614833204018180, .n 4 3 30842268356859897698029080, .n 4 4 193735514213342107127835840, .n 4 5 228348908235371291707637240, .n 4 6 73563721473781222625178900,
         .p 4 7 38758034681065754617315608, .p 4 8 117723101335427767239086080, .n 4 9 197459197388063022208218624, .n 4 10 98876595403155609766310004, .n 4 11 3325237915125864822372352, .p 5 1 2135605385145490769540864, .p 5 2 6862692040180980218008920,
         .p 5 3 79824950940289977275711760, .p 5 4 240170329817593005870857480, .p 5 5 153586996460872227217681920, .p 5 6 182121773917566072387349800, .n 5 7 123285507680442026583083008, .p 5 8 99409292934273663433446888, .p 5 9 205952471778112856533184256,
         .p 5 10 49317316249138615895321856, .p 5 11 4174309096876242408324240, .n 6 0 396195947043301407526556, .p 6 1 920360804749697028130560, .p 6 2 6196792416495789369139200, .p 6 3 792391894086602815053112, .p 6 4 43377063418239607950296940,
         .n 6 5 116143100526210858517803480, .p 6 7 116143100526210858517803480, .n 6 8 43377063418239607950296940, .n 6 9 792391894086602815053112, .n 6 10 6196792416495789369139200, .n 6 11 920360804749697028130560, .p 6 12 396195947043301407526556,
         .n 7 1 4174309096876242408324240, .n 7 2 49317316249138615895321856, .n 7 3 205952471778112856533184256, .n 7 4 99409292934273663433446888, .p 7 5 123285507680442026583083008, .n 7 6 182121773917566072387349800, .n 7 7 153586996460872227217681920,
         .n 7 8 240170329817593005870857480, .n 7 9 79824950940289977275711760, .n 7 10 6862692040180980218008920, .n 7 11 2135605385145490769540864, .p 8 1 3325237915125864822372352, .p 8 2 98876595403155609766310004, .p 8 3 197459197388063022208218624,
         .n 8 4 117723101335427767239086080, .n 8 5 38758034681065754617315608, .p 8 6 73563721473781222625178900, .p 8 7 228348908235371291707637240, .p 8 8 193735514213342107127835840, .p 8 9 30842268356859897698029080, .p 8 10 5702646909614833204018180,
         .n 8 11 170280674114998233439800, .n 9 2 89838752453693607908763648, .p 9 4 100242673569171388279678464, .p 9 5 68988485765647343047774464, .p 9 6 50015012829978172523685832, .n 9 7 67838405189165755606924560, .n 9 8 12086617523109457413030120,
         .p 9 10 532615831150089601265400, .p 10 2 28717941801048733319692288, .n 10 3 41597892693120498376808448, .n 10 4 11749256938085192689248756, .n 10 5 93703181400146126043192576, .n 10 6 81676040503334566199500800, .n 10 7 74114089677112784248658520,
         .n 10 8 24876114651181930734406780, .n 10 9 1108484499740253124091400, .p 10 10 17041581803582954100000, .p 11 4 13239640027493308184430592, .p 11 5 19332201413138522285316240, .p 11 6 72339698596668378386999040, .p 11 7 44455515437143478774445824,
         .p 11 8 677983015490829939865800, .n 12 6 25007506414989086261842916]

private def cdsKey : CDS -> Nat
  | .p c d _ => c * 64 + d
  | .n c d _ => c * 64 + d

private def cdsAddSame (x y : CDS) : Option CDS :=
  match x, y with
  | .p c d v1, .p _ _ v2 => some (.p c d (v1 + v2))
  | .n c d v1, .n _ _ v2 => some (.n c d (v1 + v2))
  | .p c d v1, .n _ _ v2 =>
    if v1 == v2 then none
    else if v1 > v2 then some (.p c d (v1 - v2))
    else some (.n c d (v2 - v1))
  | .n c d v1, .p _ _ v2 =>
    if v1 == v2 then none
    else if v1 > v2 then some (.n c d (v1 - v2))
    else some (.p c d (v2 - v1))

private def cdsMergeAux : Nat -> List CDS -> List CDS -> List CDS
  | 0, xs, ys => xs ++ ys
  | _ + 1, [], ys => ys
  | _ + 1, xs, [] => xs
  | fuel + 1, x :: xs, y :: ys =>
    let kx := cdsKey x
    let ky := cdsKey y
    if kx == ky then
      match cdsAddSame x y with
      | none => cdsMergeAux fuel xs ys
      | some z => z :: cdsMergeAux fuel xs ys
    else if kx < ky then
      x :: cdsMergeAux fuel xs (y :: ys)
    else
      y :: cdsMergeAux fuel (x :: xs) ys

private def cdsMerge (xs ys : List CDS) : List CDS :=
  cdsMergeAux (xs.length + ys.length) xs ys

private def cdsScalePos (m : Nat) : List CDS -> List CDS
  | [] => []
  | .p c d v :: tl => .p c d (m * v) :: cdsScalePos m tl
  | .n c d v :: tl => .n c d (m * v) :: cdsScalePos m tl

private def cdsScaleInt (coef : Int) (xs : List CDS) : List CDS :=
  if coef == 0 then []
  else if coef > 0 then cdsScalePos coef.natAbs xs
  else (cdsScalePos coef.natAbs xs).map (fun x => match x with | .p c d v => .n c d v | .n c d v => .p c d v)

private def cdsCombPrefix (j : Fin 10) : Nat -> List CDS
  | 0 => []
  | k + 1 =>
    if hk : k < 10 then
      cdsMerge (cdsCombPrefix j k) (cdsScaleInt (coneBinomCoeff ⟨k, hk⟩ j) (t3u3CoreWSlice ⟨k, hk⟩))
    else cdsCombPrefix j k

private def evalCDSPos (u : Nat) : List CDS -> Nat
  | [] => 0
  | .p c d v :: tl => v * (2 ^ c * 3 ^ d) ^ u + evalCDSPos u tl
  | .n _ _ _ :: tl => evalCDSPos u tl

private def evalCDSNeg (u : Nat) : List CDS -> Nat
  | [] => 0
  | .p _ _ _ :: tl => evalCDSNeg u tl
  | .n c d v :: tl => v * (2 ^ c * 3 ^ d) ^ u + evalCDSNeg u tl

private def evalCDSInt (u : Nat) (sl : List CDS) : Int :=
  (evalCDSPos u sl : Int) - (evalCDSNeg u sl : Int)

private def powFastAux : Nat -> Nat -> Nat -> Nat
  | 0, _, _ => 1
  | fuel + 1, b, e =>
    if e == 0 then 1
    else
      let h := powFastAux fuel b (e / 2)
      if e % 2 == 0 then h * h else b * (h * h)

private def powFast6 (b e : Nat) : Nat := powFastAux 6 b e

private theorem pow_mono_base_w14 (a b : Nat) (hle : a ≤ b) : ∀ n : Nat, a ^ n ≤ b ^ n
  | 0 => Nat.le_refl 1
  | n + 1 => Nat.mul_le_mul (pow_mono_base_w14 a b hle n) hle

private theorem powFastAux_eq :
    ∀ (fuel b e : Nat), e < 2 ^ fuel -> powFastAux fuel b e = b ^ e
  | 0, _, e, hlt => by
    have he0 : e = 0 := by simp at hlt; exact hlt
    subst he0; rfl
  | fuel + 1, b, e, hlt => by
    simp only [powFastAux]
    cases he0 : (e == 0) with
    | true =>
      have h0 : e = 0 := beq_iff_eq.mp he0
      subst h0; simp
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      have hne0 : e ≠ 0 := beq_eq_false_iff_ne.mp he0
      have hhalf : e / 2 < 2 ^ fuel := by rw [Nat.pow_succ] at hlt; omega
      have ih := powFastAux_eq fuel b (e / 2) hhalf
      rw [ih]
      have hsq : b ^ (e / 2) * b ^ (e / 2) = b ^ (2 * (e / 2)) := by
        rw [← Nat.pow_add, show e / 2 + e / 2 = 2 * (e / 2) by omega]
      cases hev : (e % 2 == 0) with
      | true =>
        simp only [ite_true, hsq]
        have hm0 : e % 2 = 0 := beq_iff_eq.mp hev
        rw [show 2 * (e / 2) = e by omega]
      | false =>
        simp only [Bool.false_eq_true, ite_false, hsq]
        have hm1 : e % 2 = 1 := by
          have := beq_eq_false_iff_ne.mp hev; omega
        rw [show b * b ^ (2 * (e / 2)) = b ^ (2 * (e / 2) + 1) by
              rw [Nat.pow_succ, Nat.mul_comm],
            show 2 * (e / 2) + 1 = e by omega]

private def evalCDSPosFast (u : Nat) : List CDS -> Nat
  | [] => 0
  | .p c d v :: tl => v * powFast6 (2 ^ c * 3 ^ d) u + evalCDSPosFast u tl
  | .n _ _ _ :: tl => evalCDSPosFast u tl

private def evalCDSNegFast (u : Nat) : List CDS -> Nat
  | [] => 0
  | .p _ _ _ :: tl => evalCDSNegFast u tl
  | .n c d v :: tl => v * powFast6 (2 ^ c * 3 ^ d) u + evalCDSNegFast u tl

private theorem evalCDSFast_eq (u : Nat) (hu : u < 64) :
    ∀ sl : List CDS,
      evalCDSPosFast u sl = evalCDSPos u sl ∧
      evalCDSNegFast u sl = evalCDSNeg u sl
  | [] => ⟨rfl, rfl⟩
  | .p c d v :: tl => by
    rcases evalCDSFast_eq u hu tl with ⟨hp, hn⟩
    simp only [evalCDSPosFast, evalCDSPos, evalCDSNegFast, evalCDSNeg, hp, hn,
               powFast6, powFastAux_eq 6 _ u (by omega), and_self]
  | .n c d v :: tl => by
    rcases evalCDSFast_eq u hu tl with ⟨hp, hn⟩
    simp only [evalCDSPosFast, evalCDSPos, evalCDSNegFast, evalCDSNeg, hp, hn,
               powFast6, powFastAux_eq 6 _ u (by omega), and_self]

private def lead1010CDS : List CDS -> Nat
  | [] => 0
  | .p c d v :: tl => (if c == 10 && d == 10 then v else 0) + lead1010CDS tl
  | .n _ _ _ :: tl => lead1010CDS tl

private def sumNegCDS : List CDS -> Nat
  | [] => 0
  | .p _ _ _ :: tl => sumNegCDS tl
  | .n _ _ v :: tl => v + sumNegCDS tl

private def checkNegBasesCDS (B : Nat) : List CDS -> Bool
  | [] => true
  | .p _ _ _ :: tl => checkNegBasesCDS B tl
  | .n c d _ :: tl => decide (2 ^ c * 3 ^ d ≤ B) && checkNegBasesCDS B tl

private def checkCDSDom43 (sl : List CDS) : Bool :=
  (List.range 43).all (fun k => decide (evalCDSNegFast (k + 1) sl < evalCDSPosFast (k + 1) sl)) &&
  checkNegBasesCDS 45349632 sl &&
  decide (lead1010CDS sl ≥ 1) &&
  decide (sumNegCDS sl * powFast6 45349632 43 < lead1010CDS sl * powFast6 60466176 43)

private def cdsValid64 : CDS -> Bool
  | .p _ d _ => decide (d < 64)
  | .n _ d _ => decide (d < 64)

private def coneRowExpr (k : Fin 10) : Expr4 :=
  .mul (expr4Pow (.add (.mul (.const 3) .v0) (.mul (.const 359) .v1)) (9 - k.val))
       (expr4Pow (.add (.mul (.const 5) .v0) (.mul (.const 569) .v1)) k.val)

private def coneRowSumExpr (k : Fin 10) : Nat -> Expr4
  | 0 => .const 0
  | j + 1 =>
    if hj : j < 10 then
      .add (coneRowSumExpr k j)
           (.mul (.const (coneBinomCoeff k ⟨j, hj⟩))
                 (.mul (expr4Pow .v0 (9 - j)) (expr4Pow .v1 j)))
    else coneRowSumExpr k j

set_option maxRecDepth 65536 in
private theorem t3u3_cone_comb_and_binom_certs :
    (∀ k : Fin 10, (t3u3CoreWSlice k).all cdsValid64 = true) ∧
    (∀ k : Fin 10, normExpr4 (.sub (coneRowExpr k) (coneRowSumExpr k 10)) = []) ∧
    (∀ j : Fin 10, cdsCombPrefix j 10 = t3u3ConeSliceCDS j) := by decide

set_option maxRecDepth 65536 in
private theorem t3u3_cone_dom_0 : checkCDSDom43 (t3u3ConeSliceCDS ⟨0, by decide⟩) = true := by decide

set_option maxRecDepth 65536 in
private theorem t3u3_cone_dom_1 : checkCDSDom43 (t3u3ConeSliceCDS ⟨1, by decide⟩) = true := by decide

set_option maxRecDepth 65536 in
private theorem t3u3_cone_dom_2 : checkCDSDom43 (t3u3ConeSliceCDS ⟨2, by decide⟩) = true := by decide

set_option maxRecDepth 65536 in
private theorem t3u3_cone_dom_3 : checkCDSDom43 (t3u3ConeSliceCDS ⟨3, by decide⟩) = true := by decide

set_option maxRecDepth 65536 in
private theorem t3u3_cone_dom_4 : checkCDSDom43 (t3u3ConeSliceCDS ⟨4, by decide⟩) = true := by decide

set_option maxRecDepth 65536 in
private theorem t3u3_cone_dom_5 : checkCDSDom43 (t3u3ConeSliceCDS ⟨5, by decide⟩) = true := by decide

set_option maxRecDepth 65536 in
private theorem t3u3_cone_dom_6 : checkCDSDom43 (t3u3ConeSliceCDS ⟨6, by decide⟩) = true := by decide

set_option maxRecDepth 65536 in
private theorem t3u3_cone_dom_7 : checkCDSDom43 (t3u3ConeSliceCDS ⟨7, by decide⟩) = true := by decide

set_option maxRecDepth 65536 in
private theorem t3u3_cone_dom_8 : checkCDSDom43 (t3u3ConeSliceCDS ⟨8, by decide⟩) = true := by decide

set_option maxRecDepth 65536 in
private theorem t3u3_cone_dom_9 : checkCDSDom43 (t3u3ConeSliceCDS ⟨9, by decide⟩) = true := by decide

private theorem t3u3_cone_dom_all (j : Fin 10) : checkCDSDom43 (t3u3ConeSliceCDS j) = true := by
  rcases (by have := j.isLt; omega :
    j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 ∨ j.val = 4 ∨
    j.val = 5 ∨ j.val = 6 ∨ j.val = 7 ∨ j.val = 8 ∨ j.val = 9) with
    h | h | h | h | h | h | h | h | h | h
  · have hje : j = ⟨0, by decide⟩ := Fin.ext h; rw [hje]; exact t3u3_cone_dom_0
  · have hje : j = ⟨1, by decide⟩ := Fin.ext h; rw [hje]; exact t3u3_cone_dom_1
  · have hje : j = ⟨2, by decide⟩ := Fin.ext h; rw [hje]; exact t3u3_cone_dom_2
  · have hje : j = ⟨3, by decide⟩ := Fin.ext h; rw [hje]; exact t3u3_cone_dom_3
  · have hje : j = ⟨4, by decide⟩ := Fin.ext h; rw [hje]; exact t3u3_cone_dom_4
  · have hje : j = ⟨5, by decide⟩ := Fin.ext h; rw [hje]; exact t3u3_cone_dom_5
  · have hje : j = ⟨6, by decide⟩ := Fin.ext h; rw [hje]; exact t3u3_cone_dom_6
  · have hje : j = ⟨7, by decide⟩ := Fin.ext h; rw [hje]; exact t3u3_cone_dom_7
  · have hje : j = ⟨8, by decide⟩ := Fin.ext h; rw [hje]; exact t3u3_cone_dom_8
  · have hje : j = ⟨9, by decide⟩ := Fin.ext h; rw [hje]; exact t3u3_cone_dom_9

private theorem cdsMerge_valid_and_eval (u : Nat) :
    ∀ (xs ys : List CDS),
      xs.all cdsValid64 = true -> ys.all cdsValid64 = true ->
      (cdsMerge xs ys).all cdsValid64 = true ∧
      evalCDSInt u (cdsMerge xs ys) = evalCDSInt u xs + evalCDSInt u ys := by
  have haux : ∀ (fuel : Nat) (xs ys : List CDS),
      xs.all cdsValid64 = true -> ys.all cdsValid64 = true ->
      (cdsMergeAux fuel xs ys).all cdsValid64 = true ∧
      evalCDSInt u (cdsMergeAux fuel xs ys) = evalCDSInt u xs + evalCDSInt u ys := by
    intro fuel; induction fuel with
    | zero =>
      intro xs ys hxs hys
      have happ : ∀ as bs : List CDS,
          evalCDSPos u (as ++ bs) = evalCDSPos u as + evalCDSPos u bs ∧
          evalCDSNeg u (as ++ bs) = evalCDSNeg u as + evalCDSNeg u bs := by
        intro as bs; induction as with
        | nil => simp [evalCDSPos, evalCDSNeg]
        | cons a atl iha =>
          cases a with
          | p c d v =>
            exact ⟨by simp only [List.cons_append, evalCDSPos, iha.1, Nat.add_assoc],
                   by simp only [List.cons_append, evalCDSNeg, iha.2]⟩
          | n c d v =>
            exact ⟨by simp only [List.cons_append, evalCDSPos, iha.1],
                   by simp only [List.cons_append, evalCDSNeg, iha.2, Nat.add_assoc]⟩
      rcases happ xs ys with ⟨hp, hn⟩
      refine ⟨by simp only [cdsMergeAux, List.all_append, hxs, hys, Bool.and_self], ?_⟩
      simp only [cdsMergeAux, evalCDSInt, hp, hn, Int.natCast_add]
      let p1 := (evalCDSPos u xs : Int)
      let p2 := (evalCDSPos u ys : Int)
      let n1 := (evalCDSNeg u xs : Int)
      let n2 := (evalCDSNeg u ys : Int)
      change (p1 + p2) - (n1 + n2) = (p1 - n1) + (p2 - n2)
      omega
    | succ f' ih =>
      intro xs ys hxs hys
      cases xs with
      | nil => simp [cdsMergeAux, evalCDSInt, evalCDSPos, evalCDSNeg, hys]
      | cons x xtl =>
        cases ys with
        | nil => simp [cdsMergeAux, evalCDSInt, evalCDSPos, evalCDSNeg, hxs]
        | cons y ytl =>
          simp only [List.all_cons, Bool.and_eq_true] at hxs hys
          simp only [cdsMergeAux]
          let Pm := (evalCDSPos u (cdsMergeAux f' xtl ytl) : Int)
          let Nm := (evalCDSNeg u (cdsMergeAux f' xtl ytl) : Int)
          let Px := (evalCDSPos u xtl : Int)
          let Nx := (evalCDSNeg u xtl : Int)
          let Py := (evalCDSPos u ytl : Int)
          let Ny := (evalCDSNeg u ytl : Int)
          cases hk : (cdsKey x == cdsKey y) with
          | true =>
            simp only [ite_true]
            have hkeq : cdsKey x = cdsKey y := beq_iff_eq.mp hk
            rcases ih xtl ytl hxs.2 hys.2 with ⟨hvm, hevm⟩
            change Pm - Nm = (Px - Nx) + (Py - Ny) at hevm
            cases x with
            | p c1 d1 v1 =>
              cases y with
              | p c2 d2 v2 =>
                simp only [cdsValid64, decide_eq_true_eq] at hxs hys
                simp only [cdsKey] at hkeq
                rcases (by omega : c1 = c2 ∧ d1 = d2) with ⟨rfl, rfl⟩
                refine ⟨by simp only [cdsAddSame, List.all_cons, cdsValid64, hxs.1, decide_true, hvm]; rfl, ?_⟩
                simp only [cdsAddSame, evalCDSInt, evalCDSPos, evalCDSNeg, Nat.add_mul, Int.natCast_add]
                let t1 := ((v1 * (2 ^ c1 * 3 ^ d1) ^ u : Nat) : Int)
                let t2 := ((v2 * (2 ^ c1 * 3 ^ d1) ^ u : Nat) : Int)
                change ((t1 + t2) + Pm) - Nm = ((t1 + Px) - Nx) + ((t2 + Py) - Ny)
                omega
              | n c2 d2 v2 =>
                simp only [cdsValid64, decide_eq_true_eq] at hxs hys
                simp only [cdsKey] at hkeq
                rcases (by omega : c1 = c2 ∧ d1 = d2) with ⟨rfl, rfl⟩
                simp only [cdsAddSame]
                cases hv : (v1 == v2) with
                | true =>
                  have hveq : v1 = v2 := beq_iff_eq.mp hv; subst hveq
                  refine ⟨hvm, ?_⟩
                  simp only [ite_true, evalCDSInt, evalCDSPos, evalCDSNeg, Int.natCast_add]
                  let t1 := ((v1 * (2 ^ c1 * 3 ^ d1) ^ u : Nat) : Int)
                  change Pm - Nm = ((t1 + Px) - Nx) + (Py - (t1 + Ny))
                  omega
                | false =>
                  simp only [Bool.false_eq_true, ite_false]
                  have hvne : v1 ≠ v2 := beq_eq_false_iff_ne.mp hv
                  by_cases hgt : v1 > v2
                  · simp only [hgt, ite_true]
                    refine ⟨by simp only [List.all_cons, cdsValid64, hxs.1, decide_true, hvm]; rfl, ?_⟩
                    have hle_m : v2 * (2 ^ c1 * 3 ^ d1) ^ u ≤ v1 * (2 ^ c1 * 3 ^ d1) ^ u :=
                      Nat.mul_le_mul_right _ (by omega)
                    simp only [evalCDSInt, evalCDSPos, evalCDSNeg, Nat.sub_mul, Int.natCast_add,
                               Int.ofNat_sub hle_m]
                    let t1 := ((v1 * (2 ^ c1 * 3 ^ d1) ^ u : Nat) : Int)
                    let t2 := ((v2 * (2 ^ c1 * 3 ^ d1) ^ u : Nat) : Int)
                    change ((t1 - t2) + Pm) - Nm = ((t1 + Px) - Nx) + (Py - (t2 + Ny))
                    omega
                  · simp only [hgt, ite_false]
                    refine ⟨by simp only [List.all_cons, cdsValid64, hxs.1, decide_true, hvm]; rfl, ?_⟩
                    have hle_m : v1 * (2 ^ c1 * 3 ^ d1) ^ u ≤ v2 * (2 ^ c1 * 3 ^ d1) ^ u :=
                      Nat.mul_le_mul_right _ (by omega)
                    simp only [evalCDSInt, evalCDSPos, evalCDSNeg, Nat.sub_mul, Int.natCast_add,
                               Int.ofNat_sub hle_m]
                    let t1 := ((v1 * (2 ^ c1 * 3 ^ d1) ^ u : Nat) : Int)
                    let t2 := ((v2 * (2 ^ c1 * 3 ^ d1) ^ u : Nat) : Int)
                    change Pm - ((t2 - t1) + Nm) = ((t1 + Px) - Nx) + (Py - (t2 + Ny))
                    omega
            | n c1 d1 v1 =>
              cases y with
              | p c2 d2 v2 =>
                simp only [cdsValid64, decide_eq_true_eq] at hxs hys
                simp only [cdsKey] at hkeq
                rcases (by omega : c1 = c2 ∧ d1 = d2) with ⟨rfl, rfl⟩
                simp only [cdsAddSame]
                cases hv : (v1 == v2) with
                | true =>
                  have hveq : v1 = v2 := beq_iff_eq.mp hv; subst hveq
                  refine ⟨hvm, ?_⟩
                  simp only [ite_true, evalCDSInt, evalCDSPos, evalCDSNeg, Int.natCast_add]
                  let t1 := ((v1 * (2 ^ c1 * 3 ^ d1) ^ u : Nat) : Int)
                  change Pm - Nm = (Px - (t1 + Nx)) + ((t1 + Py) - Ny)
                  omega
                | false =>
                  simp only [Bool.false_eq_true, ite_false]
                  have hvne : v1 ≠ v2 := beq_eq_false_iff_ne.mp hv
                  by_cases hgt : v1 > v2
                  · simp only [hgt, ite_true]
                    refine ⟨by simp only [List.all_cons, cdsValid64, hxs.1, decide_true, hvm]; rfl, ?_⟩
                    have hle_m : v2 * (2 ^ c1 * 3 ^ d1) ^ u ≤ v1 * (2 ^ c1 * 3 ^ d1) ^ u :=
                      Nat.mul_le_mul_right _ (by omega)
                    simp only [evalCDSInt, evalCDSPos, evalCDSNeg, Nat.sub_mul, Int.natCast_add,
                               Int.ofNat_sub hle_m]
                    let t1 := ((v1 * (2 ^ c1 * 3 ^ d1) ^ u : Nat) : Int)
                    let t2 := ((v2 * (2 ^ c1 * 3 ^ d1) ^ u : Nat) : Int)
                    change Pm - ((t1 - t2) + Nm) = (Px - (t1 + Nx)) + ((t2 + Py) - Ny)
                    omega
                  · simp only [hgt, ite_false]
                    refine ⟨by simp only [List.all_cons, cdsValid64, hxs.1, decide_true, hvm]; rfl, ?_⟩
                    have hle_m : v1 * (2 ^ c1 * 3 ^ d1) ^ u ≤ v2 * (2 ^ c1 * 3 ^ d1) ^ u :=
                      Nat.mul_le_mul_right _ (by omega)
                    simp only [evalCDSInt, evalCDSPos, evalCDSNeg, Nat.sub_mul, Int.natCast_add,
                               Int.ofNat_sub hle_m]
                    let t1 := ((v1 * (2 ^ c1 * 3 ^ d1) ^ u : Nat) : Int)
                    let t2 := ((v2 * (2 ^ c1 * 3 ^ d1) ^ u : Nat) : Int)
                    change ((t2 - t1) + Pm) - Nm = (Px - (t1 + Nx)) + ((t2 + Py) - Ny)
                    omega
              | n c2 d2 v2 =>
                simp only [cdsValid64, decide_eq_true_eq] at hxs hys
                simp only [cdsKey] at hkeq
                rcases (by omega : c1 = c2 ∧ d1 = d2) with ⟨rfl, rfl⟩
                refine ⟨by simp only [cdsAddSame, List.all_cons, cdsValid64, hxs.1, decide_true, hvm]; rfl, ?_⟩
                simp only [cdsAddSame, evalCDSInt, evalCDSPos, evalCDSNeg, Nat.add_mul, Int.natCast_add]
                let t1 := ((v1 * (2 ^ c1 * 3 ^ d1) ^ u : Nat) : Int)
                let t2 := ((v2 * (2 ^ c1 * 3 ^ d1) ^ u : Nat) : Int)
                change Pm - ((t1 + t2) + Nm) = (Px - (t1 + Nx)) + (Py - (t2 + Ny))
                omega
          | false =>
            simp only [Bool.false_eq_true, ite_false]
            by_cases hlt : cdsKey x < cdsKey y
            · simp only [hlt, ite_true]
              rcases ih xtl (y :: ytl) hxs.2 (by simp only [List.all_cons, hys.1, hys.2, Bool.and_self]) with ⟨hvm, hevm⟩
              refine ⟨by simp only [List.all_cons, hxs.1, hvm, Bool.and_self], ?_⟩
              let Pm1 := (evalCDSPos u (cdsMergeAux f' xtl (y :: ytl)) : Int)
              let Nm1 := (evalCDSNeg u (cdsMergeAux f' xtl (y :: ytl)) : Int)
              let Pyc := (evalCDSPos u (y :: ytl) : Int)
              let Nyc := (evalCDSNeg u (y :: ytl) : Int)
              change Pm1 - Nm1 = (Px - Nx) + (Pyc - Nyc) at hevm
              cases x with
              | p cx dx vx =>
                simp only [evalCDSInt, evalCDSPos, evalCDSNeg, Int.natCast_add]
                let tx := ((vx * (2 ^ cx * 3 ^ dx) ^ u : Nat) : Int)
                change (tx + Pm1) - Nm1 = ((tx + Px) - Nx) + (Pyc - Nyc)
                omega
              | n cx dx vx =>
                simp only [evalCDSInt, evalCDSPos, evalCDSNeg, Int.natCast_add]
                let tx := ((vx * (2 ^ cx * 3 ^ dx) ^ u : Nat) : Int)
                change Pm1 - (tx + Nm1) = (Px - (tx + Nx)) + (Pyc - Nyc)
                omega
            · simp only [hlt, ite_false]
              rcases ih (x :: xtl) ytl (by simp only [List.all_cons, hxs.1, hxs.2, Bool.and_self]) hys.2 with ⟨hvm, hevm⟩
              refine ⟨by simp only [List.all_cons, hys.1, hvm, Bool.and_self], ?_⟩
              let Pm2 := (evalCDSPos u (cdsMergeAux f' (x :: xtl) ytl) : Int)
              let Nm2 := (evalCDSNeg u (cdsMergeAux f' (x :: xtl) ytl) : Int)
              let Pxc := (evalCDSPos u (x :: xtl) : Int)
              let Nxc := (evalCDSNeg u (x :: xtl) : Int)
              change Pm2 - Nm2 = (Pxc - Nxc) + (Py - Ny) at hevm
              cases y with
              | p cy dy vy =>
                simp only [evalCDSInt, evalCDSPos, evalCDSNeg, Int.natCast_add]
                let ty := ((vy * (2 ^ cy * 3 ^ dy) ^ u : Nat) : Int)
                change (ty + Pm2) - Nm2 = (Pxc - Nxc) + ((ty + Py) - Ny)
                omega
              | n cy dy vy =>
                simp only [evalCDSInt, evalCDSPos, evalCDSNeg, Int.natCast_add]
                let ty := ((vy * (2 ^ cy * 3 ^ dy) ^ u : Nat) : Int)
                change Pm2 - (ty + Nm2) = (Pxc - Nxc) + (Py - (ty + Ny))
                omega
  exact fun xs ys hxs hys => haux (xs.length + ys.length) xs ys hxs hys

private theorem cdsScaleInt_valid_and_eval (u : Nat) (coef : Int) :
    ∀ xs : List CDS,
      xs.all cdsValid64 = true ->
      (cdsScaleInt coef xs).all cdsValid64 = true ∧
      evalCDSInt u (cdsScaleInt coef xs) = coef * evalCDSInt u xs := by
  have hpos : ∀ (m : Nat) (xs : List CDS),
      xs.all cdsValid64 = true ->
      (cdsScalePos m xs).all cdsValid64 = true ∧
      evalCDSPos u (cdsScalePos m xs) = m * evalCDSPos u xs ∧
      evalCDSNeg u (cdsScalePos m xs) = m * evalCDSNeg u xs := by
    intro m xs; induction xs with
    | nil => intro _; simp [cdsScalePos, evalCDSPos, evalCDSNeg]
    | cons x tl ih =>
      intro hx
      simp only [List.all_cons, Bool.and_eq_true] at hx
      rcases ih hx.2 with ⟨hv, hp, hn⟩
      cases x <;>
        (simp only [cdsValid64] at hx;
         simp only [cdsScalePos, List.all_cons, cdsValid64, hx.1, hv, Bool.and_self,
                    evalCDSPos, evalCDSNeg, hp, hn, Nat.mul_add, Nat.mul_assoc, and_self])
  have hflip : ∀ ys : List CDS,
      ys.all cdsValid64 = true ->
      (ys.map (fun x => match x with | .p c d v => .n c d v | .n c d v => .p c d v)).all cdsValid64 = true ∧
      evalCDSPos u (ys.map (fun x => match x with | .p c d v => .n c d v | .n c d v => .p c d v)) = evalCDSNeg u ys ∧
      evalCDSNeg u (ys.map (fun x => match x with | .p c d v => .n c d v | .n c d v => .p c d v)) = evalCDSPos u ys := by
    intro ys; induction ys with
    | nil => intro _; simp [evalCDSPos, evalCDSNeg]
    | cons y tl ih =>
      intro hy
      simp only [List.all_cons, Bool.and_eq_true] at hy
      rcases ih hy.2 with ⟨hv, hp, hn⟩
      cases y <;>
        (simp only [cdsValid64] at hy;
         simp only [List.map_cons, List.all_cons, cdsValid64, hy.1, hv, Bool.and_self,
                    evalCDSPos, evalCDSNeg, hp, hn, and_self])
  intro xs hxs
  unfold cdsScaleInt
  cases hz : (coef == 0) with
  | true =>
    have hc0 : coef = 0 := beq_iff_eq.mp hz
    subst hc0; simp [evalCDSInt, evalCDSPos, evalCDSNeg]
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    have hne0 : coef ≠ 0 := beq_eq_false_iff_ne.mp hz
    rcases hpos coef.natAbs xs hxs with ⟨hvp, hpp, hnp⟩
    by_cases hgt : coef > 0
    · simp only [hgt, ite_true]
      refine ⟨hvp, ?_⟩
      simp only [evalCDSInt, hpp, hnp, Int.natCast_mul]
      have ha : (coef.natAbs : Int) = coef := by omega
      rw [ha, Int.mul_sub]
    · simp only [hgt, ite_false]
      rcases hflip (cdsScalePos coef.natAbs xs) hvp with ⟨hvf, hpf, hnf⟩
      refine ⟨hvf, ?_⟩
      unfold evalCDSInt
      rw [hpf, hnf, hpp, hnp, Int.natCast_mul, Int.natCast_mul]
      have ha : coef = -((coef.natAbs : Int)) := by omega
      conv => rhs; lhs; rw [ha]
      rw [Int.neg_mul, Int.mul_sub]
      omega

private theorem checkCDSDom43_sound (sl : List CDS) (h : checkCDSDom43 sl = true) :
    ∀ u : Nat, u ≥ 1 -> evalCDSInt u sl > 0 := by
  unfold checkCDSDom43 at h
  rcases bool_and_split h with ⟨h123, hdom43_b⟩
  rcases bool_and_split h123 with ⟨h12, hlead1_b⟩
  rcases bool_and_split h12 with ⟨hall43, hnegB_b⟩
  have hdom43 : sumNegCDS sl * 45349632 ^ 43 < lead1010CDS sl * 60466176 ^ 43 := by
    have hd := of_decide_eq_true hdom43_b
    rwa [powFast6, powFastAux_eq 6 45349632 43 (by decide),
         powFast6, powFastAux_eq 6 60466176 43 (by decide)] at hd
  have hlead_le : ∀ (u : Nat) (xs : List CDS),
      lead1010CDS xs * 60466176 ^ u ≤ evalCDSPos u xs := by
    intro u xs; induction xs with
    | nil => simp [lead1010CDS, evalCDSPos]
    | cons hd tl ih =>
      cases hd with
      | p c d v =>
        simp only [lead1010CDS, evalCDSPos, Nat.add_mul]
        cases hc : (c == 10 && d == 10) with
        | true =>
          simp only [ite_true]
          simp only [Bool.and_eq_true, beq_iff_eq] at hc
          rcases hc with ⟨rfl, rfl⟩
          rw [show 2 ^ 10 * 3 ^ 10 = 60466176 by decide]
          exact Nat.add_le_add_left ih _
        | false =>
          simp only [Bool.false_eq_true, ite_false, Nat.zero_mul, Nat.zero_add]
          exact Nat.le_trans ih (Nat.le_add_left _ _)
      | n _ _ _ =>
        simp only [lead1010CDS, evalCDSPos]; exact ih
  have hneg_le : ∀ (u : Nat) (xs : List CDS),
      checkNegBasesCDS 45349632 xs = true ->
      evalCDSNeg u xs ≤ sumNegCDS xs * 45349632 ^ u := by
    intro u xs; induction xs with
    | nil => intro _; simp [evalCDSNeg, sumNegCDS]
    | cons hd tl ih =>
      cases hd with
      | p _ _ _ =>
        intro hnb; simp only [checkNegBasesCDS] at hnb
        simp only [evalCDSNeg, sumNegCDS]; exact ih hnb
      | n c d v =>
        intro hnb; simp only [checkNegBasesCDS] at hnb
        rcases bool_and_split hnb with ⟨hcur_b, htl_b⟩
        have iht := ih htl_b
        have hb_le : 2 ^ c * 3 ^ d ≤ 45349632 := of_decide_eq_true hcur_b
        have hp_le := pow_mono_base_w14 (2 ^ c * 3 ^ d) 45349632 hb_le u
        have hm := Nat.mul_le_mul_left v hp_le
        simp only [evalCDSNeg, sumNegCDS, Nat.add_mul]
        exact Nat.add_le_add hm iht
  intro u hu1
  unfold evalCDSInt
  by_cases hu43 : u ≤ 43
  · have hmem : u - 1 ∈ List.range 43 := List.mem_range.mpr (by omega)
    have hlt_f : evalCDSNegFast u sl < evalCDSPosFast u sl := by
      simpa [show u - 1 + 1 = u by omega] using
        of_decide_eq_true (List.all_eq_true.mp hall43 (u - 1) hmem)
    rcases evalCDSFast_eq u (by omega) sl with ⟨hp, hn⟩
    rw [hp, hn] at hlt_f
    omega
  · have hdom_u : ∀ d : Nat,
        sumNegCDS sl * 45349632 ^ (43 + d) < lead1010CDS sl * 60466176 ^ (43 + d) := by
      intro d; induction d with
      | zero => exact hdom43
      | succ d' ih =>
        rw [Nat.add_succ, Nat.pow_succ 45349632, Nat.pow_succ 60466176]
        have h1 : sumNegCDS sl * (45349632 ^ (43 + d') * 45349632) ≤
            (sumNegCDS sl * 45349632 ^ (43 + d')) * 60466176 := by
          rw [← Nat.mul_assoc]
          exact Nat.mul_le_mul_left _ (by decide : 45349632 ≤ 60466176)
        have h2 : (sumNegCDS sl * 45349632 ^ (43 + d')) * 60466176 <
            (lead1010CDS sl * 60466176 ^ (43 + d')) * 60466176 :=
          Nat.mul_lt_mul_of_pos_right ih (by decide)
        have hr : (lead1010CDS sl * 60466176 ^ (43 + d')) * 60466176 =
            lead1010CDS sl * (60466176 ^ (43 + d') * 60466176) := Nat.mul_assoc _ _ _
        rw [hr] at h2
        exact Nat.lt_of_le_of_lt h1 h2
    have hdu := hdom_u (u - 43)
    rw [show 43 + (u - 43) = u by omega] at hdu
    have h1 := hneg_le u sl hnegB_b
    have h2 := hlead_le u sl
    omega

private def evalP9ShapeNat (c9 c6 c4 c2 : Nat) (W K : Nat) : Nat :=
  c9 * W ^ 9 + c6 * W ^ 6 * K ^ 3 + c4 * W ^ 4 * K ^ 5 + c2 * W ^ 2 * K ^ 7

private def evalN9ShapeNat (c7 c5 c3 c0 : Nat) (W K : Nat) : Nat :=
  c7 * W ^ 7 * K ^ 2 + c5 * W ^ 5 * K ^ 4 + c3 * W ^ 3 * K ^ 6 + c0 * K ^ 9

private def powModSmall (a : Nat) : Nat -> Nat -> Nat
  | 0, p => 1 % p
  | k + 1, p => (a * powModSmall a k p) % p

private theorem powModSmall_eq (a : Nat) :
    ∀ (k p : Nat), powModSmall a k p = a ^ k % p
  | 0, p => rfl
  | k + 1, p => by
    rw [powModSmall, powModSmall_eq a k p, Nat.pow_succ, Nat.mul_comm (a ^ k) a,
        Nat.mul_mod a (a ^ k % p) p, Nat.mod_mod, ← Nat.mul_mod a (a ^ k) p]

private def evalP9Mod (p r9 r6 r4 r2 a b : Nat) : Nat :=
  (r9 * powModSmall a 9 p +
   ((r6 * powModSmall a 6 p) % p) * powModSmall b 3 p +
   ((r4 * powModSmall a 4 p) % p) * powModSmall b 5 p +
   ((r2 * powModSmall a 2 p) % p) * powModSmall b 7 p) % p

private def evalN9Mod (p r7 r5 r3 r0 a b : Nat) : Nat :=
  (((r7 * powModSmall a 7 p) % p) * powModSmall b 2 p +
   ((r5 * powModSmall a 5 p) % p) * powModSmall b 4 p +
   ((r3 * powModSmall a 3 p) % p) * powModSmall b 6 p +
   r0 * powModSmall b 9 p) % p

private theorem pow_mod_eq_mod_pow_w14 (m a : Nat) :
    ∀ k : Nat, a ^ k % m = (a % m) ^ k % m
  | 0 => rfl
  | k + 1 => by
    rw [Nat.pow_succ a k, Nat.pow_succ (a % m) k,
        Nat.mul_mod (a ^ k) a m, pow_mod_eq_mod_pow_w14 m a k,
        Nat.mul_mod ((a % m) ^ k % m) (a % m) m, Nat.mod_mod, ← Nat.mul_mod]

private theorem mul_pow_w14 (a b : Nat) : ∀ n : Nat, (a * b) ^ n = a ^ n * b ^ n
  | 0 => rfl
  | n + 1 => by rw [Nat.pow_succ, mul_pow_w14 a b n, Nat.pow_succ, Nat.pow_succ]; ac_rfl

private theorem p9Shape_nonzero_of_mod_p
    (c9 c6 c4 c2 c7 c5 c3 c0 p : Nat) (hp2 : p ≥ 2)
    (honly0 : ∀ a b : Fin p,
      evalP9Mod p (c9 % p) (c6 % p) (c4 % p) (c2 % p) a.val b.val =
        evalN9Mod p (c7 % p) (c5 % p) (c3 % p) (c0 % p) a.val b.val ->
      a.val = 0 ∧ b.val = 0) :
    ∀ W K : Nat, W ≥ 1 -> K ≥ 1 ->
      evalP9ShapeNat c9 c6 c4 c2 W K ≠ evalN9ShapeNat c7 c5 c3 c0 W K := by
  have hhom : ∀ (c W K a b : Nat), a + b = 9 ->
      (c * W) ^ a * (c * K) ^ b = c ^ 9 * (W ^ a * K ^ b) := by
    intro c W K a b hab
    rw [mul_pow_w14 c W a, mul_pow_w14 c K b]
    calc (c ^ a * W ^ a) * (c ^ b * K ^ b)
        = (c ^ a * c ^ b) * (W ^ a * K ^ b) := by ac_rfl
      _ = c ^ (a + b) * (W ^ a * K ^ b) := by rw [← Nat.pow_add]
      _ = c ^ 9 * (W ^ a * K ^ b) := by rw [hab]
  have hscale : ∀ (c W K : Nat),
      evalP9ShapeNat c9 c6 c4 c2 (c * W) (c * K) = c ^ 9 * evalP9ShapeNat c9 c6 c4 c2 W K ∧
      evalN9ShapeNat c7 c5 c3 c0 (c * W) (c * K) = c ^ 9 * evalN9ShapeNat c7 c5 c3 c0 W K := by
    intro c W K
    unfold evalP9ShapeNat evalN9ShapeNat
    have h90 := mul_pow_w14 c W 9
    have h63 := hhom c W K 6 3 rfl
    have h45 := hhom c W K 4 5 rfl
    have h27 := hhom c W K 2 7 rfl
    have h72 := hhom c W K 7 2 rfl
    have h54 := hhom c W K 5 4 rfl
    have h36 := hhom c W K 3 6 rfl
    have h09 := mul_pow_w14 c K 9
    have hm3 : ∀ (k x y : Nat), k * x * y = k * (x * y) := Nat.mul_assoc
    rw [hm3 c6, hm3 c4, hm3 c2, hm3 c7, hm3 c5, hm3 c3,
        hm3 c6 (W ^ 6), hm3 c4 (W ^ 4), hm3 c2 (W ^ 2),
        hm3 c7 (W ^ 7), hm3 c5 (W ^ 5), hm3 c3 (W ^ 3),
        h90, h63, h45, h27, h72, h54, h36, h09]
    refine ⟨?_, ?_⟩
    · simp only [Nat.mul_add]; ac_rfl
    · simp only [Nat.mul_add]; ac_rfl
  have hadd4 : ∀ (a b c d : Nat), (a + b + c + d) % p = (a % p + b % p + c % p + d % p) % p := by
    intro a b c d
    rw [Nat.add_mod (a + b + c) d, Nat.add_mod (a + b) c, Nat.add_mod a b]
    simp [Nat.add_mod]
  have ht3 : ∀ (cf W K a b : Nat),
      (cf * W ^ a * K ^ b) % p =
        (((cf % p) * powModSmall (W % p) a p) % p * powModSmall (K % p) b p) % p := by
    intro cf W K a b
    rw [powModSmall_eq, powModSmall_eq,
        Nat.mul_mod (cf * W ^ a) (K ^ b) p,
        Nat.mul_mod cf (W ^ a) p,
        pow_mod_eq_mod_pow_w14 p W a,
        pow_mod_eq_mod_pow_w14 p K b]
  have ht2 : ∀ (cf X a : Nat),
      (cf * X ^ a) % p = ((cf % p) * powModSmall (X % p) a p) % p := by
    intro cf X a
    rw [powModSmall_eq, Nat.mul_mod cf (X ^ a) p, pow_mod_eq_mod_pow_w14 p X a]
  have hdesc : ∀ (fuel W K : Nat), W ≥ 1 -> K ≥ 1 -> W + K ≤ fuel ->
      evalP9ShapeNat c9 c6 c4 c2 W K ≠ evalN9ShapeNat c7 c5 c3 c0 W K := by
    intro fuel; induction fuel with
    | zero => intro W K hW _ hle; omega
    | succ fuel' ih =>
      intro W K hW hK hle heq
      have hp_mod : evalP9ShapeNat c9 c6 c4 c2 W K % p =
          evalP9Mod p (c9 % p) (c6 % p) (c4 % p) (c2 % p) (W % p) (K % p) := by
        unfold evalP9ShapeNat evalP9Mod
        rw [hadd4, ht2 c9 W 9, ht3 c6 W K 6 3, ht3 c4 W K 4 5, ht3 c2 W K 2 7, ← hadd4]
      have hn_mod : evalN9ShapeNat c7 c5 c3 c0 W K % p =
          evalN9Mod p (c7 % p) (c5 % p) (c3 % p) (c0 % p) (W % p) (K % p) := by
        unfold evalN9ShapeNat evalN9Mod
        rw [hadd4, ht3 c7 W K 7 2, ht3 c5 W K 5 4, ht3 c3 W K 3 6, ht2 c0 K 9, ← hadd4]
      have hm_eq : evalP9Mod p (c9 % p) (c6 % p) (c4 % p) (c2 % p) (W % p) (K % p) =
          evalN9Mod p (c7 % p) (c5 % p) (c3 % p) (c0 % p) (W % p) (K % p) := by
        rw [← hp_mod, ← hn_mod, heq]
      rcases honly0 ⟨W % p, Nat.mod_lt W (by omega)⟩ ⟨K % p, Nat.mod_lt K (by omega)⟩ hm_eq with
        ⟨hw0, hk0⟩
      dsimp only at hw0 hk0
      rcases (⟨W / p, rfl⟩ : ∃ wq : Nat, wq = W / p) with ⟨W', hW'_def⟩
      rcases (⟨K / p, rfl⟩ : ∃ kq : Nat, kq = K / p) with ⟨K', hK'_def⟩
      have hW_eq : W = p * W' := by
        have := Nat.div_add_mod W p; rw [← hW'_def, hw0, Nat.add_zero] at this; exact this.symm
      have hK_eq : K = p * K' := by
        have := Nat.div_add_mod K p; rw [← hK'_def, hk0, Nat.add_zero] at this; exact this.symm
      have hW'1 : W' ≥ 1 := by
        by_cases h0 : W' = 0
        · rw [h0, Nat.mul_zero] at hW_eq; omega
        · exact Nat.pos_of_ne_zero h0
      have hK'1 : K' ≥ 1 := by
        by_cases h0 : K' = 0
        · rw [h0, Nat.mul_zero] at hK_eq; omega
        · exact Nat.pos_of_ne_zero h0
      have hW'_lt : W' < W := by
        have hm2 : 2 * W' ≤ p * W' := Nat.mul_le_mul_right W' hp2; omega
      have hK'_lt : K' < K := by
        have hm2 : 2 * K' ≤ p * K' := Nat.mul_le_mul_right K' hp2; omega
      have hsum_le : W' + K' ≤ fuel' := by omega
      rw [hW_eq, hK_eq] at heq
      rcases hscale p W' K' with ⟨hs1, hs2⟩
      rw [hs1, hs2] at heq
      have hp9_pos : 0 < p ^ 9 := nat_pow_pos_of_pos p (by omega) 9
      exact ih W' K' hW'1 hK'1 hsum_le (Nat.eq_of_mul_eq_mul_left hp9_pos heq)
  exact fun W K hW hK => hdesc (W + K) W K hW hK (Nat.le_refl _)

private def evalCoreBySlicesFast (W K u : Nat) : Int :=
  intSumPrefix 10 (fun k =>
    ((W ^ (9 - k.val) * K ^ k.val : Nat) : Int) *
      ((evalCDSPosFast u (t3u3CoreWSlice k) : Int) -
       (evalCDSNegFast u (t3u3CoreWSlice k) : Int))) 10

private def uCoeffExpected (u : Nat) (k : Fin 10) : Int :=
  match u, k.val with
  | 2, 0 => 2199023255552000
  | 2, 1 => 0
  | 2, 2 => -7507544113152000
  | 2, 3 => 13186614951936000
  | 2, 4 => -14815640420352000
  | 2, 5 => 11147786072064000
  | 2, 6 => -4686007707648000
  | 2, 7 => 826587742464000
  | 2, 8 => 0
  | 2, _ => -5230176601500
  | 3, 0 => 124978163625105714839552
  | 3, 1 => 0
  | 3, 2 => -474351183918870032646144
  | 3, 3 => 1179050514692310067691520
  | 3, 4 => -1679284066846954256252928
  | 3, 5 => 1367651174516320545476352
  | 3, 6 => -585036561636077673507840
  | 3, 7 => 102186082691158168475136
  | 3, 8 => 0
  | 3, _ => -45588202081385747868
  | _, 0 => 4966281438688031277056000000000
  | _, 1 => 0
  | _, 2 => -24307961242974469226496000000000
  | _, 3 => 77434489029329713889280000000000
  | _, 4 => -123777933834888627093504000000000
  | _, 5 => 107784756410516048719872000000000
  | _, 6 => -49072261475418592527360000000000
  | _, 7 => 9105771852569740120128000000000
  | _, 8 => 0
  | _, _ => -213372379402244410148437500

set_option maxRecDepth 65536 in
private theorem t3u3_u234_and_contrast_certs :
    (∀ k : Fin 10,
      (evalCDSPosFast 2 (t3u3CoreWSlice k) : Int) - (evalCDSNegFast 2 (t3u3CoreWSlice k) : Int) =
        uCoeffExpected 2 k ∧
      (evalCDSPosFast 3 (t3u3CoreWSlice k) : Int) - (evalCDSNegFast 3 (t3u3CoreWSlice k) : Int) =
        uCoeffExpected 3 k ∧
      (evalCDSPosFast 4 (t3u3CoreWSlice k) : Int) - (evalCDSNegFast 4 (t3u3CoreWSlice k) : Int) =
        uCoeffExpected 4 k) ∧
    (∀ a b : Fin 43,
      evalP9Mod 43 (4398046511104 % 43) (26373229903872 % 43) (22295572144128 % 43) (1653175484928 % 43) a.val b.val =
        evalN9Mod 43 (15015088226304 % 43) (29631280840704 % 43) (9372015415296 % 43) (10460353203 % 43) a.val b.val ->
      a.val = 0 ∧ b.val = 0) ∧
    (∀ a b : Fin 41,
      evalP9Mod 41 (91091955994975010816 % 41) (859366264352995676160 % 41) (996830302125598065216 % 41) (74479652107258140288 % 41) a.val b.val =
        evalN9Mod 41 (345737014518126845952 % 41) (1223967978751424385024 % 41) (426411488072942910720 % 41) (33227552537453169 % 41) a.val b.val ->
      a.val = 0 ∧ b.val = 0) ∧
    (∀ a b : Fin 53,
      evalP9Mod 53 (635684024152068003463168 % 53) (9911614595754203377827840 % 53) (13796448820546054236143616 % 53) (1165538797128926735376384 % 53) a.val b.val =
        evalN9Mod 53 (3111419039100732060991488 % 53) (15843575530865744267968512 % 53) (6281249468853579843502080 % 53) (27311664563487284499 % 53) a.val b.val ->
      a.val = 0 ∧ b.val = 0) ∧
    ((2 ^ 3 * 3 ^ 3 : Nat) : Int) * evalCoreBySlicesFast 12 19 1 = 4 * 89955036648 ∧
    ((2 ^ 6 * 3 ^ 6 : Nat) : Int) * evalCoreBySlicesFast 12 19 2 = 4 * (-25973182180043886600000) ∧
    ((2 ^ 6 * 3 ^ 6 : Nat) : Int) * evalCoreBySlicesFast 16 26 2 = 4 * 1532798562346060501094400000 := by decide

private theorem intDet_sub_single_col_w14 (N : Nat) (c_dst c_src : Fin N) (coef : Int)
    (M : Fin N -> Fin N -> Int) (hne : c_src ≠ c_dst) :
    intDet N M = intDet N (fun i j => if j = c_dst then M i c_dst - coef * M i c_src else M i j) := by
  have hs := intDet_sub_col_prefix_invariant N c_dst M 1 (fun _ => c_src) (fun _ => coef)
    (fun _ _ => hne)
  rw [hs]; congr 1; funext i j
  simp [colPrefixComb]

private theorem intDet_row0_scale_w14 (L : Nat) (coef : Int)
    (M : Fin (L + 1) -> Fin (L + 1) -> Int) :
    intDet (L + 1) (fun i j => if i.val = 0 then coef * M i j else M i j) =
      coef * intDet (L + 1) M := by
  let M' : Fin (L + 1) -> Fin (L + 1) -> Int := fun i j =>
    if i.val = 0 then coef * M i j else M i j
  have hsub_eq : ∀ j : Fin (L + 1), intSubMat M' j = intSubMat M j := by
    intro j; funext r c
    unfold intSubMat M'
    simp
  unfold intDet
  have hst : ∀ m : Nat, m ≤ L + 1 ->
      intSumPrefix (L + 1) (fun j =>
        (if j.val % 2 = 0 then (1 : Int) else -1) * M' ⟨0, Nat.zero_lt_succ L⟩ j *
          intDet L (intSubMat M' j)) m =
      coef * intSumPrefix (L + 1) (fun j =>
        (if j.val % 2 = 0 then (1 : Int) else -1) * M ⟨0, Nat.zero_lt_succ L⟩ j *
          intDet L (intSubMat M j)) m := by
    intro m hm; induction m with
    | zero => simp [intSumPrefix]
    | succ m' ih =>
      have hm_lt : m' < L + 1 := hm
      simp only [intSumPrefix, hm_lt, dite_true, ih (Nat.le_of_lt hm), hsub_eq ⟨m', hm_lt⟩]
      dsimp [M']
      rw [Int.mul_add]
      congr 1; ac_rfl
  exact hst (L + 1) (Nat.le_refl _)

private theorem evalPoly4_append_w14 (x0 x1 x2 x3 : Int) :
    ∀ xs ys : List Mono4,
      evalPoly4 x0 x1 x2 x3 (xs ++ ys) = evalPoly4 x0 x1 x2 x3 xs + evalPoly4 x0 x1 x2 x3 ys
  | [], _ => by simp [evalPoly4]
  | m :: ms, ys => by
    simp only [List.cons_append, evalPoly4, evalPoly4_append_w14 x0 x1 x2 x3 ms ys, Int.add_assoc]

private theorem intSumPrefix_ten (f : Fin 10 -> Int) :
    intSumPrefix 10 f 10 =
      f ⟨0, by decide⟩ + f ⟨1, by decide⟩ + f ⟨2, by decide⟩ + f ⟨3, by decide⟩ +
      f ⟨4, by decide⟩ + f ⟨5, by decide⟩ + f ⟨6, by decide⟩ + f ⟨7, by decide⟩ +
      f ⟨8, by decide⟩ + f ⟨9, by decide⟩ := by
  simp only [intSumPrefix, dite_true, Int.zero_add,
             (by decide : 0 < 10), (by decide : 1 < 10), (by decide : 2 < 10),
             (by decide : 3 < 10), (by decide : 4 < 10), (by decide : 5 < 10),
             (by decide : 6 < 10), (by decide : 7 < 10), (by decide : 8 < 10),
             (by decide : 9 < 10)]

private theorem intSumPrefix_congr_w14 (N : Nat) (f g : Fin N -> Int)
    (hfg : ∀ i : Fin N, f i = g i) :
    ∀ m : Nat, m ≤ N -> intSumPrefix N f m = intSumPrefix N g m
  | 0, _ => rfl
  | m + 1, hm => by
    have hlt : m < N := hm
    simp only [intSumPrefix, hlt, dite_true,
               intSumPrefix_congr_w14 N f g hfg m (Nat.le_of_lt hm), hfg ⟨m, hlt⟩]

private theorem intSumPrefix_mul_right_w14 (N : Nat) (f : Fin N -> Int) (c : Int) :
    ∀ m : Nat, m ≤ N -> intSumPrefix N (fun i => f i * c) m = intSumPrefix N f m * c
  | 0, _ => by simp [intSumPrefix]
  | m + 1, hm => by
    have hlt : m < N := hm
    simp only [intSumPrefix, hlt, dite_true,
               intSumPrefix_mul_right_w14 N f c m (Nat.le_of_lt hm), Int.add_mul]

private theorem intSumPrefix_mul_left_w14 (N : Nat) (c : Int) (f : Fin N -> Int) :
    ∀ m : Nat, m ≤ N -> intSumPrefix N (fun i => c * f i) m = c * intSumPrefix N f m
  | 0, _ => by simp [intSumPrefix]
  | m + 1, hm => by
    have hlt : m < N := hm
    simp only [intSumPrefix, hlt, dite_true,
               intSumPrefix_mul_left_w14 N c f m (Nat.le_of_lt hm), Int.mul_add]

private theorem intSumPrefix_add_w14 (N : Nat) (f g : Fin N -> Int) :
    ∀ m : Nat, m ≤ N ->
      intSumPrefix N (fun i => f i + g i) m = intSumPrefix N f m + intSumPrefix N g m
  | 0, _ => by simp [intSumPrefix]
  | m + 1, hm => by
    have hlt : m < N := hm
    simp only [intSumPrefix, hlt, dite_true,
               intSumPrefix_add_w14 N f g m (Nat.le_of_lt hm)]
    omega

private theorem intSumPrefix_swap10 (F : Fin 10 -> Fin 10 -> Int) :
    intSumPrefix 10 (fun k => intSumPrefix 10 (fun j => F k j) 10) 10 =
      intSumPrefix 10 (fun j => intSumPrefix 10 (fun k => F k j) 10) 10 := by
  have hst : ∀ m : Nat, m ≤ 10 ->
      intSumPrefix 10 (fun k => intSumPrefix 10 (fun j => F k j) 10) m =
        intSumPrefix 10 (fun j => intSumPrefix 10 (fun k => F k j) m) 10 := by
    intro m hm; induction m with
    | zero =>
      simp only [intSumPrefix]
      have hz : ∀ n : Nat, n ≤ 10 -> intSumPrefix 10 (fun _ => (0 : Int)) n = 0 := by
        intro n hn; induction n with
        | zero => rfl
        | succ n' ihn => simp [intSumPrefix, show n' < 10 by omega, ihn (Nat.le_of_lt hn)]
      exact (hz 10 (Nat.le_refl 10)).symm
    | succ m' ih =>
      have hlt : m' < 10 := hm
      conv => lhs; unfold intSumPrefix
      simp only [hlt, dite_true]
      rw [ih (Nat.le_of_lt hm), ← intSumPrefix_add_w14 10 _ _ 10 (Nat.le_refl 10)]
      congr 1; funext j
      simp [intSumPrefix, hlt]
  exact hst 10 (Nat.le_refl 10)

private theorem evalPoly4_t3u3CorePoly_eq_sum10 (x0 x1 : Int) (u : Nat) :
    evalPoly4 x0 x1 ((2 ^ u : Nat) : Int) ((3 ^ u : Nat) : Int) t3u3CorePoly =
      intSumPrefix 10 (fun k =>
        intPowNat x0 (9 - k.val) * intPowNat x1 k.val * evalCDSInt u (t3u3CoreWSlice k)) 10 := by
  have hintPow_ev : ∀ (a d : Nat), intPowNat (a : Int) d = ((a ^ d : Nat) : Int) := by
    intro a d; induction d with
    | zero => rfl
    | succ d' ih => simp [intPowNat, ih, Nat.pow_succ, Int.natCast_mul, Int.mul_comm]
  have hslice : ∀ (k : Nat) (sl : List CDS),
      evalPoly4 x0 x1 ((2 ^ u : Nat) : Int) ((3 ^ u : Nat) : Int) (cdsToPoly4 k sl) =
        intPowNat x0 (9 - k) * intPowNat x1 k * evalCDSInt u sl := by
    intro k sl; induction sl with
    | nil => simp [cdsToPoly4, evalPoly4, evalCDSInt, evalCDSPos, evalCDSNeg]
    | cons x tl ih =>
      have hpq : ∀ c d : Nat,
          intPowNat ((2 ^ u : Nat) : Int) c * intPowNat ((3 ^ u : Nat) : Int) d =
            (((2 ^ c * 3 ^ d) ^ u : Nat) : Int) := by
        intro c d
        rw [hintPow_ev, hintPow_ev, ← Int.natCast_mul]
        apply congrArg Nat.cast
        rw [pow_pow_eq_mul_w5 2 u c, pow_pow_eq_mul_w5 3 u d,
            Nat.mul_comm u c, Nat.mul_comm u d,
            ← pow_pow_eq_mul_w5 2 c u, ← pow_pow_eq_mul_w5 3 d u,
            ← mul_pow_w14 (2 ^ c) (3 ^ d) u]
      cases x with
      | p c d v =>
        simp only [cdsToPoly4, evalPoly4, evalMono4, ih, evalCDSInt, evalCDSPos, evalCDSNeg,
                   Int.natCast_add, Int.natCast_mul]
        have h1 : (v : Int) * (intPowNat x0 (9 - k) * (intPowNat x1 k *
            (intPowNat ((2 ^ u : Nat) : Int) c * intPowNat ((3 ^ u : Nat) : Int) d))) =
            intPowNat x0 (9 - k) * intPowNat x1 k * ((v : Int) * (((2 ^ c * 3 ^ d) ^ u : Nat) : Int)) := by
          rw [hpq c d]; ac_rfl
        rw [h1]
        let X := intPowNat x0 (9 - k) * intPowNat x1 k
        change X * _ + X * (_ - _) = X * ((_ + _) - _)
        rw [← Int.mul_add]; congr 1; omega
      | n c d v =>
        simp only [cdsToPoly4, evalPoly4, evalMono4, ih, evalCDSInt, evalCDSPos, evalCDSNeg,
                   Int.natCast_add, Int.natCast_mul]
        have h1 : -(v : Int) * (intPowNat x0 (9 - k) * (intPowNat x1 k *
            (intPowNat ((2 ^ u : Nat) : Int) c * intPowNat ((3 ^ u : Nat) : Int) d))) =
            intPowNat x0 (9 - k) * intPowNat x1 k * (-(v : Int) * (((2 ^ c * 3 ^ d) ^ u : Nat) : Int)) := by
          rw [hpq c d]; simp only [Int.neg_mul, Int.mul_neg]
          congr 1; ac_rfl
        rw [h1]
        let X := intPowNat x0 (9 - k) * intPowNat x1 k
        change X * (-(v : Int) * _) + X * (_ - _) = X * (_ - (_ + _))
        rw [← Int.mul_add]; congr 1
        simp only [Int.neg_mul]; omega
  unfold t3u3CorePoly
  repeat rw [evalPoly4_append_w14]
  rw [hslice 9 _, hslice 8 _, hslice 7 _, hslice 6 _, hslice 5 _,
      hslice 4 _, hslice 3 _, hslice 2 _, hslice 1 _, hslice 0 _]
  let f : Fin 10 -> Int := fun k =>
    intPowNat x0 (9 - k.val) * intPowNat x1 k.val * evalCDSInt u (t3u3CoreWSlice k)
  change f ⟨9, by decide⟩ + f ⟨8, by decide⟩ + f ⟨7, by decide⟩ + f ⟨6, by decide⟩ +
    f ⟨5, by decide⟩ + f ⟨4, by decide⟩ + f ⟨3, by decide⟩ + f ⟨2, by decide⟩ +
      f ⟨1, by decide⟩ + f ⟨0, by decide⟩ = intSumPrefix 10 f 10
  rw [intSumPrefix_ten]
  omega

private theorem det9_elim_A9_abstract (A9 : Fin 9 -> Fin 9 -> Int)
    (hc0 : ∀ r : Fin 9, A9 r ⟨0, by decide⟩ = 1)
    (hr0_1 : A9 ⟨0, by decide⟩ ⟨1, by decide⟩ = 0)
    (hr0_2 : A9 ⟨0, by decide⟩ ⟨2, by decide⟩ = 0)
    (hr0_3 : A9 ⟨0, by decide⟩ ⟨3, by decide⟩ = 1)
    (hr0_4 : A9 ⟨0, by decide⟩ ⟨4, by decide⟩ = 0)
    (hr0_5 : A9 ⟨0, by decide⟩ ⟨5, by decide⟩ = 0)
    (hr0_6 : A9 ⟨0, by decide⟩ ⟨6, by decide⟩ = 1)
    (hr0_7 : A9 ⟨0, by decide⟩ ⟨7, by decide⟩ = 0)
    (hr0_8 : A9 ⟨0, by decide⟩ ⟨8, by decide⟩ = 0) :
    intDet 9 A9 = intDet 8 (fun i j =>
      let r9 : Fin 9 := ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
      let c9 : Fin 9 := ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
      if j.val = 2 || j.val = 5 then A9 r9 c9 - 1 else A9 r9 c9) := by
  let A9_1 : Fin 9 -> Fin 9 -> Int := fun i j =>
    if j = ⟨3, by decide⟩ then A9 i ⟨3, by decide⟩ - 1 * A9 i ⟨0, by decide⟩ else A9 i j
  let A9_2 : Fin 9 -> Fin 9 -> Int := fun i j =>
    if j = ⟨6, by decide⟩ then A9_1 i ⟨6, by decide⟩ - 1 * A9_1 i ⟨0, by decide⟩ else A9_1 i j
  have h1 := intDet_sub_single_col_w14 9 ⟨3, by decide⟩ ⟨0, by decide⟩ 1 A9 (by decide)
  change intDet 9 A9 = intDet 9 A9_1 at h1
  have h2 := intDet_sub_single_col_w14 9 ⟨6, by decide⟩ ⟨0, by decide⟩ 1 A9_1 (by decide)
  change intDet 9 A9_1 = intDet 9 A9_2 at h2
  rw [h1, h2, intDet_succ_single_row0 8 A9_2 ⟨0, by decide⟩ (fun j hj => by
        rcases (by have := j.isLt; omega :
          j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 ∨ j.val = 4 ∨
          j.val = 5 ∨ j.val = 6 ∨ j.val = 7 ∨ j.val = 8) with
          h | h | h | h | h | h | h | h | h
        · exact False.elim (hj (Fin.ext h))
        · have hje : j = ⟨1, by decide⟩ := Fin.ext h; subst hje; exact hr0_1
        · have hje : j = ⟨2, by decide⟩ := Fin.ext h; subst hje; exact hr0_2
        · have hje : j = ⟨3, by decide⟩ := Fin.ext h; subst hje
          change A9 ⟨0, by decide⟩ ⟨3, by decide⟩ - 1 * A9 ⟨0, by decide⟩ ⟨0, by decide⟩ = 0
          rw [hr0_3, hc0]; rfl
        · have hje : j = ⟨4, by decide⟩ := Fin.ext h; subst hje; exact hr0_4
        · have hje : j = ⟨5, by decide⟩ := Fin.ext h; subst hje; exact hr0_5
        · have hje : j = ⟨6, by decide⟩ := Fin.ext h; subst hje
          change A9 ⟨0, by decide⟩ ⟨6, by decide⟩ - 1 * A9 ⟨0, by decide⟩ ⟨0, by decide⟩ = 0
          rw [hr0_6, hc0]; rfl
        · have hje : j = ⟨7, by decide⟩ := Fin.ext h; subst hje; exact hr0_7
        · have hje : j = ⟨8, by decide⟩ := Fin.ext h; subst hje; exact hr0_8)]
  have h00 : A9_2 ⟨0, by decide⟩ ⟨0, by decide⟩ = 1 := hc0 _
  rw [h00]
  simp only [(by decide : 0 % 2 = 0), ite_true, Int.one_mul]
  congr 1; funext i j
  rcases (by have := j.isLt; omega :
    j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 ∨ j.val = 4 ∨
    j.val = 5 ∨ j.val = 6 ∨ j.val = 7) with
    h | h | h | h | h | h | h | h
  · have hje : j = ⟨0, by decide⟩ := Fin.ext h; subst hje; rfl
  · have hje : j = ⟨1, by decide⟩ := Fin.ext h; subst hje; rfl
  · have hje : j = ⟨2, by decide⟩ := Fin.ext h; subst hje
    change A9 ⟨i.val + 1, _⟩ ⟨3, by decide⟩ - 1 * A9 ⟨i.val + 1, _⟩ ⟨0, by decide⟩ =
      A9 ⟨i.val + 1, _⟩ ⟨3, by decide⟩ - 1
    rw [hc0, Int.mul_one]
  · have hje : j = ⟨3, by decide⟩ := Fin.ext h; subst hje; rfl
  · have hje : j = ⟨4, by decide⟩ := Fin.ext h; subst hje; rfl
  · have hje : j = ⟨5, by decide⟩ := Fin.ext h; subst hje
    change A9 ⟨i.val + 1, _⟩ ⟨6, by decide⟩ - 1 * A9 ⟨i.val + 1, _⟩ ⟨0, by decide⟩ =
      A9 ⟨i.val + 1, _⟩ ⟨6, by decide⟩ - 1
    rw [hc0, Int.mul_one]
  · have hje : j = ⟨6, by decide⟩ := Fin.ext h; subst hje; rfl
  · have hje : j = ⟨7, by decide⟩ := Fin.ext h; subst hje; rfl

private theorem t3u3_det_A9_eq_B8 (w_i k_i p_i q_i : Int) :
    intDet 9 (fun i j => evalExpr4 w_i k_i p_i q_i (t3u3GenA9Expr i j)) =
      intDet 8 (fun i j => evalExpr4 w_i k_i p_i q_i (t3u3GenB8Expr i j)) := by
  rw [det9_elim_A9_abstract (fun i j => evalExpr4 w_i k_i p_i q_i (t3u3GenA9Expr i j))
    (fun _ => rfl)
    (expr4_eq_of_norm_sub_nil _ (.const 0) (by decide) w_i k_i p_i q_i)
    (expr4_eq_of_norm_sub_nil _ (.const 0) (by decide) w_i k_i p_i q_i)
    (expr4_eq_of_norm_sub_nil _ (.const 1) (by decide) w_i k_i p_i q_i)
    (expr4_eq_of_norm_sub_nil _ (.const 0) (by decide) w_i k_i p_i q_i)
    (expr4_eq_of_norm_sub_nil _ (.const 0) (by decide) w_i k_i p_i q_i)
    (expr4_eq_of_norm_sub_nil _ (.const 1) (by decide) w_i k_i p_i q_i)
    (expr4_eq_of_norm_sub_nil _ (.const 0) (by decide) w_i k_i p_i q_i)
    (expr4_eq_of_norm_sub_nil _ (.const 0) (by decide) w_i k_i p_i q_i)]
  congr 1; funext i j
  unfold t3u3GenB8Expr
  dsimp only
  cases hb : (j.val = 2 || j.val = 5)
  · simp only [Bool.false_eq_true, ite_false]
  · simp only [ite_true, evalExpr4]

private theorem det8_B8_to_C8_abstract (p_i : Int) (B8 : Fin 8 -> Fin 8 -> Int) :
    intDet 8 B8 = intDet 8 (fun i j =>
      match j.val with
      | 0 => B8 i ⟨0, by decide⟩
      | 1 => B8 i ⟨1, by decide⟩
      | 2 => B8 i ⟨2, by decide⟩
      | 3 => B8 i ⟨3, by decide⟩ - p_i * B8 i ⟨0, by decide⟩
      | 4 => B8 i ⟨4, by decide⟩ - p_i * B8 i ⟨1, by decide⟩
      | 5 => B8 i ⟨5, by decide⟩ - (p_i + 1) * B8 i ⟨2, by decide⟩
      | 6 => B8 i ⟨6, by decide⟩ - (p_i * p_i) * B8 i ⟨0, by decide⟩
      | _ => B8 i ⟨7, by decide⟩ - (p_i * p_i) * B8 i ⟨1, by decide⟩) := by
  let m1 : Fin 8 -> Fin 8 -> Int := fun i j =>
    if j = ⟨3, by decide⟩ then B8 i ⟨3, by decide⟩ - p_i * B8 i ⟨0, by decide⟩ else B8 i j
  let m2 : Fin 8 -> Fin 8 -> Int := fun i j =>
    if j = ⟨4, by decide⟩ then m1 i ⟨4, by decide⟩ - p_i * m1 i ⟨1, by decide⟩ else m1 i j
  let m3 : Fin 8 -> Fin 8 -> Int := fun i j =>
    if j = ⟨5, by decide⟩ then m2 i ⟨5, by decide⟩ - (p_i + 1) * m2 i ⟨2, by decide⟩ else m2 i j
  let m4 : Fin 8 -> Fin 8 -> Int := fun i j =>
    if j = ⟨6, by decide⟩ then m3 i ⟨6, by decide⟩ - (p_i * p_i) * m3 i ⟨0, by decide⟩ else m3 i j
  let m5 : Fin 8 -> Fin 8 -> Int := fun i j =>
    if j = ⟨7, by decide⟩ then m4 i ⟨7, by decide⟩ - (p_i * p_i) * m4 i ⟨1, by decide⟩ else m4 i j
  have s1 := intDet_sub_single_col_w14 8 ⟨3, by decide⟩ ⟨0, by decide⟩ p_i B8 (by decide)
  change intDet 8 B8 = intDet 8 m1 at s1
  have s2 := intDet_sub_single_col_w14 8 ⟨4, by decide⟩ ⟨1, by decide⟩ p_i m1 (by decide)
  change intDet 8 m1 = intDet 8 m2 at s2
  have s3 := intDet_sub_single_col_w14 8 ⟨5, by decide⟩ ⟨2, by decide⟩ (p_i + 1) m2 (by decide)
  change intDet 8 m2 = intDet 8 m3 at s3
  have s4 := intDet_sub_single_col_w14 8 ⟨6, by decide⟩ ⟨0, by decide⟩ (p_i * p_i) m3 (by decide)
  change intDet 8 m3 = intDet 8 m4 at s4
  have s5 := intDet_sub_single_col_w14 8 ⟨7, by decide⟩ ⟨1, by decide⟩ (p_i * p_i) m4 (by decide)
  change intDet 8 m4 = intDet 8 m5 at s5
  rw [s1, s2, s3, s4, s5]
  congr 1; funext i j
  rcases (by have := j.isLt; omega :
    j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 ∨ j.val = 4 ∨
    j.val = 5 ∨ j.val = 6 ∨ j.val = 7) with
    h | h | h | h | h | h | h | h
  · have hje : j = ⟨0, by decide⟩ := Fin.ext h; subst hje; rfl
  · have hje : j = ⟨1, by decide⟩ := Fin.ext h; subst hje; rfl
  · have hje : j = ⟨2, by decide⟩ := Fin.ext h; subst hje; rfl
  · have hje : j = ⟨3, by decide⟩ := Fin.ext h; subst hje; rfl
  · have hje : j = ⟨4, by decide⟩ := Fin.ext h; subst hje; rfl
  · have hje : j = ⟨5, by decide⟩ := Fin.ext h; subst hje; rfl
  · have hje : j = ⟨6, by decide⟩ := Fin.ext h; subst hje; rfl
  · have hje : j = ⟨7, by decide⟩ := Fin.ext h; subst hje; rfl

private theorem t3u3_det_B8_eq_C8 (w_i k_i p_i q_i : Int) :
    intDet 8 (fun i j => evalExpr4 w_i k_i p_i q_i (t3u3GenB8Expr i j)) =
      intDet 8 (fun i j => evalExpr4 w_i k_i p_i q_i (t3u3GenC8Expr i j)) := by
  rw [det8_B8_to_C8_abstract p_i (fun i j => evalExpr4 w_i k_i p_i q_i (t3u3GenB8Expr i j))]
  congr 1; funext i j
  rcases (by have := j.isLt; omega :
    j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 ∨ j.val = 4 ∨
    j.val = 5 ∨ j.val = 6 ∨ j.val = 7) with
    h | h | h | h | h | h | h | h
  · have hje : j = ⟨0, by decide⟩ := Fin.ext h; subst hje; rfl
  · have hje : j = ⟨1, by decide⟩ := Fin.ext h; subst hje; rfl
  · have hje : j = ⟨2, by decide⟩ := Fin.ext h; subst hje; rfl
  · have hje : j = ⟨3, by decide⟩ := Fin.ext h; subst hje; rfl
  · have hje : j = ⟨4, by decide⟩ := Fin.ext h; subst hje; rfl
  · have hje : j = ⟨5, by decide⟩ := Fin.ext h; subst hje; rfl
  · have hje : j = ⟨6, by decide⟩ := Fin.ext h; subst hje; rfl
  · have hje : j = ⟨7, by decide⟩ := Fin.ext h; subst hje; rfl

private theorem det8_C8_to_C7_abstract (w_i p_i : Int) (hpm1 : p_i - 1 ≠ 0)
    (C8 : Fin 8 -> Fin 8 -> Int) (C7 : Fin 7 -> Fin 7 -> Int)
    (hr0_0 : C8 ⟨0, by decide⟩ ⟨0, by decide⟩ = w_i)
    (hr0_1 : C8 ⟨0, by decide⟩ ⟨1, by decide⟩ = w_i * (w_i - 1))
    (hr0_2 : C8 ⟨0, by decide⟩ ⟨2, by decide⟩ = p_i - 1)
    (hr0_3 : C8 ⟨0, by decide⟩ ⟨3, by decide⟩ = 0)
    (hr0_4 : C8 ⟨0, by decide⟩ ⟨4, by decide⟩ = 0)
    (hr0_5 : C8 ⟨0, by decide⟩ ⟨5, by decide⟩ = 0)
    (hr0_6 : C8 ⟨0, by decide⟩ ⟨6, by decide⟩ = 0)
    (hr0_7 : C8 ⟨0, by decide⟩ ⟨7, by decide⟩ = 0)
    (hsub0 : ∀ j : Fin 7,
      (p_i - 1) * C7 ⟨0, by decide⟩ j =
        match j.val with
        | 0 => (p_i - 1) * C8 ⟨1, by decide⟩ ⟨0, by decide⟩ - w_i * C8 ⟨1, by decide⟩ ⟨2, by decide⟩
        | 1 => (p_i - 1) * C8 ⟨1, by decide⟩ ⟨1, by decide⟩ - (w_i * (w_i - 1)) * C8 ⟨1, by decide⟩ ⟨2, by decide⟩
        | 2 => C8 ⟨1, by decide⟩ ⟨3, by decide⟩
        | 3 => C8 ⟨1, by decide⟩ ⟨4, by decide⟩
        | 4 => C8 ⟨1, by decide⟩ ⟨5, by decide⟩
        | 5 => C8 ⟨1, by decide⟩ ⟨6, by decide⟩
        | _ => C8 ⟨1, by decide⟩ ⟨7, by decide⟩)
    (hsub_gt : ∀ (i : Fin 7) (j : Fin 7), i.val ≠ 0 ->
      C7 i j =
        let r8 : Fin 8 := ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
        match j.val with
        | 0 => (p_i - 1) * C8 r8 ⟨0, by decide⟩ - w_i * C8 r8 ⟨2, by decide⟩
        | 1 => (p_i - 1) * C8 r8 ⟨1, by decide⟩ - (w_i * (w_i - 1)) * C8 r8 ⟨2, by decide⟩
        | 2 => C8 r8 ⟨3, by decide⟩
        | 3 => C8 r8 ⟨4, by decide⟩
        | 4 => C8 r8 ⟨5, by decide⟩
        | 5 => C8 r8 ⟨6, by decide⟩
        | _ => C8 r8 ⟨7, by decide⟩) :
    intDet 8 C8 = intDet 7 C7 := by
  let pm1 : Int := p_i - 1
  let wb2 : Int := w_i * (w_i - 1)
  let s1 : Fin 8 -> Fin 8 -> Int := fun i j => if j = ⟨0, by decide⟩ then pm1 * C8 i ⟨0, by decide⟩ else C8 i j
  let s2 : Fin 8 -> Fin 8 -> Int := fun i j => if j = ⟨1, by decide⟩ then pm1 * s1 i ⟨1, by decide⟩ else s1 i j
  let s3 : Fin 8 -> Fin 8 -> Int := fun i j =>
    if j = ⟨0, by decide⟩ then s2 i ⟨0, by decide⟩ - w_i * s2 i ⟨2, by decide⟩ else s2 i j
  let s4 : Fin 8 -> Fin 8 -> Int := fun i j =>
    if j = ⟨1, by decide⟩ then s3 i ⟨1, by decide⟩ - wb2 * s3 i ⟨2, by decide⟩ else s3 i j
  have hs_scale : pm1 * (pm1 * intDet 8 C8) = intDet 8 s4 := by
    rw [← intDet_col_scale pm1 8 ⟨0, by decide⟩ C8,
        ← intDet_col_scale pm1 8 ⟨1, by decide⟩ s1,
        intDet_sub_single_col_w14 8 ⟨0, by decide⟩ ⟨2, by decide⟩ w_i s2 (by decide),
        intDet_sub_single_col_w14 8 ⟨1, by decide⟩ ⟨2, by decide⟩ wb2 s3 (by decide)]
  have hs4_piv : intDet 8 s4 = pm1 * intDet 7 (intSubMat s4 ⟨2, by decide⟩) := by
    rw [intDet_succ_single_row0 7 s4 ⟨2, by decide⟩ (fun j hj => by
      rcases (by have := j.isLt; omega :
        j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 ∨ j.val = 4 ∨
        j.val = 5 ∨ j.val = 6 ∨ j.val = 7) with
        h | h | h | h | h | h | h | h
      · have hje : j = ⟨0, by decide⟩ := Fin.ext h; subst hje
        change pm1 * C8 ⟨0, by decide⟩ ⟨0, by decide⟩ - w_i * C8 ⟨0, by decide⟩ ⟨2, by decide⟩ = 0
        rw [hr0_0, hr0_2, Int.mul_comm, Int.sub_self]
      · have hje : j = ⟨1, by decide⟩ := Fin.ext h; subst hje
        change (p_i - 1) * C8 ⟨0, by decide⟩ ⟨1, by decide⟩ -
          (w_i * (w_i - 1)) * C8 ⟨0, by decide⟩ ⟨2, by decide⟩ = 0
        rw [hr0_1, hr0_2, Int.mul_comm (p_i - 1), Int.sub_self]
      · exact False.elim (hj (Fin.ext h))
      · have hje : j = ⟨3, by decide⟩ := Fin.ext h; subst hje; exact hr0_3
      · have hje : j = ⟨4, by decide⟩ := Fin.ext h; subst hje; exact hr0_4
      · have hje : j = ⟨5, by decide⟩ := Fin.ext h; subst hje; exact hr0_5
      · have hje : j = ⟨6, by decide⟩ := Fin.ext h; subst hje; exact hr0_6
      · have hje : j = ⟨7, by decide⟩ := Fin.ext h; subst hje; exact hr0_7)]
    have h02 : s4 ⟨0, by decide⟩ ⟨2, by decide⟩ = pm1 := hr0_2
    simp only [(by decide : 2 % 2 = 0), ite_true, Int.one_mul, h02]
  have hsub_row0 : intSubMat s4 ⟨2, by decide⟩ =
      (fun i j : Fin 7 => if i.val = 0 then pm1 * C7 i j else C7 i j) := by
    funext i j
    by_cases hi0 : i.val = 0
    · have hie : i = ⟨0, by decide⟩ := Fin.ext hi0; subst hie
      simp only [ite_true]
      have hs0 := hsub0 j
      rcases (by have := j.isLt; omega :
        j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 ∨ j.val = 4 ∨ j.val = 5 ∨ j.val = 6) with
        h | h | h | h | h | h | h
      · have hje : j = ⟨0, by decide⟩ := Fin.ext h; subst hje; exact hs0.symm
      · have hje : j = ⟨1, by decide⟩ := Fin.ext h; subst hje; exact hs0.symm
      · have hje : j = ⟨2, by decide⟩ := Fin.ext h; subst hje; exact hs0.symm
      · have hje : j = ⟨3, by decide⟩ := Fin.ext h; subst hje; exact hs0.symm
      · have hje : j = ⟨4, by decide⟩ := Fin.ext h; subst hje; exact hs0.symm
      · have hje : j = ⟨5, by decide⟩ := Fin.ext h; subst hje; exact hs0.symm
      · have hje : j = ⟨6, by decide⟩ := Fin.ext h; subst hje; exact hs0.symm
    · simp only [hi0, ite_false]
      have hgt := hsub_gt i j hi0
      rcases (by have := j.isLt; omega :
        j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 ∨ j.val = 4 ∨ j.val = 5 ∨ j.val = 6) with
        h | h | h | h | h | h | h
      · have hje : j = ⟨0, by decide⟩ := Fin.ext h; subst hje; exact hgt.symm
      · have hje : j = ⟨1, by decide⟩ := Fin.ext h; subst hje; exact hgt.symm
      · have hje : j = ⟨2, by decide⟩ := Fin.ext h; subst hje; exact hgt.symm
      · have hje : j = ⟨3, by decide⟩ := Fin.ext h; subst hje; exact hgt.symm
      · have hje : j = ⟨4, by decide⟩ := Fin.ext h; subst hje; exact hgt.symm
      · have hje : j = ⟨5, by decide⟩ := Fin.ext h; subst hje; exact hgt.symm
      · have hje : j = ⟨6, by decide⟩ := Fin.ext h; subst hje; exact hgt.symm
  rw [hsub_row0, intDet_row0_scale_w14 6 pm1 C7] at hs4_piv
  rw [hs4_piv] at hs_scale
  exact Int.eq_of_mul_eq_mul_left hpm1 (Int.eq_of_mul_eq_mul_left hpm1 hs_scale)

private theorem t3u3_det_C8_eq_C7 (w_i k_i p_i q_i : Int) (hpm1 : p_i - 1 ≠ 0) :
    intDet 8 (fun i j => evalExpr4 w_i k_i p_i q_i (t3u3GenC8Expr i j)) =
      intDet 7 (fun i j => evalExpr4 w_i k_i p_i q_i (t3u3GenC7Expr i j)) := by
  refine det8_C8_to_C7_abstract w_i p_i hpm1
    (fun i j => evalExpr4 w_i k_i p_i q_i (t3u3GenC8Expr i j))
    (fun i j => evalExpr4 w_i k_i p_i q_i (t3u3GenC7Expr i j))
    (expr4_eq_of_norm_sub_nil _ .v0 (by decide) w_i k_i p_i q_i)
    (expr4_eq_of_norm_sub_nil _ (.mul .v0 (.sub .v0 (.const 1))) (by decide) w_i k_i p_i q_i)
    (expr4_eq_of_norm_sub_nil _ (.sub .v2 (.const 1)) (by decide) w_i k_i p_i q_i)
    (expr4_eq_of_norm_sub_nil _ (.const 0) (by decide) w_i k_i p_i q_i)
    (expr4_eq_of_norm_sub_nil _ (.const 0) (by decide) w_i k_i p_i q_i)
    (expr4_eq_of_norm_sub_nil _ (.const 0) (by decide) w_i k_i p_i q_i)
    (expr4_eq_of_norm_sub_nil _ (.const 0) (by decide) w_i k_i p_i q_i)
    (expr4_eq_of_norm_sub_nil _ (.const 0) (by decide) w_i k_i p_i q_i)
    ?_ ?_
  · intro j
    have hev := expr4_eq_of_norm_sub_nil _ _ (t3u3_g2_and_row20_certs.2.2 j) w_i k_i p_i q_i
    rcases (by have := j.isLt; omega :
      j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 ∨ j.val = 4 ∨ j.val = 5 ∨ j.val = 6) with
      h | h | h | h | h | h | h
    · have hje : j = ⟨0, by decide⟩ := Fin.ext h; subst hje; exact hev
    · have hje : j = ⟨1, by decide⟩ := Fin.ext h; subst hje; exact hev
    · have hje : j = ⟨2, by decide⟩ := Fin.ext h; subst hje; exact hev
    · have hje : j = ⟨3, by decide⟩ := Fin.ext h; subst hje; exact hev
    · have hje : j = ⟨4, by decide⟩ := Fin.ext h; subst hje; exact hev
    · have hje : j = ⟨5, by decide⟩ := Fin.ext h; subst hje; exact hev
    · have hje : j = ⟨6, by decide⟩ := Fin.ext h; subst hje; exact hev
  · intro i j hi0
    unfold t3u3GenC7Expr
    simp only [hi0, ite_false]
    rcases (by have := j.isLt; omega :
      j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 ∨ j.val = 4 ∨ j.val = 5 ∨ j.val = 6) with
      h | h | h | h | h | h | h
    · have hje : j = ⟨0, by decide⟩ := Fin.ext h; subst hje; rfl
    · have hje : j = ⟨1, by decide⟩ := Fin.ext h; subst hje; rfl
    · have hje : j = ⟨2, by decide⟩ := Fin.ext h; subst hje; rfl
    · have hje : j = ⟨3, by decide⟩ := Fin.ext h; subst hje; rfl
    · have hje : j = ⟨4, by decide⟩ := Fin.ext h; subst hje; rfl
    · have hje : j = ⟨5, by decide⟩ := Fin.ext h; subst hje; rfl
    · have hje : j = ⟨6, by decide⟩ := Fin.ext h; subst hje; rfl

private theorem det7_C7_to_D7_abstract (w_i p_i : Int) (C7 : Fin 7 -> Fin 7 -> Int) :
    intDet 7 C7 = intDet 7 (fun i j =>
      let twoWm1 : Int := 2 * w_i - 1
      let p2pp : Int := p_i * p_i + p_i
      match j.val with
      | 0 => C7 i ⟨0, by decide⟩
      | 1 => C7 i ⟨1, by decide⟩
      | 2 => C7 i ⟨2, by decide⟩
      | 3 => C7 i ⟨3, by decide⟩ - twoWm1 * C7 i ⟨2, by decide⟩
      | 4 => C7 i ⟨4, by decide⟩
      | 5 => C7 i ⟨5, by decide⟩ - p2pp * C7 i ⟨2, by decide⟩
      | _ => C7 i ⟨6, by decide⟩ - (twoWm1 * p2pp) * C7 i ⟨2, by decide⟩) := by
  let twoWm1 : Int := 2 * w_i - 1
  let p2pp : Int := p_i * p_i + p_i
  let d1 : Fin 7 -> Fin 7 -> Int := fun i j =>
    if j = ⟨3, by decide⟩ then C7 i ⟨3, by decide⟩ - twoWm1 * C7 i ⟨2, by decide⟩ else C7 i j
  let d2 : Fin 7 -> Fin 7 -> Int := fun i j =>
    if j = ⟨5, by decide⟩ then d1 i ⟨5, by decide⟩ - p2pp * d1 i ⟨2, by decide⟩ else d1 i j
  let d3 : Fin 7 -> Fin 7 -> Int := fun i j =>
    if j = ⟨6, by decide⟩ then d2 i ⟨6, by decide⟩ - (twoWm1 * p2pp) * d2 i ⟨2, by decide⟩ else d2 i j
  have s1 := intDet_sub_single_col_w14 7 ⟨3, by decide⟩ ⟨2, by decide⟩ twoWm1 C7 (by decide)
  change intDet 7 C7 = intDet 7 d1 at s1
  have s2 := intDet_sub_single_col_w14 7 ⟨5, by decide⟩ ⟨2, by decide⟩ p2pp d1 (by decide)
  change intDet 7 d1 = intDet 7 d2 at s2
  have s3 := intDet_sub_single_col_w14 7 ⟨6, by decide⟩ ⟨2, by decide⟩ (twoWm1 * p2pp) d2 (by decide)
  change intDet 7 d2 = intDet 7 d3 at s3
  rw [s1, s2, s3]
  congr 1; funext i j
  rcases (by have := j.isLt; omega :
    j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 ∨ j.val = 4 ∨ j.val = 5 ∨ j.val = 6) with
    h | h | h | h | h | h | h
  · have hje : j = ⟨0, by decide⟩ := Fin.ext h; subst hje; rfl
  · have hje : j = ⟨1, by decide⟩ := Fin.ext h; subst hje; rfl
  · have hje : j = ⟨2, by decide⟩ := Fin.ext h; subst hje; rfl
  · have hje : j = ⟨3, by decide⟩ := Fin.ext h; subst hje; rfl
  · have hje : j = ⟨4, by decide⟩ := Fin.ext h; subst hje; rfl
  · have hje : j = ⟨5, by decide⟩ := Fin.ext h; subst hje; rfl
  · have hje : j = ⟨6, by decide⟩ := Fin.ext h; subst hje; rfl

private theorem t3u3_det_C7_eq_D7 (w_i k_i p_i q_i : Int) :
    intDet 7 (fun i j => evalExpr4 w_i k_i p_i q_i (t3u3GenC7Expr i j)) =
      intDet 7 (fun i j => evalExpr4 w_i k_i p_i q_i (t3u3GenD7Expr i j)) := by
  rw [det7_C7_to_D7_abstract w_i p_i (fun i j => evalExpr4 w_i k_i p_i q_i (t3u3GenC7Expr i j))]
  congr 1; funext i j
  rcases (by have := j.isLt; omega :
    j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 ∨ j.val = 4 ∨ j.val = 5 ∨ j.val = 6) with
    h | h | h | h | h | h | h
  · have hje : j = ⟨0, by decide⟩ := Fin.ext h; subst hje; rfl
  · have hje : j = ⟨1, by decide⟩ := Fin.ext h; subst hje; rfl
  · have hje : j = ⟨2, by decide⟩ := Fin.ext h; subst hje; rfl
  · have hje : j = ⟨3, by decide⟩ := Fin.ext h; subst hje; rfl
  · have hje : j = ⟨4, by decide⟩ := Fin.ext h; subst hje; rfl
  · have hje : j = ⟨5, by decide⟩ := Fin.ext h; subst hje; rfl
  · have hje : j = ⟨6, by decide⟩ := Fin.ext h; subst hje; rfl

private theorem det7_D7_to_E6_abstract (w_i p_i : Int) (hnz : (2 : Int) * w_i * p_i ≠ 0)
    (D7 : Fin 7 -> Fin 7 -> Int)
    (hr0_0 : D7 ⟨0, by decide⟩ ⟨0, by decide⟩ = (1 - p_i) * w_i)
    (hr0_1 : D7 ⟨0, by decide⟩ ⟨1, by decide⟩ = w_i * ((3 * w_i + p_i) - (p_i * w_i + 1)))
    (hr0_2 : D7 ⟨0, by decide⟩ ⟨2, by decide⟩ = (2 : Int) * w_i * p_i)
    (hr0_3 : D7 ⟨0, by decide⟩ ⟨3, by decide⟩ = 0)
    (hr0_4 : D7 ⟨0, by decide⟩ ⟨4, by decide⟩ = p_i * (p_i * p_i - 1))
    (hr0_5 : D7 ⟨0, by decide⟩ ⟨5, by decide⟩ = 0)
    (hr0_6 : D7 ⟨0, by decide⟩ ⟨6, by decide⟩ = 0) :
    ((4 : Int) * p_i) * intDet 7 D7 = intDet 6 (fun i j =>
      let r7 : Fin 7 := ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
      match j.val with
      | 0 => ((2 : Int) * p_i) * D7 r7 ⟨0, by decide⟩ - (1 - p_i) * D7 r7 ⟨2, by decide⟩
      | 1 => ((2 : Int) * p_i) * D7 r7 ⟨1, by decide⟩ - ((3 * w_i + p_i) - (p_i * w_i + 1)) * D7 r7 ⟨2, by decide⟩
      | 2 => D7 r7 ⟨3, by decide⟩
      | 3 => ((2 : Int) * w_i) * D7 r7 ⟨4, by decide⟩ - (p_i * p_i - 1) * D7 r7 ⟨2, by decide⟩
      | 4 => D7 r7 ⟨5, by decide⟩
      | _ => D7 r7 ⟨6, by decide⟩) := by
  let twoP : Int := (2 : Int) * p_i
  let twoW : Int := (2 : Int) * w_i
  let f0 : Int := 1 - p_i
  let f1 : Int := (3 * w_i + p_i) - (p_i * w_i + 1)
  let f4 : Int := p_i * p_i - 1
  let e1 : Fin 7 -> Fin 7 -> Int := fun i j => if j = ⟨0, by decide⟩ then twoP * D7 i ⟨0, by decide⟩ else D7 i j
  let e2 : Fin 7 -> Fin 7 -> Int := fun i j => if j = ⟨1, by decide⟩ then twoP * e1 i ⟨1, by decide⟩ else e1 i j
  let e3 : Fin 7 -> Fin 7 -> Int := fun i j => if j = ⟨4, by decide⟩ then twoW * e2 i ⟨4, by decide⟩ else e2 i j
  let e4 : Fin 7 -> Fin 7 -> Int := fun i j =>
    if j = ⟨0, by decide⟩ then e3 i ⟨0, by decide⟩ - f0 * e3 i ⟨2, by decide⟩ else e3 i j
  let e5 : Fin 7 -> Fin 7 -> Int := fun i j =>
    if j = ⟨1, by decide⟩ then e4 i ⟨1, by decide⟩ - f1 * e4 i ⟨2, by decide⟩ else e4 i j
  let e6 : Fin 7 -> Fin 7 -> Int := fun i j =>
    if j = ⟨4, by decide⟩ then e5 i ⟨4, by decide⟩ - f4 * e5 i ⟨2, by decide⟩ else e5 i j
  have he_scale : twoW * (twoP * (twoP * intDet 7 D7)) = intDet 7 e6 := by
    rw [← intDet_col_scale twoP 7 ⟨0, by decide⟩ D7,
        ← intDet_col_scale twoP 7 ⟨1, by decide⟩ e1,
        ← intDet_col_scale twoW 7 ⟨4, by decide⟩ e2,
        intDet_sub_single_col_w14 7 ⟨0, by decide⟩ ⟨2, by decide⟩ f0 e3 (by decide),
        intDet_sub_single_col_w14 7 ⟨1, by decide⟩ ⟨2, by decide⟩ f1 e4 (by decide),
        intDet_sub_single_col_w14 7 ⟨4, by decide⟩ ⟨2, by decide⟩ f4 e5 (by decide)]
  have he6_piv : intDet 7 e6 = ((2 : Int) * w_i * p_i) * intDet 6 (intSubMat e6 ⟨2, by decide⟩) := by
    rw [intDet_succ_single_row0 6 e6 ⟨2, by decide⟩ (fun j hj => by
      rcases (by have := j.isLt; omega :
        j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 ∨ j.val = 4 ∨ j.val = 5 ∨ j.val = 6) with
        h | h | h | h | h | h | h
      · have hje : j = ⟨0, by decide⟩ := Fin.ext h; subst hje
        change ((2 : Int) * p_i) * D7 ⟨0, by decide⟩ ⟨0, by decide⟩ -
          (1 - p_i) * D7 ⟨0, by decide⟩ ⟨2, by decide⟩ = 0
        rw [hr0_0, hr0_2]
        have : ((2 : Int) * p_i) * ((1 - p_i) * w_i) = (1 - p_i) * ((2 : Int) * w_i * p_i) := by ac_rfl
        rw [this, Int.sub_self]
      · have hje : j = ⟨1, by decide⟩ := Fin.ext h; subst hje
        change ((2 : Int) * p_i) * D7 ⟨0, by decide⟩ ⟨1, by decide⟩ -
          ((3 * w_i + p_i) - (p_i * w_i + 1)) * D7 ⟨0, by decide⟩ ⟨2, by decide⟩ = 0
        rw [hr0_1, hr0_2]
        have : ((2 : Int) * p_i) * (w_i * (3 * w_i + p_i - (p_i * w_i + 1))) =
            (3 * w_i + p_i - (p_i * w_i + 1)) * ((2 : Int) * w_i * p_i) := by ac_rfl
        rw [this, Int.sub_self]
      · exact False.elim (hj (Fin.ext h))
      · have hje : j = ⟨3, by decide⟩ := Fin.ext h; subst hje; exact hr0_3
      · have hje : j = ⟨4, by decide⟩ := Fin.ext h; subst hje
        change ((2 : Int) * w_i) * D7 ⟨0, by decide⟩ ⟨4, by decide⟩ -
          (p_i * p_i - 1) * D7 ⟨0, by decide⟩ ⟨2, by decide⟩ = 0
        rw [hr0_4, hr0_2]
        have : ((2 : Int) * w_i) * (p_i * (p_i * p_i - 1)) = (p_i * p_i - 1) * ((2 : Int) * w_i * p_i) := by ac_rfl
        rw [this, Int.sub_self]
      · have hje : j = ⟨5, by decide⟩ := Fin.ext h; subst hje; exact hr0_5
      · have hje : j = ⟨6, by decide⟩ := Fin.ext h; subst hje; exact hr0_6)]
    have h02 : e6 ⟨0, by decide⟩ ⟨2, by decide⟩ = (2 : Int) * w_i * p_i := hr0_2
    simp only [(by decide : 2 % 2 = 0), ite_true, Int.one_mul, h02]
  rw [he6_piv] at he_scale
  have hsub_eq : intSubMat e6 ⟨2, by decide⟩ = (fun i j =>
      let r7 : Fin 7 := ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩
      match j.val with
      | 0 => ((2 : Int) * p_i) * D7 r7 ⟨0, by decide⟩ - (1 - p_i) * D7 r7 ⟨2, by decide⟩
      | 1 => ((2 : Int) * p_i) * D7 r7 ⟨1, by decide⟩ - ((3 * w_i + p_i) - (p_i * w_i + 1)) * D7 r7 ⟨2, by decide⟩
      | 2 => D7 r7 ⟨3, by decide⟩
      | 3 => ((2 : Int) * w_i) * D7 r7 ⟨4, by decide⟩ - (p_i * p_i - 1) * D7 r7 ⟨2, by decide⟩
      | 4 => D7 r7 ⟨5, by decide⟩
      | _ => D7 r7 ⟨6, by decide⟩) := by
    funext i j
    rcases (by have := j.isLt; omega :
      j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 ∨ j.val = 4 ∨ j.val = 5) with
      h | h | h | h | h | h
    · have hje : j = ⟨0, by decide⟩ := Fin.ext h; subst hje; rfl
    · have hje : j = ⟨1, by decide⟩ := Fin.ext h; subst hje; rfl
    · have hje : j = ⟨2, by decide⟩ := Fin.ext h; subst hje; rfl
    · have hje : j = ⟨3, by decide⟩ := Fin.ext h; subst hje; rfl
    · have hje : j = ⟨4, by decide⟩ := Fin.ext h; subst hje; rfl
    · have hje : j = ⟨5, by decide⟩ := Fin.ext h; subst hje; rfl
  rw [hsub_eq] at he_scale
  have hlhs_eq : ((2 : Int) * w_i * p_i) * (((4 : Int) * p_i) * intDet 7 D7) =
      twoW * (twoP * (twoP * intDet 7 D7)) := by
    dsimp [twoW, twoP]
    rw [show (4 : Int) = (2 : Int) * (2 : Int) from rfl]
    ac_rfl
  exact Int.eq_of_mul_eq_mul_left hnz (hlhs_eq.trans he_scale)

private theorem t3u3_det_D7_eq_E6 (w_i k_i p_i q_i : Int) (hnz : (2 : Int) * w_i * p_i ≠ 0) :
    ((4 : Int) * p_i) * intDet 7 (fun i j => evalExpr4 w_i k_i p_i q_i (t3u3GenD7Expr i j)) =
      intDet 6 (fun i j => evalExpr4 w_i k_i p_i q_i (t3u3GenE6Expr i j)) := by
  rw [det7_D7_to_E6_abstract w_i p_i hnz
    (fun i j => evalExpr4 w_i k_i p_i q_i (t3u3GenD7Expr i j))
    (expr4_eq_of_norm_sub_nil (t3u3GenD7Expr ⟨0, by decide⟩ ⟨0, by decide⟩)
      (.mul (.sub (.const 1) .v2) .v0) (by decide) w_i k_i p_i q_i)
    (expr4_eq_of_norm_sub_nil (t3u3GenD7Expr ⟨0, by decide⟩ ⟨1, by decide⟩)
      (.mul .v0 (.sub (.add (.mul (.const 3) .v0) .v2) (.add (.mul .v2 .v0) (.const 1)))) (by decide) w_i k_i p_i q_i)
    (expr4_eq_of_norm_sub_nil (t3u3GenD7Expr ⟨0, by decide⟩ ⟨2, by decide⟩)
      (.mul (.mul (.const 2) .v0) .v2) (by decide) w_i k_i p_i q_i)
    (expr4_eq_of_norm_sub_nil (t3u3GenD7Expr ⟨0, by decide⟩ ⟨3, by decide⟩)
      (.const 0) (by decide) w_i k_i p_i q_i)
    (expr4_eq_of_norm_sub_nil (t3u3GenD7Expr ⟨0, by decide⟩ ⟨4, by decide⟩)
      (.mul .v2 (.sub (.mul .v2 .v2) (.const 1))) (by decide) w_i k_i p_i q_i)
    (expr4_eq_of_norm_sub_nil (t3u3GenD7Expr ⟨0, by decide⟩ ⟨5, by decide⟩)
      (.const 0) (by decide) w_i k_i p_i q_i)
    (expr4_eq_of_norm_sub_nil (t3u3GenD7Expr ⟨0, by decide⟩ ⟨6, by decide⟩)
      (.const 0) (by decide) w_i k_i p_i q_i)]
  congr 1; funext i j
  rcases (by have := j.isLt; omega :
    j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 ∨ j.val = 4 ∨ j.val = 5) with
    h | h | h | h | h | h
  · have hje : j = ⟨0, by decide⟩ := Fin.ext h; subst hje; rfl
  · have hje : j = ⟨1, by decide⟩ := Fin.ext h; subst hje; rfl
  · have hje : j = ⟨2, by decide⟩ := Fin.ext h; subst hje; rfl
  · have hje : j = ⟨3, by decide⟩ := Fin.ext h; subst hje; rfl
  · have hje : j = ⟨4, by decide⟩ := Fin.ext h; subst hje; rfl
  · have hje : j = ⟨5, by decide⟩ := Fin.ext h; subst hje; rfl

private theorem det6_E6_to_G2_abstract (E6 : Fin 6 -> Fin 6 -> Int) :
    intDet 6 E6 = intDet 6 (fun i j =>
      if j.val = 1 then E6 i ⟨1, by decide⟩ + E6 i ⟨0, by decide⟩
      else if j.val = 5 then E6 i ⟨5, by decide⟩ + E6 i ⟨4, by decide⟩
      else if j.val = 3 then E6 i ⟨3, by decide⟩ - E6 i ⟨4, by decide⟩
      else E6 i j) := by
  let u1 : Fin 6 -> Fin 6 -> Int := fun i j =>
    if j = ⟨1, by decide⟩ then E6 i ⟨1, by decide⟩ - (-1) * E6 i ⟨0, by decide⟩ else E6 i j
  let u2 : Fin 6 -> Fin 6 -> Int := fun i j =>
    if j = ⟨5, by decide⟩ then u1 i ⟨5, by decide⟩ - (-1) * u1 i ⟨4, by decide⟩ else u1 i j
  let u3 : Fin 6 -> Fin 6 -> Int := fun i j =>
    if j = ⟨3, by decide⟩ then u2 i ⟨3, by decide⟩ - 1 * u2 i ⟨4, by decide⟩ else u2 i j
  have s1 := intDet_sub_single_col_w14 6 ⟨1, by decide⟩ ⟨0, by decide⟩ (-1) E6 (by decide)
  change intDet 6 E6 = intDet 6 u1 at s1
  have s2 := intDet_sub_single_col_w14 6 ⟨5, by decide⟩ ⟨4, by decide⟩ (-1) u1 (by decide)
  change intDet 6 u1 = intDet 6 u2 at s2
  have s3 := intDet_sub_single_col_w14 6 ⟨3, by decide⟩ ⟨4, by decide⟩ 1 u2 (by decide)
  change intDet 6 u2 = intDet 6 u3 at s3
  rw [s1, s2, s3]
  congr 1; funext i j
  rcases (by have := j.isLt; omega :
    j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 ∨ j.val = 4 ∨ j.val = 5) with
    h | h | h | h | h | h
  · have hje : j = ⟨0, by decide⟩ := Fin.ext h; subst hje; rfl
  · have hje : j = ⟨1, by decide⟩ := Fin.ext h; subst hje; dsimp [u3, u2, u1]; omega
  · have hje : j = ⟨2, by decide⟩ := Fin.ext h; subst hje; rfl
  · have hje : j = ⟨3, by decide⟩ := Fin.ext h; subst hje; dsimp [u3, u2, u1]; omega
  · have hje : j = ⟨4, by decide⟩ := Fin.ext h; subst hje; rfl
  · have hje : j = ⟨5, by decide⟩ := Fin.ext h; subst hje; dsimp [u3, u2, u1]; omega

private theorem t3u3_det_E6_eq_G2 (w_i k_i p_i q_i : Int) :
    intDet 6 (fun i j => evalExpr4 w_i k_i p_i q_i (t3u3GenE6Expr i j)) =
      intDet 6 (fun i j => evalExpr4 w_i k_i p_i q_i (t3u3GenG2Expr i j)) := by
  rw [det6_E6_to_G2_abstract (fun i j => evalExpr4 w_i k_i p_i q_i (t3u3GenE6Expr i j))]
  congr 1; funext i j
  rcases (by have := j.isLt; omega :
    j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 ∨ j.val = 4 ∨ j.val = 5) with
    h | h | h | h | h | h
  · have hje : j = ⟨0, by decide⟩ := Fin.ext h; subst hje; rfl
  · have hje : j = ⟨1, by decide⟩ := Fin.ext h; subst hje; rfl
  · have hje : j = ⟨2, by decide⟩ := Fin.ext h; subst hje; rfl
  · have hje : j = ⟨3, by decide⟩ := Fin.ext h; subst hje; rfl
  · have hje : j = ⟨4, by decide⟩ := Fin.ext h; subst hje; rfl
  · have hje : j = ⟨5, by decide⟩ := Fin.ext h; subst hje; rfl

set_option maxRecDepth 65536 in
private theorem t3u3_closed_form_all_u (W K u : Nat) (hW : W ≥ 1) (hu : u ≥ 1) :
    4 * intDet 9 (laurentTwoBaseT3U3Mat9 W K u) =
      ((2 ^ (3 * u) * 3 ^ (3 * u) : Nat) : Int) *
        evalPoly4 (W : Int) (K : Int) ((2 ^ u : Nat) : Int) ((3 ^ u : Nat) : Int) t3u3CorePoly := by
  have hexprPow_ev : ∀ (e : Expr4) (d : Nat) (x0 x1 x2 x3 : Int),
      evalExpr4 x0 x1 x2 x3 (expr4Pow e d) = intPowNat (evalExpr4 x0 x1 x2 x3 e) d := by
    intro e d x0 x1 x2 x3; induction d with
    | zero => rfl
    | succ d' ih => simp [expr4Pow, intPowNat, evalExpr4, ih]
  have hintPow_ev : ∀ (a d : Nat), intPowNat (a : Int) d = ((a ^ d : Nat) : Int) := by
    intro a d; induction d with
    | zero => rfl
    | succ d' ih => simp [intPowNat, ih, Nat.pow_succ, Int.natCast_mul, Int.mul_comm]
  have h2binom2 : ∀ n : Nat, ((2 * laurentInterpBinom n 2 : Nat) : Int) = (n : Int) * ((n : Int) - 1) := by
    intro n; cases n with
    | zero => rfl
    | succ m =>
      have h := laurentInterpBinom_succ_mul m 1
      rw [laurentInterpBinom_one_right m] at h
      change 2 * laurentInterpBinom (m + 1) 2 = (m + 1) * m at h
      rw [h, Int.natCast_mul, Int.natCast_add]
      congr 1; omega
  let P_n : Nat := 2 ^ u
  let Q_n : Nat := 3 ^ u
  have hP_ge2 : P_n ≥ 2 := by dsimp [P_n]; simpa using pow2_mono_nat hu
  let w_i : Int := (W : Int)
  let k_i : Int := (K : Int)
  let p_i : Int := (P_n : Int)
  let q_i : Int := (Q_n : Int)
  let M9 := laurentTwoBaseT3U3Mat9 W K u
  have hA9_det : intDet 9 (fun i j => evalExpr4 w_i k_i p_i q_i (t3u3GenA9Expr i j)) = 8 * intDet 9 M9 := by
    let c2_9 : Fin 9 := ⟨2, by decide⟩
    let c5_9 : Fin 9 := ⟨5, by decide⟩
    let c8_9 : Fin 9 := ⟨8, by decide⟩
    let M9_a : Fin 9 -> Fin 9 -> Int := fun i j => if j = c2_9 then 2 * M9 i c2_9 else M9 i j
    let M9_b : Fin 9 -> Fin 9 -> Int := fun i j => if j = c5_9 then 2 * M9_a i c5_9 else M9_a i j
    let M9_c : Fin 9 -> Fin 9 -> Int := fun i j => if j = c8_9 then 2 * M9_b i c8_9 else M9_b i j
    have hA9_eq : (fun i j => evalExpr4 w_i k_i p_i q_i (t3u3GenA9Expr i j)) = M9_c := by
      funext i j
      let r := (laurentRowsTwoBase9 i).1
      let s := (laurentRowsTwoBase9 i).2
      let n := r * W + s * K
      have hn_ev : (r : Int) * w_i + (s : Int) * k_i = (n : Int) := by
        simp [w_i, k_i, n, Int.natCast_add, Int.natCast_mul]
      have hpq1_ev : intPowNat p_i r * intPowNat q_i s =
          ((2 ^ (r * u) * 3 ^ (s * u) : Nat) : Int) := by
        simp only [p_i, q_i, P_n, Q_n, hintPow_ev, ← Int.natCast_mul]
        rw [pow_pow_eq_mul_w5 2 u r, pow_pow_eq_mul_w5 3 u s,
            Nat.mul_comm u r, Nat.mul_comm u s]
      have hpq2_ev : (intPowNat p_i r * intPowNat q_i s) * (intPowNat p_i r * intPowNat q_i s) =
          ((2 ^ (r * (2 * u)) * 3 ^ (s * (2 * u)) : Nat) : Int) := by
        rw [hpq1_ev, ← Int.natCast_mul]
        apply congrArg Nat.cast
        have h2 : 2 ^ (r * u) * 2 ^ (r * u) = 2 ^ (r * (2 * u)) := by
          rw [← Nat.pow_add, show r * (2 * u) = 2 * (r * u) by ac_rfl, Nat.two_mul]
        have h3 : 3 ^ (s * u) * 3 ^ (s * u) = 3 ^ (s * (2 * u)) := by
          rw [← Nat.pow_add, show s * (2 * u) = 2 * (s * u) by ac_rfl, Nat.two_mul]
        calc (2 ^ (r * u) * 3 ^ (s * u)) * (2 ^ (r * u) * 3 ^ (s * u))
            = (2 ^ (r * u) * 2 ^ (r * u)) * (3 ^ (s * u) * 3 ^ (s * u)) := by ac_rfl
          _ = 2 ^ (r * (2 * u)) * 3 ^ (s * (2 * u)) := by rw [h2, h3]
      have h2b := h2binom2 n
      rcases (by have := j.isLt; omega :
        j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 ∨ j.val = 4 ∨
        j.val = 5 ∨ j.val = 6 ∨ j.val = 7 ∨ j.val = 8) with
        hj | hj | hj | hj | hj | hj | hj | hj | hj
      · have hje : j = ⟨0, by decide⟩ := Fin.ext hj; subst hje
        change (1 : Int) = M9 i ⟨0, by decide⟩
        unfold M9 laurentTwoBaseT3U3Mat9 laurentInterpMat
        rw [show laurentColsC33_9 u ⟨0, by decide⟩ = (0, 0) from rfl]
        unfold laurentInterpEntry; simp [laurentInterpBinom_zero_right]
      · have hje : j = ⟨1, by decide⟩ := Fin.ext hj; subst hje
        change (r : Int) * w_i + (s : Int) * k_i = M9 i ⟨1, by decide⟩
        rw [hn_ev]; unfold M9 laurentTwoBaseT3U3Mat9 laurentInterpMat
        rw [show laurentColsC33_9 u ⟨1, by decide⟩ = (1, 0) from rfl]
        unfold laurentInterpEntry; simp [laurentInterpBinom_one_right, r, s, n]
      · have hje : j = ⟨2, by decide⟩ := Fin.ext hj; subst hje
        change ((r : Int) * w_i + (s : Int) * k_i) * (((r : Int) * w_i + (s : Int) * k_i) - 1) =
          2 * M9 i ⟨2, by decide⟩
        rw [hn_ev, ← h2b, Int.natCast_mul]; unfold M9 laurentTwoBaseT3U3Mat9 laurentInterpMat
        rw [show laurentColsC33_9 u ⟨2, by decide⟩ = (2, 0) from rfl]
        unfold laurentInterpEntry; simp [r, s, n]
      · have hje : j = ⟨3, by decide⟩ := Fin.ext hj; subst hje
        change evalExpr4 w_i k_i p_i q_i (.mul (expr4Pow .v2 r) (expr4Pow .v3 s)) = M9 i ⟨3, by decide⟩
        simp only [evalExpr4, hexprPow_ev, hpq1_ev]
        unfold M9 laurentTwoBaseT3U3Mat9 laurentInterpMat
        rw [show laurentColsC33_9 u ⟨3, by decide⟩ = (0, u) from rfl]
        unfold laurentInterpEntry; simp [laurentInterpBinom_zero_right, r, s]
      · have hje : j = ⟨4, by decide⟩ := Fin.ext hj; subst hje
        change evalExpr4 w_i k_i p_i q_i (.mul (expr4Pow .v2 r) (expr4Pow .v3 s)) *
          ((r : Int) * w_i + (s : Int) * k_i) = M9 i ⟨4, by decide⟩
        simp only [evalExpr4, hexprPow_ev, hpq1_ev, hn_ev, ← Int.natCast_mul]
        unfold M9 laurentTwoBaseT3U3Mat9 laurentInterpMat
        rw [show laurentColsC33_9 u ⟨4, by decide⟩ = (1, u) from rfl]
        unfold laurentInterpEntry; dsimp only [r, s, n]; rw [laurentInterpBinom_one_right]
        apply congrArg Nat.cast; ac_rfl
      · have hje : j = ⟨5, by decide⟩ := Fin.ext hj; subst hje
        change evalExpr4 w_i k_i p_i q_i (.mul (expr4Pow .v2 r) (expr4Pow .v3 s)) *
          (((r : Int) * w_i + (s : Int) * k_i) * (((r : Int) * w_i + (s : Int) * k_i) - 1)) =
          2 * M9 i ⟨5, by decide⟩
        simp only [evalExpr4, hexprPow_ev, hpq1_ev, hn_ev, ← h2b, ← Int.natCast_mul]
        unfold M9 laurentTwoBaseT3U3Mat9 laurentInterpMat
        rw [show laurentColsC33_9 u ⟨5, by decide⟩ = (2, u) from rfl]
        unfold laurentInterpEntry; dsimp only [r, s, n]
        rw [show (2 : Int) = ((2 : Nat) : Int) from rfl, ← Int.natCast_mul]
        apply congrArg Nat.cast; ac_rfl
      · have hje : j = ⟨6, by decide⟩ := Fin.ext hj; subst hje
        change (evalExpr4 w_i k_i p_i q_i (.mul (expr4Pow .v2 r) (expr4Pow .v3 s))) *
          (evalExpr4 w_i k_i p_i q_i (.mul (expr4Pow .v2 r) (expr4Pow .v3 s))) = M9 i ⟨6, by decide⟩
        simp only [evalExpr4, hexprPow_ev, hpq2_ev]
        unfold M9 laurentTwoBaseT3U3Mat9 laurentInterpMat
        rw [show laurentColsC33_9 u ⟨6, by decide⟩ = (0, 2 * u) from rfl]
        unfold laurentInterpEntry; simp [laurentInterpBinom_zero_right, r, s]
      · have hje : j = ⟨7, by decide⟩ := Fin.ext hj; subst hje
        change ((evalExpr4 w_i k_i p_i q_i (.mul (expr4Pow .v2 r) (expr4Pow .v3 s))) *
          (evalExpr4 w_i k_i p_i q_i (.mul (expr4Pow .v2 r) (expr4Pow .v3 s)))) *
          ((r : Int) * w_i + (s : Int) * k_i) = M9 i ⟨7, by decide⟩
        simp only [evalExpr4, hexprPow_ev, hpq2_ev, hn_ev, ← Int.natCast_mul]
        unfold M9 laurentTwoBaseT3U3Mat9 laurentInterpMat
        rw [show laurentColsC33_9 u ⟨7, by decide⟩ = (1, 2 * u) from rfl]
        unfold laurentInterpEntry; dsimp only [r, s, n]; rw [laurentInterpBinom_one_right]
        apply congrArg Nat.cast; ac_rfl
      · have hje : j = ⟨8, by decide⟩ := Fin.ext hj; subst hje
        change ((evalExpr4 w_i k_i p_i q_i (.mul (expr4Pow .v2 r) (expr4Pow .v3 s))) *
          (evalExpr4 w_i k_i p_i q_i (.mul (expr4Pow .v2 r) (expr4Pow .v3 s)))) *
          (((r : Int) * w_i + (s : Int) * k_i) * (((r : Int) * w_i + (s : Int) * k_i) - 1)) =
          2 * M9 i ⟨8, by decide⟩
        simp only [evalExpr4, hexprPow_ev, hpq2_ev, hn_ev, ← h2b, ← Int.natCast_mul]
        unfold M9 laurentTwoBaseT3U3Mat9 laurentInterpMat
        rw [show laurentColsC33_9 u ⟨8, by decide⟩ = (2, 2 * u) from rfl]
        unfold laurentInterpEntry; dsimp only [r, s, n]
        rw [show (2 : Int) = ((2 : Nat) : Int) from rfl, ← Int.natCast_mul]
        apply congrArg Nat.cast; ac_rfl
    rw [hA9_eq]
    have hs8 : intDet 9 M9_c = 2 * intDet 9 M9_b := intDet_col_scale 2 9 c8_9 M9_b
    have hs5 : intDet 9 M9_b = 2 * intDet 9 M9_a := intDet_col_scale 2 9 c5_9 M9_a
    have hs2 : intDet 9 M9_a = 2 * intDet 9 M9 := intDet_col_scale 2 9 c2_9 M9
    rw [hs8, hs5, hs2]; omega
  have hpm1_nz : p_i - 1 ≠ 0 := by dsimp [p_i]; omega
  have h2wp_nz : (2 : Int) * w_i * p_i ≠ 0 := by
    have hw_pos : w_i > 0 := by dsimp [w_i]; omega
    have hp_pos : p_i > 0 := by dsimp [p_i]; omega
    exact Int.ne_of_gt (Int.mul_pos (Int.mul_pos (by decide) hw_pos) hp_pos)
  have hG2_poly : intDet 6 (fun i j => evalExpr4 w_i k_i p_i q_i (t3u3GenG2Expr i j)) =
      (8 * intPowNat p_i 4 * intPowNat q_i 3) * evalPoly4 w_i k_i p_i q_i t3u3CorePoly := by
    have hd_ev := (fmDet_bound_and_eval w_i k_i p_i q_i 6 g2FM (by decide)
      t3u3_g2_and_row20_certs.1).2
    have hmat : (fun i j => evalFM w_i k_i p_i q_i (g2FM i j)) =
        (fun i j => evalExpr4 w_i k_i p_i q_i (t3u3GenG2Expr i j)) := by
      funext i j
      rw [evalFM_eq_evalPoly4, t3u3_g2_and_row20_certs.2.1 i j, evalPoly4_normExpr4]
    rw [hmat, g2_det6_eq_core] at hd_ev
    have hcore_b : t3u3CoreFM.all (fmBound 20) = true := by decide
    have hm_ev := (fmMul_bound_and_eval w_i k_i p_i q_i 4 20 (by decide)
      [.p 0 0 4 3 8] t3u3CoreFM (by decide) hcore_b).2
    rw [hm_ev, evalFM_eq_evalPoly4 w_i k_i p_i q_i t3u3CoreFM, fmToPoly4_t3u3CoreFM] at hd_ev
    have hlead : evalFM w_i k_i p_i q_i [.p 0 0 4 3 8] =
        8 * intPowNat p_i 4 * intPowNat q_i 3 := by
      simp [evalFM, evalFMOne, fmOneToMono4, evalMono4, intPowNat]; ac_rfl
    rw [hlead] at hd_ev
    exact hd_ev.symm
  have hchain : (8 * p_i) * (4 * intDet 9 M9) =
      (8 * p_i) * ((intPowNat p_i 3 * intPowNat q_i 3) * evalPoly4 w_i k_i p_i q_i t3u3CorePoly) := by
    have hp4 : intPowNat p_i 4 = p_i * intPowNat p_i 3 := by simp [intPowNat, Int.mul_comm]
    calc
      (8 * p_i) * (4 * intDet 9 M9) = ((4 : Int) * p_i) * (8 * intDet 9 M9) := by ac_rfl
      _ = ((4 : Int) * p_i) * intDet 7 (fun i j => evalExpr4 w_i k_i p_i q_i (t3u3GenD7Expr i j)) := by
            rw [← hA9_det, t3u3_det_A9_eq_B8, t3u3_det_B8_eq_C8,
                t3u3_det_C8_eq_C7 w_i k_i p_i q_i hpm1_nz, t3u3_det_C7_eq_D7]
      _ = intDet 6 (fun i j => evalExpr4 w_i k_i p_i q_i (t3u3GenG2Expr i j)) := by
            rw [t3u3_det_D7_eq_E6 w_i k_i p_i q_i h2wp_nz, t3u3_det_E6_eq_G2]
      _ = (8 * intPowNat p_i 4 * intPowNat q_i 3) * evalPoly4 w_i k_i p_i q_i t3u3CorePoly := hG2_poly
      _ = (8 * p_i) * ((intPowNat p_i 3 * intPowNat q_i 3) * evalPoly4 w_i k_i p_i q_i t3u3CorePoly) := by
            rw [hp4]; ac_rfl
  have h8p_nz : 8 * p_i ≠ 0 := by dsimp [p_i]; omega
  have h4 := Int.eq_of_mul_eq_mul_left h8p_nz hchain
  have hpq3 : intPowNat p_i 3 * intPowNat q_i 3 = ((2 ^ (3 * u) * 3 ^ (3 * u) : Nat) : Int) := by
    simp only [p_i, q_i, P_n, Q_n, hintPow_ev, ← Int.natCast_mul]
    rw [pow_pow_eq_mul_w5 2 u 3, pow_pow_eq_mul_w5 3 u 3, Nat.mul_comm u 3]
  rw [hpq3] at h4
  exact h4

set_option exponentiation.threshold 1024 in
/--
  Theorem W14.2c (`laurent_9x9_t3u3_all_u_cone_positivity_and_multiu_nonvanishing`,
  `zero custom axioms`):
  Rank-3 `9 × 9` `(T = 3, U = 3)` Exact All-`u` Closed Form, Universal All-`u` Strict Positivity
  Across the Collatz Cone, Global `u ∈ {1, 2, 3, 4}` Cone-Free Non-Vanishing, & `(12, 19)`
  Lower-Convergent Sign-Flip Contrast (`Branch P3.3`, `W14_H2`).
-/
theorem laurent_9x9_t3u3_all_u_cone_positivity_and_multiu_nonvanishing :
    (∀ (W K u : Nat), W ≥ 1 -> u ≥ 1 ->
      4 * intDet 9 (laurentTwoBaseT3U3Mat9 W K u) =
        ((2 ^ (3 * u) * 3 ^ (3 * u) : Nat) : Int) *
          evalPoly4 (W : Int) (K : Int) ((2 ^ u : Nat) : Int) ((3 ^ u : Nat) : Int) t3u3CorePoly) ∧
    (∀ (W K u : Nat), W ≥ 1 -> K ≥ 1 -> u ≥ 1 ->
      3 ^ W < 2 ^ K -> 3 * K ≤ 5 * W ->
      intDet 9 (laurentTwoBaseT3U3Mat9 W K u) > 0 ∧
      intDet 9 (laurentTwoBaseT3U3Mat9 W K u) ≠ 0) ∧
    (∀ (W K u : Nat), W ≥ 1 -> K ≥ 1 -> 1 ≤ u -> u ≤ 4 ->
      intDet 9 (laurentTwoBaseT3U3Mat9 W K u) ≠ 0) ∧
    (3 * 19 ≤ 5 * 12 ∧ 2 ^ 19 < 3 ^ 12 ∧
      intDet 9 (laurentTwoBaseT3U3Mat9 12 19 1) = 89955036648 ∧
      intDet 9 (laurentTwoBaseT3U3Mat9 12 19 2) = -25973182180043886600000 ∧
      intDet 9 (laurentTwoBaseT3U3Mat9 16 26 2) = 1532798562346060501094400000) := by
  have hintPow_ev : ∀ (a d : Nat), intPowNat (a : Int) d = ((a ^ d : Nat) : Int) := by
    intro a d; induction d with
    | zero => rfl
    | succ d' ih => simp [intPowNat, ih, Nat.pow_succ, Int.natCast_mul, Int.mul_comm]
  have hexprPow_ev : ∀ (e : Expr4) (x0 x1 x2 x3 : Int) (d : Nat),
      evalExpr4 x0 x1 x2 x3 (expr4Pow e d) = intPowNat (evalExpr4 x0 x1 x2 x3 e) d := by
    intro e x0 x1 x2 x3 d; induction d with
    | zero => rfl
    | succ d' ih => simp [expr4Pow, evalExpr4, intPowNat, ih]
  have hclosed_u := t3u3_closed_form_all_u
  have hcone_all_u : ∀ (W K u : Nat), W ≥ 1 -> K ≥ 1 -> u ≥ 1 ->
      3 ^ W < 2 ^ K -> 3 * K ≤ 5 * W ->
      intDet 9 (laurentTwoBaseT3U3Mat9 W K u) > 0 ∧
      intDet 9 (laurentTwoBaseT3U3Mat9 W K u) ≠ 0 := by
    have hconv : 2 ^ 569 < 3 ^ 359 := by
      have h2 : 2 ^ 569 = 2 ^ 200 * (2 ^ 200 * 2 ^ 169) := by
        rw [show (569 : Nat) = 200 + (200 + 169) from rfl,
            Nat.pow_add 2 200 (200 + 169), Nat.pow_add 2 200 169]
      have h3 : 3 ^ 359 = 3 ^ 180 * 3 ^ 179 := by
        rw [show (359 : Nat) = 180 + 179 from rfl, Nat.pow_add 3 180 179]
      rw [h2, h3]; decide
    rcases t3u3_cone_comb_and_binom_certs with ⟨hw_valid, hbinom_id, hcomb_id⟩
    intro W K u hW hK hu hgt hcone
    have hslope : 569 * W < 359 * K := by
      by_cases hsl : 569 * W < 359 * K
      · exact hsl
      · exfalso
        have hge : 359 * K ≤ 569 * W := by omega
        have hp1 : 2 ^ (359 * K) ≤ 2 ^ (569 * W) := nat_pow_mono_exp_pos 2 _ _ (by decide) hge
        have hp2 : 2 ^ (569 * W) = (2 ^ 569) ^ W := (pow_pow_eq_mul_w5 2 569 W).symm
        have hp3 : (2 ^ 569) ^ W ≤ (3 ^ 359) ^ W := pow_mono_base_w14 _ _ (Nat.le_of_lt hconv) W
        have hp4 : (3 ^ 359) ^ W = 3 ^ (359 * W) := pow_pow_eq_mul_w5 3 359 W
        have hp5 : (3 ^ W) ^ 359 < (2 ^ K) ^ 359 := by
          have hst : ∀ (a b n : Nat), a < b -> a ^ (n + 1) < b ^ (n + 1) := by
            intro a b n hab; induction n with
            | zero => simpa using hab
            | succ n' ih =>
              rw [Nat.pow_succ a (n' + 1), Nat.pow_succ b (n' + 1)]
              exact Nat.lt_of_le_of_lt
                (Nat.mul_le_mul_right a (Nat.le_of_lt ih))
                (Nat.mul_lt_mul_of_pos_left hab (nat_pow_pos_of_pos b (by omega) (n' + 1)))
          exact hst (3 ^ W) (2 ^ K) 358 hgt
        rw [pow_pow_eq_mul_w5 3 W 359, Nat.mul_comm W 359,
            pow_pow_eq_mul_w5 2 K 359, Nat.mul_comm K 359] at hp5
        exact Nat.not_le_of_gt hp5 (Nat.le_trans hp1 (by rw [hp2, ← hp4]; exact hp3))
    let A := 359 * K - 569 * W
    let B := 5 * W - 3 * K
    have hA1 : A ≥ 1 := by omega
    have h88W : (88 : Int) * (W : Int) = 3 * (A : Int) + 359 * (B : Int) := by dsimp [A, B]; omega
    have h88K : (88 : Int) * (K : Int) = 5 * (A : Int) + 569 * (B : Int) := by dsimp [A, B]; omega
    have hm_pow : ∀ (s x : Int) (n : Nat), intPowNat (s * x) n = intPowNat s n * intPowNat x n := by
      intro s x n; induction n with
      | zero => simp [intPowNat]
      | succ n' ih => simp only [intPowNat, ih]; ac_rfl
    have h88_ev : intPowNat 88 9 *
        evalPoly4 (W : Int) (K : Int) ((2 ^ u : Nat) : Int) ((3 ^ u : Nat) : Int) t3u3CorePoly =
        evalPoly4 ((88 : Int) * (W : Int)) ((88 : Int) * (K : Int))
          ((2 ^ u : Nat) : Int) ((3 ^ u : Nat) : Int) t3u3CorePoly := by
      rw [evalPoly4_t3u3CorePoly_eq_sum10 (W : Int) (K : Int) u,
          evalPoly4_t3u3CorePoly_eq_sum10 ((88 : Int) * (W : Int)) ((88 : Int) * (K : Int)) u,
          ← intSumPrefix_mul_left_w14 10 (intPowNat 88 9) _ 10 (Nat.le_refl 10)]
      apply intSumPrefix_congr_w14 10 _ _ _ 10 (Nat.le_refl 10)
      intro k
      rw [hm_pow 88 (W : Int) (9 - k.val), hm_pow 88 (K : Int) k.val]
      have hk9 : (9 - k.val) + k.val = 9 := by have := k.isLt; omega
      have h88_sp : intPowNat 88 9 = intPowNat 88 (9 - k.val) * intPowNat 88 k.val := by
        rw [← intPowNat_add_w14 88 (9 - k.val) k.val, hk9]
      rw [h88_sp]; ac_rfl
    have hrow_ev : ∀ k : Fin 10,
        intPowNat ((88 : Int) * (W : Int)) (9 - k.val) * intPowNat ((88 : Int) * (K : Int)) k.val =
          intSumPrefix 10 (fun j =>
            coneBinomCoeff k j * (intPowNat (A : Int) (9 - j.val) * intPowNat (B : Int) j.val)) 10 := by
      intro k
      have heq := expr4_eq_of_norm_sub_nil _ _ (hbinom_id k) (A : Int) (B : Int) 0 0
      have hlhs : evalExpr4 (A : Int) (B : Int) 0 0 (coneRowExpr k) =
          intPowNat ((88 : Int) * (W : Int)) (9 - k.val) * intPowNat ((88 : Int) * (K : Int)) k.val := by
        unfold coneRowExpr
        rw [evalExpr4, hexprPow_ev, hexprPow_ev]
        simp only [evalExpr4]
        rw [← h88W, ← h88K]
      have hrhs : ∀ m : Nat, m ≤ 10 ->
          evalExpr4 (A : Int) (B : Int) 0 0 (coneRowSumExpr k m) =
            intSumPrefix 10 (fun j =>
              coneBinomCoeff k j * (intPowNat (A : Int) (9 - j.val) * intPowNat (B : Int) j.val)) m := by
        intro m hm; induction m with
        | zero => rfl
        | succ m' ih =>
          have hlt : m' < 10 := hm
          simp only [coneRowSumExpr, intSumPrefix, hlt, dite_true, evalExpr4,
                     hexprPow_ev, ih (Nat.le_of_lt hm)]
      rw [← hlhs, heq, hrhs 10 (Nat.le_refl 10)]
    have hcomb_ev : ∀ j : Fin 10,
        intSumPrefix 10 (fun k => coneBinomCoeff k j * evalCDSInt u (t3u3CoreWSlice k)) 10 =
          evalCDSInt u (t3u3ConeSliceCDS j) := by
      intro j
      have hst : ∀ m : Nat, m ≤ 10 ->
          (cdsCombPrefix j m).all cdsValid64 = true ∧
          evalCDSInt u (cdsCombPrefix j m) =
            intSumPrefix 10 (fun k => coneBinomCoeff k j * evalCDSInt u (t3u3CoreWSlice k)) m := by
        intro m hm; induction m with
        | zero => simp [cdsCombPrefix, intSumPrefix, evalCDSInt, evalCDSPos, evalCDSNeg]
        | succ m' ih =>
          have hlt : m' < 10 := hm
          rcases ih (Nat.le_of_lt hm) with ⟨hvm, hem⟩
          rcases cdsScaleInt_valid_and_eval u (coneBinomCoeff ⟨m', hlt⟩ j)
            (t3u3CoreWSlice ⟨m', hlt⟩) (hw_valid ⟨m', hlt⟩) with ⟨hvs, hes⟩
          rcases cdsMerge_valid_and_eval u _ _ hvm hvs with ⟨hv_all, he_all⟩
          simp only [cdsCombPrefix, intSumPrefix, hlt, dite_true]
          exact ⟨hv_all, by rw [he_all, hem, hes]⟩
      have h10 := (hst 10 (Nat.le_refl 10)).2
      rw [hcomb_id j] at h10
      exact h10.symm
    have hcone_eq : evalPoly4 ((88 : Int) * (W : Int)) ((88 : Int) * (K : Int))
        ((2 ^ u : Nat) : Int) ((3 ^ u : Nat) : Int) t3u3CorePoly =
        intSumPrefix 10 (fun j =>
          (intPowNat (A : Int) (9 - j.val) * intPowNat (B : Int) j.val) *
            evalCDSInt u (t3u3ConeSliceCDS j)) 10 := by
      rw [evalPoly4_t3u3CorePoly_eq_sum10 ((88 : Int) * (W : Int)) ((88 : Int) * (K : Int)) u]
      have hstep1 : intSumPrefix 10 (fun k =>
            intPowNat ((88 : Int) * (W : Int)) (9 - k.val) *
              intPowNat ((88 : Int) * (K : Int)) k.val * evalCDSInt u (t3u3CoreWSlice k)) 10 =
          intSumPrefix 10 (fun k =>
            intSumPrefix 10 (fun j =>
              (intPowNat (A : Int) (9 - j.val) * intPowNat (B : Int) j.val) *
                (coneBinomCoeff k j * evalCDSInt u (t3u3CoreWSlice k))) 10) 10 := by
        apply intSumPrefix_congr_w14 10 _ _ _ 10 (Nat.le_refl 10)
        intro k
        rw [hrow_ev k, ← intSumPrefix_mul_right_w14 10 _ _ 10 (Nat.le_refl 10)]
        apply intSumPrefix_congr_w14 10 _ _ _ 10 (Nat.le_refl 10)
        intro j; ac_rfl
      rw [hstep1, intSumPrefix_swap10]
      apply intSumPrefix_congr_w14 10 _ _ _ 10 (Nat.le_refl 10)
      intro j
      rw [intSumPrefix_mul_left_w14 10 _ _ 10 (Nat.le_refl 10), hcomb_ev j]
    have hsum_pos : intSumPrefix 10 (fun j =>
        (intPowNat (A : Int) (9 - j.val) * intPowNat (B : Int) j.val) *
          evalCDSInt u (t3u3ConeSliceCDS j)) 10 > 0 := by
      have hd_st : ∀ d : Nat, 1 + d ≤ 10 ->
          intSumPrefix 10 (fun j =>
            (intPowNat (A : Int) (9 - j.val) * intPowNat (B : Int) j.val) *
              evalCDSInt u (t3u3ConeSliceCDS j)) (1 + d) > 0 := by
        intro d hd; induction d with
        | zero =>
          simp only [intSumPrefix, (by decide : 0 < 10), dite_true, Int.zero_add]
          have hf0 := checkCDSDom43_sound (t3u3ConeSliceCDS ⟨0, by decide⟩) (t3u3_cone_dom_all ⟨0, by decide⟩) u hu
          have hAB0 : intPowNat (A : Int) 9 * intPowNat (B : Int) 0 > 0 := by
            rw [hintPow_ev, hintPow_ev, Nat.pow_zero, Int.natCast_one, Int.mul_one]
            have hpA := nat_pow_pos_of_pos A hA1 9
            omega
          exact Int.mul_pos hAB0 hf0
        | succ d' ih =>
          rw [Nat.add_succ]
          have hlt : 1 + d' < 10 := hd
          simp only [intSumPrefix, hlt, dite_true]
          have hprev := ih (by omega)
          have hfj := checkCDSDom43_sound (t3u3ConeSliceCDS ⟨1 + d', hlt⟩)
            (t3u3_cone_dom_all ⟨1 + d', hlt⟩) u hu
          have hAB_nn : 0 ≤ intPowNat (A : Int) (9 - (1 + d')) * intPowNat (B : Int) (1 + d') := by
            rw [hintPow_ev, hintPow_ev, ← Int.natCast_mul]
            exact Int.natCast_nonneg _
          have hnn := Int.mul_nonneg hAB_nn (Int.le_of_lt hfj)
          exact Int.lt_of_lt_of_le hprev (by omega)
      exact hd_st 9 (by decide)
    rw [hcone_eq] at h88_ev
    have h88_pos : intPowNat 88 9 > 0 := by decide
    have hcore_pos : evalPoly4 (W : Int) (K : Int) ((2 ^ u : Nat) : Int) ((3 ^ u : Nat) : Int) t3u3CorePoly > 0 := by
      by_cases hp : evalPoly4 (W : Int) (K : Int) ((2 ^ u : Nat) : Int) ((3 ^ u : Nat) : Int) t3u3CorePoly > 0
      · exact hp
      · exfalso
        have hle0 : evalPoly4 (W : Int) (K : Int) ((2 ^ u : Nat) : Int) ((3 ^ u : Nat) : Int) t3u3CorePoly ≤ 0 := by omega
        have hm := Int.mul_nonpos_of_nonneg_of_nonpos (Int.le_of_lt h88_pos) hle0
        omega
    have h4det := hclosed_u W K u hW hu
    have h6_pos : ((2 ^ (3 * u) * 3 ^ (3 * u) : Nat) : Int) > 0 := by
      have hn : 2 ^ (3 * u) * 3 ^ (3 * u) ≥ 1 :=
        Nat.mul_le_mul (nat_pow_pos_of_pos 2 (by decide) _) (pow3_pos_nat _)
      omega
    have hrhs_pos := Int.mul_pos h6_pos hcore_pos
    rw [← h4det] at hrhs_pos
    exact ⟨by omega, by omega⟩
  rcases t3u3_u234_and_contrast_certs with ⟨hu_vals, hm43, hm41, hm53, hv12_1, hv12_2, hv16_2⟩
  have heval_fast : ∀ (W K u : Nat), u < 64 ->
      evalPoly4 (W : Int) (K : Int) ((2 ^ u : Nat) : Int) ((3 ^ u : Nat) : Int) t3u3CorePoly =
        evalCoreBySlicesFast W K u := by
    intro W K u hu64
    rw [evalPoly4_t3u3CorePoly_eq_sum10 (W : Int) (K : Int) u]
    unfold evalCoreBySlicesFast
    apply intSumPrefix_congr_w14 10 _ _ _ 10 (Nat.le_refl 10)
    intro k
    rw [hintPow_ev, hintPow_ev, ← Int.natCast_mul]
    rcases evalCDSFast_eq u hu64 (t3u3CoreWSlice k) with ⟨hp, hn⟩
    rw [hp, hn]; rfl
  have hu_shape_eq : ∀ (W K u g c9 c6 c4 c2 c7 c5 c3 c0 : Nat),
      u < 64 ->
      (∀ k : Fin 10,
        (evalCDSPosFast u (t3u3CoreWSlice k) : Int) - (evalCDSNegFast u (t3u3CoreWSlice k) : Int) =
          match k.val with
          | 0 => (g : Int) * (c9 : Int)
          | 1 => 0
          | 2 => -((g : Int) * (c7 : Int))
          | 3 => (g : Int) * (c6 : Int)
          | 4 => -((g : Int) * (c5 : Int))
          | 5 => (g : Int) * (c4 : Int)
          | 6 => -((g : Int) * (c3 : Int))
          | 7 => (g : Int) * (c2 : Int)
          | 8 => 0
          | _ => -((g : Int) * (c0 : Int))) ->
      evalPoly4 (W : Int) (K : Int) ((2 ^ u : Nat) : Int) ((3 ^ u : Nat) : Int) t3u3CorePoly =
        (g : Int) * ((evalP9ShapeNat c9 c6 c4 c2 W K : Int) -
                     (evalN9ShapeNat c7 c5 c3 c0 W K : Int)) := by
    intro W K u g c9 c6 c4 c2 c7 c5 c3 c0 hu64 hk_eq
    rw [heval_fast W K u hu64]
    unfold evalCoreBySlicesFast
    rw [intSumPrefix_ten]
    simp only [hk_eq]
    unfold evalP9ShapeNat evalN9ShapeNat
    simp only [Nat.sub_self, Nat.pow_zero, Nat.mul_one, Nat.one_mul, Int.natCast_add, Int.natCast_mul,
               Int.mul_zero, Int.add_zero, Int.mul_neg]
    rw [Int.mul_sub]
    simp only [Int.mul_add]
    have ht9 : ((W ^ 9 : Nat) : Int) * ((g : Int) * (c9 : Int)) =
        (g : Int) * ((c9 : Int) * ((W ^ 9 : Nat) : Int)) := by ac_rfl
    have ht7 : (((W ^ 7 : Nat) : Int) * ((K ^ 2 : Nat) : Int)) * ((g : Int) * (c7 : Int)) =
        (g : Int) * ((((c7 : Int) * ((W ^ 7 : Nat) : Int)) * ((K ^ 2 : Nat) : Int))) := by ac_rfl
    have ht6 : (((W ^ 6 : Nat) : Int) * ((K ^ 3 : Nat) : Int)) * ((g : Int) * (c6 : Int)) =
        (g : Int) * ((((c6 : Int) * ((W ^ 6 : Nat) : Int)) * ((K ^ 3 : Nat) : Int))) := by ac_rfl
    have ht5 : (((W ^ 5 : Nat) : Int) * ((K ^ 4 : Nat) : Int)) * ((g : Int) * (c5 : Int)) =
        (g : Int) * ((((c5 : Int) * ((W ^ 5 : Nat) : Int)) * ((K ^ 4 : Nat) : Int))) := by ac_rfl
    have ht4' : (((W ^ 4 : Nat) : Int) * ((K ^ 5 : Nat) : Int)) * ((g : Int) * (c4 : Int)) =
        (g : Int) * ((((c4 : Int) * ((W ^ 4 : Nat) : Int)) * ((K ^ 5 : Nat) : Int))) := by ac_rfl
    have ht3 : (((W ^ 3 : Nat) : Int) * ((K ^ 6 : Nat) : Int)) * ((g : Int) * (c3 : Int)) =
        (g : Int) * ((((c3 : Int) * ((W ^ 3 : Nat) : Int)) * ((K ^ 6 : Nat) : Int))) := by ac_rfl
    have ht2 : (((W ^ 2 : Nat) : Int) * ((K ^ 7 : Nat) : Int)) * ((g : Int) * (c2 : Int)) =
        (g : Int) * ((((c2 : Int) * ((W ^ 2 : Nat) : Int)) * ((K ^ 7 : Nat) : Int))) := by ac_rfl
    have ht0 : ((K ^ 9 : Nat) : Int) * ((g : Int) * (c0 : Int)) =
        (g : Int) * ((c0 : Int) * ((K ^ 9 : Nat) : Int)) := by ac_rfl
    rw [ht9, ht7, ht6, ht5, ht4', ht3, ht2, ht0]
    omega
  have hglobal_1_4 : ∀ (W K u : Nat), W ≥ 1 -> K ≥ 1 -> 1 ≤ u -> u ≤ 4 ->
      intDet 9 (laurentTwoBaseT3U3Mat9 W K u) ≠ 0 := by
    intro W K u hW hK hu1 hu4
    rcases (by omega : u = 1 ∨ u = 2 ∨ u = 3 ∨ u = 4) with rfl | rfl | rfl | rfl
    · exact laurent_9x9_t3u3_factorization_nonzero_and_cone_positivity.2.2.1 W K hW hK
    · intro hz
      have hc := hclosed_u W K 2 hW (by decide)
      rw [hz, Int.mul_zero] at hc
      have hsh := hu_shape_eq W K 2 500
        4398046511104 26373229903872 22295572144128 1653175484928
        15015088226304 29631280840704 9372015415296 10460353203 (by decide)
        (fun k => by revert k; decide)
      rw [hsh, show ((2 ^ (3 * 2) * 3 ^ (3 * 2) : Nat) : Int) = 46656 by decide] at hc
      have hpeq : evalP9ShapeNat 4398046511104 26373229903872 22295572144128 1653175484928 W K =
          evalN9ShapeNat 15015088226304 29631280840704 9372015415296 10460353203 W K := by omega
      exact p9Shape_nonzero_of_mod_p
        4398046511104 26373229903872 22295572144128 1653175484928
        15015088226304 29631280840704 9372015415296 10460353203 43 (by decide) hm43 W K hW hK hpeq
    · intro hz
      have hc := hclosed_u W K 3 hW (by decide)
      rw [hz, Int.mul_zero] at hc
      have hsh := hu_shape_eq W K 3 1372
        91091955994975010816 859366264352995676160 996830302125598065216 74479652107258140288
        345737014518126845952 1223967978751424385024 426411488072942910720 33227552537453169 (by decide)
        (fun k => by revert k; decide)
      rw [hsh, show ((2 ^ (3 * 3) * 3 ^ (3 * 3) : Nat) : Int) = 10077696 by decide] at hc
      have hpeq : evalP9ShapeNat 91091955994975010816 859366264352995676160 996830302125598065216 74479652107258140288 W K =
          evalN9ShapeNat 345737014518126845952 1223967978751424385024 426411488072942910720 33227552537453169 W K := by omega
      exact p9Shape_nonzero_of_mod_p
        91091955994975010816 859366264352995676160 996830302125598065216 74479652107258140288
        345737014518126845952 1223967978751424385024 426411488072942910720 33227552537453169 41 (by decide) hm41 W K hW hK hpeq
    · intro hz
      have hc := hclosed_u W K 4 hW (by decide)
      rw [hz, Int.mul_zero] at hc
      have hsh := hu_shape_eq W K 4 7812500
        635684024152068003463168 9911614595754203377827840 13796448820546054236143616 1165538797128926735376384
        3111419039100732060991488 15843575530865744267968512 6281249468853579843502080 27311664563487284499 (by decide)
        (fun k => by revert k; decide)
      rw [hsh, show ((2 ^ (3 * 4) * 3 ^ (3 * 4) : Nat) : Int) = 2176782336 by decide] at hc
      have hpeq : evalP9ShapeNat 635684024152068003463168 9911614595754203377827840 13796448820546054236143616 1165538797128926735376384 W K =
          evalN9ShapeNat 3111419039100732060991488 15843575530865744267968512 6281249468853579843502080 27311664563487284499 W K := by omega
      exact p9Shape_nonzero_of_mod_p
        635684024152068003463168 9911614595754203377827840 13796448820546054236143616 1165538797128926735376384
        3111419039100732060991488 15843575530865744267968512 6281249468853579843502080 27311664563487284499 53 (by decide) hm53 W K hW hK hpeq
  refine ⟨hclosed_u, hcone_all_u, hglobal_1_4, ?_⟩
  have hc12_1 := hclosed_u 12 19 1 (by decide) (by decide)
  have hc12_2 := hclosed_u 12 19 2 (by decide) (by decide)
  have hc16_2 := hclosed_u 16 26 2 (by decide) (by decide)
  rw [heval_fast 12 19 1 (by decide), show 3 * 1 = 3 from rfl, hv12_1] at hc12_1
  rw [heval_fast 12 19 2 (by decide), show 3 * 2 = 6 from rfl, hv12_2] at hc12_2
  rw [heval_fast 16 26 2 (by decide), show 3 * 2 = 6 from rfl, hv16_2] at hc16_2
  exact ⟨by decide, by decide, by omega, by omega, by omega⟩

-- ----------------------------------------------------------------------------
-- Section 2D: Cross-Block Brox Recurrence, `5 × d_mult` 2-Adic Quotient Boost,
--             & Two-Pivot Balanced `m`-Block Elimination (Choice-Free)
-- ----------------------------------------------------------------------------

private theorem blockWeightSum_append_w14 :
    ∀ (xs ys : List (Nat × Nat)),
      blockWeightSum (xs ++ ys) = blockWeightSum xs + blockWeightSum ys
  | [], _ => by simp [blockWeightSum]
  | x :: xs, ys => by
    simp only [List.cons_append, blockWeightSum, blockWeightSum_append_w14 xs ys]; omega

private theorem blockStepSum_append_w14 :
    ∀ (xs ys : List (Nat × Nat)),
      blockStepSum (xs ++ ys) = blockStepSum xs + blockStepSum ys
  | [], _ => by simp [blockStepSum]
  | x :: xs, ys => by
    simp only [List.cons_append, blockStepSum, blockStepSum_append_w14 xs ys]; omega

private theorem drop_len_append_w14 :
    ∀ (xs ys : List (Nat × Nat)), (xs ++ ys).drop xs.length = ys
  | [], _ => rfl
  | _ :: xs, ys => drop_len_append_w14 xs ys

private theorem take_len_append_w14 :
    ∀ (xs ys : List (Nat × Nat)), (xs ++ ys).take xs.length = xs
  | [], _ => rfl
  | x :: xs, ys => congrArg (x :: ·) (take_len_append_w14 xs ys)

private theorem broxSpiralCarry_append_nonempty (bt : Nat × Nat) (stail : List (Nat × Nat)) :
    ∀ (b0 : Nat × Nat) (ptail : List (Nat × Nat)),
      broxSpiralCarry ((b0 :: ptail) ++ (bt :: stail)) =
        3 ^ blockWeightSum (bt :: stail) * broxSpiralCarry (b0 :: ptail) +
          2 ^ (b0.2 + blockStepSum ptail + bt.1) * broxSpiralCarry (bt :: stail)
  | b0, [] => by
    simp only [List.cons_append, List.nil_append, broxSpiralCarry, blockStepSum, Nat.add_zero]
  | b0, b1 :: ptl => by
    have ih := broxSpiralCarry_append_nonempty bt stail b1 ptl
    change broxSpiralCarry (b1 :: (ptl ++ (bt :: stail))) =
      3 ^ blockWeightSum (bt :: stail) * broxSpiralCarry (b1 :: ptl) +
        2 ^ (b1.2 + blockStepSum ptl + bt.1) * broxSpiralCarry (bt :: stail) at ih
    have hw_app : blockWeightSum (b1 :: (ptl ++ (bt :: stail))) =
        blockWeightSum (b1 :: ptl) + blockWeightSum (bt :: stail) :=
      blockWeightSum_append_w14 (b1 :: ptl) (bt :: stail)
    simp only [List.cons_append, broxSpiralCarry, blockStepSum]
    rw [hw_app, ih,
        Nat.pow_add 3 (blockWeightSum (b1 :: ptl)) (blockWeightSum (bt :: stail)),
        Nat.mul_add (2 ^ (b0.2 + b1.1)),
        Nat.mul_add (3 ^ blockWeightSum (bt :: stail)),
        ← Nat.mul_assoc (2 ^ (b0.2 + b1.1)) (2 ^ (b1.2 + blockStepSum ptl + bt.1)),
        ← Nat.pow_add 2 (b0.2 + b1.1) (b1.2 + blockStepSum ptl + bt.1),
        show b0.2 + b1.1 + (b1.2 + blockStepSum ptl + bt.1) =
          b0.2 + (b1.1 + b1.2 + blockStepSum ptl) + bt.1 by omega]
    ac_rfl

private theorem pow3_mod16_nonzero (w : Nat) :
    3 ^ w % 16 = 1 ∨ 3 ^ w % 16 = 3 ∨ 3 ^ w % 16 = 9 ∨ 3 ^ w % 16 = 11 := by
  induction w with
  | zero => exact Or.inl rfl
  | succ w' ih =>
    rw [Nat.pow_succ, Nat.mul_mod]
    rcases ih with h | h | h | h <;> rw [h] <;> decide

/--
  Theorem W14.2d (`m_block_two_pivot_telescoping_and_2adic_quotient_boost`,
  choice-free `zero custom axioms`):
  Exact `∀ t ≥ 1` Cross-Block Carry & Quotient Telescoping, Universal `5 × d_mult` 2-Adic Quotient
  Boost (`q_j ≥ 75` under `15 ∣ q_j`, `q_j ≥ 1275` under `255 ∣ q_j`), Two-Pivot Cross-Block
  Telescoping Squeeze, & Near-Balanced `[(17, 2), (17, 2), (17, 26)]` `42,843×` Elimination
  (`Branch P3.4`, `W14_H2`).
-/
theorem m_block_two_pivot_telescoping_and_2adic_quotient_boost :
    ((∀ (b0 bt : Nat × Nat) (ptail stail : List (Nat × Nat)),
        let pref := b0 :: ptail
        let suf := bt :: stail
        let blocks := pref ++ suf
        let W := blockWeightSum blocks
        let K := blockStepSum blocks
        3 ^ W < 2 ^ K ->
        2 ^ (b0.2 + blockStepSum ptail + bt.1) * broxSpiralCarry (rotBlocks pref.length blocks) =
          3 ^ blockWeightSum pref * broxSpiralCarry blocks +
            (2 ^ K - 3 ^ W) * broxSpiralCarry pref ∧
        (∀ q0 qt : Nat,
          (2 ^ K - 3 ^ W) * q0 = broxSpiralCarry blocks ->
          (2 ^ K - 3 ^ W) * qt = broxSpiralCarry (rotBlocks pref.length blocks) ->
          2 ^ (b0.2 + blockStepSum ptail + bt.1) * qt =
            3 ^ blockWeightSum pref * q0 + broxSpiralCarry pref)) ∧
     (∀ (b0 b1 : Nat × Nat) (tail : List (Nat × Nat)),
        let blocks := b0 :: b1 :: tail
        let W := blockWeightSum blocks
        let K := blockStepSum blocks
        3 ^ W < 2 ^ K ->
        2 ^ (b0.2 + b1.1) * broxSpiralCarry (rotBlocks 1 blocks) =
          3 ^ b0.1 * broxSpiralCarry blocks + (2 ^ K - 3 ^ W) * (2 ^ b0.2 - 1) ∧
        (∀ q0 q1 : Nat,
          (2 ^ K - 3 ^ W) * q0 = broxSpiralCarry blocks ->
          (2 ^ K - 3 ^ W) * q1 = broxSpiralCarry (rotBlocks 1 blocks) ->
          2 ^ (b0.2 + b1.1) * q1 = 3 ^ b0.1 * q0 + (2 ^ b0.2 - 1)))) ∧
    ((∀ (w0 a0 w1 q0 q1 d_mult : Nat),
        a0 ≥ 4 -> d_mult % 16 = 15 -> d_mult ∣ q0 ->
        2 ^ (a0 + w1) * q1 = 3 ^ w0 * q0 + (2 ^ a0 - 1) ->
        (3 ^ w0 * q0) % 16 = 1 ∧ q0 ≥ 5 * d_mult) ∧
     (∀ (w0 a0 w1 q0 q1 : Nat),
        a0 ≥ 4 ->
        2 ^ (a0 + w1) * q1 = 3 ^ w0 * q0 + (2 ^ a0 - 1) ->
        (15 ∣ q0 -> q0 ≥ 75) ∧ (255 ∣ q0 -> q0 ≥ 1275))) ∧
    (∀ (b0 b1 : Nat × Nat) (tail : List (Nat × Nat)) (qs : List Nat) (d_mult : Nat),
      let blocks := b0 :: b1 :: tail
      let W := blockWeightSum blocks
      let K := blockStepSum blocks
      let D := 2 ^ K - 3 ^ W
      let Wt := blockWeightSum tail
      let Et := blockStepSum (b1 :: tail) - blockWeightSum (b1 :: tail)
      (∀ b ∈ blocks, b.1 ≥ 1 ∧ b.2 ≥ 1) ->
      3 ^ W < 2 ^ K ->
      qs.length = blocks.length ->
      (∀ j : Nat, j < blocks.length -> D * natAt qs j = broxSpiralCarry (rotBlocks j blocks)) ->
      d_mult ∣ natListGcd qs ->
      broxSpiralCarry blocks + 3 ^ (b1.1 + Wt) ≤
        3 ^ (b1.1 + Wt) * 2 ^ b0.2 + 2 ^ (b0.2 + b1.1) * 3 ^ Wt * (2 ^ Et - 1) ∧
      d_mult * D + 3 ^ (b1.1 + Wt) ≤
        3 ^ (b1.1 + Wt) * 2 ^ b0.2 + 2 ^ (b0.2 + b1.1) * 3 ^ Wt * (2 ^ Et - 1)) ∧
    (let blocks_bal : List (Nat × Nat) := [(17, 2), (17, 2), (17, 26)]
     let D_bal := 2 ^ blockStepSum blocks_bal - 3 ^ blockWeightSum blocks_bal
     (∀ j : Nat, j < 3 ->
       3 * D_bal + 3 ^ (51 - (blockAt blocks_bal j).1) ≤
         3 ^ (51 - (blockAt blocks_bal j).1) * 2 ^ 30) ∧
     3 * D_bal + 3 ^ 34 >
       3 ^ 34 * 2 ^ 2 + 2 ^ 19 * 3 ^ 17 * (2 ^ 28 - 1) ∧
     42843 * broxSpiralCarry blocks_bal < 3 * D_bal ∧
     ¬ (∃ qs : List Nat,
       qs.length = 3 ∧
       ∀ j : Nat, j < 3 -> D_bal * natAt qs j = broxSpiralCarry (rotBlocks j blocks_bal))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hgen : ∀ (b0 bt : Nat × Nat) (ptail stail : List (Nat × Nat)),
        let pref := b0 :: ptail
        let suf := bt :: stail
        let blocks := pref ++ suf
        let W := blockWeightSum blocks
        let K := blockStepSum blocks
        3 ^ W < 2 ^ K ->
        2 ^ (b0.2 + blockStepSum ptail + bt.1) * broxSpiralCarry (rotBlocks pref.length blocks) =
          3 ^ blockWeightSum pref * broxSpiralCarry blocks +
            (2 ^ K - 3 ^ W) * broxSpiralCarry pref ∧
        (∀ q0 qt : Nat,
          (2 ^ K - 3 ^ W) * q0 = broxSpiralCarry blocks ->
          (2 ^ K - 3 ^ W) * qt = broxSpiralCarry (rotBlocks pref.length blocks) ->
          2 ^ (b0.2 + blockStepSum ptail + bt.1) * qt =
            3 ^ blockWeightSum pref * q0 + broxSpiralCarry pref) := by
      intro b0 bt ptail stail; dsimp only; intro hgt
      let pref := b0 :: ptail
      let suf := bt :: stail
      let blocks := pref ++ suf
      let e1 := b0.2 + blockStepSum ptail + bt.1
      let e2 := bt.2 + blockStepSum stail + b0.1
      have hrot : rotBlocks pref.length blocks = suf ++ pref := by
        unfold rotBlocks
        rw [drop_len_append_w14 pref suf, take_len_append_w14 pref suf]
      rw [hrot]
      have h1 := broxSpiralCarry_append_nonempty bt stail b0 ptail
      have h2 := broxSpiralCarry_append_nonempty b0 ptail bt stail
      have he12 : e1 + e2 = blockStepSum blocks := by
        dsimp only [blocks, pref, suf, e1, e2]
        rw [blockStepSum_append_w14]
        simp only [blockStepSum]; omega
      have hw12 : blockWeightSum pref + blockWeightSum suf = blockWeightSum blocks :=
        (blockWeightSum_append_w14 pref suf).symm
      have hstep_nat : 2 ^ e1 * broxSpiralCarry (suf ++ pref) +
            3 ^ blockWeightSum blocks * broxSpiralCarry pref =
          3 ^ blockWeightSum pref * broxSpiralCarry blocks +
            2 ^ blockStepSum blocks * broxSpiralCarry pref := by
        dsimp only [blocks, pref, suf, e1, e2] at h1 h2 he12 hw12 ⊢
        rw [h1, h2,
            Nat.mul_add (2 ^ (b0.2 + blockStepSum ptail + bt.1)),
            ← Nat.mul_assoc (2 ^ (b0.2 + blockStepSum ptail + bt.1))
              (2 ^ (bt.2 + blockStepSum stail + b0.1)),
            ← Nat.pow_add 2 (b0.2 + blockStepSum ptail + bt.1)
              (bt.2 + blockStepSum stail + b0.1), he12,
            Nat.mul_add (3 ^ blockWeightSum (b0 :: ptail)),
            ← Nat.mul_assoc (3 ^ blockWeightSum (b0 :: ptail))
              (3 ^ blockWeightSum (bt :: stail)),
            ← Nat.pow_add 3 (blockWeightSum (b0 :: ptail))
              (blockWeightSum (bt :: stail)), hw12]
        ac_rfl
      have hsub_step : 2 ^ e1 * broxSpiralCarry (suf ++ pref) =
          3 ^ blockWeightSum pref * broxSpiralCarry blocks +
            (2 ^ blockStepSum blocks - 3 ^ blockWeightSum blocks) * broxSpiralCarry pref := by
        rw [Nat.sub_mul]
        have hle_m : 3 ^ blockWeightSum blocks * broxSpiralCarry pref ≤
            2 ^ blockStepSum blocks * broxSpiralCarry pref :=
          Nat.mul_le_mul_right _ (Nat.le_of_lt hgt)
        omega
      refine ⟨hsub_step, ?_⟩
      intro q0 qt hq0 hqt
      let D := 2 ^ blockStepSum blocks - 3 ^ blockWeightSum blocks
      have hD_pos : 0 < D := Nat.sub_pos_of_lt hgt
      have hmul_D : D * (2 ^ e1 * qt) =
          D * (3 ^ blockWeightSum pref * q0 + broxSpiralCarry pref) := by
        calc D * (2 ^ e1 * qt)
            = 2 ^ e1 * (D * qt) := by ac_rfl
          _ = 2 ^ e1 * broxSpiralCarry (suf ++ pref) := by rw [hqt]
          _ = 3 ^ blockWeightSum pref * broxSpiralCarry blocks + D * broxSpiralCarry pref := hsub_step
          _ = 3 ^ blockWeightSum pref * (D * q0) + D * broxSpiralCarry pref := by rw [← hq0]
          _ = D * (3 ^ blockWeightSum pref * q0 + broxSpiralCarry pref) := by
                rw [Nat.mul_add]; ac_rfl
      exact Nat.eq_of_mul_eq_mul_left hD_pos hmul_D
    refine ⟨hgen, fun b0 b1 tail hgt => ?_⟩
    simpa [broxSpiralCarry, blockWeightSum, blockStepSum] using hgen b0 b1 [] tail hgt
  · have hboost : ∀ (w0 a0 w1 q0 q1 d_mult : Nat),
        a0 ≥ 4 -> d_mult % 16 = 15 -> d_mult ∣ q0 ->
        2 ^ (a0 + w1) * q1 = 3 ^ w0 * q0 + (2 ^ a0 - 1) ->
        (3 ^ w0 * q0) % 16 = 1 ∧ q0 ≥ 5 * d_mult := by
      intro w0 a0 w1 q0 q1 d_mult ha4 hd15 ⟨k_q, hkq⟩ hrec
      have h16_lhs : (2 ^ (a0 + w1) * q1) % 16 = 0 := by
        have hp : 2 ^ (a0 + w1) = 16 * 2 ^ (a0 + w1 - 4) := by
          conv => lhs; rw [show a0 + w1 = 4 + (a0 + w1 - 4) by omega, Nat.pow_add]
        rw [hp, Nat.mul_assoc, Nat.mul_mod_right]
      have h16_a0 : 2 ^ a0 % 16 = 0 := by
        have hp : 2 ^ a0 = 16 * 2 ^ (a0 - 4) := by
          conv => lhs; rw [show a0 = 4 + (a0 - 4) by omega, Nat.pow_add]
        rw [hp, Nat.mul_mod_right]
      have h2a_ge16 : 2 ^ a0 ≥ 16 := by
        simpa using nat_pow_mono_exp_pos 2 4 a0 (by decide) ha4
      have h15_mod : (2 ^ a0 - 1) % 16 = 15 := by omega
      have h3q_mod1 : (3 ^ w0 * q0) % 16 = 1 := by
        have hm := congrArg (· % 16) hrec
        rw [h16_lhs, Nat.add_mod, h15_mod] at hm
        omega
      refine ⟨h3q_mod1, ?_⟩
      rcases (by omega : k_q % 16 = 0 ∨ k_q % 16 = 1 ∨ k_q % 16 = 2 ∨ k_q % 16 = 3 ∨
        k_q % 16 = 4 ∨ k_q ≥ 5) with hm0 | hm1 | hm2 | hm3 | hm4 | hk5
      · by_cases hk_ge5 : k_q ≥ 5
        · rw [hkq, Nat.mul_comm d_mult k_q]; exact Nat.mul_le_mul_right d_mult hk_ge5
        · have hk0 : k_q = 0 := by omega
          rw [hk0, Nat.mul_zero] at hkq; rw [hkq, Nat.mul_zero] at h3q_mod1; cases h3q_mod1
      · have hqm : q0 % 16 = 15 := by rw [hkq, Nat.mul_mod, hd15, hm1]
        rw [Nat.mul_mod, hqm] at h3q_mod1
        rcases pow3_mod16_nonzero w0 with h | h | h | h <;> rw [h] at h3q_mod1 <;> cases h3q_mod1
      · have hqm : q0 % 16 = 14 := by rw [hkq, Nat.mul_mod, hd15, hm2]
        rw [Nat.mul_mod, hqm] at h3q_mod1
        rcases pow3_mod16_nonzero w0 with h | h | h | h <;> rw [h] at h3q_mod1 <;> cases h3q_mod1
      · have hqm : q0 % 16 = 13 := by rw [hkq, Nat.mul_mod, hd15, hm3]
        rw [Nat.mul_mod, hqm] at h3q_mod1
        rcases pow3_mod16_nonzero w0 with h | h | h | h <;> rw [h] at h3q_mod1 <;> cases h3q_mod1
      · have hqm : q0 % 16 = 12 := by rw [hkq, Nat.mul_mod, hd15, hm4]
        rw [Nat.mul_mod, hqm] at h3q_mod1
        rcases pow3_mod16_nonzero w0 with h | h | h | h <;> rw [h] at h3q_mod1 <;> cases h3q_mod1
      · rw [hkq, Nat.mul_comm d_mult k_q]
        exact Nat.mul_le_mul_right d_mult hk5
    refine ⟨hboost, fun w0 a0 w1 q0 q1 ha4 hrec =>
      ⟨fun h15 => (hboost w0 a0 w1 q0 q1 15 ha4 (by decide) h15 hrec).2,
       fun h255 => (hboost w0 a0 w1 q0 q1 255 ha4 (by decide) h255 hrec).2⟩⟩
  · intro b0 b1 tail qs d_mult; dsimp only; intro hpos hgt hq_len hqs_eq hd_gcd
    let Wt := blockWeightSum tail
    let Et := blockStepSum (b1 :: tail) - blockWeightSum (b1 :: tail)
    have hpos_tl : ∀ b ∈ (b1 :: tail), b.1 ≥ 1 ∧ b.2 ≥ 1 :=
      fun b hb => hpos b (List.mem_cons_of_mem b0 hb)
    have hbd_tl := ((m_block_brox_carry_bound_and_cross_block_squeeze.1 b1 tail hpos_tl).1
      0 (by simp)).2
    have hrot0 : rotBlocks 0 (b1 :: tail) = b1 :: tail := by simp [rotBlocks]
    have hw_sub : blockWeightSum (b1 :: tail) - (blockAt (b1 :: tail) 0).1 = Wt := by
      simp [blockAt, blockWeightSum, Wt]
    rw [hrot0, hw_sub] at hbd_tl
    change broxSpiralCarry (b1 :: tail) + 3 ^ Wt ≤ 3 ^ Wt * 2 ^ Et at hbd_tl
    have hEt_ge1 : 2 ^ Et ≥ 1 := nat_pow_pos_of_pos 2 (by decide) Et
    have htl_le : broxSpiralCarry (b1 :: tail) ≤ 3 ^ Wt * (2 ^ Et - 1) := by
      rw [Nat.mul_sub_left_distrib, Nat.mul_one]; omega
    have hb0_pos : 2 ^ b0.2 ≥ 2 := by
      simpa using pow2_mono_nat (hpos b0 List.mem_cons_self).2
    have htwo_piv : broxSpiralCarry (b0 :: b1 :: tail) + 3 ^ (b1.1 + Wt) ≤
        3 ^ (b1.1 + Wt) * 2 ^ b0.2 + 2 ^ (b0.2 + b1.1) * 3 ^ Wt * (2 ^ Et - 1) := by
      simp only [broxSpiralCarry]
      change 3 ^ (b1.1 + Wt) * (2 ^ b0.2 - 1) + 2 ^ (b0.2 + b1.1) * broxSpiralCarry (b1 :: tail) +
          3 ^ (b1.1 + Wt) ≤ _
      have hm_tl := Nat.mul_le_mul_left (2 ^ (b0.2 + b1.1)) htl_le
      rw [← Nat.mul_assoc (2 ^ (b0.2 + b1.1)) (3 ^ Wt)] at hm_tl
      have hlhs : 3 ^ (b1.1 + Wt) * (2 ^ b0.2 - 1) + 3 ^ (b1.1 + Wt) =
          3 ^ (b1.1 + Wt) * 2 ^ b0.2 := by
        rw [Nat.mul_sub_left_distrib, Nat.mul_one]
        have h1 : 3 ^ (b1.1 + Wt) * 1 ≤ 3 ^ (b1.1 + Wt) * 2 ^ b0.2 :=
          Nat.mul_le_mul_left _ (by omega)
        omega
      omega
    dsimp only [Wt, Et] at htwo_piv
    refine ⟨htwo_piv, ?_⟩
    have hc0_pos :=
      ((m_block_brox_carry_bound_and_cross_block_squeeze.1 b0 (b1 :: tail) hpos).1 0 (by simp)).1
    have hq0_eq := hqs_eq 0 (by simp)
    simp only [rotBlocks, List.drop_zero, List.take_zero, List.append_nil] at hq0_eq hc0_pos
    have hq0_pos : natAt qs 0 ≥ 1 := by
      by_cases hz : natAt qs 0 = 0
      · rw [hz, Nat.mul_zero] at hq0_eq; omega
      · omega
    have hd_q0 : d_mult ∣ natAt qs 0 :=
      Nat.dvd_trans hd_gcd (natListGcd_dvd_natAt qs 0 (by rw [hq_len]; simp))
    rcases hd_q0 with ⟨k0, hk0⟩
    have hdm_le : d_mult ≤ natAt qs 0 := by
      cases k0 with
      | zero => rw [Nat.mul_zero] at hk0; omega
      | succ k' => rw [hk0, Nat.mul_succ]; omega
    have hmD : d_mult * (2 ^ blockStepSum (b0 :: b1 :: tail) - 3 ^ blockWeightSum (b0 :: b1 :: tail)) ≤
        broxSpiralCarry (b0 :: b1 :: tail) := by
      rw [← hq0_eq, Nat.mul_comm]
      exact Nat.mul_le_mul_left _ hdm_le
    omega
  · dsimp only
    let blocks_bal : List (Nat × Nat) := [(17, 2), (17, 2), (17, 26)]
    let D_bal := 2 ^ blockStepSum blocks_bal - 3 ^ blockWeightSum blocks_bal
    have hsingle_fail : ∀ j : Nat, j < 3 ->
        3 * D_bal + 3 ^ (51 - (blockAt blocks_bal j).1) ≤
          3 ^ (51 - (blockAt blocks_bal j).1) * 2 ^ 30 := by
      intro j hj
      rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl <;> decide
    have htwo_win : 3 * D_bal + 3 ^ 34 >
        3 ^ 34 * 2 ^ 2 + 2 ^ 19 * 3 ^ 17 * (2 ^ 28 - 1) := by decide
    have hmargin_42843 : 42843 * broxSpiralCarry blocks_bal < 3 * D_bal := by decide
    refine ⟨hsingle_fail, htwo_win, hmargin_42843, ?_⟩
    rintro ⟨qs, hq_len, hqs_eq⟩
    have hpos_b : ∀ b ∈ blocks_bal, b.1 ≥ 1 ∧ b.2 ≥ 1 := by decide
    have hgt_b : 3 ^ blockWeightSum blocks_bal < 2 ^ blockStepSum blocks_bal := by decide
    have h2_div : ∀ b ∈ blocks_bal, 2 ∣ b.2 := by decide
    have h3_gcd : 3 ∣ natListGcd qs :=
      (m_block_companion_prime_quotient_cascades.1
        (17, 2) [(17, 2), (17, 26)] qs hpos_b hgt_b hq_len hqs_eq).2.1 h2_div
    have htwo_le : broxSpiralCarry blocks_bal + 3 ^ 34 ≤
        3 ^ 34 * 2 ^ 2 + 2 ^ 19 * 3 ^ 17 * (2 ^ 28 - 1) := by decide
    have hq0_eq := hqs_eq 0 (by decide)
    simp only [rotBlocks, List.drop_zero, List.take_zero, List.append_nil] at hq0_eq
    have hq0_pos : natAt qs 0 ≥ 1 := by
      by_cases hz : natAt qs 0 = 0
      · rw [hz, Nat.mul_zero] at hq0_eq
        have hc_pos : broxSpiralCarry blocks_bal ≥ 1 := by decide
        dsimp only [blocks_bal] at hc_pos
        omega
      · omega
    rcases Nat.dvd_trans h3_gcd (natListGcd_dvd_natAt qs 0 (by omega)) with ⟨k0, hk0⟩
    have h3_le : 3 ≤ natAt qs 0 := by
      cases k0 with
      | zero => rw [Nat.mul_zero] at hk0; omega
      | succ k' => rw [hk0, Nat.mul_succ]; omega
    have hmD : 3 * (2 ^ blockStepSum [(17, 2), (17, 2), (17, 26)] - 3 ^ blockWeightSum [(17, 2), (17, 2), (17, 26)]) ≤
        broxSpiralCarry [(17, 2), (17, 2), (17, 26)] := by
      rw [← hq0_eq, Nat.mul_comm]; exact Nat.mul_le_mul_left _ h3_le
    dsimp only [D_bal, blocks_bal] at htwo_win htwo_le
    omega

end CollatzFormal
