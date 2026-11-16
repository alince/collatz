/-
  CollatzFormal/CSWave3Synthesis.lean
  Wave 3 Campaign Synthesis: Final Irreducible Core Compression at `x = 1` &
  Unique First-Hit Bijection (`T3.13`–`T3.16`), `bbchallenge` `2^w` & `3^w`
  Myhill–Nerode Regular Barrier, `∀ d ≥ 1` Coordinatewise-Monotone Identity
  Collapse, & Infinite Parametric Dyadic/Triadic Sieves (`T2.7`–`T2.9`), and
  Sharp 1-Block GCD/Mod-24 Squeeze (`q0 ≥ 17`), Complete `[]`-Axiom 2-Block
  Brox Reduction (`SubexponentialCubicGapProp`), & Master Equivalences (`T9`–`T11`).

  Zero external dependencies (pure Lean 4.35.0 Core), zero `sorry`,
  zero `native_decide`, zero custom `axiom`.
-/

import CollatzFormal.CSFullConjecture

namespace CollatzFormal

-- ============================================================================
-- SECTION 8: Track 3 Wave 3 — Final Irreducible Core Compression at `x = 1`,
--            First-Hit Bijection (`[]` Axioms), & Forward-Iteration-Free
--            `Mod373248` Range Equivalences (`#26/#27`, `T3.13`–`T3.16`)
-- ============================================================================

def backwardOneTotalSteps (u : List Bool) (q : Nat) : Nat :=
  u.length + (canonicalSuffixShift u 1 + q * (2 * 3 ^ (parityWeight u - 1)))

def IsFirstHitOnePair (u : List Bool) (q : Nat) : Prop :=
  IsCoreParityWord u ∧
  ∀ k : Nat, k < backwardOneTotalSteps u q ->
    collatzIter k (exactBackwardQuotient 1 u q) ≠ 1

def firstHitStepsAux : Nat -> Nat -> Nat
  | 0, _ => 0
  | fuel + 1, cur =>
    if cur == 1 then 0
    else 1 + firstHitStepsAux fuel (collatzStep cur)

def Mod373248OneGeneratorRangeProp : Prop :=
  ∀ n : Nat, IsSurvivingMod373248Class n ->
    ∃ (u : List Bool) (q : Nat),
      IsCoreParityWord u ∧ exactBackwardQuotient 1 u q = n

def Mod373248UniqueFirstHitRangeProp : Prop :=
  ∀ n : Nat, IsSurvivingMod373248Class n ->
    ∃ (tail : List Bool) (q : Nat),
      IsFirstHitOnePair (true :: true :: tail) q ∧
      parityWeight (true :: true :: tail) ≥ 3 ∧
      exactBackwardQuotient 1 (true :: true :: tail) q = n

-- ----------------------------------------------------------------------------
-- T3.13: Total Convergent Generator `exactBackwardQuotient 1 u q`, `[true]`
--        Closed Form, & Universal `{1, 2}`-Loop Extension (`[]` Axioms)
-- ----------------------------------------------------------------------------

/--
  Theorem T3.13a (`one_generator_pos_odd_and_reaches_one`, `[]` axioms):
  Because `1 % 3 ≠ 0` unconditionally, for EVERY core parity word `u` and EVERY `q : Nat`,
  `y := exactBackwardQuotient 1 u q` is a positive odd integer converging to `1` in
  `backwardOneTotalSteps u q` compressed steps!
-/
theorem one_generator_pos_odd_and_reaches_one (u : List Bool) (q : Nat)
    (hu : IsCoreParityWord u) :
    let y := exactBackwardQuotient 1 u q
    y ≥ 1 ∧ y % 2 = 1 ∧
    2 ^ backwardOneTotalSteps u q = 3 ^ parityWeight u * y + affineCarry u ∧
    collatzIter (backwardOneTotalSteps u q) y = 1 := by
  dsimp only
  have hw : parityWeight u ≥ 1 := reverse_head_true_imp_weight_pos u hu.2
  rcases exactBackwardQuotient_spec 1 u q hw (by decide) with ⟨hy_pos, heq, hiter, hodd_imp⟩
  rw [Nat.mul_one] at heq
  exact ⟨hy_pos, hodd_imp hu.1, heq, hiter⟩

theorem pow2_two_mul_eq_pow4 : ∀ m : Nat, 2 ^ (2 * m) = 4 ^ m
  | 0 => rfl
  | m + 1 => by
    rw [show 2 * (m + 1) = 2 * m + 2 by omega, Nat.pow_add, pow2_two_mul_eq_pow4 m,
        show (2 : Nat) ^ 2 = 4 from rfl, ← Nat.pow_succ]

/--
  Theorem T3.13b (`one_generator_singleton_true_closed_form`, `[]` axioms):
  At `u = [true]`, `exactBackwardQuotient 1 [true] q = (4 ^ (q + 1) - 1) / 3` (`1, 5, 21, 85, 341, ...`).
-/
theorem one_generator_singleton_true_closed_form (q : Nat) :
    canonicalSuffixShift [true] 1 = 1 ∧
    backwardOneTotalSteps [true] q = 2 * (q + 1) ∧
    3 * exactBackwardQuotient 1 [true] q + 1 = 4 ^ (q + 1) ∧
    exactBackwardQuotient 1 [true] q = (4 ^ (q + 1) - 1) / 3 := by
  have hcs : canonicalSuffixShift [true] 1 = 1 := by decide
  have hsteps : backwardOneTotalSteps [true] q = 2 * (q + 1) := by
    unfold backwardOneTotalSteps
    rw [hcs]
    have hw1 : parityWeight [true] = 1 := rfl
    rw [hw1]
    simp only [List.length_singleton, Nat.sub_self, Nat.pow_zero, Nat.mul_one]
    omega
  rcases one_generator_pos_odd_and_reaches_one [true] q ⟨rfl, rfl⟩ with ⟨_, _, heq, _⟩
  rw [hsteps, pow2_two_mul_eq_pow4 (q + 1)] at heq
  have hc1 : affineCarry [true] = 1 := rfl
  have hp1 : 3 ^ parityWeight [true] = 3 := rfl
  rw [hc1, hp1] at heq
  have hlin : 3 * exactBackwardQuotient 1 [true] q + 1 = 4 ^ (q + 1) := heq.symm
  exact ⟨hcs, hsteps, hlin, by omega⟩

theorem nat_mul_left_cancel_pos (m a b : Nat) (hm : m > 0) (heq : m * a = m * b) : a = b := by
  have hd := congrArg (fun z => z / m) heq
  rw [Nat.mul_comm m a, Nat.mul_div_cancel a hm,
      Nat.mul_comm m b, Nat.mul_div_cancel b hm] at hd
  exact hd

/--
  Theorem T3.13c (`one_generator_trivial_loop_extension`, `[]` axioms):
  Appending the canonical zero-run and a final `true` traverses `{1, 2}` once more, producing
  a distinct core word `uLoop` with `exactBackwardQuotient 1 uLoop 0 = exactBackwardQuotient 1 u q`
  and `¬ IsFirstHitOnePair uLoop 0`.
-/
theorem one_generator_trivial_loop_extension (u : List Bool) (q : Nat)
    (hu : IsCoreParityWord u) :
    let shift := canonicalSuffixShift u 1 + q * (2 * 3 ^ (parityWeight u - 1))
    let uLoop := (u ++ List.replicate shift false) ++ [true]
    IsCoreParityWord uLoop ∧
    canonicalSuffixShift uLoop 1 = 1 ∧
    exactBackwardQuotient 1 uLoop 0 = exactBackwardQuotient 1 u q ∧
    ¬ IsFirstHitOnePair uLoop 0 := by
  dsimp only
  let w := parityWeight u
  let shift := canonicalSuffixShift u 1 + q * (2 * 3 ^ (w - 1))
  let v := u ++ List.replicate shift false
  let uLoop := v ++ [true]
  let y := exactBackwardQuotient 1 u q
  have hw : w ≥ 1 := reverse_head_true_imp_weight_pos u hu.2
  rcases one_generator_pos_odd_and_reaches_one u q hu with ⟨_, _, heq_u, hiter_u⟩
  change 2 ^ (u.length + shift) = 3 ^ w * y + affineCarry u at heq_u
  change collatzIter (u.length + shift) y = 1 at hiter_u
  have huLoop_core : IsCoreParityWord uLoop := by
    refine ⟨?_, ?_⟩
    · dsimp [uLoop, v]
      rw [List.append_assoc]
      exact head_append_of_some u _ true hu.1
    · dsimp [uLoop]
      rw [List.reverse_append]
      rfl
  rcases affineCarry_append_replicate_false u shift with ⟨hwt_v, hcar_v⟩
  change parityWeight v = w at hwt_v
  change affineCarry v = affineCarry u at hcar_v
  have hv_len : v.length = u.length + shift := by
    dsimp [v]; rw [List.length_append, List.length_replicate]
  have hwt_loop : parityWeight uLoop = w + 1 := by
    dsimp [uLoop]; rw [parityWeight_append, hwt_v]; rfl
  have hlen_loop : uLoop.length = v.length + 1 := by
    dsimp [uLoop]; rw [List.length_append]; rfl
  have hcar_loop : affineCarry uLoop = 3 * affineCarry u + 2 ^ v.length := by
    dsimp [uLoop]
    rw [affineCarry_append v [true], hcar_v]
    have hp1 : 3 ^ parityWeight [true] = 3 := rfl
    have hc1 : affineCarry [true] = 1 := rfl
    rw [hp1, hc1, Nat.mul_one]
  have hloop_eq : 2 ^ (uLoop.length + 1) = 3 ^ parityWeight uLoop * y + affineCarry uLoop := by
    rw [hlen_loop, hwt_loop, hcar_loop, hv_len]
    calc
      2 ^ (u.length + shift + 1 + 1)
          = 2 ^ (u.length + shift) * 4 := by
              rw [show u.length + shift + 1 + 1 = (u.length + shift) + 2 by omega, Nat.pow_add]
      _ = 3 * 2 ^ (u.length + shift) + 2 ^ (u.length + shift) := by omega
      _ = 3 * (3 ^ w * y + affineCarry u) + 2 ^ (u.length + shift) := by rw [heq_u]
      _ = 3 ^ (w + 1) * y + (3 * affineCarry u + 2 ^ (u.length + shift)) := by
            rw [Nat.pow_succ, Nat.mul_comm (3 ^ w) 3, Nat.mul_add, Nat.mul_assoc, Nat.add_assoc]
  have h1_lt_P : 1 < 2 * 3 ^ (parityWeight uLoop - 1) := by
    rw [hwt_loop, show w + 1 - 1 = w by omega]
    have hp3_ge3 : 3 ^ w ≥ 3 := by
      rw [show w = (w - 1) + 1 by omega, Nat.pow_succ]
      have hp0 := pow3_pos_nat (w - 1); omega
    omega
  have hcongr_loop : (2 ^ (uLoop.length + 1) * 1) % 3 ^ parityWeight uLoop =
      affineCarry uLoop % 3 ^ parityWeight uLoop := by
    rw [Nat.mul_one, hloop_eq, Nat.add_mod, Nat.mul_mod (3 ^ parityWeight uLoop),
        Nat.mod_self, Nat.zero_mul, Nat.zero_mod, Nat.zero_add, Nat.mod_mod]
  have hcs_loop : canonicalSuffixShift uLoop 1 = 1 :=
    ((canonicalSuffixShift_spec_unique uLoop 1 (by rw [hwt_loop]; omega) (by decide)).2.2
      1 h1_lt_P hcongr_loop).symm
  rcases one_generator_pos_odd_and_reaches_one uLoop 0 huLoop_core with ⟨_, _, heq_l0, _⟩
  have hsteps_l0 : backwardOneTotalSteps uLoop 0 = uLoop.length + 1 := by
    unfold backwardOneTotalSteps; rw [hcs_loop]; simp
  rw [hsteps_l0] at heq_l0
  have hy_eq : exactBackwardQuotient 1 uLoop 0 = y := by
    apply nat_mul_left_cancel_pos (3 ^ parityWeight uLoop) _ _ (pow3_pos_nat _)
    omega
  have hnot_fh : ¬ IsFirstHitOnePair uLoop 0 := by
    intro hfh
    have hlt_k : u.length + shift < backwardOneTotalSteps uLoop 0 := by
      rw [hsteps_l0, hlen_loop, hv_len]; omega
    have hne := hfh.2 (u.length + shift) hlt_k
    rw [hy_eq] at hne
    exact hne hiter_u
  exact ⟨huLoop_core, hcs_loop, hy_eq, hnot_fh⟩

-- ----------------------------------------------------------------------------
-- T3.14: Canonical First-Hit Bijection (`[]` Axioms, Zero `Classical.choice`)
-- ----------------------------------------------------------------------------

theorem pow3_odd_nat_sec8 : ∀ w : Nat, 3 ^ w % 2 = 1
  | 0 => rfl
  | w + 1 => by rw [Nat.pow_succ, Nat.mul_mod, pow3_odd_nat_sec8 w]

theorem nat_affine_of_parityOfIter : ∀ (k n : Nat),
    2 ^ k * collatzIter k n = 3 ^ parityWeight (parityOfIter k n) * n + affineCarry (parityOfIter k n)
  | 0, n => by simp [collatzIter, parityOfIter, parityWeight, affineCarry, affineCarryAux]
  | k + 1, n => by
    have ih := nat_affine_of_parityOfIter k (collatzStep n)
    simp only [collatzIter, parityOfIter]
    cases hb : (n % 2 == 0) with
    | true =>
      have hev : n % 2 = 0 := of_decide_eq_true hb
      simp only [ite_true, parityWeight]
      have hcar : affineCarry (false :: parityOfIter k (collatzStep n)) =
          2 * affineCarry (parityOfIter k (collatzStep n)) := by
        change affineCarry ([false] ++ parityOfIter k (collatzStep n)) = _
        rw [affineCarry_append]
        have hc0 : affineCarry [false] = 0 := rfl
        have hl1 : [false].length = 1 := rfl
        rw [hc0, hl1, Nat.mul_zero, Nat.zero_add]
      have hstep : 2 * collatzStep n = n := by
        unfold collatzStep; rw [hb]; simp; omega
      rw [hcar, Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, Nat.mul_assoc, ih,
          Nat.mul_add, ← Nat.mul_assoc 2, Nat.mul_comm 2 (3 ^ _), Nat.mul_assoc, hstep]
    | false =>
      have hne : n % 2 ≠ 0 := of_decide_eq_false hb
      simp only [Bool.false_eq_true, ite_false, parityWeight]
      have hcar : affineCarry (true :: parityOfIter k (collatzStep n)) =
          3 ^ parityWeight (parityOfIter k (collatzStep n)) +
          2 * affineCarry (parityOfIter k (collatzStep n)) := by
        change affineCarry ([true] ++ parityOfIter k (collatzStep n)) = _
        rw [affineCarry_append]
        have hc1 : affineCarry [true] = 1 := rfl
        have hl1 : [true].length = 1 := rfl
        rw [hc1, hl1, Nat.mul_one]
      have hstep : 2 * collatzStep n = 3 * n + 1 := by
        unfold collatzStep; rw [hb]; simp; omega
      rw [hcar, Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, Nat.mul_assoc, ih,
          Nat.mul_add, ← Nat.mul_assoc 2, Nat.mul_comm 2 (3 ^ _), Nat.mul_assoc, hstep,
          Nat.add_comm 1 (parityWeight _), Nat.pow_succ, Nat.mul_add, Nat.mul_one,
          Nat.mul_assoc (3 ^ parityWeight _) 3 n]
      omega

theorem eq_parityOfIter_of_nat_affine : ∀ (v : List Bool) (y x : Nat),
    2 ^ v.length * x = 3 ^ parityWeight v * y + affineCarry v ->
    v = parityOfIter v.length y
  | [], _, _, _ => rfl
  | false :: rest, y, x, heq => by
    have hcar : affineCarry (false :: rest) = 2 * affineCarry rest := by
      change affineCarry ([false] ++ rest) = 2 * affineCarry rest
      rw [affineCarry_append]
      have hc0 : affineCarry [false] = 0 := rfl
      have hl1 : [false].length = 1 := rfl
      rw [hc0, hl1, Nat.mul_zero, Nat.zero_add]
    simp only [List.length_cons, parityWeight] at heq ⊢
    rw [hcar, Nat.pow_succ, Nat.mul_comm (2 ^ rest.length) 2, Nat.mul_assoc] at heq
    have hp3_odd : 3 ^ parityWeight rest % 2 = 1 := pow3_odd_nat_sec8 (parityWeight rest)
    have hmod2 : (3 ^ parityWeight rest * y + 2 * affineCarry rest) % 2 = 0 := by
      rw [← heq]; omega
    have hy_ev : y % 2 = 0 := by
      rw [Nat.add_mod, Nat.mul_mod (3 ^ parityWeight rest) y 2, hp3_odd, Nat.one_mul] at hmod2
      omega
    have hb : (y % 2 == 0) = true := decide_eq_true hy_ev
    have hstep : 2 * collatzStep y = y := by
      unfold collatzStep; rw [hb]; simp; omega
    have heq_rest : 2 ^ rest.length * x = 3 ^ parityWeight rest * collatzStep y + affineCarry rest := by
      rw [← hstep, ← Nat.mul_assoc (3 ^ parityWeight rest) 2,
          Nat.mul_comm (3 ^ parityWeight rest) 2, Nat.mul_assoc] at heq
      omega
    have ih := eq_parityOfIter_of_nat_affine rest (collatzStep y) x heq_rest
    simp only [parityOfIter, hb, ite_true, List.cons.injEq, true_and]
    exact ih
  | true :: rest, y, x, heq => by
    have hcar : affineCarry (true :: rest) = 3 ^ parityWeight rest + 2 * affineCarry rest := by
      change affineCarry ([true] ++ rest) = 3 ^ parityWeight rest + 2 * affineCarry rest
      rw [affineCarry_append]
      have hc1 : affineCarry [true] = 1 := rfl
      have hl1 : [true].length = 1 := rfl
      rw [hc1, hl1, Nat.mul_one]
    simp only [List.length_cons, parityWeight] at heq ⊢
    rw [hcar, Nat.pow_succ, Nat.mul_comm (2 ^ rest.length) 2, Nat.mul_assoc,
        Nat.add_comm 1 (parityWeight rest), Nat.pow_succ] at heq
    have hp3_odd : 3 ^ parityWeight rest % 2 = 1 := pow3_odd_nat_sec8 (parityWeight rest)
    have hcomb : 3 ^ parityWeight rest * 3 * y + (3 ^ parityWeight rest + 2 * affineCarry rest) =
        3 ^ parityWeight rest * (3 * y + 1) + 2 * affineCarry rest := by
      rw [Nat.mul_add, Nat.mul_one, Nat.mul_assoc (3 ^ parityWeight rest) 3 y, Nat.add_assoc]
    rw [hcomb] at heq
    have hmod2 : (3 ^ parityWeight rest * (3 * y + 1) + 2 * affineCarry rest) % 2 = 0 := by
      rw [← heq]; omega
    have h3y1_ev : (3 * y + 1) % 2 = 0 := by
      rw [Nat.add_mod, Nat.mul_mod (3 ^ parityWeight rest) (3 * y + 1) 2, hp3_odd, Nat.one_mul] at hmod2
      omega
    have hy_odd : y % 2 = 1 := by omega
    have hb : (y % 2 == 0) = false := decide_eq_false (by omega)
    have hstep : 2 * collatzStep y = 3 * y + 1 := by
      unfold collatzStep; rw [hb]; simp; omega
    have heq_rest : 2 ^ rest.length * x = 3 ^ parityWeight rest * collatzStep y + affineCarry rest := by
      rw [← hstep, ← Nat.mul_assoc (3 ^ parityWeight rest) 2,
          Nat.mul_comm (3 ^ parityWeight rest) 2, Nat.mul_assoc] at heq
      omega
    have ih := eq_parityOfIter_of_nat_affine rest (collatzStep y) x heq_rest
    simp only [parityOfIter, hb, Bool.false_eq_true, ite_false, List.cons.injEq, true_and]
    exact ih

theorem replicate_false_cons_true_inj : ∀ (s1 s2 : Nat) (r1 r2 : List Bool),
    List.replicate s1 false ++ (true :: r1) = List.replicate s2 false ++ (true :: r2) ->
    s1 = s2 ∧ r1 = r2
  | 0, 0, r1, r2, h => by simp at h; exact ⟨rfl, h⟩
  | 0, _ + 1, _, _, h => by simp [List.replicate_succ] at h
  | _ + 1, 0, _, _, h => by simp [List.replicate_succ] at h
  | s1 + 1, s2 + 1, r1, r2, h => by
    simp only [List.replicate_succ, List.cons_append, List.cons.injEq] at h
    rcases replicate_false_cons_true_inj s1 s2 r1 r2 h.2 with ⟨hs, hr⟩
    exact ⟨by omega, hr⟩

theorem append_replicate_false_inj_of_last_true (u1 u2 : List Bool) (s1 s2 : Nat)
    (hl1 : u1.reverse.head? = some true) (hl2 : u2.reverse.head? = some true)
    (heq : u1 ++ List.replicate s1 false = u2 ++ List.replicate s2 false) :
    u1 = u2 ∧ s1 = s2 := by
  have hrev := congrArg List.reverse heq
  rw [List.reverse_append, List.reverse_append, List.reverse_replicate, List.reverse_replicate] at hrev
  cases hr1 : u1.reverse with
  | nil => rw [hr1] at hl1; simp at hl1
  | cons b1 r1 =>
    rw [hr1] at hl1 hrev; simp at hl1; subst hl1
    cases hr2 : u2.reverse with
    | nil => rw [hr2] at hl2; simp at hl2
    | cons b2 r2 =>
      rw [hr2] at hl2 hrev; simp at hl2; subst hl2
      rcases replicate_false_cons_true_inj s1 s2 r1 r2 hrev with ⟨hs, hr_eq⟩
      have hu_eq : u1 = u2 := by
        have hc := congrArg List.reverse (hr1.trans (congrArg (List.cons true) hr_eq |>.trans hr2.symm))
        simpa using hc
      exact ⟨hu_eq, hs⟩

theorem firstHitStepsAux_spec : ∀ (fuel cur : Nat),
    collatzIter fuel cur = 1 ->
    let k0 := firstHitStepsAux fuel cur
    k0 ≤ fuel ∧
    collatzIter k0 cur = 1 ∧
    (∀ j : Nat, j < k0 -> collatzIter j cur ≠ 1)
  | 0, cur, h0 => by
    simp only [firstHitStepsAux]
    refine ⟨Nat.le_refl 0, h0, fun j hj => by omega⟩
  | fuel + 1, cur, hsucc => by
    dsimp only [firstHitStepsAux]
    cases hb : (cur == 1) with
    | true =>
      have hc1 : cur = 1 := of_decide_eq_true hb
      subst hc1
      simp only [ite_true]
      exact ⟨by omega, rfl, fun j hj => by omega⟩
    | false =>
      have hc_ne1 : cur ≠ 1 := of_decide_eq_false hb
      simp only [Bool.false_eq_true, ite_false]
      simp only [collatzIter] at hsucc
      rcases firstHitStepsAux_spec fuel (collatzStep cur) hsucc with ⟨hle, hk1, hmin⟩
      refine ⟨by omega, ?_, ?_⟩
      · rw [Nat.add_comm 1, collatzIter]
        exact hk1
      · intro j hj
        cases j with
        | zero => exact hc_ne1
        | succ j' =>
          simp only [collatzIter]
          exact hmin j' (by omega)

theorem exactBackwardQuotient_of_trail_eq_full (x z trail : Nat) (u : List Bool)
    (hw : parityWeight u ≥ 1) (hx : x % 3 ≠ 0)
    (heq : 2 ^ (u.length + trail) * x = 3 ^ parityWeight u * z + affineCarry u) :
    ∃ q : Nat,
      trail = canonicalSuffixShift u x + q * (2 * 3 ^ (parityWeight u - 1)) ∧
      exactBackwardQuotient x u q = z := by
  let w := parityWeight u
  let P := 2 * 3 ^ (w - 1)
  let M := 3 ^ w
  have hP_pos : P > 0 := by dsimp [P]; have hp := pow3_pos_nat (w - 1); omega
  have hM_pos : M > 0 := pow3_pos_nat w
  obtain ⟨q, a', ha'_lt, htrail_eq⟩ : ∃ q a' : Nat, a' < P ∧ trail = a' + q * P := by
    refine ⟨trail / P, trail % P, Nat.mod_lt trail hP_pos, ?_⟩
    have hdm := (Nat.div_add_mod trail P).symm
    rw [Nat.mul_comm P (trail / P)] at hdm; omega
  have hcongr_trail : (2 ^ (u.length + trail) * x) % M = affineCarry u % M := by
    change 2 ^ (u.length + trail) * x = M * z + affineCarry u at heq
    have hm0 : (M * z) % M = 0 := by rw [Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod]
    rw [heq, Nat.add_mod, hm0, Nat.zero_add, Nat.mod_mod]
  have hcongr_a' : (2 ^ (u.length + a') * x) % M = affineCarry u % M := by
    have hpq : 2 ^ (q * P) % M = 1 := pow2_period_mul_mod_pow3 w hw q
    have hsplit_exp : u.length + trail = q * P + (u.length + a') := by omega
    rw [hsplit_exp, Nat.pow_add, Nat.mul_assoc, Nat.mul_mod, hpq, Nat.one_mul,
        Nat.mod_mod] at hcongr_trail
    exact hcongr_trail
  rcases canonicalSuffixShift_spec_unique u x hw hx with ⟨_, _, huniq⟩
  have ha'_eq : a' = canonicalSuffixShift u x := huniq a' ha'_lt hcongr_a'
  refine ⟨q, by rw [← ha'_eq]; exact htrail_eq, ?_⟩
  unfold exactBackwardQuotient
  change (2 ^ (u.length + (canonicalSuffixShift u x + q * P)) * x - affineCarry u) / M = z
  rw [← ha'_eq, ← htrail_eq, heq]
  change (M * z + affineCarry u - affineCarry u) / M = z
  have hsub : M * z + affineCarry u - affineCarry u = M * z := by omega
  rw [hsub, Nat.mul_comm M z, Nat.mul_div_cancel z hM_pos]

/--
  Theorem T3.14a (`first_hit_one_pair_sound_and_injective`, `[]` axioms):
  Every `(u, q)` satisfying `IsFirstHitOnePair u q` produces an odd integer `y > 1` (`y ≥ 3`)
  converging to `1`, and `(u, q) ↦ exactBackwardQuotient 1 u q` is globally injective on
  `IsFirstHitOnePair`!
-/
theorem first_hit_one_pair_sound_and_injective (u1 u2 : List Bool) (q1 q2 : Nat)
    (h1 : IsFirstHitOnePair u1 q1) (h2 : IsFirstHitOnePair u2 q2) :
    let y1 := exactBackwardQuotient 1 u1 q1
    y1 > 1 ∧ y1 % 2 = 1 ∧ collatzIter (backwardOneTotalSteps u1 q1) y1 = 1 ∧
    (exactBackwardQuotient 1 u1 q1 = exactBackwardQuotient 1 u2 q2 -> u1 = u2 ∧ q1 = q2) := by
  dsimp only
  let y := exactBackwardQuotient 1 u1 q1
  let L1 := backwardOneTotalSteps u1 q1
  let L2 := backwardOneTotalSteps u2 q2
  rcases one_generator_pos_odd_and_reaches_one u1 q1 h1.1 with ⟨hy_ge1, hy_odd, heq1, hiter1⟩
  have hu1_len : u1.length ≥ 1 := by
    cases u1 with
    | nil => have hh := h1.1.1; simp at hh
    | cons _ _ => simp
  have hL1_pos : L1 ≥ 1 := by unfold L1 backwardOneTotalSteps; omega
  have hy_ne1 : y ≠ 1 := h1.2 0 hL1_pos
  have hy_gt1 : y > 1 := by omega
  refine ⟨hy_gt1, hy_odd, hiter1, ?_⟩
  intro hy_eq
  rcases one_generator_pos_odd_and_reaches_one u2 q2 h2.1 with ⟨_, _, heq2, hiter2⟩
  rw [← hy_eq] at heq2 hiter2
  have hL_eq : L1 = L2 := by
    by_cases hlt1 : L1 < L2
    · have hne := h2.2 L1 hlt1
      rw [← hy_eq] at hne
      exact False.elim (hne hiter1)
    · by_cases hlt2 : L2 < L1
      · exact False.elim (h1.2 L2 hlt2 hiter2)
      · omega
  let s1 := canonicalSuffixShift u1 1 + q1 * (2 * 3 ^ (parityWeight u1 - 1))
  let s2 := canonicalSuffixShift u2 1 + q2 * (2 * 3 ^ (parityWeight u2 - 1))
  let v1 := u1 ++ List.replicate s1 false
  let v2 := u2 ++ List.replicate s2 false
  have hv1_len : v1.length = L1 := by
    dsimp [v1, L1]; unfold backwardOneTotalSteps; rw [List.length_append, List.length_replicate]
  have hv2_len : v2.length = L2 := by
    dsimp [v2, L2]; unfold backwardOneTotalSteps; rw [List.length_append, List.length_replicate]
  rcases affineCarry_append_replicate_false u1 s1 with ⟨hwt_v1, hcar_v1⟩
  rcases affineCarry_append_replicate_false u2 s2 with ⟨hwt_v2, hcar_v2⟩
  have hv1_aff : 2 ^ v1.length * 1 = 3 ^ parityWeight v1 * y + affineCarry v1 := by
    rw [Nat.mul_one, hv1_len, hwt_v1, hcar_v1]; exact heq1
  have hv2_aff : 2 ^ v2.length * 1 = 3 ^ parityWeight v2 * y + affineCarry v2 := by
    rw [Nat.mul_one, hv2_len, hwt_v2, hcar_v2]; exact heq2
  have hv1_par := eq_parityOfIter_of_nat_affine v1 y 1 hv1_aff
  have hv2_par := eq_parityOfIter_of_nat_affine v2 y 1 hv2_aff
  rw [hv1_len] at hv1_par
  rw [hv2_len, ← hL_eq] at hv2_par
  have hv12_eq : v1 = v2 := hv1_par.trans hv2_par.symm
  rcases append_replicate_false_inj_of_last_true u1 u2 s1 s2 h1.1.2 h2.1.2 hv12_eq with
    ⟨hu_eq, hs_eq⟩
  subst hu_eq
  dsimp [s1, s2] at hs_eq
  have hP_pos : 2 * 3 ^ (parityWeight u1 - 1) > 0 := by
    have hp := pow3_pos_nat (parityWeight u1 - 1); omega
  have hqP_eq : q1 * (2 * 3 ^ (parityWeight u1 - 1)) = q2 * (2 * 3 ^ (parityWeight u1 - 1)) := by
    omega
  have hq_eq : q1 = q2 := by
    have hd := congrArg (fun z => z / (2 * 3 ^ (parityWeight u1 - 1))) hqP_eq
    rw [Nat.mul_div_cancel q1 hP_pos, Nat.mul_div_cancel q2 hP_pos] at hd
    exact hd
  exact ⟨rfl, hq_eq⟩

/--
  Theorem T3.14b (`convergent_odd_gt1_iff_unique_first_hit_pair`, `[]` axioms):
  An integer `n` satisfies `n > 1 ∧ n % 2 = 1 ∧ ∃ k, collatzIter k n = 1` IF AND ONLY IF
  there exists a UNIQUE `(u, q)` satisfying `IsFirstHitOnePair u q ∧ exactBackwardQuotient 1 u q = n`!
-/
theorem convergent_odd_gt1_iff_unique_first_hit_pair (n : Nat) :
    (n > 1 ∧ n % 2 = 1 ∧ ∃ k : Nat, collatzIter k n = 1) ↔
      ∃ (u : List Bool) (q : Nat),
        IsFirstHitOnePair u q ∧
        exactBackwardQuotient 1 u q = n ∧
        (∀ (u' : List Bool) (q' : Nat),
          IsFirstHitOnePair u' q' -> exactBackwardQuotient 1 u' q' = n -> u' = u ∧ q' = q) := by
  constructor
  · rintro ⟨hn_gt1, hn_odd, ⟨fuel, hfuel⟩⟩
    rcases firstHitStepsAux_spec fuel n hfuel with ⟨_, hk0_eq1, hk0_min⟩
    let k0 := firstHitStepsAux fuel n
    change collatzIter k0 n = 1 at hk0_eq1
    change ∀ j : Nat, j < k0 -> collatzIter j n ≠ 1 at hk0_min
    have hk0_pos : k0 ≥ 1 := by
      cases hk : k0 with
      | zero => rw [hk] at hk0_eq1; simp [collatzIter] at hk0_eq1; omega
      | succ _ => omega
    let v := parityOfIter k0 n
    have hv_len : v.length = k0 := parityOfIter_length k0 n
    have hv_head : v.head? = some true := by
      dsimp [v]
      rw [show k0 = (k0 - 1) + 1 by omega]
      simp only [parityOfIter]
      have hb : (n % 2 == 0) = false := decide_eq_false (by omega)
      rw [hb]; rfl
    have hv_wt_pos : parityWeight v ≥ 1 := by
      cases hv : v with
      | nil => rw [hv] at hv_head; simp at hv_head
      | cons b rest =>
        rw [hv] at hv_head; simp at hv_head; subst hv_head
        simp [parityWeight]
    have hv_aff_nat : 2 ^ k0 * 1 = 3 ^ parityWeight v * n + affineCarry v := by
      have h := nat_affine_of_parityOfIter k0 n
      rw [hk0_eq1] at h
      exact h
    have hstrip := stripTrailingFalse_spec v
    let u := (stripTrailingFalse v).1
    let trail := (stripTrailingFalse v).2
    rcases hstrip with ⟨hrep, hcases, hhead_imp⟩
    change u ++ List.replicate trail false = v at hrep
    have hu_last : u.reverse.head? = some true := by
      rcases hcases with ⟨_, hwt0⟩ | ⟨_, hlast⟩
      · omega
      · exact hlast
    have hu_core : IsCoreParityWord u := ⟨hhead_imp hv_head, hu_last⟩
    rcases affineCarry_append_replicate_false u trail with ⟨hwt_u, hcar_u⟩
    rw [hrep] at hwt_u hcar_u
    have hlen_u : u.length + trail = k0 := by
      have hl := congrArg List.length hrep
      rw [List.length_append, List.length_replicate, hv_len] at hl
      exact hl
    have hu_aff : 2 ^ (u.length + trail) * 1 = 3 ^ parityWeight u * n + affineCarry u := by
      rw [hlen_u, ← hwt_u, ← hcar_u]; exact hv_aff_nat
    have hwu_pos : parityWeight u ≥ 1 := by omega
    rcases exactBackwardQuotient_of_trail_eq_full 1 n trail u hwu_pos (by decide) hu_aff with
      ⟨q, htrail_eq, hy_eq⟩
    have hsteps_eq : backwardOneTotalSteps u q = k0 := by
      unfold backwardOneTotalSteps
      rw [← htrail_eq, hlen_u]
    have hfh : IsFirstHitOnePair u q := by
      refine ⟨hu_core, ?_⟩
      intro j hj
      rw [hsteps_eq] at hj
      rw [hy_eq]
      exact hk0_min j hj
    refine ⟨u, q, hfh, hy_eq, ?_⟩
    intro u' q' hfh' hy_eq'
    exact (first_hit_one_pair_sound_and_injective u' u q' q hfh' hfh).2.2.2
      (hy_eq'.trans hy_eq.symm)
  · rintro ⟨u, q, hfh, hy_eq, _⟩
    rcases first_hit_one_pair_sound_and_injective u u q q hfh hfh with
      ⟨hy_gt1, hy_odd, hiter1, _⟩
    rw [hy_eq] at hy_gt1 hy_odd hiter1
    exact ⟨hy_gt1, hy_odd, ⟨backwardOneTotalSteps u q, hiter1⟩⟩

-- ----------------------------------------------------------------------------
-- T3.15 & T3.16: Forward-Iteration-Free `Mod373248` Range Equivalences &
--                Universal `w ≤ 2` / `true :: false :: _` Disjointness
-- ----------------------------------------------------------------------------

theorem mod373248_one_generator_reaches_one_aux : ∀ (fuel n : Nat),
    Mod373248OneGeneratorRangeProp -> 1 ≤ n -> n ≤ fuel ->
    ∃ k : Nat, collatzIter k n = 1
  | 0, n, _, hn1, hle => by omega
  | fuel + 1, n, hprop, hn1, hle => by
    by_cases hn2 : n ≤ 2
    · have hc : n = 1 ∨ n = 2 := by omega
      rcases hc with rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, by decide⟩
    · by_cases hdesc : ∃ m : Nat, 0 < collatzIter m n ∧ collatzIter m n < n
      · rcases hdesc with ⟨m, hm_pos, hm_lt⟩
        rcases mod373248_one_generator_reaches_one_aux fuel (collatzIter m n) hprop
            (by omega) (by omega) with ⟨k2, hk2⟩
        refine ⟨m + k2, ?_⟩
        rw [collatzIter_add m k2 n]; exact hk2
      · have hnoDesc : ∀ m : Nat, ¬ (0 < collatzIter m n ∧ collatzIter m n < n) :=
          fun m hm => hdesc ⟨m, hm⟩
        have hminReach : ∀ m : Nat, 1 ≤ m -> m < n -> ∃ k1 : Nat, collatzIter k1 m = 1 :=
          fun m hm1 hm_lt => mod373248_one_generator_reaches_one_aux fuel m hprop hm1 (by omega)
        have hs : IsSurvivingMod373248Class n :=
          minimal_counterexample_mod373248_in_10314_classes n (by omega) hnoDesc hminReach
        rcases hprop n hs with ⟨u, q, hu, hy_eq⟩
        rcases one_generator_pos_odd_and_reaches_one u q hu with ⟨_, _, _, hiter1⟩
        rw [hy_eq] at hiter1
        exact ⟨backwardOneTotalSteps u q, hiter1⟩

/--
  Theorem T3.15 (`collatz_standard_iff_mod373248_one_generator_range`):
  Forward-iteration-free global equivalence compressing `CollatzConjectureStandard`
  to `Mod373248OneGeneratorRangeProp` (eliminating BOTH `collatzIter K n` AND
  `3^w`-divisibility side conditions)!
-/
theorem collatz_standard_iff_mod373248_one_generator_range :
    CollatzConjectureStandard ↔ Mod373248OneGeneratorRangeProp := by
  constructor
  · intro hstd n hs
    have hn27 : n ≥ 27 := survivingMod373248_ge_27 n hs
    have hs1296 : IsSurvivingMod1296Class n :=
      (survivingMod46656_imp_mod1296 n (survivingMod373248_imp_mod46656 n hs)).1
    have hn_odd : n % 2 = 1 := by rcases hs1296 with ⟨h16, _, _, _, _⟩; omega
    rcases (collatz_standard_iff_compressed.mp hstd) n (by omega) with ⟨k, hk⟩
    rcases (convergent_odd_gt1_iff_unique_first_hit_pair n).mp ⟨by omega, hn_odd, ⟨k, hk⟩⟩ with
      ⟨u, q, hfh, hy_eq, _⟩
    exact ⟨u, q, hfh.1, hy_eq⟩
  · intro hprop
    rw [collatz_standard_iff_compressed]
    intro n hn
    exact mod373248_one_generator_reaches_one_aux n n hprop (by omega) (Nat.le_refl n)

theorem exactBackwardQuotient_true_false_mod4_eq_one (x : Nat) (rest : List Bool) (q : Nat)
    (hx : x % 3 ≠ 0) :
    exactBackwardQuotient x (true :: false :: rest) q % 4 = 1 := by
  let u := true :: false :: rest
  let y := exactBackwardQuotient x u q
  have hw : parityWeight u ≥ 1 := by dsimp [u]; simp [parityWeight]
  rcases exactBackwardQuotient_spec x u q hw hx with ⟨_, heq, _, hodd_imp⟩
  have hy_odd : y % 2 = 1 := hodd_imp rfl
  let shift := canonicalSuffixShift u x + q * (2 * 3 ^ (parityWeight u - 1))
  let v := u ++ List.replicate shift false
  rcases affineCarry_append_replicate_false u shift with ⟨hwt_v, hcar_v⟩
  have hv_len : v.length = u.length + shift := by
    dsimp [v]; rw [List.length_append, List.length_replicate]
  have hv_aff : 2 ^ v.length * x = 3 ^ parityWeight v * y + affineCarry v := by
    rw [hv_len, hwt_v, hcar_v]; exact heq
  have hv_par := eq_parityOfIter_of_nat_affine v y x hv_aff
  have hv_cons : v = true :: false :: (rest ++ List.replicate shift false) := rfl
  rw [hv_cons] at hv_par
  simp only [List.length_cons, parityOfIter, List.cons.injEq] at hv_par
  have hb0 : (y % 2 == 0) = false := decide_eq_false (by omega)
  rw [hb0] at hv_par
  have hstep_y : collatzStep y = (3 * y + 1) / 2 := collatzStep_of_odd_nat y hy_odd
  have hb1 : (collatzStep y % 2 == 0) = true := by
    cases hb : (collatzStep y % 2 == 0) with
    | true => rfl
    | false => rw [hb] at hv_par; simp at hv_par
  have hstep_ev : ((3 * y + 1) / 2) % 2 = 0 := by
    rw [← hstep_y]; exact of_decide_eq_true hb1
  change y % 4 = 1
  omega

theorem pow2_six_mul_eq_pow64 : ∀ q : Nat, 2 ^ (6 * q) = 64 ^ q
  | 0 => rfl
  | q + 1 => by
    rw [show 6 * (q + 1) = 6 * q + 6 by omega, Nat.pow_add, pow2_six_mul_eq_pow64 q,
        show (2 : Nat) ^ 6 = 64 from rfl, ← Nat.pow_succ]

theorem one_generator_pair_true_closed_form_and_mod16 (q : Nat) :
    canonicalSuffixShift [true, true] 1 = 3 ∧
    9 * exactBackwardQuotient 1 [true, true] q + 5 = 32 * 64 ^ q ∧
    exactBackwardQuotient 1 [true, true] q = (32 * 64 ^ q - 5) / 9 ∧
    exactBackwardQuotient 1 [true, true] q % 16 = 3 := by
  have hcs : canonicalSuffixShift [true, true] 1 = 3 := by decide
  have hsteps : backwardOneTotalSteps [true, true] q = 5 + 6 * q := by
    unfold backwardOneTotalSteps
    rw [hcs]
    have hw2 : parityWeight [true, true] = 2 := rfl
    rw [hw2]
    simp only [List.length_cons, List.length_nil]
    omega
  rcases one_generator_pos_odd_and_reaches_one [true, true] q ⟨rfl, rfl⟩ with ⟨_, _, heq, _⟩
  rw [hsteps, Nat.pow_add, pow2_six_mul_eq_pow64 q] at heq
  have hp9 : 3 ^ parityWeight [true, true] = 9 := rfl
  have hc5 : affineCarry [true, true] = 5 := rfl
  have h32 : (2 : Nat) ^ 5 = 32 := rfl
  rw [hp9, hc5, h32] at heq
  have hlin : 9 * exactBackwardQuotient 1 [true, true] q + 5 = 32 * 64 ^ q := heq.symm
  have hmod16 : (9 * exactBackwardQuotient 1 [true, true] q + 5) % 16 = 0 := by
    rw [hlin, show 32 * 64 ^ q = 16 * (2 * 64 ^ q) by omega, Nat.mul_mod, Nat.mod_self,
        Nat.zero_mul, Nat.zero_mod]
  exact ⟨hcs, hlin, by omega, by omega⟩

/--
  Theorem T3.16a (`one_generator_weight_le_two_never_surviving_mod1296`, `[]` axioms):
  Every core word `u` with `parityWeight u ≤ 2` OR starting with `true :: false :: _`
  has `exactBackwardQuotient 1 u q` unconditionally disjoint from `IsSurvivingMod1296Class`
  (and hence disjoint from `IsSurvivingMod373248Class`) across ALL `q : Nat`!
-/
theorem one_generator_weight_le_two_never_surviving_mod1296 (u : List Bool) (q : Nat)
    (hu : IsCoreParityWord u)
    (hlow : parityWeight u ≤ 2 ∨ ∃ rest : List Bool, u = true :: false :: rest) :
    (∀ x : Nat, x % 3 ≠ 0 -> ∀ rest : List Bool,
      exactBackwardQuotient x (true :: false :: rest) q % 4 = 1) ∧
    exactBackwardQuotient 1 [true, true] q = (32 * 64 ^ q - 5) / 9 ∧
    exactBackwardQuotient 1 [true, true] q % 16 = 3 ∧
    ¬ IsSurvivingMod1296Class (exactBackwardQuotient 1 u q) ∧
    ¬ IsSurvivingMod373248Class (exactBackwardQuotient 1 u q) := by
  rcases one_generator_pair_true_closed_form_and_mod16 q with ⟨_, _, hcf11, hm16_11⟩
  have hnot1296 : ¬ IsSurvivingMod1296Class (exactBackwardQuotient 1 u q) := by
    intro hs1296
    have hm16 : exactBackwardQuotient 1 u q % 16 = 7 ∨
        exactBackwardQuotient 1 u q % 16 = 11 ∨
        exactBackwardQuotient 1 u q % 16 = 15 := hs1296.1
    rcases hlow with hw_le2 | ⟨rest, rfl⟩
    · cases hu_def : u with
      | nil => have hh := hu.1; rw [hu_def] at hh; simp at hh
      | cons b0 t1 =>
        have hb0 : b0 = true := by have hh := hu.1; rw [hu_def] at hh; simp at hh; exact hh
        subst hb0
        cases t1 with
        | nil =>
          subst hu_def
          have hlin := (one_generator_singleton_true_closed_form q).2.2.1
          have hm4 : (3 * exactBackwardQuotient 1 [true] q + 1) % 4 = 0 := by
            rw [hlin, Nat.pow_succ, Nat.mul_mod]; simp
          omega
        | cons b1 t2 =>
          cases b1 with
          | false =>
            subst hu_def
            have hm4 := exactBackwardQuotient_true_false_mod4_eq_one 1 t2 q (by decide)
            omega
          | true =>
            subst hu_def
            cases t2 with
            | nil => omega
            | cons b2 t3 =>
              have hlast : (b2 :: t3).reverse.head? = some true :=
                append_last_true_imp_right_last_true [true, true] (b2 :: t3) hu.2 (by simp)
              have hw_pos : parityWeight (b2 :: t3) ≥ 1 :=
                reverse_head_true_imp_weight_pos (b2 :: t3) hlast
              simp only [parityWeight] at hw_le2
              omega
    · have hm4 := exactBackwardQuotient_true_false_mod4_eq_one 1 rest q (by decide)
      omega
  have hnot373248 : ¬ IsSurvivingMod373248Class (exactBackwardQuotient 1 u q) :=
    fun hs37 => hnot1296 (survivingMod46656_imp_mod1296 _ (survivingMod373248_imp_mod46656 _ hs37)).1
  exact ⟨fun x hx rest => exactBackwardQuotient_true_false_mod4_eq_one x rest q hx,
         hcf11, hm16_11, hnot1296, hnot373248⟩

/--
  Theorem T3.16b (`collatz_standard_iff_mod373248_unique_first_hit_range`):
  Sharpened forward-iteration-free global equivalence restricting every `Mod373248`
  generator witness to its unique first-hit pair `(true :: true :: tail, q)` of weight `≥ 3`!
-/
theorem collatz_standard_iff_mod373248_unique_first_hit_range :
    CollatzConjectureStandard ↔ Mod373248UniqueFirstHitRangeProp := by
  constructor
  · intro hstd n hs
    have hn27 : n ≥ 27 := survivingMod373248_ge_27 n hs
    have hs1296 : IsSurvivingMod1296Class n :=
      (survivingMod46656_imp_mod1296 n (survivingMod373248_imp_mod46656 n hs)).1
    have hn_odd : n % 2 = 1 := by rcases hs1296 with ⟨h16, _, _, _, _⟩; omega
    rcases (collatz_standard_iff_compressed.mp hstd) n (by omega) with ⟨k, hk⟩
    rcases (convergent_odd_gt1_iff_unique_first_hit_pair n).mp ⟨by omega, hn_odd, ⟨k, hk⟩⟩ with
      ⟨u, q, hfh, hy_eq, _⟩
    have hw_ge3 : parityWeight u ≥ 3 := by
      by_cases hge : parityWeight u ≥ 3
      · exact hge
      · have hdisj := (one_generator_weight_le_two_never_surviving_mod1296 u q hfh.1
            (Or.inl (by omega))).2.2.2.2
        rw [hy_eq] at hdisj
        exact False.elim (hdisj hs)
    cases hu_def : u with
    | nil => have hh := hfh.1.1; rw [hu_def] at hh; simp at hh
    | cons b0 t1 =>
      have hb0 : b0 = true := by have hh := hfh.1.1; rw [hu_def] at hh; simp at hh; exact hh
      subst hb0
      cases t1 with
      | nil => subst hu_def; simp [parityWeight] at hw_ge3
      | cons b1 tail =>
        cases b1 with
        | false =>
          subst hu_def
          have hdisj := (one_generator_weight_le_two_never_surviving_mod1296
              (true :: false :: tail) q hfh.1 (Or.inr ⟨tail, rfl⟩)).2.2.2.2
          rw [hy_eq] at hdisj
          exact False.elim (hdisj hs)
        | true =>
          subst hu_def
          exact ⟨tail, q, hfh, hw_ge3, hy_eq⟩
  · intro hprop
    apply collatz_standard_iff_mod373248_one_generator_range.mpr
    intro n hs
    rcases hprop n hs with ⟨tail, q, hfh, _, hy_eq⟩
    exact ⟨true :: true :: tail, q, hfh.1, hy_eq⟩

-- ============================================================================
-- SECTION 9: Track 2 Wave 3 — `bbchallenge` / Myhill–Nerode `2^w` & `3^w`
--            Regular Invariant Barrier, All-Dimension `∀ d ≥ 1` Coordinatewise-
--            Monotone Upper-Triangular Collapse, & Infinite Parametric Dyadic /
--            Triadic Minimal-Counterexample Excluded Families (`#28/#29`, `T2.7`–`T2.9`)
-- ============================================================================

-- ----------------------------------------------------------------------------
-- T2.7: Exact `1`-Equation Parity Language, `2^w` Binary-Gap Family,
--       `3^w` Myhill–Nerode Witness Family, & `∀ N ≥ 1` Finite-DFA Refuter
-- ----------------------------------------------------------------------------

/--
  Exact `1`-convergent Diophantine parity language (`IsValidOneEquationWord`):
  `v ∈ L_OneEq` iff `∃ n ≥ 1, 2 ^ v.length = 3 ^ parityWeight v * n + affineCarry v`.
-/
def IsValidOneEquationWord (v : List Bool) : Prop :=
  ∃ n : Nat, n ≥ 1 ∧ 2 ^ v.length = 3 ^ parityWeight v * n + affineCarry v

theorem affineCarry_eq_zero_of_weight_zero_sec9 : ∀ (v : List Bool),
    parityWeight v = 0 -> affineCarry v = 0
  | [], _ => rfl
  | false :: rest, hw => by
    simp only [parityWeight] at hw
    have hcar : affineCarry (false :: rest) = 2 * affineCarry rest := by
      change affineCarry ([false] ++ rest) = 2 * affineCarry rest
      rw [affineCarry_append]
      have hc0 : affineCarry [false] = 0 := rfl
      have hl1 : [false].length = 1 := rfl
      rw [hc0, hl1, Nat.mul_zero, Nat.zero_add]
    rw [hcar, affineCarry_eq_zero_of_weight_zero_sec9 rest hw, Nat.mul_zero]
  | true :: _, hw => by simp [parityWeight] at hw

theorem validOneEquationWord_of_weight_zero (v : List Bool) (hw : parityWeight v = 0) :
    IsValidOneEquationWord v := by
  refine ⟨2 ^ v.length, pow_pos_base 2 (by decide) v.length, ?_⟩
  rw [hw, affineCarry_eq_zero_of_weight_zero_sec9 v hw]
  simp

theorem validOneEquationWord_append_replicate_false_iff (u : List Bool)
    (hw : parityWeight u ≥ 1) (k : Nat) :
    IsValidOneEquationWord (u ++ List.replicate k false) ↔
      ∃ q : Nat, k = canonicalSuffixShift u 1 + q * (2 * 3 ^ (parityWeight u - 1)) := by
  rcases affineCarry_append_replicate_false u k with ⟨hwt, hcar⟩
  have hlen : (u ++ List.replicate k false).length = u.length + k := by
    rw [List.length_append, List.length_replicate]
  constructor
  · rintro ⟨n, _, heq⟩
    rw [hlen, hwt, hcar] at heq
    have heq1 : 2 ^ (u.length + k) * 1 = 3 ^ parityWeight u * n + affineCarry u := by
      rw [Nat.mul_one]; exact heq
    rcases exactBackwardQuotient_of_trail_eq_full 1 n k u hw (by decide) heq1 with ⟨q, hk_eq, _⟩
    exact ⟨q, hk_eq⟩
  · rintro ⟨q, rfl⟩
    rcases exactBackwardQuotient_spec 1 u q hw (by decide) with ⟨hy_pos, heq, _, _⟩
    rw [Nat.mul_one] at heq
    refine ⟨exactBackwardQuotient 1 u q, hy_pos, ?_⟩
    rw [hlen, hwt, hcar]
    exact heq

def binGapStep (b : Bool) : List Bool :=
  if b then [true, false] else [true]

def binGapWord : List Bool -> List Bool
  | [] => []
  | b :: bs => binGapStep b ++ binGapWord bs

theorem binGapWord_weight : ∀ (bs : List Bool), parityWeight (binGapWord bs) = bs.length
  | [] => rfl
  | b :: bs => by
    simp only [binGapWord, parityWeight_append, List.length_cons]
    have hs : parityWeight (binGapStep b) = 1 := by cases b <;> rfl
    rw [hs, binGapWord_weight bs, Nat.add_comm 1 bs.length]

theorem binGapStep_carry (b : Bool) : affineCarry (binGapStep b) = 1 := by
  cases b <;> rfl

theorem add_right_cancel_mod_sec9 (M a b K : Nat) (hM : M > 0)
    (hmod : (a + K) % M = (b + K) % M) : a % M = b % M := by
  let pad := M * K - K
  have hpad : K + pad = M * K := by
    dsimp [pad]
    have hm : 1 * K ≤ M * K := Nat.mul_le_mul_right K hM
    omega
  have hcancel : ∀ z : Nat, ((z + K) % M + pad) % M = z % M := by
    intro z
    rw [Nat.mod_add_mod, Nat.add_assoc, hpad, Nat.add_mod,
        Nat.mul_mod M K M, Nat.mod_self, Nat.zero_mul, Nat.zero_mod, Nat.add_zero, Nat.mod_mod]
  simpa only [hcancel] using congrArg (fun t => (t + pad) % M) hmod

theorem mul_mod_mul_left_sec9 (M A B : Nat) (hM : M > 0) (hB : B > 0) :
    (M * A) % (M * B) = M * (A % B) := by
  let q := A / B
  let r := A % B
  have hr : r < B := Nat.mod_lt A hB
  have hA : A = B * q + r := (Nat.div_add_mod A B).symm
  have hMr : M * r < M * B := Nat.mul_lt_mul_of_pos_left hr hM
  have hMA : M * A = (M * B) * q + M * r := by
    rw [hA, Nat.mul_add, Nat.mul_assoc]
  rw [hMA, Nat.add_mod, Nat.mul_mod (M * B) q (M * B), Nat.mod_self,
      Nat.zero_mul, Nat.zero_mod, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hMr]

theorem binGapWord_cross_congr_inj : ∀ (bs1 bs2 : List Bool),
    bs1.length = bs2.length ->
    (2 ^ (binGapWord bs2).length * affineCarry (binGapWord bs1)) % 3 ^ bs1.length =
      (2 ^ (binGapWord bs1).length * affineCarry (binGapWord bs2)) % 3 ^ bs1.length ->
    bs1 = bs2
  | [], [], _, _ => rfl
  | [], _ :: _, hlen, _ => by simp at hlen
  | _ :: _, [], hlen, _ => by simp at hlen
  | b1 :: r1, b2 :: r2, hlen, hmod => by
    simp only [List.length_cons] at hlen hmod
    have hr_len : r1.length = r2.length := by omega
    let w := r1.length
    let u := binGapWord r1
    let v := binGapWord r2
    let s1 := (binGapStep b1).length
    let s2 := (binGapStep b2).length
    have hwu : parityWeight u = w := binGapWord_weight r1
    have hwv : parityWeight v = w := by rw [binGapWord_weight r2, ← hr_len]
    have hcar1 : affineCarry (binGapWord (b1 :: r1)) = 3 ^ w + 2 ^ s1 * affineCarry u := by
      simp only [binGapWord]
      rw [affineCarry_append, hwu, binGapStep_carry b1, Nat.mul_one]
    have hcar2 : affineCarry (binGapWord (b2 :: r2)) = 3 ^ w + 2 ^ s2 * affineCarry v := by
      simp only [binGapWord]
      rw [affineCarry_append, hwv, binGapStep_carry b2, Nat.mul_one]
    have hlen1 : (binGapWord (b1 :: r1)).length = s1 + u.length := by
      simp [binGapWord, List.length_append, s1, u]
    have hlen2 : (binGapWord (b2 :: r2)).length = s2 + v.length := by
      simp [binGapWord, List.length_append, s2, v]
    change (2 ^ (binGapWord (b2 :: r2)).length * affineCarry (binGapWord (b1 :: r1))) % 3 ^ (w + 1) =
      (2 ^ (binGapWord (b1 :: r1)).length * affineCarry (binGapWord (b2 :: r2))) % 3 ^ (w + 1) at hmod
    rw [hlen1, hlen2, hcar1, hcar2] at hmod
    have hexp_lhs : 2 ^ (s2 + v.length) * (3 ^ w + 2 ^ s1 * affineCarry u) =
        3 ^ w * 2 ^ (s2 + v.length) + 2 ^ (s1 + s2) * (2 ^ v.length * affineCarry u) := by
      have hmul : 2 ^ (s2 + v.length) * (2 ^ s1 * affineCarry u) =
          2 ^ (s1 + s2) * (2 ^ v.length * affineCarry u) := by
        calc
          2 ^ (s2 + v.length) * (2 ^ s1 * affineCarry u)
              = (2 ^ (s2 + v.length) * 2 ^ s1) * affineCarry u := (Nat.mul_assoc _ _ _).symm
          _ = 2 ^ (s2 + v.length + s1) * affineCarry u := by rw [← Nat.pow_add]
          _ = 2 ^ ((s1 + s2) + v.length) * affineCarry u := by
                rw [show s2 + v.length + s1 = (s1 + s2) + v.length by omega]
          _ = (2 ^ (s1 + s2) * 2 ^ v.length) * affineCarry u := by rw [Nat.pow_add]
          _ = 2 ^ (s1 + s2) * (2 ^ v.length * affineCarry u) := Nat.mul_assoc _ _ _
      rw [Nat.mul_add, Nat.mul_comm (2 ^ (s2 + v.length)) (3 ^ w), hmul]
    have hexp_rhs : 2 ^ (s1 + u.length) * (3 ^ w + 2 ^ s2 * affineCarry v) =
        3 ^ w * 2 ^ (s1 + u.length) + 2 ^ (s1 + s2) * (2 ^ u.length * affineCarry v) := by
      have hmul : 2 ^ (s1 + u.length) * (2 ^ s2 * affineCarry v) =
          2 ^ (s1 + s2) * (2 ^ u.length * affineCarry v) := by
        calc
          2 ^ (s1 + u.length) * (2 ^ s2 * affineCarry v)
              = (2 ^ (s1 + u.length) * 2 ^ s2) * affineCarry v := (Nat.mul_assoc _ _ _).symm
          _ = 2 ^ (s1 + u.length + s2) * affineCarry v := by rw [← Nat.pow_add]
          _ = 2 ^ ((s1 + s2) + u.length) * affineCarry v := by
                rw [show s1 + u.length + s2 = (s1 + s2) + u.length by omega]
          _ = (2 ^ (s1 + s2) * 2 ^ u.length) * affineCarry v := by rw [Nat.pow_add]
          _ = 2 ^ (s1 + s2) * (2 ^ u.length * affineCarry v) := Nat.mul_assoc _ _ _
      rw [Nat.mul_add, Nat.mul_comm (2 ^ (s1 + u.length)) (3 ^ w), hmul]
    rw [hexp_lhs, hexp_rhs] at hmod
    have hr_eq : r1 = r2 := by
      cases hw_c : w with
      | zero =>
        cases r1 with
        | nil =>
          cases r2 with
          | nil => rfl
          | cons _ _ => simp at hr_len
        | cons _ _ => dsimp [w] at hw_c; simp at hw_c
      | succ w' =>
        have hw_pos : w ≥ 1 := by omega
        have hp_succ : 3 ^ (w + 1) = 3 ^ w * 3 := Nat.pow_succ 3 w
        have hmod_w :
            (3 ^ w * 2 ^ (s2 + v.length) + 2 ^ (s1 + s2) * (2 ^ v.length * affineCarry u)) % 3 ^ w =
            (3 ^ w * 2 ^ (s1 + u.length) + 2 ^ (s1 + s2) * (2 ^ u.length * affineCarry v)) % 3 ^ w := by
          rw [← mod_mul_mod_eq _ (3 ^ w) 3, ← mod_mul_mod_eq (3 ^ w * 2 ^ (s1 + u.length) + _) (3 ^ w) 3,
              ← hp_succ, hmod]
        have hm0_l : (3 ^ w * 2 ^ (s2 + v.length)) % 3 ^ w = 0 := by
          rw [Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod]
        have hm0_r : (3 ^ w * 2 ^ (s1 + u.length)) % 3 ^ w = 0 := by
          rw [Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod]
        rw [Nat.add_mod, hm0_l, Nat.zero_add, Nat.mod_mod,
            Nat.add_mod (3 ^ w * 2 ^ (s1 + u.length)), hm0_r, Nat.zero_add, Nat.mod_mod] at hmod_w
        have hsub_mod := coprime_pow2_cancel_pow3 (s1 + s2) w
          (2 ^ v.length * affineCarry u) (2 ^ u.length * affineCarry v) hw_pos hmod_w
        exact binGapWord_cross_congr_inj r1 r2 hr_len hsub_mod
    subst hr_eq
    dsimp [u, v, w] at hmod
    have hM_pos : 3 ^ (r1.length + 1) > 0 := pow3_pos_nat (r1.length + 1)
    have hlead_mod := add_right_cancel_mod_sec9 (3 ^ (r1.length + 1))
      (3 ^ r1.length * 2 ^ (s2 + (binGapWord r1).length))
      (3 ^ r1.length * 2 ^ (s1 + (binGapWord r1).length))
      (2 ^ (s1 + s2) * (2 ^ (binGapWord r1).length * affineCarry (binGapWord r1)))
      hM_pos hmod
    rw [Nat.pow_succ 3 r1.length,
        mul_mod_mul_left_sec9 (3 ^ r1.length) _ 3 (pow3_pos_nat r1.length) (by decide),
        mul_mod_mul_left_sec9 (3 ^ r1.length) _ 3 (pow3_pos_nat r1.length) (by decide)] at hlead_mod
    have hmod3 := nat_mul_left_cancel_pos (3 ^ r1.length) _ _ (pow3_pos_nat r1.length) hlead_mod
    have hmod3_comm :
        (2 ^ (binGapWord r1).length * 2 ^ s2) % 3 =
        (2 ^ (binGapWord r1).length * 2 ^ s1) % 3 := by
      rw [← Nat.pow_add, ← Nat.pow_add, Nat.add_comm _ s2, Nat.add_comm _ s1]
      exact hmod3
    have hs_mod3 : 2 ^ s2 % 3 = 2 ^ s1 % 3 :=
      coprime_pow2_cancel_pow3 (binGapWord r1).length 1 (2 ^ s2) (2 ^ s1) (by decide) hmod3_comm
    have hb_eq : b1 = b2 := by
      dsimp [s1, s2, binGapStep] at hs_mod3
      cases b1 <;> cases b2 <;> simp at hs_mod3 ⊢
    rw [hb_eq]

/--
  Theorem T2.7a (`binGapWord_pairwise_myhill_nerode_distinguished`, `∀ w ≥ 1`):
  Every pair of distinct length-`w` binary words `bs1 ≠ bs2` (`w ≥ 1`) maps to fixed-weight-`w`
  parity words `u1 = binGapWord bs1`, `u2 = binGapWord bs2` with distinct `canonicalSuffixShift · 1`,
  separated in `IsValidOneEquationWord` by `s = List.replicate (canonicalSuffixShift u1 1) false`!
-/
theorem binGapWord_pairwise_myhill_nerode_distinguished (bs1 bs2 : List Bool)
    (hlen : bs1.length = bs2.length) (hw : bs1.length ≥ 1) (hne : bs1 ≠ bs2) :
    let u1 := binGapWord bs1
    let u2 := binGapWord bs2
    let k := canonicalSuffixShift u1 1
    parityWeight u1 = bs1.length ∧
    parityWeight u2 = bs1.length ∧
    canonicalSuffixShift u1 1 ≠ canonicalSuffixShift u2 1 ∧
    IsValidOneEquationWord (u1 ++ List.replicate k false) ∧
    ¬ IsValidOneEquationWord (u2 ++ List.replicate k false) := by
  dsimp only
  let w := bs1.length
  let u1 := binGapWord bs1
  let u2 := binGapWord bs2
  have hw1 : parityWeight u1 = w := binGapWord_weight bs1
  have hw2 : parityWeight u2 = w := by rw [binGapWord_weight bs2, ← hlen]
  have hshift_ne : canonicalSuffixShift u1 1 ≠ canonicalSuffixShift u2 1 := by
    intro heq_s
    let a := canonicalSuffixShift u1 1
    rcases canonicalSuffixShift_spec_unique u1 1 (by omega) (by decide) with ⟨_, hc1, _⟩
    rcases canonicalSuffixShift_spec_unique u2 1 (by omega) (by decide) with ⟨_, hc2, _⟩
    rw [Nat.mul_one, hw1] at hc1
    rw [Nat.mul_one, hw2, ← heq_s] at hc2
    have hcross : (2 ^ u2.length * affineCarry u1) % 3 ^ w =
        (2 ^ u1.length * affineCarry u2) % 3 ^ w := by
      calc
        (2 ^ u2.length * affineCarry u1) % 3 ^ w
            = ((2 ^ u2.length % 3 ^ w) * (affineCarry u1 % 3 ^ w)) % 3 ^ w := Nat.mul_mod _ _ _
        _ = ((2 ^ u2.length % 3 ^ w) * (2 ^ (u1.length + a) % 3 ^ w)) % 3 ^ w := by rw [← hc1]
        _ = (2 ^ (u1.length + u2.length + a)) % 3 ^ w := by
              rw [← Nat.mul_mod, ← Nat.pow_add,
                  show u2.length + (u1.length + a) = u1.length + u2.length + a by omega]
        _ = ((2 ^ u1.length % 3 ^ w) * (2 ^ (u2.length + a) % 3 ^ w)) % 3 ^ w := by
              rw [← Nat.mul_mod, ← Nat.pow_add,
                  show u1.length + (u2.length + a) = u1.length + u2.length + a by omega]
        _ = ((2 ^ u1.length % 3 ^ w) * (affineCarry u2 % 3 ^ w)) % 3 ^ w := by rw [hc2]
        _ = (2 ^ u1.length * affineCarry u2) % 3 ^ w := (Nat.mul_mod _ _ _).symm
    exact hne (binGapWord_cross_congr_inj bs1 bs2 hlen hcross)
  let k := canonicalSuffixShift u1 1
  have hval1 : IsValidOneEquationWord (u1 ++ List.replicate k false) :=
    (validOneEquationWord_append_replicate_false_iff u1 (by omega) k).mpr ⟨0, by simp [k]⟩
  have hnval2 : ¬ IsValidOneEquationWord (u2 ++ List.replicate k false) := by
    intro hv2
    rcases (validOneEquationWord_append_replicate_false_iff u2 (by omega) k).mp hv2 with ⟨q, hq_eq⟩
    have hk_lt : k < 2 * 3 ^ (parityWeight u2 - 1) := by
      rw [hw2, ← hw1]
      exact (canonicalSuffixShift_spec_unique u1 1 (by omega) (by decide)).1
    cases q with
    | zero => simp [k] at hq_eq; exact hshift_ne hq_eq
    | succ q' =>
      rw [Nat.succ_mul] at hq_eq
      omega
  exact ⟨hw1, hw2, hshift_ne, hval1, hnval2⟩

def mnListAt : List (List Bool) -> Nat -> List Bool
  | [], _ => []
  | u :: _, 0 => u
  | _ :: us, i + 1 => mnListAt us i

theorem mnListAt_append_left : ∀ (L1 L2 : List (List Bool)) (i : Nat),
    i < L1.length -> mnListAt (L1 ++ L2) i = mnListAt L1 i
  | [], _, _, hi => by simp at hi
  | u :: _, _, 0, _ => rfl
  | _ :: us, L2, i + 1, hi => by
    simp only [List.length_cons] at hi
    exact mnListAt_append_left us L2 i (by omega)

theorem mnListAt_append_right : ∀ (L1 L2 : List (List Bool)) (i : Nat),
    L1.length ≤ i -> mnListAt (L1 ++ L2) i = mnListAt L2 (i - L1.length)
  | [], L2, i, _ => by simp
  | _ :: us, L2, 0, hle => by simp at hle
  | _ :: us, L2, i + 1, hle => by
    simp only [List.length_cons] at hle ⊢
    rw [show i + 1 - (us.length + 1) = i - us.length by omega]
    exact mnListAt_append_right us L2 i (by omega)

def mnWeightBlockAux (j start : Nat) : Nat -> List (List Bool)
  | 0 => []
  | count + 1 =>
    (List.replicate j true ++ List.replicate start false) :: mnWeightBlockAux j (start + 1) count

def mnWeightBlock (j : Nat) : List (List Bool) :=
  mnWeightBlockAux j 0 (2 * 3 ^ (j - 1))

def mnWitnessFamily : Nat -> List (List Bool)
  | 0 => [[]]
  | w + 1 => mnWitnessFamily w ++ mnWeightBlock (w + 1)

theorem mnWeightBlockAux_length (j : Nat) : ∀ (count start : Nat),
    (mnWeightBlockAux j start count).length = count
  | 0, _ => rfl
  | count + 1, start => by
    simp [mnWeightBlockAux, mnWeightBlockAux_length j count (start + 1)]

theorem mnWeightBlockAux_at (j : Nat) : ∀ (count start idx : Nat),
    idx < count ->
    mnListAt (mnWeightBlockAux j start count) idx =
      List.replicate j true ++ List.replicate (start + idx) false
  | 0, _, _, hlt => by omega
  | _ + 1, start, 0, _ => by simp [mnWeightBlockAux, mnListAt]
  | count + 1, start, idx + 1, hlt => by
    simp only [mnWeightBlockAux, mnListAt]
    rw [mnWeightBlockAux_at j count (start + 1) idx (by omega)]
    rw [show start + 1 + idx = start + (idx + 1) by omega]

theorem mnWitnessFamily_length : ∀ w : Nat, (mnWitnessFamily w).length = 3 ^ w
  | 0 => rfl
  | w + 1 => by
    simp only [mnWitnessFamily, List.length_append, mnWitnessFamily_length w,
               mnWeightBlock, Nat.add_sub_cancel, mnWeightBlockAux_length, Nat.pow_succ]
    omega

theorem mnWitnessFamily_weight_le : ∀ (w i : Nat),
    i < (mnWitnessFamily w).length -> parityWeight (mnListAt (mnWitnessFamily w) i) ≤ w
  | 0, i, hi => by
    rw [mnWitnessFamily_length 0] at hi
    have hi0 : i = 0 := by omega
    subst hi0; exact Nat.le_refl 0
  | w + 1, i, hi => by
    simp only [mnWitnessFamily] at hi ⊢
    by_cases hlt : i < (mnWitnessFamily w).length
    · rw [mnListAt_append_left _ _ i hlt]
      exact Nat.le_trans (mnWitnessFamily_weight_le w i hlt) (by omega)
    · rw [mnListAt_append_right _ _ i (by omega)]
      simp only [List.length_append, mnWeightBlock, Nat.add_sub_cancel, mnWeightBlockAux_length] at hi
      let e := i - (mnWitnessFamily w).length
      have he_lt : e < 2 * 3 ^ w := by dsimp [e]; omega
      change parityWeight (mnListAt (mnWeightBlockAux (w + 1) 0 (2 * 3 ^ w)) e) ≤ w + 1
      rw [mnWeightBlockAux_at (w + 1) (2 * 3 ^ w) 0 e he_lt, Nat.zero_add,
          (affineCarry_append_replicate_false (List.replicate (w + 1) true) e).1,
          parityWeight_replicate_true_local]
      exact Nat.le_refl _

theorem replicate_false_append_replicate_false : ∀ (a b : Nat),
    List.replicate a false ++ List.replicate b false = List.replicate (a + b) false
  | 0, b => by simp
  | a + 1, b => by
    rw [List.replicate_succ, List.cons_append, replicate_false_append_replicate_false a b,
        Nat.succ_add, List.replicate_succ]

theorem separate_diff_weight_zero_suffixes (u1 u2 : List Bool)
    (hw1 : parityWeight u1 = 0) (hw2 : parityWeight u2 ≥ 1) :
    ∃ k : Nat, IsValidOneEquationWord (u1 ++ List.replicate k false) ∧
      ¬ IsValidOneEquationWord (u2 ++ List.replicate k false) := by
  let a2 := canonicalSuffixShift u2 1
  let k := if a2 = 0 then 1 else 0
  have hk_ne : k ≠ a2 := by dsimp [k]; by_cases h0 : a2 = 0 <;> simp [h0] <;> omega
  have hP2_ge2 : 2 * 3 ^ (parityWeight u2 - 1) ≥ 2 := by
    have hp := pow3_pos_nat (parityWeight u2 - 1); omega
  have hk_lt : k < 2 * 3 ^ (parityWeight u2 - 1) := by
    dsimp [k]; by_cases h0 : a2 = 0 <;> simp [h0] <;> omega
  refine ⟨k, ?_, ?_⟩
  · apply validOneEquationWord_of_weight_zero
    rw [(affineCarry_append_replicate_false u1 k).1]; exact hw1
  · intro hv2
    rcases (validOneEquationWord_append_replicate_false_iff u2 hw2 k).mp hv2 with ⟨q, hq⟩
    cases q with
    | zero => simp at hq; exact hk_ne hq
    | succ _ => rw [Nat.succ_mul] at hq; omega

theorem pow3_strict_mono_step (a b : Nat) (hlt : a < b) : 3 * 3 ^ a ≤ 3 ^ b := by
  have hb_eq : b = (a + 1) + (b - (a + 1)) := by omega
  rw [hb_eq, Nat.pow_add, Nat.pow_succ 3 a, Nat.mul_comm (3 ^ a) 3]
  have hp := pow3_pos_nat (b - (a + 1))
  have hm := Nat.mul_le_mul_left (3 * 3 ^ a) hp
  simpa using hm

theorem separate_strict_lt_weights (u1 u2 : List Bool)
    (hw1_pos : parityWeight u1 ≥ 1) (hlt_w : parityWeight u1 < parityWeight u2) :
    ∃ k : Nat, IsValidOneEquationWord (u1 ++ List.replicate k false) ∧
      ¬ IsValidOneEquationWord (u2 ++ List.replicate k false) := by
  let P1 := 2 * 3 ^ (parityWeight u1 - 1)
  let P2 := 2 * 3 ^ (parityWeight u2 - 1)
  have h3_le : 3 * 3 ^ (parityWeight u1 - 1) ≤ 3 ^ (parityWeight u2 - 1) :=
    pow3_strict_mono_step (parityWeight u1 - 1) (parityWeight u2 - 1) (by omega)
  have hP2_ge : P2 ≥ 3 * P1 := by dsimp [P1, P2]; omega
  let a1 := canonicalSuffixShift u1 1
  let a2 := canonicalSuffixShift u2 1
  have ha1_lt : a1 < P1 := (canonicalSuffixShift_spec_unique u1 1 hw1_pos (by decide)).1
  have hP1_pos : P1 > 0 := by dsimp [P1]; have hp := pow3_pos_nat (parityWeight u1 - 1); omega
  let q1 := if a1 = a2 then 1 else 0
  let k := a1 + q1 * P1
  have hk_ne_a2 : k ≠ a2 := by
    dsimp [k, q1]
    by_cases heq : a1 = a2
    · simp [heq]; omega
    · simp [heq]
  have hk_lt_P2 : k < P2 := by
    dsimp [k, q1]
    by_cases heq : a1 = a2 <;> simp [heq] <;> omega
  refine ⟨k, ?_, ?_⟩
  · exact (validOneEquationWord_append_replicate_false_iff u1 hw1_pos k).mpr ⟨q1, rfl⟩
  · intro hv2
    rcases (validOneEquationWord_append_replicate_false_iff u2 (by omega) k).mp hv2 with ⟨q2, hq2⟩
    change k = a2 + q2 * P2 at hq2
    cases q2 with
    | zero => simp at hq2; exact hk_ne_a2 hq2
    | succ _ => rw [Nat.succ_mul] at hq2; omega

theorem separate_same_core_lt_exp (j e1 e2 : Nat)
    (hj : j ≥ 1) (hlt : e1 < e2) (he2_lt : e2 < 2 * 3 ^ (j - 1)) :
    let u1 := List.replicate j true ++ List.replicate e1 false
    let u2 := List.replicate j true ++ List.replicate e2 false
    ∃ k : Nat, IsValidOneEquationWord (u1 ++ List.replicate k false) ∧
      ¬ IsValidOneEquationWord (u2 ++ List.replicate k false) := by
  dsimp only
  let c := List.replicate j true
  let u1 := c ++ List.replicate e1 false
  let u2 := c ++ List.replicate e2 false
  have hwc : parityWeight c = j := parityWeight_replicate_true_local j
  have hwu1 : parityWeight u1 = j := by
    rw [(affineCarry_append_replicate_false c e1).1, hwc]
  let k := canonicalSuffixShift u1 1
  refine ⟨k, ?_, ?_⟩
  · exact (validOneEquationWord_append_replicate_false_iff u1 (by omega) k).mpr ⟨0, by simp [k]⟩
  · intro hv2
    have hv1 : IsValidOneEquationWord (u1 ++ List.replicate k false) :=
      (validOneEquationWord_append_replicate_false_iff u1 (by omega) k).mpr ⟨0, by simp [k]⟩
    have hc1 : u1 ++ List.replicate k false = c ++ List.replicate (e1 + k) false := by
      dsimp [u1]; rw [List.append_assoc, replicate_false_append_replicate_false]
    have hc2 : u2 ++ List.replicate k false = c ++ List.replicate (e2 + k) false := by
      dsimp [u2]; rw [List.append_assoc, replicate_false_append_replicate_false]
    rw [hc1] at hv1
    rw [hc2] at hv2
    rcases (validOneEquationWord_append_replicate_false_iff c (by omega) (e1 + k)).mp hv1 with ⟨q1, hq1⟩
    rcases (validOneEquationWord_append_replicate_false_iff c (by omega) (e2 + k)).mp hv2 with ⟨q2, hq2⟩
    rw [hwc] at hq1 hq2
    let P := 2 * 3 ^ (j - 1)
    change e1 + k = canonicalSuffixShift c 1 + q1 * P at hq1
    change e2 + k = canonicalSuffixShift c 1 + q2 * P at hq2
    have hlt1 : q1 * P < q2 * P := by omega
    have hlt2 : q2 * P < (q1 + 1) * P := by rw [Nat.add_mul, Nat.one_mul]; omega
    have hq1_lt_q2 : q1 < q2 := by
      by_cases h : q1 < q2
      · exact h
      · have hm := Nat.mul_le_mul_right P (by omega : q2 ≤ q1); omega
    have hq2_lt_succ : q2 < q1 + 1 := by
      by_cases h : q2 < q1 + 1
      · exact h
      · have hm := Nat.mul_le_mul_right P (by omega : q1 + 1 ≤ q2); omega
    omega

theorem mnWitnessFamily_lt_sep : ∀ (w i1 i2 : Nat),
    i1 < i2 -> i2 < (mnWitnessFamily w).length ->
    ∃ k : Nat,
      ¬ (IsValidOneEquationWord (mnListAt (mnWitnessFamily w) i1 ++ List.replicate k false) ↔
         IsValidOneEquationWord (mnListAt (mnWitnessFamily w) i2 ++ List.replicate k false))
  | 0, i1, i2, h12, hi2 => by
    rw [mnWitnessFamily_length 0] at hi2; omega
  | w + 1, i1, i2, h12, hi2 => by
    let N0 := (mnWitnessFamily w).length
    have hi2_tot : i2 < N0 + 2 * 3 ^ w := by
      simp only [mnWitnessFamily, List.length_append, mnWeightBlock,
                 Nat.add_sub_cancel, mnWeightBlockAux_length] at hi2
      exact hi2
    by_cases h2_lt : i2 < N0
    · rcases mnWitnessFamily_lt_sep w i1 i2 h12 h2_lt with ⟨k, hsep⟩
      refine ⟨k, ?_⟩
      simp only [mnWitnessFamily]
      rw [mnListAt_append_left _ _ i1 (by omega), mnListAt_append_left _ _ i2 h2_lt]
      exact hsep
    · by_cases h1_lt : i1 < N0
      · have hw1_le : parityWeight (mnListAt (mnWitnessFamily w) i1) ≤ w :=
          mnWitnessFamily_weight_le w i1 h1_lt
        let e2 := i2 - N0
        have he2_lt : e2 < 2 * 3 ^ w := by dsimp [e2]; omega
        have hu2_eq : mnListAt (mnWitnessFamily (w + 1)) i2 =
            List.replicate (w + 1) true ++ List.replicate e2 false := by
          simp only [mnWitnessFamily]
          rw [mnListAt_append_right _ _ i2 (by omega)]
          change mnListAt (mnWeightBlockAux (w + 1) 0 (2 * 3 ^ w)) e2 = _
          rw [mnWeightBlockAux_at (w + 1) (2 * 3 ^ w) 0 e2 he2_lt, Nat.zero_add]
        have hu1_eq : mnListAt (mnWitnessFamily (w + 1)) i1 = mnListAt (mnWitnessFamily w) i1 := by
          simp only [mnWitnessFamily]
          exact mnListAt_append_left _ _ i1 h1_lt
        have hw2_eq : parityWeight (mnListAt (mnWitnessFamily (w + 1)) i2) = w + 1 := by
          rw [hu2_eq, (affineCarry_append_replicate_false _ e2).1, parityWeight_replicate_true_local]
        by_cases hw1_0 : parityWeight (mnListAt (mnWitnessFamily w) i1) = 0
        · rcases separate_diff_weight_zero_suffixes
              (mnListAt (mnWitnessFamily (w + 1)) i1)
              (mnListAt (mnWitnessFamily (w + 1)) i2)
              (by rw [hu1_eq]; exact hw1_0) (by omega) with ⟨k, hv1, hnv2⟩
          exact ⟨k, fun hiff => hnv2 (hiff.mp hv1)⟩
        · rcases separate_strict_lt_weights
              (mnListAt (mnWitnessFamily (w + 1)) i1)
              (mnListAt (mnWitnessFamily (w + 1)) i2)
              (by rw [hu1_eq]; omega) (by rw [hu1_eq, hw2_eq]; omega) with ⟨k, hv1, hnv2⟩
          exact ⟨k, fun hiff => hnv2 (hiff.mp hv1)⟩
      · let e1 := i1 - N0
        let e2 := i2 - N0
        have he1_lt_e2 : e1 < e2 := by dsimp [e1, e2]; omega
        have he2_lt : e2 < 2 * 3 ^ w := by dsimp [e2]; omega
        have hu1_eq : mnListAt (mnWitnessFamily (w + 1)) i1 =
            List.replicate (w + 1) true ++ List.replicate e1 false := by
          simp only [mnWitnessFamily]
          rw [mnListAt_append_right _ _ i1 (by omega)]
          change mnListAt (mnWeightBlockAux (w + 1) 0 (2 * 3 ^ w)) e1 = _
          rw [mnWeightBlockAux_at (w + 1) (2 * 3 ^ w) 0 e1 (by omega), Nat.zero_add]
        have hu2_eq : mnListAt (mnWitnessFamily (w + 1)) i2 =
            List.replicate (w + 1) true ++ List.replicate e2 false := by
          simp only [mnWitnessFamily]
          rw [mnListAt_append_right _ _ i2 (by omega)]
          change mnListAt (mnWeightBlockAux (w + 1) 0 (2 * 3 ^ w)) e2 = _
          rw [mnWeightBlockAux_at (w + 1) (2 * 3 ^ w) 0 e2 he2_lt, Nat.zero_add]
        rcases separate_same_core_lt_exp (w + 1) e1 e2 (by omega) he1_lt_e2 (by simpa using he2_lt) with
          ⟨k, hv1, hnv2⟩
        refine ⟨k, ?_⟩
        rw [hu1_eq, hu2_eq]
        exact fun hiff => hnv2 (hiff.mp hv1)

/--
  Theorem T2.7b (`mnWitnessFamily_card_pow3_and_pairwise_distinguished`, `∀ w : Nat`):
  `mnWitnessFamily w` has exact cardinality `3 ^ w`, every word has `parityWeight ≤ w`,
  and EVERY pair of distinct indices `i1 ≠ i2 < 3 ^ w` produces distinct words separated
  in `IsValidOneEquationWord` by an explicit pure-`false` suffix `List.replicate k false`!
-/
theorem mnWitnessFamily_card_pow3_and_pairwise_distinguished (w : Nat) :
    (mnWitnessFamily w).length = 3 ^ w ∧
    (∀ i : Nat, i < 3 ^ w -> parityWeight (mnListAt (mnWitnessFamily w) i) ≤ w) ∧
    (∀ i1 i2 : Nat, i1 < 3 ^ w -> i2 < 3 ^ w -> i1 ≠ i2 ->
      let u1 := mnListAt (mnWitnessFamily w) i1
      let u2 := mnListAt (mnWitnessFamily w) i2
      u1 ≠ u2 ∧
      ∃ k : Nat,
        ¬ (IsValidOneEquationWord (u1 ++ List.replicate k false) ↔
           IsValidOneEquationWord (u2 ++ List.replicate k false))) := by
  have hlen := mnWitnessFamily_length w
  refine ⟨hlen, ?_, ?_⟩
  · intro i hi
    exact mnWitnessFamily_weight_le w i (by omega)
  · intro i1 i2 hi1 hi2 hne
    dsimp only
    have hsep : ∃ k : Nat,
        ¬ (IsValidOneEquationWord (mnListAt (mnWitnessFamily w) i1 ++ List.replicate k false) ↔
           IsValidOneEquationWord (mnListAt (mnWitnessFamily w) i2 ++ List.replicate k false)) := by
      by_cases hlt : i1 < i2
      · exact mnWitnessFamily_lt_sep w i1 i2 hlt (by omega)
      · rcases mnWitnessFamily_lt_sep w i2 i1 (by omega) (by omega) with ⟨k, hk⟩
        exact ⟨k, fun hiff => hk hiff.symm⟩
    refine ⟨?_, hsep⟩
    intro heq
    rcases hsep with ⟨k, hk⟩
    rw [heq] at hk
    exact hk Iff.rfl

def dfaRun {N : Nat} (delta : Fin N -> Bool -> Fin N) : Fin N -> List Bool -> Fin N
  | q, [] => q
  | q, b :: bs => dfaRun delta (delta q b) bs

theorem dfaRun_append {N : Nat} (delta : Fin N -> Bool -> Fin N) :
    ∀ (u v : List Bool) (q : Fin N),
      dfaRun delta q (u ++ v) = dfaRun delta (dfaRun delta q u) v
  | [], _, _ => rfl
  | b :: bs, v, q => dfaRun_append delta bs v (delta q b)

def findIndexBelow (pred : Nat -> Bool) : Nat -> Option Nat
  | 0 => none
  | m + 1 => if pred m then some m else findIndexBelow pred m

theorem findIndexBelow_spec (pred : Nat -> Bool) : ∀ m : Nat,
    (∀ idx : Nat, findIndexBelow pred m = some idx -> idx < m ∧ pred idx = true) ∧
    (findIndexBelow pred m = none -> ∀ idx : Nat, idx < m -> pred idx = false)
  | 0 => ⟨fun _ h => by simp [findIndexBelow] at h, fun _ _ hlt => by omega⟩
  | m + 1 => by
    simp only [findIndexBelow]
    cases hp : pred m with
    | true =>
      simp only [ite_true]
      refine ⟨?_, fun h => by simp at h⟩
      intro idx hs; simp at hs; subst hs; exact ⟨by omega, hp⟩
    | false =>
      simp only [Bool.false_eq_true, ite_false]
      rcases findIndexBelow_spec pred m with ⟨hsome, hnone⟩
      refine ⟨?_, ?_⟩
      · intro idx hs
        rcases hsome idx hs with ⟨hlt, ht⟩
        exact ⟨by omega, ht⟩
      · intro hn idx hlt
        by_cases heq : idx = m
        · subst heq; exact hp
        · exact hnone hn idx (by omega)

theorem pigeonhole_fin_nat : ∀ (N M : Nat),
    N < M -> ∀ f : Fin M -> Fin N, ∃ i1 i2 : Fin M, i1 ≠ i2 ∧ f i1 = f i2
  | 0, M, hlt, f => by
    have h0 : (f ⟨0, hlt⟩).val < 0 := (f ⟨0, hlt⟩).isLt
    omega
  | N + 1, M, hlt, f => by
    have hM2 : M ≥ 2 := by omega
    let last : Fin M := ⟨M - 1, by omega⟩
    let pred : Nat -> Bool := fun idx =>
      if h : idx < M - 1 then decide ((f ⟨idx, by omega⟩).val = (f last).val) else false
    rcases findIndexBelow_spec pred (M - 1) with ⟨hsome, hnone⟩
    cases hf : findIndexBelow pred (M - 1) with
    | some idx =>
      rcases hsome idx hf with ⟨hidx_lt, hp_true⟩
      dsimp [pred] at hp_true
      simp only [hidx_lt, dite_true] at hp_true
      have hval_eq : (f ⟨idx, by omega⟩).val = (f last).val := of_decide_eq_true hp_true
      refine ⟨⟨idx, by omega⟩, last, ?_, Fin.eq_of_val_eq hval_eq⟩
      intro heq
      have hv := congrArg (@Fin.val M) heq
      dsimp [last] at hv
      omega
    | none =>
      have hno := hnone hf
      have hne_last : ∀ idx : Nat, (h : idx < M - 1) -> (f ⟨idx, by omega⟩).val ≠ (f last).val := by
        intro idx h heq
        have hp_f := hno idx h
        dsimp [pred] at hp_f
        simp only [h, dite_true] at hp_f
        exact of_decide_eq_false hp_f heq
      let f' : Fin (M - 1) -> Fin N := fun i =>
        let vi := (f ⟨i.val, by omega⟩).val
        have hvi_lt : vi < N + 1 := (f ⟨i.val, by omega⟩).isLt
        have hvi_ne : vi ≠ (f last).val := hne_last i.val i.isLt
        if hlt_last : vi < (f last).val then
          ⟨vi, by have hl := (f last).isLt; omega⟩
        else
          ⟨vi - 1, by omega⟩
      rcases pigeonhole_fin_nat N (M - 1) (by omega) f' with ⟨i1, i2, hi_ne, hf'_eq⟩
      refine ⟨⟨i1.val, by omega⟩, ⟨i2.val, by omega⟩, ?_, ?_⟩
      · intro heq
        have hv : i1.val = i2.val := congrArg (@Fin.val M) heq
        exact hi_ne (Fin.eq_of_val_eq hv)
      · apply Fin.eq_of_val_eq
        have hv_eq := congrArg Fin.val hf'_eq
        dsimp [f'] at hv_eq
        have hne1 := hne_last i1.val i1.isLt
        have hne2 := hne_last i2.val i2.isLt
        by_cases h1 : (f ⟨i1.val, by omega⟩).val < (f last).val <;>
        by_cases h2 : (f ⟨i2.val, by omega⟩).val < (f last).val <;>
        simp only [h1, h2, dite_true, dite_false] at hv_eq <;>
        omega

theorem pow3_gt_self : ∀ n : Nat, n < 3 ^ n
  | 0 => by decide
  | n + 1 => by
    have ih := pow3_gt_self n
    rw [Nat.pow_succ]
    omega

/--
  Theorem T2.7c (`no_finite_dfa_recognizes_one_equation_language`, `∀ N ≥ 1`):
  Universal `bbchallenge` Regular-Language Impossibility Barrier:
  For EVERY finite state count `N ≥ 1` and EVERY deterministic finite automaton
  `(delta : Fin N -> Bool -> Fin N, q0 : Fin N, accept : Fin N -> Bool)`,
  there exists an explicit parity word `v : List Bool` misclassified by the DFA:
  `(accept (dfaRun delta q0 v) = true) ↔ ¬ IsValidOneEquationWord v`!
-/
theorem no_finite_dfa_recognizes_one_equation_language (N : Nat) (_hN : N ≥ 1)
    (delta : Fin N -> Bool -> Fin N) (q0 : Fin N) (accept : Fin N -> Bool) :
    ∃ v : List Bool, (accept (dfaRun delta q0 v) = true) ↔ ¬ IsValidOneEquationWord v := by
  have hgt : N < 3 ^ N := pow3_gt_self N
  let f : Fin (3 ^ N) -> Fin N :=
    fun i => dfaRun delta q0 (mnListAt (mnWitnessFamily N) i.val)
  rcases pigeonhole_fin_nat N (3 ^ N) hgt f with ⟨i1, i2, hi_ne, hstate_eq⟩
  have hval_ne : i1.val ≠ i2.val := fun h => hi_ne (Fin.eq_of_val_eq h)
  rcases (mnWitnessFamily_card_pow3_and_pairwise_distinguished N).2.2
      i1.val i2.val i1.isLt i2.isLt hval_ne with ⟨_, ⟨k, hsep⟩⟩
  let u1 := mnListAt (mnWitnessFamily N) i1.val
  let u2 := mnListAt (mnWitnessFamily N) i2.val
  let s := List.replicate k false
  let v1 := u1 ++ s
  let v2 := u2 ++ s
  have hrun_eq : dfaRun delta q0 v1 = dfaRun delta q0 v2 := by
    dsimp [v1, v2, u1, u2]
    rw [dfaRun_append, dfaRun_append]
    dsimp [f] at hstate_eq
    rw [hstate_eq]
  cases hacc : accept (dfaRun delta q0 v1) with
  | true =>
    by_cases hv1 : IsValidOneEquationWord v1
    · have hnv2 : ¬ IsValidOneEquationWord v2 := fun hv2 => hsep ⟨fun _ => hv2, fun _ => hv1⟩
      refine ⟨v2, ?_⟩
      rw [← hrun_eq, hacc]
      exact ⟨fun _ => hnv2, fun _ => rfl⟩
    · refine ⟨v1, ?_⟩
      rw [hacc]
      exact ⟨fun _ => hv1, fun _ => rfl⟩
  | false =>
    by_cases hv1 : IsValidOneEquationWord v1
    · refine ⟨v1, ?_⟩
      rw [hacc]
      exact ⟨fun h => by simp at h, fun hnv => False.elim (hnv hv1)⟩
    · have hv2 : IsValidOneEquationWord v2 := by
        by_cases hv2 : IsValidOneEquationWord v2
        · exact hv2
        · exact False.elim (hsep ⟨fun h => False.elim (hv1 h), fun h => False.elim (hv2 h)⟩)
      refine ⟨v2, ?_⟩
      rw [← hrun_eq, hacc]
      exact ⟨fun h => by simp at h, fun hnv => False.elim (hnv hv2)⟩

-- ----------------------------------------------------------------------------
-- T2.8: All-Dimension `∀ d ≥ 1` Coordinatewise-Monotone Upper-Triangular
--       Identity Collapse vs `d = 2` Top-Left-Monotone 6-Rule Sharpness
-- ----------------------------------------------------------------------------

def natSumPrefix (d : Nat) (f : Fin d -> Nat) : Nat -> Nat
  | 0 => 0
  | n + 1 => natSumPrefix d f n + (if hn : n < d then f ⟨n, hn⟩ else 0)

def natSumFin (d : Nat) (f : Fin d -> Nat) : Nat :=
  natSumPrefix d f d

def natMatMul (d : Nat) (A B : Fin d -> Fin d -> Nat) : Fin d -> Fin d -> Nat :=
  fun i j => natSumFin d (fun k => A i k * B k j)

def natMatVec (d : Nat) (A : Fin d -> Fin d -> Nat) (v : Fin d -> Nat) : Fin d -> Nat :=
  fun i => natSumFin d (fun k => A i k * v k)

def natMatId (d : Nat) : Fin d -> Fin d -> Nat :=
  fun i j => if i.val = j.val then 1 else 0

structure NatAffineDim (d : Nat) where
  M : Fin d -> Fin d -> Nat
  v : Fin d -> Nat

def compNatAffineDim (d : Nat) (A B : NatAffineDim d) : NatAffineDim d where
  M := natMatMul d A.M B.M
  v := fun i => natMatVec d A.M B.v i + A.v i

def evalWordNatAffineDim (d : Nat) (interp : MixedSRSSym -> NatAffineDim d) :
    List MixedSRSSym -> NatAffineDim d
  | [] => { M := natMatId d, v := fun _ => 0 }
  | s :: w => compNatAffineDim d (interp s) (evalWordNatAffineDim d interp w)

def orientsNatAffineDim (d : Nat) (hd : 0 < d) (lhs rhs : NatAffineDim d) : Prop :=
  (∀ i j : Fin d, lhs.M i j ≥ rhs.M i j) ∧
  (∀ i : Fin d, lhs.v i ≥ rhs.v i) ∧
  lhs.v ⟨0, hd⟩ > rhs.v ⟨0, hd⟩

def IsUpperTriMat (d : Nat) (A : Fin d -> Fin d -> Nat) : Prop :=
  ∀ i j : Fin d, i.val > j.val -> A i j = 0

theorem natSumPrefix_congr (d : Nat) (f g : Fin d -> Nat) (hfg : ∀ k : Fin d, f k = g k) :
    ∀ n : Nat, natSumPrefix d f n = natSumPrefix d g n
  | 0 => rfl
  | n + 1 => by
    simp only [natSumPrefix, natSumPrefix_congr d f g hfg n]
    by_cases hn : n < d
    · simp [hn, hfg ⟨n, hn⟩]
    · simp [hn]

theorem natSumPrefix_add (d : Nat) (f g : Fin d -> Nat) :
    ∀ n : Nat, natSumPrefix d (fun k => f k + g k) n = natSumPrefix d f n + natSumPrefix d g n
  | 0 => rfl
  | n + 1 => by
    simp only [natSumPrefix, natSumPrefix_add d f g n]
    by_cases hn : n < d <;> simp [hn] <;> omega

theorem natSumPrefix_single (d : Nat) (i0 : Fin d) (c : Nat) :
    ∀ n : Nat, natSumPrefix d (fun k => if k.val = i0.val then c else 0) n =
      (if i0.val < n then c else 0)
  | 0 => by simp [natSumPrefix]
  | n + 1 => by
    simp only [natSumPrefix, natSumPrefix_single d i0 c n]
    by_cases hn : n < d
    · simp only [hn, dite_true]
      by_cases heq : n = i0.val
      · subst heq; simp
      · have hiff : (i0.val < n + 1) ↔ (i0.val < n) := by omega
        simp [heq, hiff]
    · simp only [hn, dite_false]
      have hlt1 : i0.val < n := by have hi := i0.isLt; omega
      have hlt2 : i0.val < n + 1 := by omega
      simp [hlt1, hlt2]

theorem natSumFin_eq_single (d : Nat) (f : Fin d -> Nat) (i0 : Fin d)
    (hzero : ∀ k : Fin d, k.val ≠ i0.val -> f k = 0) :
    natSumFin d f = f i0 := by
  unfold natSumFin
  have hfg : ∀ k : Fin d, f k = (if k.val = i0.val then f i0 else 0) := by
    intro k
    by_cases hk : k.val = i0.val
    · simp only [hk, ite_true]; exact congrArg f (Fin.eq_of_val_eq hk)
    · simp only [hk, ite_false]; exact hzero k hk
  rw [natSumPrefix_congr d f _ hfg d, natSumPrefix_single d i0 (f i0) d]
  simp [i0.isLt]

theorem natSumFin_eq_pair (d : Nat) (f : Fin d -> Nat) (i0 j0 : Fin d)
    (hne : i0.val ≠ j0.val)
    (hzero : ∀ k : Fin d, k.val ≠ i0.val -> k.val ≠ j0.val -> f k = 0) :
    natSumFin d f = f i0 + f j0 := by
  unfold natSumFin
  let g1 : Fin d -> Nat := fun k => if k.val = i0.val then f i0 else 0
  let g2 : Fin d -> Nat := fun k => if k.val = j0.val then f j0 else 0
  have hfg : ∀ k : Fin d, f k = g1 k + g2 k := by
    intro k; dsimp [g1, g2]
    by_cases h1 : k.val = i0.val
    · rw [Fin.eq_of_val_eq h1]
      simp [hne]
    · by_cases h2 : k.val = j0.val
      · have hne' : j0.val ≠ i0.val := fun h => hne h.symm
        rw [Fin.eq_of_val_eq h2]
        simp [hne']
      · simp [h1, h2, hzero k h1 h2]
  rw [natSumPrefix_congr d f _ hfg d, natSumPrefix_add d g1 g2 d,
      natSumPrefix_single d i0 (f i0) d, natSumPrefix_single d j0 (f j0) d]
  simp [i0.isLt, j0.isLt]

theorem natMatMul_right_id (d : Nat) (A : Fin d -> Fin d -> Nat) (i j : Fin d) :
    natMatMul d A (natMatId d) i j = A i j := by
  unfold natMatMul
  rw [natSumFin_eq_single d _ j]
  · simp [natMatId]
  · intro k hk; simp [natMatId, hk]

theorem natMatVec_id (d : Nat) (v : Fin d -> Nat) (i : Fin d) :
    natMatVec d (natMatId d) v i = v i := by
  unfold natMatVec
  rw [natSumFin_eq_single d _ i]
  · simp [natMatId]
  · intro k hk
    have hne : i.val ≠ k.val := fun h => hk h.symm
    simp [natMatId, hne]

theorem evalWord2_M (d : Nat) (interp : MixedSRSSym -> NatAffineDim d)
    (s1 s2 : MixedSRSSym) (i j : Fin d) :
    (evalWordNatAffineDim d interp [s1, s2]).M i j =
      natMatMul d (interp s1).M (interp s2).M i j := by
  simp only [evalWordNatAffineDim, compNatAffineDim]
  have hcongr : ∀ k : Fin d,
      (interp s1).M i k * natMatMul d (interp s2).M (natMatId d) k j =
        (interp s1).M i k * (interp s2).M k j := by
    intro k; rw [natMatMul_right_id]
  exact natSumPrefix_congr d _ _ hcongr d

theorem evalWord3_M (d : Nat) (interp : MixedSRSSym -> NatAffineDim d)
    (s1 s2 s3 : MixedSRSSym) (i j : Fin d) :
    (evalWordNatAffineDim d interp [s1, s2, s3]).M i j =
      natMatMul d (interp s1).M (natMatMul d (interp s2).M (interp s3).M) i j := by
  simp only [evalWordNatAffineDim, compNatAffineDim]
  have hcongr : ∀ k : Fin d,
      (interp s1).M i k * (evalWordNatAffineDim d interp [s2, s3]).M k j =
        (interp s1).M i k * natMatMul d (interp s2).M (interp s3).M k j := by
    intro k; rw [evalWord2_M]
  exact natSumPrefix_congr d _ _ hcongr d

theorem natMatMul_upperTri_diag (d : Nat) (A B : Fin d -> Fin d -> Nat)
    (hA : IsUpperTriMat d A) (hB : IsUpperTriMat d B) (i : Fin d) :
    natMatMul d A B i i = A i i * B i i := by
  unfold natMatMul
  apply natSumFin_eq_single d _ i
  intro k hk
  by_cases hlt : k.val < i.val
  · rw [hA i k hlt, Nat.zero_mul]
  · rw [hB k i (by omega), Nat.mul_zero]

theorem natMatMul_upperTri (d : Nat) (A B : Fin d -> Fin d -> Nat)
    (hA : IsUpperTriMat d A) (hB : IsUpperTriMat d B) :
    IsUpperTriMat d (natMatMul d A B) := by
  intro i j hij
  unfold natMatMul
  rw [natSumFin_eq_single d _ i]
  · rw [hB i j hij, Nat.mul_zero]
  · intro k hk
    by_cases hlt : k.val < i.val
    · rw [hA i k hlt, Nat.zero_mul]
    · rw [hB k j (by omega), Nat.mul_zero]

def IsFlatBelowBand (d delta : Nat) (A : Fin d -> Fin d -> Nat) : Prop :=
  IsUpperTriMat d A ∧
  (∀ p : Fin d, A p p = 1) ∧
  (∀ p q : Fin d, p.val < q.val -> q.val - p.val < delta -> A p q = 0)

theorem natMatMul_flat_flat (d delta : Nat) (A B : Fin d -> Fin d -> Nat)
    (hA : IsFlatBelowBand d delta A) (hB : IsFlatBelowBand d delta B)
    (i j : Fin d) (hij : i.val < j.val) (hdel : j.val - i.val = delta) :
    natMatMul d A B i j = B i j + A i j := by
  unfold natMatMul
  rw [natSumFin_eq_pair d _ i j (by omega)]
  · rw [hA.2.1 i, hB.2.1 j, Nat.one_mul, Nat.mul_one]
  · intro k hki hkj
    by_cases hlt1 : k.val < i.val
    · rw [hA.1 i k hlt1, Nat.zero_mul]
    · by_cases hlt2 : k.val < j.val
      · rw [hA.2.2 i k (by omega) (by omega), Nat.zero_mul]
      · rw [hB.1 k j (by omega), Nat.mul_zero]

theorem natMatMul_flat_preserve (d delta : Nat) (A B : Fin d -> Fin d -> Nat)
    (hA : IsFlatBelowBand d delta A) (hB : IsFlatBelowBand d delta B) :
    IsFlatBelowBand d delta (natMatMul d A B) := by
  refine ⟨natMatMul_upperTri d A B hA.1 hB.1, ?_, ?_⟩
  · intro p
    rw [natMatMul_upperTri_diag d A B hA.1 hB.1 p, hA.2.1 p, hB.2.1 p, Nat.mul_one]
  · intro p q hpq hlt_d
    have hsubA : IsFlatBelowBand d (q.val - p.val) A :=
      ⟨hA.1, hA.2.1, fun x y hxy hlt => hA.2.2 x y hxy (by omega)⟩
    have hsubB : IsFlatBelowBand d (q.val - p.val) B :=
      ⟨hB.1, hB.2.1, fun x y hxy hlt => hB.2.2 x y hxy (by omega)⟩
    rw [natMatMul_flat_flat d (q.val - p.val) A B hsubA hsubB p q hpq rfl,
        hB.2.2 p q hpq hlt_d, hA.2.2 p q hpq hlt_d, Nat.add_zero]

theorem natMatMul_left_arb_flat (d delta : Nat) (L B : Fin d -> Fin d -> Nat)
    (hL : IsUpperTriMat d L) (hB : IsFlatBelowBand d delta B)
    (i j : Fin d) (hij : i.val < j.val) (hdel : j.val - i.val = delta) :
    natMatMul d L B i j = L i i * B i j + L i j := by
  unfold natMatMul
  rw [natSumFin_eq_pair d _ i j (by omega)]
  · rw [hB.2.1 j, Nat.mul_one]
  · intro k hki hkj
    by_cases hlt1 : k.val < i.val
    · rw [hL i k hlt1, Nat.zero_mul]
    · by_cases hlt2 : k.val < j.val
      · rw [hB.2.2 k j hlt2 (by omega), Nat.mul_zero]
      · rw [hB.1 k j (by omega), Nat.mul_zero]

theorem natMatMul_flat_right_arb (d delta : Nat) (A R : Fin d -> Fin d -> Nat)
    (hA : IsFlatBelowBand d delta A) (hR : IsUpperTriMat d R)
    (i j : Fin d) (hij : i.val < j.val) (hdel : j.val - i.val = delta) :
    natMatMul d A R i j = R i j + A i j * R j j := by
  unfold natMatMul
  rw [natSumFin_eq_pair d _ i j (by omega)]
  · rw [hA.2.1 i, Nat.one_mul]
  · intro k hki hkj
    by_cases hlt1 : k.val < i.val
    · rw [hA.1 i k hlt1, Nat.zero_mul]
    · by_cases hlt2 : k.val < j.val
      · rw [hA.2.2 i k (by omega) (by omega), Nat.zero_mul]
      · rw [hR k j (by omega), Nat.mul_zero]

theorem superdiag_band_collapse_all_dim (d : Nat) (hd : 0 < d)
    (interp : MixedSRSSym -> NatAffineDim d)
    (hup : ∀ s : MixedSRSSym, IsUpperTriMat d (interp s).M)
    (hdiag_pos : ∀ (s : MixedSRSSym) (i : Fin d), (interp s).M i i ≥ 1)
    (hR2  : orientsNatAffineDim d hd (evalWordNatAffineDim d interp [.L, .B1])
              (evalWordNatAffineDim d interp [.L, .T2]))
    (hR5  : orientsNatAffineDim d hd (evalWordNatAffineDim d interp [.T1, .B0])
              (evalWordNatAffineDim d interp [.B1, .T0]))
    (hR7  : orientsNatAffineDim d hd (evalWordNatAffineDim d interp [.T2, .B0])
              (evalWordNatAffineDim d interp [.B0, .T1]))
    (hR9  : orientsNatAffineDim d hd (evalWordNatAffineDim d interp [.T0, .R])
              (evalWordNatAffineDim d interp [.B1, .R]))
    (hR11 : orientsNatAffineDim d hd (evalWordNatAffineDim d interp [.T2, .R])
              (evalWordNatAffineDim d interp [.B1, .B0, .R])) :
    ∀ delta : Nat,
      IsFlatBelowBand d delta (interp .B0).M ∧
      IsFlatBelowBand d delta (interp .B1).M ∧
      IsFlatBelowBand d delta (interp .T0).M ∧
      IsFlatBelowBand d delta (interp .T1).M ∧
      IsFlatBelowBand d delta (interp .T2).M := by
  have hdiag1 : ∀ i : Fin d,
      (interp .B0).M i i = 1 ∧ (interp .B1).M i i = 1 ∧
      (interp .T0).M i i = 1 ∧ (interp .T1).M i i = 1 ∧ (interp .T2).M i i = 1 := by
    intro i
    have hr2 := hR2.1 i i
    have hr5 := hR5.1 i i
    have hr7 := hR7.1 i i
    have hr9 := hR9.1 i i
    have hr11 := hR11.1 i i
    rw [evalWord2_M, evalWord2_M,
        natMatMul_upperTri_diag d _ _ (hup .L) (hup .B1) i,
        natMatMul_upperTri_diag d _ _ (hup .L) (hup .T2) i] at hr2
    rw [evalWord2_M, evalWord2_M,
        natMatMul_upperTri_diag d _ _ (hup .T1) (hup .B0) i,
        natMatMul_upperTri_diag d _ _ (hup .B1) (hup .T0) i] at hr5
    rw [evalWord2_M, evalWord2_M,
        natMatMul_upperTri_diag d _ _ (hup .T2) (hup .B0) i,
        natMatMul_upperTri_diag d _ _ (hup .B0) (hup .T1) i] at hr7
    rw [evalWord2_M, evalWord2_M,
        natMatMul_upperTri_diag d _ _ (hup .T0) (hup .R) i,
        natMatMul_upperTri_diag d _ _ (hup .B1) (hup .R) i] at hr9
    rw [evalWord2_M, evalWord3_M,
        natMatMul_upperTri_diag d _ _ (hup .T2) (hup .R) i,
        natMatMul_upperTri_diag d _ _ (hup .B1) (natMatMul_upperTri d _ _ (hup .B0) (hup .R)) i,
        natMatMul_upperTri_diag d _ _ (hup .B0) (hup .R) i,
        ← Nat.mul_assoc] at hr11
    exact upper_triangular_top_left_unit_collapse_any_dim
      ((interp .L).M i i) ((interp .R).M i i) ((interp .B0).M i i) ((interp .B1).M i i)
      ((interp .T0).M i i) ((interp .T1).M i i) ((interp .T2).M i i)
      (hdiag_pos .L i) (hdiag_pos .R i) (hdiag_pos .B0 i) (hdiag_pos .B1 i)
      (hdiag_pos .T0 i) (hdiag_pos .T1 i) (hdiag_pos .T2 i)
      hr2 hr5 hr7 hr9 hr11
  intro delta
  induction delta with
  | zero =>
    refine ⟨⟨hup .B0, fun i => (hdiag1 i).1, fun _ _ _ h => by omega⟩,
            ⟨hup .B1, fun i => (hdiag1 i).2.1, fun _ _ _ h => by omega⟩,
            ⟨hup .T0, fun i => (hdiag1 i).2.2.1, fun _ _ _ h => by omega⟩,
            ⟨hup .T1, fun i => (hdiag1 i).2.2.2.1, fun _ _ _ h => by omega⟩,
            ⟨hup .T2, fun i => (hdiag1 i).2.2.2.2, fun _ _ _ h => by omega⟩⟩
  | succ del ih =>
    rcases ih with ⟨hfB0, hfB1, hfT0, hfT1, hfT2⟩
    have hstep : ∀ (i j : Fin d), i.val < j.val -> j.val - i.val = del ->
        (interp .B0).M i j = 0 ∧ (interp .B1).M i j = 0 ∧
        (interp .T0).M i j = 0 ∧ (interp .T1).M i j = 0 ∧ (interp .T2).M i j = 0 := by
      intro i j hij hdel
      by_cases hdel0 : del = 0
      · omega
      · have hr2 := hR2.1 i j
        have hr5 := hR5.1 i j
        have hr7 := hR7.1 i j
        have hr9 := hR9.1 i j
        have hr11 := hR11.1 i j
        rw [evalWord2_M, evalWord2_M,
            natMatMul_left_arb_flat d del (interp .L).M (interp .B1).M (hup .L) hfB1 i j hij hdel,
            natMatMul_left_arb_flat d del (interp .L).M (interp .T2).M (hup .L) hfT2 i j hij hdel] at hr2
        rw [evalWord2_M, evalWord2_M,
            natMatMul_flat_flat d del (interp .T1).M (interp .B0).M hfT1 hfB0 i j hij hdel,
            natMatMul_flat_flat d del (interp .B1).M (interp .T0).M hfB1 hfT0 i j hij hdel] at hr5
        rw [evalWord2_M, evalWord2_M,
            natMatMul_flat_flat d del (interp .T2).M (interp .B0).M hfT2 hfB0 i j hij hdel,
            natMatMul_flat_flat d del (interp .B0).M (interp .T1).M hfB0 hfT1 i j hij hdel] at hr7
        rw [evalWord2_M, evalWord2_M,
            natMatMul_flat_right_arb d del (interp .T0).M (interp .R).M hfT0 (hup .R) i j hij hdel,
            natMatMul_flat_right_arb d del (interp .B1).M (interp .R).M hfB1 (hup .R) i j hij hdel] at hr9
        -- Compute `(evalWord [.B1, .B0, .R]).M i j` directly using `natSumFin_eq_pair`:
        have hB0R_diag : natMatMul d (interp .B0).M (interp .R).M j j = (interp .R).M j j := by
          rw [natMatMul_upperTri_diag d _ _ (hup .B0) (hup .R) j, (hdiag1 j).1, Nat.one_mul]
        have hB0R_ij : natMatMul d (interp .B0).M (interp .R).M i j =
            (interp .R).M i j + (interp .B0).M i j * (interp .R).M j j :=
          natMatMul_flat_right_arb d del (interp .B0).M (interp .R).M hfB0 (hup .R) i j hij hdel
        have hB1B0R_ij : natMatMul d (interp .B1).M (natMatMul d (interp .B0).M (interp .R).M) i j =
            ((interp .R).M i j + (interp .B0).M i j * (interp .R).M j j) +
              (interp .B1).M i j * (interp .R).M j j := by
          unfold natMatMul
          rw [natSumFin_eq_pair d _ i j (by omega)]
          · change (interp .B1).M i i * natMatMul d (interp .B0).M (interp .R).M i j +
                (interp .B1).M i j * natMatMul d (interp .B0).M (interp .R).M j j = _
            rw [(hdiag1 i).2.1, Nat.one_mul, hB0R_ij, hB0R_diag]
          · intro k hki hkj
            change (interp .B1).M i k * natMatMul d (interp .B0).M (interp .R).M k j = 0
            by_cases hlt1 : k.val < i.val
            · rw [hfB1.1 i k hlt1, Nat.zero_mul]
            · by_cases hlt2 : k.val < j.val
              · rw [hfB1.2.2 i k (by omega) (by omega), Nat.zero_mul]
              · rw [natMatMul_upperTri d _ _ (hup .B0) (hup .R) k j (by omega), Nat.mul_zero]
        rw [evalWord2_M, evalWord3_M,
            natMatMul_flat_right_arb d del (interp .T2).M (interp .R).M hfT2 (hup .R) i j hij hdel,
            hB1B0R_ij] at hr11
        have hmL_pos : (interp .L).M i i ≥ 1 := hdiag_pos .L i
        have hmR_pos : (interp .R).M j j ≥ 1 := hdiag_pos .R j
        have h1 : (interp .B1).M i j ≥ (interp .T2).M i j := by
          by_cases h : (interp .B1).M i j ≥ (interp .T2).M i j
          · exact h
          · have hm := Nat.mul_lt_mul_of_pos_left (by omega : (interp .B1).M i j < (interp .T2).M i j)
              (by omega : 0 < (interp .L).M i i)
            omega
        have h2 : (interp .T0).M i j ≥ (interp .B1).M i j := by
          by_cases h : (interp .T0).M i j ≥ (interp .B1).M i j
          · exact h
          · have hm := Nat.mul_lt_mul_of_pos_right (by omega : (interp .T0).M i j < (interp .B1).M i j)
              (by omega : 0 < (interp .R).M j j)
            omega
        have h3 : (interp .T2).M i j ≥ (interp .B0).M i j + (interp .B1).M i j := by
          rw [Nat.add_assoc, ← Nat.add_mul] at hr11
          by_cases h : (interp .T2).M i j ≥ (interp .B0).M i j + (interp .B1).M i j
          · exact h
          · have hm := Nat.mul_lt_mul_of_pos_right
              (by omega : (interp .T2).M i j < (interp .B0).M i j + (interp .B1).M i j)
              (by omega : 0 < (interp .R).M j j)
            omega
        omega
    have hext : ∀ (s : MixedSRSSym),
        IsFlatBelowBand d del (interp s).M ->
        (∀ i j : Fin d, i.val < j.val -> j.val - i.val = del -> (interp s).M i j = 0) ->
        IsFlatBelowBand d (del + 1) (interp s).M := by
      intro s hf hs0
      refine ⟨hf.1, hf.2.1, ?_⟩
      intro p q hpq hlt1
      by_cases hlt_del : q.val - p.val < del
      · exact hf.2.2 p q hpq hlt_del
      · exact hs0 p q hpq (by omega)
    exact ⟨hext .B0 hfB0 (fun i j hij hd' => (hstep i j hij hd').1),
           hext .B1 hfB1 (fun i j hij hd' => (hstep i j hij hd').2.1),
           hext .T0 hfT0 (fun i j hij hd' => (hstep i j hij hd').2.2.1),
           hext .T1 hfT1 (fun i j hij hd' => (hstep i j hij hd').2.2.2.1),
           hext .T2 hfT2 (fun i j hij hd' => (hstep i j hij hd').2.2.2.2)⟩

/--
  Theorem T2.8a (`all_dim_coord_monotone_upper_triangular_impossibility`, `∀ d ≥ 1`):
  In EVERY dimension `d ≥ 1`, ANY coordinatewise-monotone (`∀ s i, M_s i i ≥ 1`)
  upper-triangular Natural Matrix Interpretation orienting `{R2, R5, R7, R9, R11}`
  collapses to `M_s = I_d` across all 5 interior symbols `{B0, B1, T0, T1, T2}` and
  is unconditionally refuted on `R8_t2b1` (`[T2, B1] -> [B1, T2]`)!
-/
theorem all_dim_coord_monotone_upper_triangular_impossibility (d : Nat) (hd : 0 < d)
    (interp : MixedSRSSym -> NatAffineDim d)
    (hup : ∀ s : MixedSRSSym, IsUpperTriMat d (interp s).M)
    (hdiag_pos : ∀ (s : MixedSRSSym) (i : Fin d), (interp s).M i i ≥ 1)
    (hR2  : orientsNatAffineDim d hd (evalWordNatAffineDim d interp [.L, .B1])
              (evalWordNatAffineDim d interp [.L, .T2]))
    (hR5  : orientsNatAffineDim d hd (evalWordNatAffineDim d interp [.T1, .B0])
              (evalWordNatAffineDim d interp [.B1, .T0]))
    (hR7  : orientsNatAffineDim d hd (evalWordNatAffineDim d interp [.T2, .B0])
              (evalWordNatAffineDim d interp [.B0, .T1]))
    (hR8  : orientsNatAffineDim d hd (evalWordNatAffineDim d interp [.T2, .B1])
              (evalWordNatAffineDim d interp [.B1, .T2]))
    (hR9  : orientsNatAffineDim d hd (evalWordNatAffineDim d interp [.T0, .R])
              (evalWordNatAffineDim d interp [.B1, .R]))
    (hR11 : orientsNatAffineDim d hd (evalWordNatAffineDim d interp [.T2, .R])
              (evalWordNatAffineDim d interp [.B1, .B0, .R])) :
    False := by
  rcases superdiag_band_collapse_all_dim d hd interp hup hdiag_pos hR2 hR5 hR7 hR9 hR11 d with
    ⟨_, hfB1, _, _, hfT2⟩
  have hB1_id : ∀ i j : Fin d, (interp .B1).M i j = natMatId d i j := by
    intro i j; unfold natMatId
    by_cases heq : i.val = j.val
    · rw [Fin.eq_of_val_eq heq]; simp [hfB1.2.1 j]
    · by_cases hgt : i.val > j.val
      · simp [heq, hfB1.1 i j hgt]
      · simp [heq, hfB1.2.2 i j (by omega) (by have hj := j.isLt; omega)]
  have hT2_id : ∀ i j : Fin d, (interp .T2).M i j = natMatId d i j := by
    intro i j; unfold natMatId
    by_cases heq : i.val = j.val
    · rw [Fin.eq_of_val_eq heq]; simp [hfT2.2.1 j]
    · by_cases hgt : i.val > j.val
      · simp [heq, hfT2.1 i j hgt]
      · simp [heq, hfT2.2.2 i j (by omega) (by have hj := j.isLt; omega)]
  have heval_v2 : ∀ (s1 s2 : MixedSRSSym),
      (∀ i j : Fin d, (interp s1).M i j = natMatId d i j) ->
      (∀ i j : Fin d, (interp s2).M i j = natMatId d i j) ->
      (evalWordNatAffineDim d interp [s1, s2]).v ⟨0, hd⟩ =
        (interp s2).v ⟨0, hd⟩ + (interp s1).v ⟨0, hd⟩ := by
    intro s1 s2 hs1 hs2
    simp only [evalWordNatAffineDim, compNatAffineDim]
    have hv_zero : natMatVec d (interp s2).M (fun _ => 0) = fun _ => 0 := by
      funext p; unfold natMatVec
      rw [natSumFin_eq_single d _ p]
      · simp
      · intro k _; simp
    rw [hv_zero]
    simp only [Nat.zero_add]
    have hmv : natMatVec d (interp s1).M (interp s2).v ⟨0, hd⟩ = (interp s2).v ⟨0, hd⟩ := by
      unfold natMatVec natSumFin
      have hc : ∀ k : Fin d, (interp s1).M ⟨0, hd⟩ k * (interp s2).v k =
          natMatId d ⟨0, hd⟩ k * (interp s2).v k := by
        intro k; rw [hs1]
      rw [natSumPrefix_congr d _ _ hc d]
      exact natMatVec_id d (interp s2).v ⟨0, hd⟩
    rw [hmv]
  have hstrict := hR8.2.2
  rw [heval_v2 .T2 .B1 hT2_id hB1_id, heval_v2 .B1 .T2 hB1_id hT2_id] at hstrict
  omega

def sub6UpperTri2DCert : MixedSRSSym -> UpperTri2D
  | .L  => { m := 1, p := 8, n := 8, c := 0, d := 6 }
  | .R  => { m := 1, p := 7, n := 0, c := 0, d := 1 }
  | .B0 => { m := 1, p := 0, n := 0, c := 0, d := 0 }
  | .B1 => { m := 1, p := 0, n := 2, c := 0, d := 1 }
  | .T0 => { m := 1, p := 0, n := 0, c := 2, d := 3 }
  | .T1 => { m := 1, p := 0, n := 0, c := 6, d := 8 }
  | .T2 => { m := 1, p := 7, n := 1, c := 7, d := 0 }

/--
  Theorem T2.8b (`sub6_admits_2d_top_left_monotone_upper_triangular_cert` — Exact Sharpness):
  Dropping `(M_s)_{1,1} ≥ 1` (requiring ONLY top-left `(M_s)_{0,0} ≥ 1`) makes the exact
  6-rule subset `{R2, R5, R7, R8, R9, R11}` of `T2.8a` FEASIBLE already at `d = 2`!
-/
theorem sub6_admits_2d_top_left_monotone_upper_triangular_cert :
    (∀ s : MixedSRSSym, (sub6UpperTri2DCert s).m ≥ 1) ∧
    (sub6UpperTri2DCert .B0).n = 0 ∧
    orientsUpperTri2D (evalWordUpperTri2D sub6UpperTri2DCert [.L, .B1])
      (evalWordUpperTri2D sub6UpperTri2DCert [.L, .T2]) ∧
    orientsUpperTri2D (evalWordUpperTri2D sub6UpperTri2DCert [.T1, .B0])
      (evalWordUpperTri2D sub6UpperTri2DCert [.B1, .T0]) ∧
    orientsUpperTri2D (evalWordUpperTri2D sub6UpperTri2DCert [.T2, .B0])
      (evalWordUpperTri2D sub6UpperTri2DCert [.B0, .T1]) ∧
    orientsUpperTri2D (evalWordUpperTri2D sub6UpperTri2DCert [.T2, .B1])
      (evalWordUpperTri2D sub6UpperTri2DCert [.B1, .T2]) ∧
    orientsUpperTri2D (evalWordUpperTri2D sub6UpperTri2DCert [.T0, .R])
      (evalWordUpperTri2D sub6UpperTri2DCert [.B1, .R]) ∧
    orientsUpperTri2D (evalWordUpperTri2D sub6UpperTri2DCert [.T2, .R])
      (evalWordUpperTri2D sub6UpperTri2DCert [.B1, .B0, .R]) := by
  refine ⟨?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s; cases s <;> decide
  · unfold orientsUpperTri2D; decide
  · unfold orientsUpperTri2D; decide
  · unfold orientsUpperTri2D; decide
  · unfold orientsUpperTri2D; decide
  · unfold orientsUpperTri2D; decide
  · unfold orientsUpperTri2D; decide

-- ----------------------------------------------------------------------------
-- T2.9: Infinite Parametric `∀ k ≥ 2` Dyadic & `∀ k ≥ 3` Triadic
--       Minimal-Counterexample Excluded Families (`[]` Axioms)
-- ----------------------------------------------------------------------------

def dyadicEntryExcludedResidue (k : Nat) : Nat :=
  if k % 2 == 0 then 2 ^ k - 1 else 3 * 2 ^ k - 1

theorem pow3_mod4_parity : ∀ k : Nat,
    (k % 2 = 0 -> 3 ^ k % 4 = 1) ∧ (k % 2 = 1 -> 3 ^ k % 4 = 3)
  | 0 => ⟨fun _ => rfl, fun h => by omega⟩
  | k + 1 => by
    rcases pow3_mod4_parity k with ⟨hev, hodd⟩
    refine ⟨?_, ?_⟩
    · intro h1
      have hk_odd : k % 2 = 1 := by omega
      rw [Nat.pow_succ, Nat.mul_mod, hodd hk_odd]
    · intro h1
      have hk_ev : k % 2 = 0 := by omega
      rw [Nat.pow_succ, Nat.mul_mod, hev hk_ev]

/--
  Theorem T2.9a (`infinite_dyadic_entry_merger_excluded_family`, `∀ k ≥ 2, ∀ q : Nat`):
  Every integer `n = 2 ^ (k + 2) * q + dyadicEntryExcludedResidue k` (`k ≥ 2, q ≥ 0`)
  coalesces with `n' = (n - 1) / 2` (`1 ≤ n' < n`) via `collatzIter (k + 2) n = collatzIter (k + 1) n'`,
  the residue classes are pairwise disjoint across all `2 ≤ k1 < k2`, and for every `k ≥ 8`
  `dyadicEntryExcludedResidue k % 512` survives `IsSurvivingMod512Residue` (`255` or `511`)!
-/
theorem infinite_dyadic_entry_merger_excluded_family (k q : Nat) (hk : k ≥ 2) :
    let r := dyadicEntryExcludedResidue k
    let n := 2 ^ (k + 2) * q + r
    let nPrime := (n - 1) / 2
    r < 2 ^ (k + 2) ∧
    1 ≤ nPrime ∧ nPrime < n ∧
    collatzIter (k + 2) n = collatzIter (k + 1) nPrime ∧
    (k ≥ 8 -> IsSurvivingMod512Residue (r % 512)) ∧
    (∀ k2 : Nat, k < k2 -> dyadicEntryExcludedResidue k2 % 2 ^ (k + 2) ≠ r) ∧
    ((∀ m : Nat, ¬ (0 < collatzIter m n ∧ collatzIter m n < n)) ->
     (∀ m : Nat, 1 ≤ m -> m < n -> ∃ k1 : Nat, collatzIter k1 m = 1) -> False) := by
  dsimp only
  let r := dyadicEntryExcludedResidue k
  let n := 2 ^ (k + 2) * q + r
  let nPrime := (n - 1) / 2
  have hp2k_ge4 : 2 ^ k ≥ 4 := by
    rw [show k = 2 + (k - 2) by omega, Nat.pow_add]
    have hp := pow_pos_base 2 (by decide) (k - 2)
    change 4 * 2 ^ (k - 2) ≥ 4; omega
  have hp2k2 : 2 ^ (k + 2) = 2 ^ k * 4 := by rw [Nat.pow_add]
  obtain ⟨u1, hu1_pos, hu1_odd, hn1_eq, h3u1_mod4, hr_lt⟩ :
      ∃ u1 : Nat, u1 ≥ 1 ∧ u1 % 2 = 1 ∧ n + 1 = 2 ^ k * u1 ∧
        (3 ^ k * u1 - 1) % 4 = 0 ∧ r < 2 ^ (k + 2) := by
    have h3_ge1 : 3 ^ k ≥ 1 := pow3_pos_nat k
    by_cases hev : k % 2 = 0
    · have hb : (k % 2 == 0) = true := decide_eq_true hev
      have hr_val : r = 2 ^ k - 1 := by dsimp [r, dyadicEntryExcludedResidue]; rw [hb]; rfl
      refine ⟨4 * q + 1, by omega, by omega, ?_, ?_, by omega⟩
      · dsimp [n]; rw [hp2k2, hr_val, Nat.mul_add, Nat.mul_one, Nat.mul_assoc (2 ^ k) 4 q]
        omega
      · have hp4 := (pow3_mod4_parity k).1 hev
        have h3_pos : 3 ^ k * (4 * q + 1) ≥ 1 * 1 :=
          Nat.mul_le_mul h3_ge1 (by omega : 1 ≤ 4 * q + 1)
        have hq4 : (4 * q + 1) % 4 = 1 := by omega
        have hm4 : (3 ^ k * (4 * q + 1)) % 4 = 1 := by rw [Nat.mul_mod, hp4, hq4]
        omega
    · have hodd : k % 2 = 1 := by omega
      have hb : (k % 2 == 0) = false := decide_eq_false hev
      have hr_val : r = 3 * 2 ^ k - 1 := by dsimp [r, dyadicEntryExcludedResidue]; rw [hb]; rfl
      refine ⟨4 * q + 3, by omega, by omega, ?_, ?_, by omega⟩
      · dsimp [n]; rw [hp2k2, hr_val, Nat.mul_add, Nat.mul_assoc (2 ^ k) 4 q, Nat.mul_comm (2 ^ k) 3]
        omega
      · have hp4 := (pow3_mod4_parity k).2 hodd
        have h3_pos : 3 ^ k * (4 * q + 3) ≥ 1 * 1 :=
          Nat.mul_le_mul h3_ge1 (by omega : 1 ≤ 4 * q + 3)
        have hq4 : (4 * q + 3) % 4 = 3 := by omega
        have hm4 : (3 ^ k * (4 * q + 3)) % 4 = 1 := by rw [Nat.mul_mod, hp4, hq4]
        omega
  have hn_ge3 : n ≥ 3 := by
    have hm := Nat.mul_le_mul hp2k_ge4 hu1_pos; omega
  have hnp_lo : 1 ≤ nPrime := by dsimp [nPrime]; omega
  have hnp_hi : nPrime < n := by dsimp [nPrime]; omega
  have hcoal : collatzIter (k + 2) n = collatzIter (k + 1) nPrime := by
    have hn_eq : n = 2 ^ k * u1 - 1 := by omega
    have hiter_k_n : collatzIter k n = 3 ^ k * u1 - 1 := by
      rw [hn_eq]; exact odd_run_iter k u1 hu1_pos
    have h3k_pos : 3 ^ k * u1 ≥ 3 := by
      have hm : 3 ^ k ≥ 9 := by
        rw [show k = 2 + (k - 2) by omega, Nat.pow_add]
        have hp := pow3_pos_nat (k - 2); change 9 * 3 ^ (k - 2) ≥ 9; omega
      have hp := Nat.mul_le_mul hm hu1_pos; omega
    have hiter_k1_n : collatzIter (k + 1) n = (3 ^ k * u1 - 1) / 2 := by
      rw [collatzIter_add k 1 n, hiter_k_n]
      exact collatzStep_of_even_nat _ (by omega)
    have hiter_k2_n : collatzIter (k + 2) n = (3 ^ k * u1 - 1) / 4 := by
      rw [show k + 2 = (k + 1) + 1 by omega, collatzIter_add (k + 1) 1 n, hiter_k1_n]
      change collatzStep ((3 ^ k * u1 - 1) / 2) = (3 ^ k * u1 - 1) / 4
      rw [collatzStep_of_even_nat _ (by omega)]
      omega
    have hnp1 : nPrime + 1 = 2 ^ (k - 1) * u1 := by
      have hp_split : 2 ^ k * u1 = 2 * (2 ^ (k - 1) * u1) := by
        conv => lhs; rw [show k = (k - 1) + 1 by omega, Nat.pow_succ,
                         Nat.mul_comm (2 ^ (k - 1)) 2, Nat.mul_assoc]
      dsimp [nPrime]; omega
    have hnp_eq : nPrime = 2 ^ (k - 1) * u1 - 1 := by omega
    have hiter_km1_np : collatzIter (k - 1) nPrime = 3 ^ (k - 1) * u1 - 1 := by
      rw [hnp_eq]; exact odd_run_iter (k - 1) u1 hu1_pos
    have h3km1_rel : 3 * (3 ^ (k - 1) * u1) = 3 ^ k * u1 := by
      conv => rhs; rw [show k = (k - 1) + 1 by omega, Nat.pow_succ,
                       Nat.mul_comm (3 ^ (k - 1)) 3, Nat.mul_assoc]
    have h3km1_mod4 : (3 ^ (k - 1) * u1) % 4 = 3 := by omega
    have hiter_k_np : collatzIter k nPrime = (3 ^ (k - 1) * u1 - 1) / 2 := by
      rw [show k = (k - 1) + 1 by omega, collatzIter_add (k - 1) 1 nPrime, hiter_km1_np]
      exact collatzStep_of_even_nat _ (by omega)
    have hiter_k1_np : collatzIter (k + 1) nPrime = (3 ^ k * u1 - 1) / 4 := by
      rw [collatzIter_add k 1 nPrime, hiter_k_np]
      change collatzStep ((3 ^ (k - 1) * u1 - 1) / 2) = (3 ^ k * u1 - 1) / 4
      rw [collatzStep_of_odd_nat _ (by omega)]
      omega
    rw [hiter_k2_n, hiter_k1_np]
  have hsurv512 : k ≥ 8 -> IsSurvivingMod512Residue (r % 512) := by
    intro hk8
    by_cases hk8_eq : k = 8
    · subst hk8_eq
      have hr8 : r % 512 = 255 := by dsimp [r, dyadicEntryExcludedResidue]
      rw [hr8]; unfold IsSurvivingMod512Residue IsSurvivingMod64Residue; decide
    · have hk9 : k ≥ 9 := by omega
      have hdiv512 : 2 ^ k = 512 * 2 ^ (k - 9) := by
        have hs : k = 9 + (k - 9) := by omega
        rw [congrArg (2 ^ ·) hs, Nat.pow_add]
      have hp_pos : 2 ^ (k - 9) ≥ 1 := pow_pos_base 2 (by decide) (k - 9)
      have hr512 : r % 512 = 511 := by
        dsimp [r, dyadicEntryExcludedResidue]
        cases hev : (k % 2 == 0)
        · simp only [Bool.false_eq_true, ite_false]
          rw [hdiv512]; omega
        · simp only [ite_true]
          rw [hdiv512]; omega
      rw [hr512]; unfold IsSurvivingMod512Residue IsSurvivingMod64Residue; decide
  have hdisj : ∀ k2 : Nat, k < k2 -> dyadicEntryExcludedResidue k2 % 2 ^ (k + 2) ≠ r := by
    intro k2 hlt heq_mod
    have hr_mod : r % 2 ^ (k + 2) = r := Nat.mod_eq_of_lt hr_lt
    have hk1_split : 2 ^ (k + 2) = 2 ^ (k + 1) * 2 := Nat.pow_succ 2 (k + 1)
    have hmod_k1 : dyadicEntryExcludedResidue k2 % 2 ^ (k + 1) = r % 2 ^ (k + 1) := by
      rw [← mod_mul_mod_eq (dyadicEntryExcludedResidue k2) (2 ^ (k + 1)) 2,
          ← mod_mul_mod_eq r (2 ^ (k + 1)) 2, ← hk1_split, heq_mod, hr_mod]
    have hp1_mod : (dyadicEntryExcludedResidue k2 + 1) % 2 ^ (k + 1) = (r + 1) % 2 ^ (k + 1) := by
      rw [Nat.add_mod, hmod_k1, ← Nat.add_mod]
    have hlhs0 : (dyadicEntryExcludedResidue k2 + 1) % 2 ^ (k + 1) = 0 := by
      have hp_k2 : 2 ^ k2 = 2 ^ (k + 1) * 2 ^ (k2 - (k + 1)) := by
        have hs : k2 = (k + 1) + (k2 - (k + 1)) := by omega
        rw [congrArg (2 ^ ·) hs, Nat.pow_add]
      have hp2_pos : 2 ^ k2 ≥ 1 := pow_pos_base 2 (by decide) k2
      unfold dyadicEntryExcludedResidue
      cases hev2 : (k2 % 2 == 0)
      · simp only [Bool.false_eq_true, ite_false]
        have h3pos : 3 * 2 ^ k2 ≥ 1 := by omega
        rw [Nat.sub_add_cancel h3pos, hp_k2,
            show 3 * (2 ^ (k + 1) * 2 ^ (k2 - (k + 1))) = 2 ^ (k + 1) * (3 * 2 ^ (k2 - (k + 1))) by
              rw [← Nat.mul_assoc, Nat.mul_comm 3, Nat.mul_assoc],
            Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod]
      · simp only [ite_true]
        rw [Nat.sub_add_cancel hp2_pos, hp_k2, Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod]
    have hrhs_ne : (r + 1) % 2 ^ (k + 1) = 2 ^ k := by
      dsimp [r, dyadicEntryExcludedResidue]
      have hp1 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
      cases hev1 : (k % 2 == 0)
      · simp only [Bool.false_eq_true, ite_false]
        rw [Nat.sub_add_cancel (by omega), hp1,
            show 3 * 2 ^ k = (2 * 2 ^ k) * 1 + 2 ^ k by omega,
            Nat.add_mod, Nat.mul_one, Nat.mod_self, Nat.zero_add, Nat.mod_mod,
            Nat.mod_eq_of_lt (by omega)]
      · simp only [ite_true]
        rw [Nat.sub_add_cancel (by omega), hp1, Nat.mod_eq_of_lt (by omega)]
    rw [hlhs0, hrhs_ne] at hp1_mod
    omega
  refine ⟨hr_lt, hnp_lo, hnp_hi, hcoal, hsurv512, hdisj, ?_⟩
  intro hnoDesc hminReach
  exact minimal_counterexample_no_coalescence n nPrime (k + 1) (k + 2)
    (by omega) hnoDesc hminReach hnp_lo hnp_hi hcoal.symm

def triadicPeriod6Coeff (k : Nat) : Nat :=
  match k % 6 with
  | 0 => 37
  | 1 => 35
  | 2 => 1
  | 3 => 17
  | 4 => 19
  | _ => 53

def triadicExcludedResidue (k : Nat) : Nat :=
  (27 * triadicPeriod6Coeff k * 9 ^ k - 7) / 2

theorem pow8_period6_mod27 (k : Nat) : 8 ^ k % 27 = 8 ^ (k % 6) % 27 := by
  have hp6 : ∀ m : Nat, 8 ^ (6 * m) % 27 = 1 := by
    intro m; induction m with
    | zero => rfl
    | succ m' ih =>
      rw [show 6 * (m' + 1) = 6 * m' + 6 by omega, Nat.pow_add, Nat.mul_mod, ih]
  have hsplit : 8 ^ k = 8 ^ (6 * (k / 6) + k % 6) :=
    congrArg (8 ^ ·) (Nat.div_add_mod k 6).symm
  rw [hsplit, Nat.pow_add, Nat.mul_mod, hp6 (k / 6), Nat.one_mul, Nat.mod_mod]

theorem triadicPeriod6Coeff_spec (k : Nat) :
    let c := triadicPeriod6Coeff k
    c ≥ 1 ∧ c ≤ 53 ∧ c % 2 = 1 ∧ c % 3 ≠ 0 ∧
    512 * c * 8 ^ k ≥ 512 ∧
    (512 * c * 8 ^ k - 179) % 27 = 0 := by
  dsimp only
  have hmod6 : k % 6 = 0 ∨ k % 6 = 1 ∨ k % 6 = 2 ∨ k % 6 = 3 ∨ k % 6 = 4 ∨ k % 6 = 5 := by omega
  have hp8_pos : 8 ^ k ≥ 1 := pow_pos_base 8 (by decide) k
  have hp8_m27 := pow8_period6_mod27 k
  rcases hmod6 with h0 | h1 | h2 | h3 | h4 | h5
  · simp only [triadicPeriod6Coeff, h0] at hp8_m27 ⊢
    have hm : (512 * 37 * 8 ^ k) % 27 = 17 := by rw [Nat.mul_mod, hp8_m27]
    exact ⟨by decide, by decide, by decide, by decide, by omega, by omega⟩
  · simp only [triadicPeriod6Coeff, h1] at hp8_m27 ⊢
    have hm : (512 * 35 * 8 ^ k) % 27 = 17 := by rw [Nat.mul_mod, hp8_m27]
    exact ⟨by decide, by decide, by decide, by decide, by omega, by omega⟩
  · simp only [triadicPeriod6Coeff, h2] at hp8_m27 ⊢
    have hm : (512 * 1 * 8 ^ k) % 27 = 17 := by rw [Nat.mul_mod, hp8_m27]
    exact ⟨by decide, by decide, by decide, by decide, by omega, by omega⟩
  · simp only [triadicPeriod6Coeff, h3] at hp8_m27 ⊢
    have hm : (512 * 17 * 8 ^ k) % 27 = 17 := by rw [Nat.mul_mod, hp8_m27]
    exact ⟨by decide, by decide, by decide, by decide, by omega, by omega⟩
  · simp only [triadicPeriod6Coeff, h4] at hp8_m27 ⊢
    have hm : (512 * 19 * 8 ^ k) % 27 = 17 := by rw [Nat.mul_mod, hp8_m27]
    exact ⟨by decide, by decide, by decide, by decide, by omega, by omega⟩
  · simp only [triadicPeriod6Coeff, h5] at hp8_m27 ⊢
    have hm : (512 * 53 * 8 ^ k) % 27 = 17 := by rw [Nat.mul_mod, hp8_m27]
    exact ⟨by decide, by decide, by decide, by decide, by omega, by omega⟩

theorem collatz_stage1_five_steps (m : Nat) :
    collatzIter 5 (32 * m + 23) = 27 * m + 20 := by
  have h := collatzIter_mod_pow2_universal 5 23 m
  have hs : affineStepSlope 5 23 = 27 := by decide
  have hc : collatzIter 5 23 = 20 := by decide
  simpa [hs, hc] using h

theorem collatz_stage2_neg5_pump : ∀ (j A : Nat),
    A ≥ 1 -> collatzIter (3 * j) (8 ^ j * A - 5) = 9 ^ j * A - 5
  | 0, A, _ => by simp [collatzIter]
  | j + 1, A, hA => by
    let B := 8 ^ j * A
    have hB_pos : B ≥ 1 := Nat.mul_le_mul (pow_pos_base 8 (by decide) j) hA
    have hsplit_arg : 8 ^ (j + 1) * A - 5 = 2 ^ 3 * (B - 1) + 3 := by
      dsimp [B]
      rw [Nat.pow_succ 8 j, Nat.mul_comm (8 ^ j) 8, Nat.mul_assoc]
      change 8 * (8 ^ j * A) - 5 = 8 * (8 ^ j * A - 1) + 3
      omega
    have hstep3 : collatzIter 3 (8 ^ (j + 1) * A - 5) = 8 ^ j * (9 * A) - 5 := by
      rw [hsplit_arg, collatzIter_mod_pow2_universal 3 3 (B - 1)]
      have hs : affineStepSlope 3 3 = 9 := by decide
      have hc : collatzIter 3 3 = 4 := by decide
      rw [hs, hc]
      dsimp [B]
      have hcomm : 9 * (8 ^ j * A) = 8 ^ j * (9 * A) := by
        rw [← Nat.mul_assoc 9 (8 ^ j) A, Nat.mul_comm 9 (8 ^ j), Nat.mul_assoc]
      omega
    rw [show 3 * (j + 1) = 3 + 3 * j by omega, collatzIter_add 3 (3 * j),
        hstep3, collatz_stage2_neg5_pump j (9 * A) (by omega),
        Nat.pow_succ 9 j, Nat.mul_assoc]

theorem collatz_stage3_five_steps (M : Nat) :
    collatzIter 5 (32 * M + 11) = 27 * M + 10 := by
  have h := collatzIter_mod_pow2_universal 5 11 M
  have hs : affineStepSlope 5 11 = 27 := by decide
  have hc : collatzIter 5 11 = 10 := by decide
  simpa [hs, hc] using h

theorem pow2_3k10_lt_pow3_2k6 (k : Nat) (hk : k ≥ 3) :
    2 ^ (3 * k + 10) < 3 ^ (2 * k + 6) := by
  induction k with
  | zero => omega
  | succ k' ih =>
    by_cases hk2 : k' = 2
    · subst hk2; decide
    · have hih := ih (by omega)
      have h2 : 2 ^ (3 * (k' + 1) + 10) = 8 * 2 ^ (3 * k' + 10) := by
        rw [show 3 * (k' + 1) + 10 = (3 * k' + 10) + 3 by omega, Nat.pow_add]
        omega
      have h3 : 3 ^ (2 * (k' + 1) + 6) = 9 * 3 ^ (2 * k' + 6) := by
        rw [show 2 * (k' + 1) + 6 = (2 * k' + 6) + 2 by omega, Nat.pow_add]
        omega
      omega

theorem pow8_eq_pow2_triple : ∀ k : Nat, 8 ^ k = 2 ^ (3 * k)
  | 0 => rfl
  | k + 1 => by
    rw [Nat.pow_succ 8 k, pow8_eq_pow2_triple k,
        show 3 * (k + 1) = 3 * k + 3 by omega, Nat.pow_add]

theorem pow9_eq_pow3_double : ∀ k : Nat, 9 ^ k = 3 ^ (2 * k)
  | 0 => rfl
  | k + 1 => by
    rw [Nat.pow_succ 9 k, pow9_eq_pow3_double k,
        show 2 * (k + 1) = 2 * k + 2 by omega, Nat.pow_add]

theorem pow9_odd_nat : ∀ k : Nat, 9 ^ k % 2 = 1
  | 0 => rfl
  | k + 1 => by rw [Nat.pow_succ, Nat.mul_mod, pow9_odd_nat k]

/--
  Theorem T2.9b (`infinite_triadic_backward_merger_excluded_family`, `∀ k ≥ 3, ∀ q : Nat`):
  Every integer `n = q * 3 ^ (2 * k + 6) + triadicExcludedResidue k` (`k ≥ 3, q ≥ 0`)
  has `triadicExcludedResidue k % 729 = 361` (surviving 100% of `Mod-729` exclusions!),
  is reached in `3 * k + 10` compressed steps from a strictly smaller positive predecessor `n'`,
  and the classes `triadicExcludedResidue k mod 3 ^ (2 * k + 6)` are pairwise disjoint!
-/
theorem infinite_triadic_backward_merger_excluded_family (k q : Nat) (hk : k ≥ 3) :
    let c := triadicPeriod6Coeff k
    let r := triadicExcludedResidue k
    let mod3 := 3 ^ (2 * k + 6)
    let n := q * mod3 + r
    let nPrime := q * 2 ^ (3 * k + 10) + (512 * c * 8 ^ k - 179) / 27
    (512 * c * 8 ^ k - 179) % 27 = 0 ∧
    27 ≤ r ∧ r < mod3 ∧
    r % 729 = 361 ∧ IsSurvivingMod729Residue (r % 729) ∧
    1 ≤ nPrime ∧ nPrime < n ∧
    collatzIter (3 * k + 10) nPrime = n ∧
    (∀ k2 : Nat, k < k2 -> triadicExcludedResidue k2 % mod3 ≠ r) ∧
    ((∀ m : Nat, ¬ (0 < collatzIter m n ∧ collatzIter m n < n)) ->
     (∀ m : Nat, 1 ≤ m -> m < n -> ∃ k1 : Nat, collatzIter k1 m = 1) -> False) := by
  dsimp only
  let c := triadicPeriod6Coeff k
  let r := triadicExcludedResidue k
  let mod3 := 3 ^ (2 * k + 6)
  let n := q * mod3 + r
  let baseNp := (512 * c * 8 ^ k - 179) / 27
  let nPrime := q * 2 ^ (3 * k + 10) + baseNp
  rcases triadicPeriod6Coeff_spec k with ⟨hc_ge1, hc_le53, hc_odd, hc_n3, h512_ge, hdiv27⟩
  change c ≥ 1 at hc_ge1
  change c ≤ 53 at hc_le53
  change c % 2 = 1 at hc_odd
  change c % 3 ≠ 0 at hc_n3
  change 512 * c * 8 ^ k ≥ 512 at h512_ge
  change (512 * c * 8 ^ k - 179) % 27 = 0 at hdiv27
  have hp9_odd : 9 ^ k % 2 = 1 := pow9_odd_nat k
  have hp9_ge729 : 9 ^ k ≥ 729 := by
    rw [show k = 3 + (k - 3) by omega, Nat.pow_add]
    have hp := pow_pos_base 9 (by decide) (k - 3)
    change 729 * 9 ^ (k - 3) ≥ 729; omega
  have hmod3_eq : mod3 = 729 * 9 ^ k := by
    dsimp [mod3]
    rw [Nat.pow_add, pow9_eq_pow3_double k, Nat.mul_comm]
  have h27c9 : 27 * c * 9 ^ k = 27 * (c * 9 ^ k) := Nat.mul_assoc 27 c (9 ^ k)
  have hc9_lo : 729 ≤ c * 9 ^ k := by simpa using Nat.mul_le_mul hc_ge1 hp9_ge729
  have hc9_hi : c * 9 ^ k ≤ 53 * 9 ^ k := Nat.mul_le_mul_right (9 ^ k) hc_le53
  have h2r_eq : 2 * r + 7 = 27 * c * 9 ^ k := by
    change 2 * ((27 * c * 9 ^ k - 7) / 2) + 7 = 27 * c * 9 ^ k
    have hprod_odd : (27 * c * 9 ^ k) % 2 = 1 := by
      rw [Nat.mul_mod, Nat.mul_mod 27 c 2, hc_odd, hp9_odd]
    have hprod_ge : 27 * c * 9 ^ k ≥ 27 * 729 := by
      rw [h27c9]; omega
    omega
  have h2r_assoc : 2 * r + 7 = 27 * (c * 9 ^ k) := by rw [h2r_eq, h27c9]
  have hr_ge27 : 27 ≤ r := by
    omega
  have hr_lt_mod3 : r < mod3 := by
    rw [hmod3_eq]
    omega
  have hr_mod729 : r % 729 = 361 := by
    have hp9_div27 : 9 ^ k = 27 * 3 ^ (2 * k - 3) := by
      rw [pow9_eq_pow3_double k]
      have hs : 2 * k = 3 + (2 * k - 3) := by omega
      rw [congrArg (3 ^ ·) hs, Nat.pow_add]
    have h3_odd : 3 ^ (2 * k - 3) % 2 = 1 := pow3_odd_nat (2 * k - 3)
    let oddProd := c * 3 ^ (2 * k - 3)
    have hodd_p : oddProd % 2 = 1 := by dsimp [oddProd]; rw [Nat.mul_mod, hc_odd, h3_odd]
    let t := oddProd / 2
    have hodd_eq : oddProd = 2 * t + 1 := by dsimp [t]; omega
    have h2r_729 : 2 * r + 7 = 729 * (2 * t + 1) := by
      rw [h2r_eq, hp9_div27]
      calc
        27 * c * (27 * 3 ^ (2 * k - 3))
            = (27 * 27) * (c * 3 ^ (2 * k - 3)) := by
              rw [Nat.mul_assoc 27 c, ← Nat.mul_assoc c 27, Nat.mul_comm c 27,
                  Nat.mul_assoc 27 c, ← Nat.mul_assoc 27 27]
        _ = 729 * oddProd := rfl
        _ = 729 * (2 * t + 1) := by rw [hodd_eq]
    have hr_decomp : r = 729 * t + 361 := by omega
    rw [hr_decomp]; omega
  have hsurv729 : IsSurvivingMod729Residue (r % 729) := by
    rw [hr_mod729]; unfold IsSurvivingMod729Residue; decide
  have h27_base : 27 * baseNp + 179 = 512 * c * 8 ^ k := by dsimp [baseNp]; omega
  have hnp_ge1 : 1 ≤ nPrime := by
    have hb_ge1 : baseNp ≥ 1 := by omega
    dsimp [nPrime]; omega
  have hpow_lt := pow2_3k10_lt_pow3_2k6 k hk
  have h1024_8k : 1024 * 8 ^ k = 2 ^ (3 * k + 10) := by
    rw [pow8_eq_pow2_triple k, Nat.pow_add 2 (3 * k) 10, Nat.mul_comm]
  have hbase_lt_r : baseNp < r := by
    have hlt_exp : 1024 * 8 ^ k < 729 * 9 ^ k := by
      rw [h1024_8k, ← hmod3_eq]; exact hpow_lt
    have hmul_c : c * (1024 * 8 ^ k) < c * (729 * 9 ^ k) :=
      Nat.mul_lt_mul_of_pos_left hlt_exp (by omega)
    have hl : 2 * (512 * c * 8 ^ k) = c * (1024 * 8 ^ k) := by
      rw [← Nat.mul_assoc 2 (512 * c), ← Nat.mul_assoc 2 512 c,
          show 2 * 512 = 1024 from rfl, Nat.mul_comm 1024 c, Nat.mul_assoc]
    have hr_mul : 27 * (27 * c * 9 ^ k) = c * (729 * 9 ^ k) := by
      rw [← Nat.mul_assoc 27 (27 * c), ← Nat.mul_assoc 27 27 c,
          show 27 * 27 = 729 from rfl, Nat.mul_comm 729 c, Nat.mul_assoc]
    omega
  have hnp_lt_n : nPrime < n := by
    dsimp [nPrime, n]
    have hq_le : q * 2 ^ (3 * k + 10) ≤ q * mod3 := Nat.mul_le_mul_left q (by omega)
    omega
  -- 3-Stage exact compressed trajectory `collatzIter (3 * k + 10) nPrime = n`:
  let A := 864 * q + 16 * c
  have hA_pos : A ≥ 1 := by dsimp [A]; omega
  have h27_np : 27 * nPrime + 179 = 32 * (8 ^ k * A) := by
    dsimp [nPrime, A]
    rw [Nat.mul_add, Nat.add_assoc, h27_base, ← h1024_8k]
    calc
      27 * (q * (1024 * 8 ^ k)) + 512 * c * 8 ^ k
          = (27648 * q) * 8 ^ k + (512 * c) * 8 ^ k := by
            rw [← Nat.mul_assoc 27 q, ← Nat.mul_assoc (27 * q) 1024,
                show 27 * q * 1024 = 27648 * q by omega]
      _ = (27648 * q + 512 * c) * 8 ^ k := (Nat.add_mul _ _ (8 ^ k)).symm
      _ = (32 * (864 * q + 16 * c)) * 8 ^ k := by
            rw [show 27648 * q + 512 * c = 32 * (864 * q + 16 * c) by omega]
      _ = 32 * (8 ^ k * (864 * q + 16 * c)) := by
            rw [Nat.mul_assoc 32 _ (8 ^ k), Nat.mul_comm (864 * q + 16 * c) (8 ^ k)]
  have hnp_mod32 : nPrime % 32 = 23 := by omega
  let m1 := nPrime / 32
  have hnp_m1 : nPrime = 32 * m1 + 23 := by
    have hdm := (Nat.div_add_mod nPrime 32).symm
    rw [hnp_mod32] at hdm; exact hdm
  have hm1_target : 27 * m1 + 20 = 8 ^ k * A - 5 := by omega
  have h9kA_eq : 9 ^ k * A = 16 * (9 ^ k * (54 * q + c)) := by
    dsimp [A]
    have h16 : 864 * q + 16 * c = 16 * (54 * q + c) := by omega
    rw [h16, ← Nat.mul_assoc (9 ^ k) 16, Nat.mul_comm (9 ^ k) 16, Nat.mul_assoc]
  have hodd_9k_54 : (9 ^ k * (54 * q + c)) % 2 = 1 := by
    rw [Nat.mul_mod, hp9_odd]; omega
  let M := (9 ^ k * (54 * q + c)) / 2
  have h2M1 : 9 ^ k * (54 * q + c) = 2 * M + 1 := by dsimp [M]; omega
  have h9kA_sub5 : 9 ^ k * A - 5 = 32 * M + 11 := by
    rw [h9kA_eq, h2M1]; omega
  have h27M10_eq_n : 27 * M + 10 = n := by
    have hdouble : 2 * (27 * M + 10) + 7 = 27 * (2 * M + 1) := by omega
    have h2n : 2 * n + 7 = 27 * (9 ^ k * (54 * q + c)) := by
      dsimp [n]
      rw [Nat.mul_add 2 (q * mod3) r, Nat.add_assoc, h2r_eq, hmod3_eq]
      calc
        2 * (q * (729 * 9 ^ k)) + 27 * c * 9 ^ k
            = 27 * (9 ^ k * (54 * q)) + 27 * (9 ^ k * c) := by
              rw [show 2 * (q * (729 * 9 ^ k)) = 27 * (9 ^ k * (54 * q)) by
                    rw [← Nat.mul_assoc 2 q, ← Nat.mul_assoc (2 * q) 729,
                        show 2 * q * 729 = 27 * (54 * q) by omega,
                        Nat.mul_assoc 27 (54 * q) (9 ^ k), Nat.mul_comm (54 * q) (9 ^ k)],
                  Nat.mul_assoc 27 c (9 ^ k), Nat.mul_comm c (9 ^ k)]
        _ = 27 * (9 ^ k * (54 * q + c)) := by rw [← Nat.mul_add 27, ← Nat.mul_add (9 ^ k)]
    rw [← h2M1] at hdouble
    omega
  have hiter_3k10 : collatzIter (3 * k + 10) nPrime = n := by
    rw [show 3 * k + 10 = 5 + (3 * k + 5) by omega,
        collatzIter_add 5 (3 * k + 5) nPrime,
        hnp_m1, collatz_stage1_five_steps m1, hm1_target,
        collatzIter_add (3 * k) 5 (8 ^ k * A - 5),
        collatz_stage2_neg5_pump k A hA_pos,
        h9kA_sub5, collatz_stage3_five_steps M, h27M10_eq_n]
  have hdisj : ∀ k2 : Nat, k < k2 -> triadicExcludedResidue k2 % mod3 ≠ r := by
    intro k2 hlt heq_mod
    let M4 := 3 ^ (2 * k + 4)
    have hmod3_split : mod3 = M4 * 9 := by
      dsimp [mod3, M4]
      rw [show 2 * k + 6 = (2 * k + 4) + 2 by omega, Nat.pow_add]
    have hr_mod : r % mod3 = r := Nat.mod_eq_of_lt hr_lt_mod3
    have hmod_M4 : triadicExcludedResidue k2 % M4 = r % M4 := by
      rw [← mod_mul_mod_eq (triadicExcludedResidue k2) M4 9,
          ← mod_mul_mod_eq r M4 9, ← hmod3_split, heq_mod, hr_mod]
    have h2r7_M4 : (2 * triadicExcludedResidue k2 + 7) % M4 = (2 * r + 7) % M4 := by
      rw [Nat.add_mod, Nat.mul_mod 2 _ M4, hmod_M4, ← Nat.mul_mod, ← Nat.add_mod]
    rcases triadicPeriod6Coeff_spec k2 with ⟨hc2_ge1, _, hc2_odd, _, _, _⟩
    have hp9_k2_odd : 9 ^ k2 % 2 = 1 := pow9_odd_nat k2
    have h2rk2 : 2 * triadicExcludedResidue k2 + 7 = 3 ^ (2 * k2 + 3) * triadicPeriod6Coeff k2 := by
      unfold triadicExcludedResidue
      have hp_odd : (27 * triadicPeriod6Coeff k2 * 9 ^ k2) % 2 = 1 := by
        rw [Nat.mul_mod, Nat.mul_mod 27 _ 2, hc2_odd, hp9_k2_odd]
      have hp9_ge : 9 ^ k2 ≥ 9 := by
        rw [show k2 = 1 + (k2 - 1) by omega, Nat.pow_add]
        have hp := pow_pos_base 9 (by decide) (k2 - 1)
        change 9 * 9 ^ (k2 - 1) ≥ 9; omega
      have hc2_9_lo : 9 ≤ triadicPeriod6Coeff k2 * 9 ^ k2 := by
        simpa using Nat.mul_le_mul hc2_ge1 hp9_ge
      have hge : 27 * triadicPeriod6Coeff k2 * 9 ^ k2 ≥ 27 * 9 := by
        rw [Nat.mul_assoc 27 (triadicPeriod6Coeff k2) (9 ^ k2)]; omega
      have hval : 2 * ((27 * triadicPeriod6Coeff k2 * 9 ^ k2 - 7) / 2) + 7 =
          27 * triadicPeriod6Coeff k2 * 9 ^ k2 := by omega
      rw [hval, pow9_eq_pow3_double k2,
          show 3 ^ (2 * k2 + 3) = 27 * 3 ^ (2 * k2) by
            rw [Nat.add_comm (2 * k2) 3, Nat.pow_add],
          Nat.mul_assoc 27 (3 ^ (2 * k2)), Nat.mul_comm (3 ^ (2 * k2)), ← Nat.mul_assoc]
    have hlhs0 : (2 * triadicExcludedResidue k2 + 7) % M4 = 0 := by
      rw [h2rk2]
      dsimp [M4]
      rw [show 2 * k2 + 3 = (2 * k + 4) + (2 * k2 - 2 * k - 1) by omega,
          Nat.pow_add, Nat.mul_assoc, Nat.mul_mod (3 ^ (2 * k + 4)),
          Nat.mod_self, Nat.zero_mul, Nat.zero_mod]
    have hrhs_ne : (2 * r + 7) % M4 = 3 ^ (2 * k + 3) * (c % 3) := by
      rw [h2r_eq, pow9_eq_pow3_double k]
      have hrew : 27 * c * 3 ^ (2 * k) = 3 ^ (2 * k + 3) * c := by
        rw [show 2 * k + 3 = 3 + 2 * k by omega, Nat.pow_add,
            show (3 : Nat) ^ 3 = 27 from rfl,
            Nat.mul_assoc 27 (3 ^ (2 * k)) c, Nat.mul_comm (3 ^ (2 * k)) c, ← Nat.mul_assoc]
      have hM4_eq : M4 = 3 ^ (2 * k + 3) * 3 := Nat.pow_succ 3 (2 * k + 3)
      rw [hrew, hM4_eq, mul_mod_mul_left_sec9 (3 ^ (2 * k + 3)) c 3 (pow3_pos_nat _) (by decide)]
    rw [hlhs0, hrhs_ne] at h2r7_M4
    have hp3_pos : 3 ^ (2 * k + 3) > 0 := pow3_pos_nat (2 * k + 3)
    have hc_mod3_pos : c % 3 ≥ 1 := by omega
    have hm := Nat.mul_le_mul hp3_pos hc_mod3_pos
    omega
  refine ⟨hdiv27, hr_ge27, hr_lt_mod3, hr_mod729, hsurv729, hnp_ge1, hnp_lt_n, hiter_3k10, hdisj, ?_⟩
  intro hnoDesc hminReach
  exact minimal_counterexample_no_coalescence n nPrime (3 * k + 10) 0
    (by omega) hnoDesc hminReach hnp_ge1 hnp_lt_n
    (by simp only [collatzIter]; exact hiter_3k10)

-- ============================================================================
-- SECTION 10: Track 1 Wave 3 — Sharp 1-Block GCD/Mod-24 Squeeze, Complete
--             `[]`-Axiom 2-Block Cycle Reduction, & Unified Two-Barrier
--             Master Core (`#30/#31`, `T9`–`T11`)
-- ============================================================================

def NoOneBlockPositiveCycles : Prop :=
  ∀ (x0 w1 a1 : Nat),
    x0 > 2 -> w1 ≥ 1 -> a1 ≥ 1 ->
    parityOfIter (w1 + a1) x0 = List.replicate w1 true ++ List.replicate a1 false ->
    collatzIter (w1 + a1) x0 ≠ x0

def NoTwoBlockPositiveCycles : Prop :=
  ∀ (x0 w1 a1 w2 a2 : Nat),
    x0 > 2 -> w1 ≥ 1 -> a1 ≥ 1 -> w2 ≥ 1 -> a2 ≥ 1 ->
    parityOfIter (w1 + a1 + w2 + a2) x0 =
      List.replicate w1 true ++ List.replicate a1 false ++
      (List.replicate w2 true ++ List.replicate a2 false) ->
    collatzIter (w1 + a1 + w2 + a2) x0 ≠ x0

def twoBlockBroxCarry (w1 a1 w2 a2 : Nat) : Nat :=
  let _ := w1
  3 ^ w2 * (2 ^ a1 - 1) + 2 ^ (a1 + w2) * (2 ^ a2 - 1)

def IsPrimitiveTwoBlockBroxWitness (w1 a1 w2 a2 q0 q1 : Nat) : Prop :=
  let W := w1 + w2
  let K := w1 + a1 + w2 + a2
  let D := 2 ^ K - 3 ^ W
  let x0 := 2 ^ w1 * q0 - 1
  let x1 := 2 ^ w2 * q1 - 1
  w1 ≥ 2 ∧ a1 ≥ 1 ∧ w2 ≥ 1 ∧ a2 ≥ 1 ∧
  q0 ≥ 3 ∧ q1 ≥ 3 ∧ q0 % 2 = 1 ∧ q1 % 2 = 1 ∧
  W ≥ 8 ∧ K ≥ 13 ∧
  21 ^ W < 7 ^ W * 2 ^ K ∧ 7 ^ W * 2 ^ K ≤ 22 ^ W ∧
  2 ^ (w1 + a1) < 3 ^ w1 ∧ 3 ^ w2 < 2 ^ (w2 + a2) ∧
  (D % 24 = 5 ∨ D % 24 = 7 ∨ D % 24 = 13 ∨ D % 24 = 23) ∧
  23 * D < 3 ^ W ∧
  x0 ≥ 47 ∧ x1 ≥ x0 + 2 ∧
  (x0 % 96 = 7 ∨ x0 % 96 = 31 ∨ x0 % 96 = 47 ∨ x0 % 96 = 59 ∨
   x0 % 96 = 71 ∨ x0 % 96 = 79 ∨ x0 % 96 = 91 ∨ x0 % 96 = 95) ∧
  x1 % 3 ≠ 0 ∧
  D * q0 = twoBlockBroxCarry w1 a1 w2 a2 ∧
  D * q1 = twoBlockBroxCarry w2 a2 w1 a1 ∧
  27 * 2 ^ (W + a1 - 3) * D ^ 3 < 2 ^ (3 * K)

def SubexponentialCubicGapProp : Prop :=
  ∀ (K W : Nat), W ≥ 6 -> 3 ^ W < 2 ^ K ->
    27 * 2 ^ (W - 2) * (2 ^ K - 3 ^ W) ^ 3 ≥ 2 ^ (3 * K)

def IsWave3SharpenedBroxWitness (w1 : Nat) (init : List Bool) (q0 : Nat) : Prop :=
  IsSharpenedBroxCycleWitness w1 init q0 ∧
  let K := w1 + 2 + init.length
  let W := w1 + parityWeight init
  let D := 2 ^ K - 3 ^ W
  let x0 := 2 ^ w1 * q0 - 1
  (parityWeight init = 0 ->
    let a1 := init.length + 2
    w1 ≥ 13 ∧ a1 ≥ 8 ∧ q0 ≥ 17 ∧
    (q0 % 24 = 3 ∨ q0 % 24 = 9 ∨ q0 % 24 = 17 ∨ q0 % 24 = 19) ∧
    (x0 % 96 = 31 ∨ x0 % 96 = 95) ∧
    D ∣ Nat.gcd (2 ^ a1 - 1) (3 ^ w1 - 2 ^ w1) ∧
    (17 * 3 ^ w1) / (2 ^ a1) = 17 * 2 ^ w1 - 1) ∧
  (∀ (b_a1 w2 a2 : Nat),
    b_a1 ≥ 1 -> w2 ≥ 1 -> a2 ≥ 1 ->
    false :: (init ++ [false]) =
      List.replicate b_a1 false ++ (List.replicate w2 true ++ List.replicate a2 false) ->
    ∃ q1 : Nat, IsPrimitiveTwoBlockBroxWitness w1 b_a1 w2 a2 q0 q1)

-- ----------------------------------------------------------------------------
-- T9: Sharp 1-Block GCD Lock, `{2, 3}`-Smooth Quotient Elimination,
--     Mod-24/Mod-96 Squeeze, & Exact `↔` Equivalence (`[]` Axioms)
-- ----------------------------------------------------------------------------

theorem pow2_mod24_ge3 : ∀ k : Nat, k ≥ 3 ->
    (k % 2 = 0 -> 2 ^ k % 24 = 16) ∧ (k % 2 = 1 -> 2 ^ k % 24 = 8)
  | 0, hk => by omega
  | 1, hk => by omega
  | 2, hk => by omega
  | 3, _ => ⟨fun h => by omega, fun _ => rfl⟩
  | k + 4, _ => by
    rcases pow2_mod24_ge3 (k + 3) (by omega) with ⟨hev, hodd⟩
    refine ⟨?_, ?_⟩
    · intro h0
      have h1 : (k + 3) % 2 = 1 := by omega
      rw [Nat.pow_succ, Nat.mul_mod, hodd h1]
    · intro h1
      have h0 : (k + 3) % 2 = 0 := by omega
      rw [Nat.pow_succ, Nat.mul_mod, hev h0]

theorem pow3_mod24_ge1 : ∀ w : Nat, w ≥ 1 ->
    (w % 2 = 0 -> 3 ^ w % 24 = 9) ∧ (w % 2 = 1 -> 3 ^ w % 24 = 3)
  | 0, hw => by omega
  | 1, _ => ⟨fun h => by omega, fun _ => rfl⟩
  | w + 2, _ => by
    rcases pow3_mod24_ge1 (w + 1) (by omega) with ⟨hev, hodd⟩
    refine ⟨?_, ?_⟩
    · intro h0
      have h1 : (w + 1) % 2 = 1 := by omega
      rw [Nat.pow_succ, Nat.mul_mod, hodd h1]
    · intro h1
      have h0 : (w + 1) % 2 = 0 := by omega
      rw [Nat.pow_succ, Nat.mul_mod, hev h0]

theorem det_mod24_and_ge5_constructive (K W : Nat)
    (hK : K ≥ 3) (hW : W ≥ 1) (hgt : 3 ^ W < 2 ^ K) :
    let D := 2 ^ K - 3 ^ W
    (D % 24 = 5 ∨ D % 24 = 7 ∨ D % 24 = 13 ∨ D % 24 = 23) ∧ D ≥ 5 := by
  dsimp only
  let D := 2 ^ K - 3 ^ W
  have hadd : (D + 3 ^ W) % 24 = 2 ^ K % 24 := by dsimp [D]; rw [Nat.sub_add_cancel (by omega)]
  rcases pow2_mod24_ge3 K hK with ⟨hK_ev, hK_odd⟩
  rcases pow3_mod24_ge1 W hW with ⟨hW_ev, hW_odd⟩
  have hD24 : D % 24 = 5 ∨ D % 24 = 7 ∨ D % 24 = 13 ∨ D % 24 = 23 := by
    by_cases hk : K % 2 = 0 <;> by_cases hw : W % 2 = 0
    · rw [hK_ev hk] at hadd
      have hw24 := hW_ev hw
      rw [Nat.add_mod, hw24] at hadd; omega
    · rw [hK_ev hk] at hadd
      have hw24 := hW_odd (by omega)
      rw [Nat.add_mod, hw24] at hadd; omega
    · rw [hK_odd (by omega)] at hadd
      have hw24 := hW_ev hw
      rw [Nat.add_mod, hw24] at hadd; omega
    · rw [hK_odd (by omega)] at hadd
      have hw24 := hW_odd (by omega)
      rw [Nat.add_mod, hw24] at hadd; omega
  exact ⟨hD24, by omega⟩

/--
  Theorem T9a (`one_block_gcd_and_congruence_lock`, `[]` axioms):
  Universal GCD & Congruence Lock on 1-Block Positive Cycles:
  Whenever `w1 ≥ 2`, `a1 ≥ 1`, `3 ^ w1 < 2 ^ (w1 + a1)`, and `(2 ^ (w1 + a1) - 3 ^ w1) * q0 = 2 ^ a1 - 1`,
  letting `D := 2 ^ (w1 + a1) - 3 ^ w1` and `x0 := 2 ^ w1 * q0 - 1`:
  `3 ^ w1 - 2 ^ w1 = D * x0`, `3 ^ w1 * q0 - 1 = 2 ^ a1 * x0`,
  `D ∣ Nat.gcd (2 ^ a1 - 1) (3 ^ w1 - 2 ^ w1)`, `2 ^ a1 % D = 1`, and `2 ^ w1 % D = 3 ^ w1 % D`.
-/
theorem one_block_gcd_and_congruence_lock (w1 a1 q0 : Nat)
    (hw1 : w1 ≥ 2) (ha1 : a1 ≥ 1) (hgt : 3 ^ w1 < 2 ^ (w1 + a1))
    (hbrox : (2 ^ (w1 + a1) - 3 ^ w1) * q0 = 2 ^ a1 - 1) :
    let D := 2 ^ (w1 + a1) - 3 ^ w1
    let x0 := 2 ^ w1 * q0 - 1
    q0 ≥ 1 ∧ q0 % 2 = 1 ∧
    3 ^ w1 - 2 ^ w1 = D * x0 ∧
    3 ^ w1 * q0 - 1 = 2 ^ a1 * x0 ∧
    D ∣ Nat.gcd (2 ^ a1 - 1) (3 ^ w1 - 2 ^ w1) ∧
    2 ^ a1 % D = 1 ∧
    2 ^ w1 % D = 3 ^ w1 % D := by
  dsimp only
  let D := 2 ^ (w1 + a1) - 3 ^ w1
  let x0 := 2 ^ w1 * q0 - 1
  change D * q0 = 2 ^ a1 - 1 at hbrox
  have hp2a1_ge2 : 2 ^ a1 ≥ 2 := by
    rw [show a1 = (a1 - 1) + 1 by omega, Nat.pow_succ]
    have hp := pow2_pos_nat (a1 - 1); omega
  have hp2a1_ev : 2 ^ a1 % 2 = 0 := by
    rw [show a1 = (a1 - 1) + 1 by omega, Nat.pow_succ]; omega
  have hrhs_odd : (2 ^ a1 - 1) % 2 = 1 := by omega
  have hq0_ge1 : q0 ≥ 1 := by
    cases q0 with
    | zero => rw [Nat.mul_zero] at hbrox; omega
    | succ _ => omega
  have hq0_odd : q0 % 2 = 1 := by
    by_cases ho : q0 % 2 = 1
    · exact ho
    · have hev : (D * q0) % 2 = 0 := by
        rw [Nat.mul_mod, show q0 % 2 = 0 by omega, Nat.mul_zero, Nat.zero_mod]
      rw [hbrox] at hev; omega
  have hD_ge5 : D ≥ 5 :=
    (det_mod24_and_ge5_constructive (w1 + a1) w1 (by omega) (by omega) hgt).2
  have h2w_lt_3w : 2 ^ w1 < 3 ^ w1 := by
    have hp := pow2_succ_lt_pow3 w1 hw1
    have h2 : 2 ^ w1 ≤ 2 ^ (w1 + 1) := pow2_mono_nat (by omega)
    omega
  have hp2w_ge4 : 2 ^ w1 ≥ 4 := by simpa using pow2_mono_nat hw1
  have hx0_p1 : x0 + 1 = 2 ^ w1 * q0 := by
    have hm := Nat.mul_le_mul hp2w_ge4 hq0_ge1
    dsimp [x0]; omega
  have hDx0_add : D * x0 + D = 2 ^ w1 * (2 ^ a1 - 1) := by
    calc
      D * x0 + D = D * (x0 + 1) := by rw [Nat.mul_add, Nat.mul_one]
      _ = D * (2 ^ w1 * q0) := by rw [hx0_p1]
      _ = 2 ^ w1 * (D * q0) := by rw [← Nat.mul_assoc, Nat.mul_comm D, Nat.mul_assoc]
      _ = 2 ^ w1 * (2 ^ a1 - 1) := by rw [hbrox]
  have hlin_comb : 2 ^ w1 * (2 ^ a1 - 1) = (3 ^ w1 - 2 ^ w1) + D := by
    have h1 : 2 ^ w1 * (2 ^ a1 - 1) + 2 ^ w1 = 2 ^ (w1 + a1) := by
      calc
        2 ^ w1 * (2 ^ a1 - 1) + 2 ^ w1 = 2 ^ w1 * ((2 ^ a1 - 1) + 1) := by
          rw [Nat.mul_add, Nat.mul_one]
        _ = 2 ^ w1 * 2 ^ a1 := by rw [Nat.sub_add_cancel (by omega)]
        _ = 2 ^ (w1 + a1) := (Nat.pow_add 2 w1 a1).symm
    have h2 : D + 3 ^ w1 = 2 ^ (w1 + a1) := by dsimp [D]; omega
    omega
  have hcarry_eq : 3 ^ w1 - 2 ^ w1 = D * x0 := by omega
  have hsyr_eq : 3 ^ w1 * q0 - 1 = 2 ^ a1 * x0 := by
    have h1 : 2 ^ a1 * x0 + 2 ^ a1 = (2 ^ a1 - 1) + 3 ^ w1 * q0 := by
      calc
        2 ^ a1 * x0 + 2 ^ a1 = 2 ^ a1 * (x0 + 1) := by rw [Nat.mul_add, Nat.mul_one]
        _ = 2 ^ a1 * (2 ^ w1 * q0) := by rw [hx0_p1]
        _ = 2 ^ (w1 + a1) * q0 := by
              rw [← Nat.mul_assoc, Nat.mul_comm (2 ^ a1) (2 ^ w1), ← Nat.pow_add]
        _ = (D + 3 ^ w1) * q0 := by rw [show D + 3 ^ w1 = 2 ^ (w1 + a1) by dsimp [D]; omega]
        _ = D * q0 + 3 ^ w1 * q0 := Nat.add_mul D (3 ^ w1) q0
        _ = (2 ^ a1 - 1) + 3 ^ w1 * q0 := by rw [hbrox]
    have h3q_pos : 3 ^ w1 * q0 ≥ 1 := by
      simpa using Nat.mul_le_mul (pow3_pos_nat w1) hq0_ge1
    omega
  have hdvd_gcd : D ∣ Nat.gcd (2 ^ a1 - 1) (3 ^ w1 - 2 ^ w1) :=
    Nat.dvd_gcd ⟨q0, hbrox.symm⟩ ⟨x0, hcarry_eq⟩
  have hmod_a1 : 2 ^ a1 % D = 1 := by
    have hrew : 2 ^ a1 = 1 + D * q0 := by omega
    rw [hrew, Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod,
        Nat.add_zero, Nat.mod_mod, Nat.mod_eq_of_lt (by omega)]
  have hmod_w1 : 2 ^ w1 % D = 3 ^ w1 % D := by
    have hrew : 3 ^ w1 = 2 ^ w1 + D * x0 := by omega
    rw [hrew, Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod,
        Nat.add_zero, Nat.mod_mod]
  exact ⟨hq0_ge1, hq0_odd, hcarry_eq, hsyr_eq, hdvd_gcd, hmod_a1, hmod_w1⟩

theorem two_mul_add_one_le_pow3 : ∀ r : Nat, 2 * r + 1 ≤ 3 ^ r
  | 0 => by decide
  | r + 1 => by
    have ih := two_mul_add_one_le_pow3 r
    rw [Nat.pow_succ]; omega

theorem seven_mul_pow2_le_pow3_ge13 (w : Nat) (hw : w ≥ 13) :
    7 * w * 2 ^ w ≤ 3 ^ w := by
  induction w with
  | zero => omega
  | succ m ih =>
    by_cases hm12 : m = 12
    · subst hm12; decide
    · have hih := ih (by omega)
      have h2 : 7 * (m + 1) * 2 ^ (m + 1) = (14 * m + 14) * 2 ^ m := by
        rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm (7 * (m + 1) * 2 ^ m) 2]
        calc
          2 * (7 * (m + 1) * 2 ^ m) = (2 * (7 * (m + 1))) * 2 ^ m := (Nat.mul_assoc _ _ _).symm
          _ = (14 * m + 14) * 2 ^ m := by rw [show 2 * (7 * (m + 1)) = 14 * m + 14 by omega]
      have hle21 : (14 * m + 14) * 2 ^ m ≤ (21 * m) * 2 ^ m :=
        Nat.mul_le_mul_right (2 ^ m) (by omega)
      have h21_eq : (21 * m) * 2 ^ m = 3 * (7 * m * 2 ^ m) := by
        rw [show 21 * m = 3 * (7 * m) by omega, Nat.mul_assoc 3 (7 * m) (2 ^ m)]
      have h3_step : 3 * (7 * m * 2 ^ m) ≤ 3 ^ (m + 1) := by
        rw [Nat.pow_succ 3 m, Nat.mul_comm (3 ^ m) 3]
        exact Nat.mul_le_mul_left 3 hih
      omega

theorem one_block_w1_ge_13_and_a1_ge_8 (w1 a1 : Nat)
    (hw1 : w1 ≥ 2) (ha1 : a1 ≥ 1)
    (hgt : 3 ^ w1 < 2 ^ (w1 + a1))
    (hD_le : 2 ^ (w1 + a1) - 3 ^ w1 ≤ 2 ^ a1 - 1) :
    w1 ≥ 13 ∧ a1 ≥ 8 := by
  have hprod_lt : (2 ^ w1 - 1) * 2 ^ a1 < 3 ^ w1 := by
    have hp2w : 2 ^ w1 ≥ 4 := by simpa using pow2_mono_nat hw1
    have hp2a : 2 ^ a1 ≥ 2 := by simpa using pow2_mono_nat ha1
    have hsplit : 2 ^ (w1 + a1) = (2 ^ w1 - 1) * 2 ^ a1 + 2 ^ a1 := by
      calc
        2 ^ (w1 + a1) = 2 ^ w1 * 2 ^ a1 := Nat.pow_add 2 w1 a1
        _ = ((2 ^ w1 - 1) + 1) * 2 ^ a1 := by rw [Nat.sub_add_cancel (by omega)]
        _ = (2 ^ w1 - 1) * 2 ^ a1 + 2 ^ a1 := by rw [Nat.add_mul, Nat.one_mul]
    omega
  have hw1_ge13 : w1 ≥ 13 := by
    by_cases hw13 : w1 ≥ 13
    · exact hw13
    · exfalso
      have hw_cases :
          w1 = 2 ∨ w1 = 3 ∨ w1 = 4 ∨ w1 = 5 ∨ w1 = 6 ∨ w1 = 7 ∨
          w1 = 8 ∨ w1 = 9 ∨ w1 = 10 ∨ w1 = 11 ∨ w1 = 12 := by omega
      by_cases ha8 : a1 ≥ 8
      · have hp256 : 256 ≤ 2 ^ a1 := by simpa using pow2_mono_nat ha8
        have hm := Nat.mul_le_mul_left (2 ^ w1 - 1) hp256
        rcases hw_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          omega
      · have ha_cases :
            a1 = 1 ∨ a1 = 2 ∨ a1 = 3 ∨ a1 = 4 ∨ a1 = 5 ∨ a1 = 6 ∨ a1 = 7 := by omega
        rcases hw_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          rcases ha_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          omega
  have ha1_ge8 : a1 ≥ 8 := by
    have h3_13 : 2 ^ 20 < 3 ^ 13 := by decide
    have h2_le_3 : 2 ^ (w1 - 13) ≤ 3 ^ (w1 - 13) := pow2_le_pow3 (w1 - 13)
    have hmul : 2 ^ 20 * 2 ^ (w1 - 13) < 3 ^ 13 * 3 ^ (w1 - 13) := by
      have hm1 : 2 ^ 20 * 2 ^ (w1 - 13) < 3 ^ 13 * 2 ^ (w1 - 13) :=
        Nat.mul_lt_mul_of_pos_right h3_13 (pow2_pos_nat _)
      have hm2 : 3 ^ 13 * 2 ^ (w1 - 13) ≤ 3 ^ 13 * 3 ^ (w1 - 13) :=
        Nat.mul_le_mul_left _ h2_le_3
      omega
    rw [← Nat.pow_add 2 20 (w1 - 13), ← Nat.pow_add 3 13 (w1 - 13),
        show 20 + (w1 - 13) = w1 + 7 by omega,
        show 13 + (w1 - 13) = w1 by omega] at hmul
    by_cases ha8 : a1 ≥ 8
    · exact ha8
    · have hle : 2 ^ (w1 + a1) ≤ 2 ^ (w1 + 7) := pow2_mono_nat (by omega)
      omega
  exact ⟨hw1_ge13, ha1_ge8⟩

theorem eq_add_sub_of_add_eq (X A B Y M : Nat)
    (hBA : B ≤ A) (h1 : X + A = M) (h2 : B + Y = M) :
    Y = X + (A - B) := by omega

theorem mod24_add_cancel_helper (r p3 p2 : Nat) (hr : r < 24)
    (hadd : (r + p3) % 24 = p2) :
    (p3 = 9 ∧ p2 = 16 -> r = 7) ∧
    (p3 = 9 ∧ p2 = 8  -> r = 23) ∧
    (p3 = 3 ∧ p2 = 8  -> r = 5) ∧
    (p3 = 3 ∧ p2 = 16 -> r = 13) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (rintro ⟨rfl, rfl⟩; omega)

theorem mod24_sub1_helper (a : Nat) (ha : a ≥ 2) :
    (a % 24 = 16 -> (a - 1) % 24 = 15) ∧
    (a % 24 = 8  -> (a - 1) % 24 = 7) := by
  have hadd : ((a - 1) % 24 + 1) % 24 = a % 24 := by
    conv => rhs; rw [show a = (a - 1) + 1 by omega, Nat.add_mod]
  have hlt : (a - 1) % 24 < 24 := Nat.mod_lt (a - 1) (by decide)
  generalize (a - 1) % 24 = r at hadd hlt
  refine ⟨?_, ?_⟩ <;> (intro hm; rw [hm] at hadd; omega)

theorem solve_brox_mod24_unit (d r rhs : Nat) (hr : r < 24)
    (hprod : (d * r) % 24 = rhs) :
    (d = 7  ∧ rhs = 15 -> r = 9) ∧
    (d = 23 ∧ rhs = 7  -> r = 17) ∧
    (d = 5  ∧ rhs = 15 -> r = 3) ∧
    (d = 13 ∧ rhs = 7  -> r = 19) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (rintro ⟨rfl, rfl⟩; omega)

theorem mod96_of_mod32_31_nondiv3 (x0 : Nat)
    (h32 : x0 % 32 = 31) (h3 : x0 % 3 ≠ 0) :
    x0 % 96 = 31 ∨ x0 % 96 = 95 := by
  have hr32 : (x0 % 96) % 32 = x0 % 32 := mod_mul_mod_eq x0 32 3
  have hr3 : (x0 % 96) % 3 = x0 % 3 := mod_mul_mod_eq x0 3 32
  have hlt96 : x0 % 96 < 96 := Nat.mod_lt x0 (by decide)
  rw [h32] at hr32
  generalize x0 % 96 = r at hr32 hr3 hlt96
  omega

theorem one_block_no_pow3_quotient (w1 a1 q0 D : Nat)
    (hw1 : w1 ≥ 2) (hw13 : w1 ≥ 13) (ha1 : a1 ≥ 1)
    (hgt : 3 ^ w1 < 2 ^ (w1 + a1))
    (hD : D = 2 ^ (w1 + a1) - 3 ^ w1)
    (hD_ge5 : D ≥ 5)
    (hbrox : D * q0 = 2 ^ a1 - 1) :
    ∀ r : Nat, q0 ≠ 3 ^ r := by
  intro r hqr
  subst hqr
  have hp2w : 2 ^ w1 ≥ 4 := by simpa using pow2_mono_nat hw1
  have hp3r : 3 ^ r ≥ 1 := pow3_pos_nat r
  have h2w3r_pos : 2 ^ w1 * 3 ^ r ≥ 4 := by simpa using Nat.mul_le_mul hp2w hp3r
  have hfactor : 3 ^ (w1 + r) - 1 = 2 ^ a1 * (2 ^ w1 * 3 ^ r - 1) := by
    have h1 : 2 ^ a1 * (2 ^ w1 * 3 ^ r - 1) + 2 ^ a1 = 2 ^ (w1 + a1) * 3 ^ r := by
      calc
        2 ^ a1 * (2 ^ w1 * 3 ^ r - 1) + 2 ^ a1
            = 2 ^ a1 * ((2 ^ w1 * 3 ^ r - 1) + 1) := by rw [Nat.mul_add, Nat.mul_one]
        _ = 2 ^ a1 * (2 ^ w1 * 3 ^ r) := by rw [Nat.sub_add_cancel (by omega)]
        _ = 2 ^ (w1 + a1) * 3 ^ r := by
              rw [← Nat.mul_assoc, Nat.mul_comm (2 ^ a1) (2 ^ w1), ← Nat.pow_add]
    have h2 : D * 3 ^ r + 3 ^ (w1 + r) = 2 ^ (w1 + a1) * 3 ^ r := by
      rw [Nat.pow_add 3 w1 r, ← Nat.add_mul D (3 ^ w1) (3 ^ r),
          show D + 3 ^ w1 = 2 ^ (w1 + a1) by omega]
    have hp2a : 2 ^ a1 ≥ 2 := by simpa using pow2_mono_nat ha1
    have hsub := eq_add_sub_of_add_eq (2 ^ a1 * (2 ^ w1 * 3 ^ r - 1)) (2 ^ a1)
      (D * 3 ^ r) (3 ^ (w1 + r)) (2 ^ (w1 + a1) * 3 ^ r) (by omega) h1 h2
    omega
  have hdvd : 2 ^ a1 ∣ (3 ^ (w1 + r) - 1) := ⟨2 ^ w1 * 3 ^ r - 1, hfactor⟩
  have hlte := pow2_dvd_pow3_sub_one_le_four_mul (w1 + r) a1 (by omega) hdvd
  have h5_lt : 5 * 3 ^ r < 2 ^ a1 := by
    have hm : 5 * 3 ^ r ≤ D * 3 ^ r := Nat.mul_le_mul_right (3 ^ r) hD_ge5
    have hp2a : 2 ^ a1 ≥ 2 := by simpa using pow2_mono_nat ha1
    omega
  have hr_lin := two_mul_add_one_le_pow3 r
  have h2a_lt_7w : 2 ^ a1 < 7 * w1 := by omega
  have hm_exp : 2 ^ (w1 + a1) < 7 * w1 * 2 ^ w1 := by
    rw [Nat.pow_add 2 w1 a1, Nat.mul_comm (7 * w1) (2 ^ w1)]
    exact Nat.mul_lt_mul_of_pos_left h2a_lt_7w (pow2_pos_nat w1)
  have h7_le := seven_mul_pow2_le_pow3_ge13 w1 hw13
  omega

theorem one_block_q0_mod24_lock (w1 a1 q0 D : Nat)
    (hw1 : w1 ≥ 2) (ha8 : a1 ≥ 8)
    (hgt : 3 ^ w1 < 2 ^ (w1 + a1))
    (hD : D = 2 ^ (w1 + a1) - 3 ^ w1)
    (hbrox : D * q0 = 2 ^ a1 - 1) :
    (w1 % 2 = 0 -> q0 % 24 = 9 ∨ q0 % 24 = 17) ∧
    (w1 % 2 = 1 -> q0 % 24 = 3 ∨ q0 % 24 = 19) := by
  rcases pow2_mod24_ge3 (w1 + a1) (by omega) with ⟨hK24_ev, hK24_odd⟩
  rcases pow2_mod24_ge3 a1 (by omega) with ⟨ha24_ev, ha24_odd⟩
  rcases pow3_mod24_ge1 w1 (by omega) with ⟨hw24_ev, hw24_odd⟩
  have hD_add24 : (D + 3 ^ w1) % 24 = 2 ^ (w1 + a1) % 24 := by
    rw [show D + 3 ^ w1 = 2 ^ (w1 + a1) by omega]
  have hp2a_ge2 : 2 ^ a1 ≥ 2 := by simpa using pow2_mono_nat (by omega : 1 ≤ a1)
  have hbrox24 : ((D % 24) * (q0 % 24)) % 24 = (2 ^ a1 - 1) % 24 := by
    rw [← Nat.mul_mod, hbrox]
  have hq24_lt : q0 % 24 < 24 := Nat.mod_lt q0 (by decide)
  have hD24_lt : D % 24 < 24 := Nat.mod_lt D (by decide)
  have hcancel := mod24_add_cancel_helper (D % 24) (3 ^ w1 % 24) (2 ^ (w1 + a1) % 24) hD24_lt
    (by rw [← Nat.add_mod]; exact hD_add24)
  have hsub1 := mod24_sub1_helper (2 ^ a1) hp2a_ge2
  have hsolve := solve_brox_mod24_unit (D % 24) (q0 % 24) ((2 ^ a1 - 1) % 24) hq24_lt hbrox24
  refine ⟨?_, ?_⟩
  · intro hw_ev
    have hw3 := hw24_ev hw_ev
    by_cases ha_ev : a1 % 2 = 0
    · left
      exact hsolve.1 ⟨hcancel.1 ⟨hw3, hK24_ev (by omega)⟩, hsub1.1 (ha24_ev ha_ev)⟩
    · right
      exact hsolve.2.1 ⟨hcancel.2.1 ⟨hw3, hK24_odd (by omega)⟩, hsub1.2 (ha24_odd (by omega))⟩
  · intro hw_odd
    have hw3 := hw24_odd hw_odd
    by_cases ha_ev : a1 % 2 = 0
    · left
      exact hsolve.2.2.1 ⟨hcancel.2.2.1 ⟨hw3, hK24_odd (by omega)⟩, hsub1.1 (ha24_ev ha_ev)⟩
    · right
      exact hsolve.2.2.2 ⟨hcancel.2.2.2 ⟨hw3, hK24_ev (by omega)⟩, hsub1.2 (ha24_odd (by omega))⟩

theorem one_block_x0_mod96_lock (w1 a1 q0 x0 : Nat)
    (hw13 : w1 ≥ 13) (hq0_ge1 : q0 ≥ 1)
    (hx0 : x0 = 2 ^ w1 * q0 - 1)
    (hsyr : 3 ^ w1 * q0 - 1 = 2 ^ a1 * x0) :
    x0 % 96 = 31 ∨ x0 % 96 = 95 := by
  have hx0_mod32 : x0 % 32 = 31 := by
    have h2w_32 : 2 ^ w1 = 32 * 2 ^ (w1 - 5) := by
      conv => lhs; rw [show w1 = 5 + (w1 - 5) by omega]
      rw [Nat.pow_add]
    have hp_pos : 2 ^ (w1 - 5) * q0 ≥ 1 := Nat.mul_le_mul (pow2_pos_nat _) hq0_ge1
    rw [hx0, h2w_32, Nat.mul_assoc]
    generalize 2 ^ (w1 - 5) * q0 = m at hp_pos
    omega
  have hx0_n3 : x0 % 3 ≠ 0 := by
    intro hx3
    have hrhs3 : (2 ^ a1 * x0) % 3 = 0 := by rw [Nat.mul_mod, hx3, Nat.mul_zero, Nat.zero_mod]
    have h3w_eq : 3 ^ w1 * q0 = 3 * (3 ^ (w1 - 1) * q0) := by
      conv => lhs; rw [show w1 = (w1 - 1) + 1 by omega]
      rw [Nat.pow_succ, Nat.mul_comm (3 ^ (w1 - 1)) 3, Nat.mul_assoc]
    have h3w_pos : 3 ^ (w1 - 1) * q0 ≥ 1 :=
      Nat.mul_le_mul (pow3_pos_nat (w1 - 1)) hq0_ge1
    rw [← hsyr, h3w_eq] at hrhs3
    generalize 3 ^ (w1 - 1) * q0 = m at h3w_pos hrhs3
    omega
  exact mod96_of_mod32_31_nondiv3 x0 hx0_mod32 hx0_n3

theorem one_block_17fold_prefix_squeeze (w1 a1 D : Nat)
    (hw1 : w1 ≥ 2) (ha1 : a1 ≥ 1) (hgt : 3 ^ w1 < 2 ^ (w1 + a1))
    (hD : D = 2 ^ (w1 + a1) - 3 ^ w1)
    (h17D_le : 17 * D ≤ 2 ^ a1 - 1) :
    (17 * 3 ^ w1) / (2 ^ a1) = 17 * 2 ^ w1 - 1 := by
  have hp2w : 2 ^ w1 ≥ 4 := by simpa using pow2_mono_nat hw1
  have hp2a : 2 ^ a1 ≥ 2 := by simpa using pow2_mono_nat ha1
  have h1 : 2 ^ a1 * (17 * 2 ^ w1 - 1) + 2 ^ a1 = 17 * 2 ^ (w1 + a1) := by
    calc
      2 ^ a1 * (17 * 2 ^ w1 - 1) + 2 ^ a1
          = 2 ^ a1 * ((17 * 2 ^ w1 - 1) + 1) := by rw [Nat.mul_add, Nat.mul_one]
      _ = 2 ^ a1 * (17 * 2 ^ w1) := by rw [Nat.sub_add_cancel (by omega)]
      _ = 17 * (2 ^ w1 * 2 ^ a1) := by
            rw [← Nat.mul_assoc, Nat.mul_comm (2 ^ a1) 17, Nat.mul_assoc,
                Nat.mul_comm (2 ^ a1) (2 ^ w1)]
      _ = 17 * 2 ^ (w1 + a1) := by rw [← Nat.pow_add]
  have h2 : 17 * D + 17 * 3 ^ w1 = 17 * 2 ^ (w1 + a1) := by
    rw [← Nat.mul_add 17 D (3 ^ w1), show D + 3 ^ w1 = 2 ^ (w1 + a1) by omega]
  have hdecomp : 17 * 3 ^ w1 = 2 ^ a1 * (17 * 2 ^ w1 - 1) + (2 ^ a1 - 17 * D) :=
    eq_add_sub_of_add_eq (2 ^ a1 * (17 * 2 ^ w1 - 1)) (2 ^ a1) (17 * D)
      (17 * 3 ^ w1) (17 * 2 ^ (w1 + a1)) (by omega) h1 h2
  have hrem_lt : 2 ^ a1 - 17 * D < 2 ^ a1 := by omega
  have hdm := div_mod_of_mul_add_lt (2 ^ a1) (17 * 2 ^ w1 - 1) (2 ^ a1 - 17 * D) hrem_lt
  rw [← hdecomp] at hdm
  exact hdm.2

/--
  Theorem T9b (`one_block_no_pow3_quotient_and_q0_ge_17`, `[]` axioms):
  Universal Elimination of ALL `{2, 3}`-Smooth Quotients `q0 = 3^r`, Mod-24/Mod-96 Squeeze,
  `q0 ≥ 17` (`q0 ≥ 19` for odd `w1`), `w1 ≥ 13, a1 ≥ 8`, and `17`-Fold Binary Prefix Squeeze!
-/
theorem one_block_no_pow3_quotient_and_q0_ge_17 (w1 a1 q0 : Nat)
    (hw1 : w1 ≥ 2) (ha1 : a1 ≥ 1) (hgt : 3 ^ w1 < 2 ^ (w1 + a1))
    (hbrox : (2 ^ (w1 + a1) - 3 ^ w1) * q0 = 2 ^ a1 - 1) :
    let x0 := 2 ^ w1 * q0 - 1
    w1 ≥ 13 ∧ a1 ≥ 8 ∧
    (∀ r : Nat, q0 ≠ 3 ^ r) ∧
    (q0 % 24 = 3 ∨ q0 % 24 = 9 ∨ q0 % 24 = 17 ∨ q0 % 24 = 19) ∧
    q0 ≥ 17 ∧
    (w1 % 2 = 1 -> q0 ≥ 19) ∧
    (x0 % 96 = 31 ∨ x0 % 96 = 95) ∧
    (17 * 3 ^ w1) / (2 ^ a1) = 17 * 2 ^ w1 - 1 := by
  dsimp only
  rcases one_block_gcd_and_congruence_lock w1 a1 q0 hw1 ha1 hgt hbrox with
    ⟨hq0_ge1, _, _, hsyr_eq, _, _, _⟩
  have hD_le : 2 ^ (w1 + a1) - 3 ^ w1 ≤ 2 ^ a1 - 1 := by
    have hm := Nat.mul_le_mul_left (2 ^ (w1 + a1) - 3 ^ w1) hq0_ge1
    rw [Nat.mul_one, hbrox] at hm; exact hm
  rcases one_block_w1_ge_13_and_a1_ge_8 w1 a1 hw1 ha1 hgt hD_le with ⟨hw13, ha8⟩
  have hD_ge5 : 2 ^ (w1 + a1) - 3 ^ w1 ≥ 5 :=
    (det_mod24_and_ge5_constructive (w1 + a1) w1 (by omega) (by omega) hgt).2
  have hno_pow3 := one_block_no_pow3_quotient w1 a1 q0 (2 ^ (w1 + a1) - 3 ^ w1)
    hw1 hw13 ha1 hgt rfl hD_ge5 hbrox
  have hmod24_split := one_block_q0_mod24_lock w1 a1 q0 (2 ^ (w1 + a1) - 3 ^ w1)
    hw1 ha8 hgt rfl hbrox
  have hq24_4 : q0 % 24 = 3 ∨ q0 % 24 = 9 ∨ q0 % 24 = 17 ∨ q0 % 24 = 19 := by
    by_cases hw_ev : w1 % 2 = 0
    · rcases hmod24_split.1 hw_ev with h9 | h17
      · exact Or.inr (Or.inl h9)
      · exact Or.inr (Or.inr (Or.inl h17))
    · rcases hmod24_split.2 (by omega) with h3 | h19
      · exact Or.inl h3
      · exact Or.inr (Or.inr (Or.inr h19))
  have hq_odd_w1 : w1 % 2 = 1 -> q0 ≥ 19 := by
    intro hw_odd
    have hne3 : q0 ≠ 3 := hno_pow3 1
    rcases hmod24_split.2 hw_odd with h3 | h19 <;> omega
  have hq_ge17 : q0 ≥ 17 := by
    by_cases hw_ev : w1 % 2 = 0
    · have hne9 : q0 ≠ 9 := hno_pow3 2
      rcases hmod24_split.1 hw_ev with h9 | h17 <;> omega
    · have h19 := hq_odd_w1 (by omega); omega
  have hx0_96 := one_block_x0_mod96_lock w1 a1 q0 (2 ^ w1 * q0 - 1) hw13 hq0_ge1 rfl hsyr_eq
  have h17D_le : 17 * (2 ^ (w1 + a1) - 3 ^ w1) ≤ 2 ^ a1 - 1 := by
    have hm := Nat.mul_le_mul_right (2 ^ (w1 + a1) - 3 ^ w1) hq_ge17
    rw [Nat.mul_comm q0 _, hbrox] at hm; exact hm
  have hdiv17 := one_block_17fold_prefix_squeeze w1 a1 (2 ^ (w1 + a1) - 3 ^ w1)
    hw1 ha1 hgt rfl h17D_le
  exact ⟨hw13, ha8, hno_pow3, hq24_4, hq_ge17, hq_odd_w1, hx0_96, hdiv17⟩

theorem odd_run_parityOfIter : ∀ (w u : Nat),
    u ≥ 1 -> parityOfIter w (2 ^ w * u - 1) = List.replicate w true
  | 0, _, _ => rfl
  | w + 1, u, hu => by
    have hp2w : 2 ^ w * u ≥ 1 := Nat.mul_le_mul (pow2_pos_nat w) hu
    have harg : 2 ^ (w + 1) * u - 1 = 2 * (2 ^ w * u) - 1 := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ w) 2, Nat.mul_assoc]
    have hodd_b : ((2 ^ (w + 1) * u - 1) % 2 == 0) = false :=
      decide_eq_false (by omega)
    have hstep : collatzStep (2 ^ (w + 1) * u - 1) = 2 ^ w * (3 * u) - 1 := by
      rw [collatzStep_of_odd_nat _ (by omega)]
      have hcomm : 3 * (2 ^ w * u) = 2 ^ w * (3 * u) := by
        rw [← Nat.mul_assoc 3 (2 ^ w) u, Nat.mul_comm 3 (2 ^ w), Nat.mul_assoc]
      omega
    simp [parityOfIter, hodd_b, hstep, List.replicate_succ]
    exact odd_run_parityOfIter w (3 * u) (by omega)

theorem even_run_parityOfIter : ∀ (a m : Nat),
    parityOfIter a (2 ^ a * m) = List.replicate a false
  | 0, _ => rfl
  | a + 1, m => by
    have hmul : 2 ^ (a + 1) * m = 2 * (2 ^ a * m) := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ a) 2, Nat.mul_assoc]
    have hev_b : ((2 ^ (a + 1) * m) % 2 == 0) = true :=
      decide_eq_true (by rw [hmul]; omega)
    have hstep : collatzStep (2 ^ (a + 1) * m) = 2 ^ a * m := by
      rw [collatzStep_of_even_nat _ (by rw [hmul]; omega), hmul]
      omega
    simp [parityOfIter, hev_b, hstep, List.replicate_succ]
    exact even_run_parityOfIter a m

theorem syracuse_block_iter_and_parity (x xNext w a u : Nat)
    (hu : u ≥ 1) (hx : x + 1 = 2 ^ w * u) (ha : 3 ^ w * u - 1 = 2 ^ a * xNext) :
    collatzIter (w + a) x = xNext ∧
    parityOfIter (w + a) x = List.replicate w true ++ List.replicate a false := by
  refine ⟨syracuse_block_iter x xNext w a u hu hx ha, ?_⟩
  have hx_eq : x = 2 ^ w * u - 1 := by omega
  rw [parityOfIter_append_split w a x, hx_eq, odd_run_parityOfIter w u hu,
      odd_run_iter w u hu, ha, even_run_parityOfIter a xNext]

theorem extract_one_block_cycle_q0 (x0 w1 a1 : Nat)
    (hx0 : x0 > 2) (hw1 : w1 ≥ 1) (ha1 : a1 ≥ 1)
    (hv : parityOfIter (w1 + a1) x0 = List.replicate w1 true ++ List.replicate a1 false)
    (hcyc : collatzIter (w1 + a1) x0 = x0) :
    ∃ q0 : Nat,
      w1 ≥ 13 ∧ a1 ≥ 8 ∧ q0 ≥ 17 ∧ q0 % 2 = 1 ∧
      3 ^ w1 < 2 ^ (w1 + a1) ∧
      x0 = 2 ^ w1 * q0 - 1 ∧
      (2 ^ (w1 + a1) - 3 ^ w1) * q0 = 2 ^ a1 - 1 := by
  let u := List.replicate w1 true ++ List.replicate a1 false
  have hu_len : u.length = w1 + a1 := by
    dsimp [u]; rw [List.length_append, List.length_replicate, List.length_replicate]
  have hu_wt : parityWeight u = w1 := by
    dsimp [u]
    rw [parityWeight_append, parityWeight_replicate_true_local, parityWeight_replicate_false, Nat.add_zero]
  have hpar : matchesParity u (x0 : Int) := by
    have hm := parityOfIter_matches (w1 + a1) x0
    rwa [hv] at hm
  have hcyc_int : collatzIterInt u.length (x0 : Int) = (x0 : Int) := by
    rw [hu_len, collatzIterInt_ofNat, hcyc]
  have hbs := bohm_sontacchi_cycle_equation_universal u (x0 : Int) hpar hcyc_int
  rw [hu_len, hu_wt, one_cycle_carry_closed_form_universal w1 a1] at hbs
  have h2w_lt_3w_int : (2 : Int) ^ w1 < (3 : Int) ^ w1 := by
    have hp1 : 2 ^ (w1 - 1) ≤ 3 ^ (w1 - 1) := pow2_le_pow3 (w1 - 1)
    have hp2 : 2 ^ w1 < 3 ^ w1 := by
      rw [show w1 = (w1 - 1) + 1 by omega, Nat.pow_succ, Nat.pow_succ]
      have hp0 := pow2_pos_nat (w1 - 1); omega
    have hc1 := natCast_pow2 w1
    have hc2 := natCast_pow3 w1
    omega
  have hgt : 3 ^ w1 < 2 ^ (w1 + a1) := by
    by_cases hlt : 3 ^ w1 < 2 ^ (w1 + a1)
    · exact hlt
    · have hc2 := natCast_pow2 (w1 + a1)
      have hc3 := natCast_pow3 w1
      have hnonpos : (2 : Int) ^ (w1 + a1) - (3 : Int) ^ w1 ≤ 0 := by omega
      have hmul_le : ((2 : Int) ^ (w1 + a1) - (3 : Int) ^ w1) * (x0 : Int) ≤ 0 := by
        have hm := Int.mul_nonneg (by omega : 0 ≤ -((2 : Int) ^ (w1 + a1) - (3 : Int) ^ w1))
          (by omega : 0 ≤ (x0 : Int))
        rw [Int.neg_mul] at hm; omega
      omega
  have hw1_ge2 : w1 ≥ 2 := by
    by_cases hw2 : w1 ≥ 2
    · exact hw2
    · have hw1_eq1 : w1 = 1 := by omega
      subst hw1_eq1
      simp only [Int.pow_succ, Int.pow_zero, Int.one_mul] at hbs
      by_cases ha2 : a1 ≥ 2
      · have hp8 : 2 ^ (1 + a1) ≥ 8 := by simpa using pow2_mono_nat (by omega : 3 ≤ 1 + a1)
        have hc2 := natCast_pow2 (1 + a1)
        have hm : ((2 : Int) ^ (1 + a1) - 3) * (x0 : Int) ≥ 5 * 3 := by
          have hm1 : 5 * (x0 : Int) ≤ ((2 : Int) ^ (1 + a1) - 3) * (x0 : Int) := by
            have hd := Int.mul_nonneg (by omega : 0 ≤ ((2 : Int) ^ (1 + a1) - 3) - 5)
              (by omega : 0 ≤ (x0 : Int))
            rw [Int.sub_mul] at hd; omega
          omega
        omega
      · have ha1_eq1 : a1 = 1 := by omega
        subst ha1_eq1; omega
  have ha1_ge2 : a1 ≥ 2 := by
    by_cases ha2 : a1 ≥ 2
    · exact ha2
    · have ha1_eq1 : a1 = 1 := by omega
      subst ha1_eq1
      have hlt := pow2_succ_lt_pow3 w1 hw1_ge2; omega
  let rest := List.replicate (a1 - 1) false
  have hv_brox : parityOfIter (w1 + a1) x0 = List.replicate w1 true ++ (false :: rest) := by
    rw [hv, show a1 = (a1 - 1) + 1 by omega, List.replicate_succ]
  have hwt_rest : parityWeight rest = 0 := parityWeight_replicate_false _
  rcases extract_brox_q0_from_min_cycle x0 (w1 + a1) w1 rest hw1_ge2
      (by rw [hwt_rest, Nat.add_zero]; exact hgt) hcyc hv_brox with
    ⟨q0, _, hq0_odd, hx0_eq, hbrox_r⟩
  rw [hwt_rest, Nat.add_zero, broxOddCarry_replicate_false (a1 - 1),
      show a1 - 1 + 1 = a1 by omega] at hbrox_r
  rcases one_block_no_pow3_quotient_and_q0_ge_17 w1 a1 q0 hw1_ge2 ha1 hgt hbrox_r with
    ⟨hw13, ha8, _, _, hq17, _, _, _⟩
  exact ⟨q0, hw13, ha8, hq17, hq0_odd, hgt, hx0_eq, hbrox_r⟩

/--
  Theorem T9c (`no_one_block_cycles_iff_sharpened_gcd_mod24`, `[]` axioms):
  `NoOneBlockPositiveCycles` holds IF AND ONLY IF no `(w1, a1, q0)` satisfies the
  Wave 3 GCD, mod-24, mod-96, and `17`-fold binary-prefix squeeze conditions!
-/
theorem no_one_block_cycles_iff_sharpened_gcd_mod24 :
    NoOneBlockPositiveCycles ↔
      ∀ (w1 a1 q0 : Nat),
        ¬ (w1 ≥ 13 ∧ a1 ≥ 8 ∧ q0 ≥ 17 ∧
           3 ^ w1 < 2 ^ (w1 + a1) ∧
           let D := 2 ^ (w1 + a1) - 3 ^ w1
           let x0 := 2 ^ w1 * q0 - 1
           D * q0 = 2 ^ a1 - 1 ∧
           D ∣ Nat.gcd (2 ^ a1 - 1) (3 ^ w1 - 2 ^ w1) ∧
           (q0 % 24 = 3 ∨ q0 % 24 = 9 ∨ q0 % 24 = 17 ∨ q0 % 24 = 19) ∧
           (x0 % 96 = 31 ∨ x0 % 96 = 95) ∧
           (17 * 3 ^ w1) / (2 ^ a1) = 17 * 2 ^ w1 - 1) := by
  constructor
  · intro hno1 w1 a1 q0 ⟨hw13, ha8, hq17, hgt, hbrox, _, _, _, _⟩
    rcases one_block_gcd_and_congruence_lock w1 a1 q0 (by omega) (by omega) hgt hbrox with
      ⟨_, _, _, hsyr_eq, _, _, _⟩
    let x0 := 2 ^ w1 * q0 - 1
    have hp2w : 2 ^ w1 ≥ 8192 := by simpa using pow2_mono_nat hw13
    have hx0_gt2 : x0 > 2 := by
      have hm := Nat.mul_le_mul hp2w hq17; dsimp [x0]; omega
    have hx0_p1 : x0 + 1 = 2 ^ w1 * q0 := by
      have hm := Nat.mul_le_mul hp2w hq17; dsimp [x0]; omega
    rcases syracuse_block_iter_and_parity x0 x0 w1 a1 q0 (by omega) hx0_p1 hsyr_eq with
      ⟨hcyc, hv⟩
    exact hno1 x0 w1 a1 hx0_gt2 (by omega) (by omega) hv hcyc
  · intro hnowit x0 w1 a1 hx0 hw1 ha1 hv hcyc
    rcases extract_one_block_cycle_q0 x0 w1 a1 hx0 hw1 ha1 hv hcyc with
      ⟨q0, hw13, ha8, hq17, _, hgt, _, hbrox⟩
    rcases one_block_gcd_and_congruence_lock w1 a1 q0 (by omega) ha1 hgt hbrox with
      ⟨_, _, _, _, hdvd_gcd, _, _⟩
    rcases one_block_no_pow3_quotient_and_q0_ge_17 w1 a1 q0 (by omega) ha1 hgt hbrox with
      ⟨_, _, _, hq24, _, _, hx96, hdiv17⟩
    exact hnowit w1 a1 q0 ⟨hw13, ha8, hq17, hgt, hbrox, hdvd_gcd, hq24, hx96, hdiv17⟩

-- ----------------------------------------------------------------------------
-- T10a: Closed-Form 2-Block Brox Carries, Cross-Carry Bridge, &
--       Cleared-Denominator 2-Block Reciprocal Identity (`[]` Axioms)
-- ----------------------------------------------------------------------------

theorem broxOddCarry_replicate_true_false : ∀ (w a2 : Nat),
    broxOddCarry (List.replicate w true ++ List.replicate a2 false) =
      3 ^ w + 2 ^ (w + 1) * (2 ^ a2 - 1)
  | 0, a2 => by
    simp only [List.replicate_zero, List.nil_append, Nat.pow_zero, Nat.zero_add, Nat.pow_one]
    rw [broxOddCarry_replicate_false a2]
    have hp : 2 ^ a2 ≥ 1 := pow2_pos_nat a2
    have h2 : 2 ^ (a2 + 1) = 2 * 2 ^ a2 := by rw [Nat.pow_succ, Nat.mul_comm]
    omega
  | w + 1, a2 => by
    simp only [List.replicate_succ, List.cons_append, broxOddCarry,
               parityWeight_append, parityWeight_replicate_true_local,
               parityWeight_replicate_false, Nat.add_zero]
    rw [broxOddCarry_replicate_true_false w a2,
        Nat.pow_succ 3 w, Nat.pow_succ 2 (w + 1)]
    have hcomm : 2 * (2 ^ (w + 1) * (2 ^ a2 - 1)) = (2 ^ (w + 1) * 2) * (2 ^ a2 - 1) := by
      rw [← Nat.mul_assoc 2, Nat.mul_comm 2 (2 ^ (w + 1))]
    omega

theorem broxOddCarry_prepend_replicate_false (u : List Bool) : ∀ c : Nat,
    broxOddCarry (List.replicate c false ++ u) =
      3 ^ parityWeight u * (2 ^ c - 1) + 2 ^ c * broxOddCarry u
  | 0 => by simp
  | c + 1 => by
    simp only [List.replicate_succ, List.cons_append, broxOddCarry,
               parityWeight_append, parityWeight_replicate_false, Nat.zero_add]
    rw [broxOddCarry_prepend_replicate_false u c]
    have hp : 2 ^ c ≥ 1 := pow2_pos_nat c
    have h2 : 2 ^ (c + 1) = 2 * 2 ^ c := by rw [Nat.pow_succ, Nat.mul_comm]
    calc
      2 * (3 ^ parityWeight u * (2 ^ c - 1) + 2 ^ c * broxOddCarry u) + 3 ^ parityWeight u
          = 3 ^ parityWeight u * (2 * (2 ^ c - 1) + 1) + (2 * 2 ^ c) * broxOddCarry u := by
            rw [Nat.mul_add 2, ← Nat.mul_assoc 2 (3 ^ parityWeight u),
                Nat.mul_comm 2 (3 ^ parityWeight u), Nat.mul_assoc (3 ^ parityWeight u) 2,
                ← Nat.mul_assoc 2 (2 ^ c), Nat.add_comm _ (3 ^ parityWeight u),
                ← Nat.add_assoc, Nat.mul_add (3 ^ parityWeight u), Nat.mul_one,
                Nat.add_comm (3 ^ parityWeight u)]
      _ = 3 ^ parityWeight u * (2 ^ (c + 1) - 1) + 2 ^ (c + 1) * broxOddCarry u := by
            rw [h2, show 2 * (2 ^ c - 1) + 1 = 2 * 2 ^ c - 1 by omega]

theorem twoBlockBroxCarry_eq_broxOddCarry (w1 a1 w2 a2 : Nat)
    (ha1 : a1 ≥ 1) :
    broxOddCarry (List.replicate (a1 - 1) false ++ (List.replicate w2 true ++ List.replicate a2 false)) =
      twoBlockBroxCarry w1 a1 w2 a2 := by
  rw [broxOddCarry_prepend_replicate_false _ (a1 - 1),
      parityWeight_append, parityWeight_replicate_true_local,
      parityWeight_replicate_false, Nat.add_zero,
      broxOddCarry_replicate_true_false w2 a2]
  unfold twoBlockBroxCarry
  dsimp only
  have hp : 2 ^ (a1 - 1) ≥ 1 := pow2_pos_nat (a1 - 1)
  have h2a1 : 2 ^ a1 = 2 * 2 ^ (a1 - 1) := by
    conv => lhs; rw [show a1 = (a1 - 1) + 1 by omega]
    rw [Nat.pow_succ, Nat.mul_comm]
  calc
    3 ^ w2 * (2 ^ (a1 - 1) - 1) + 2 ^ (a1 - 1) * (3 ^ w2 + 2 ^ (w2 + 1) * (2 ^ a2 - 1))
        = 3 ^ w2 * (2 ^ (a1 - 1) - 1 + 2 ^ (a1 - 1)) +
            (2 ^ (a1 - 1) * 2 ^ (w2 + 1)) * (2 ^ a2 - 1) := by
          rw [Nat.mul_add (2 ^ (a1 - 1)), Nat.mul_comm (2 ^ (a1 - 1)) (3 ^ w2),
              ← Nat.add_assoc, ← Nat.mul_add (3 ^ w2), Nat.mul_assoc (2 ^ (a1 - 1))]
    _ = 3 ^ w2 * (2 ^ a1 - 1) + 2 ^ (a1 + w2) * (2 ^ a2 - 1) := by
          rw [show 2 ^ (a1 - 1) - 1 + 2 ^ (a1 - 1) = 2 ^ a1 - 1 by omega,
              ← Nat.pow_add 2 (a1 - 1) (w2 + 1),
              show (a1 - 1) + (w2 + 1) = a1 + w2 by omega]

theorem two_block_numerator_identities (w1 a1 w2 a2 : Nat)
    (_hw1 : w1 ≥ 1) (_ha1 : a1 ≥ 1) (_hw2 : w2 ≥ 1) (_ha2 : a2 ≥ 1)
    (hgt : 3 ^ (w1 + w2) < 2 ^ (w1 + a1 + w2 + a2)) :
    let W := w1 + w2
    let K := w1 + a1 + w2 + a2
    let D := 2 ^ K - 3 ^ W
    let C1 := 3 ^ w1 - 2 ^ w1
    let C2 := 3 ^ w2 - 2 ^ w2
    let H0 := twoBlockBroxCarry w1 a1 w2 a2
    let H1 := twoBlockBroxCarry w2 a2 w1 a1
    2 ^ w1 * H0 = D + (3 ^ w2 * C1 + 2 ^ (w1 + a1) * C2) ∧
    2 ^ w2 * H1 = D + (3 ^ w1 * C2 + 2 ^ (w2 + a2) * C1) ∧
    3 ^ w1 * H0 - D = 2 ^ a1 * (2 ^ w2 * H1 - D) := by
  dsimp only
  let W := w1 + w2
  let K := w1 + a1 + w2 + a2
  let D := 2 ^ K - 3 ^ W
  let C1 := 3 ^ w1 - 2 ^ w1
  let C2 := 3 ^ w2 - 2 ^ w2
  let H0 := twoBlockBroxCarry w1 a1 w2 a2
  let H1 := twoBlockBroxCarry w2 a2 w1 a1
  have h2le3_1 : 2 ^ w1 ≤ 3 ^ w1 := pow2_le_pow3 w1
  have h2le3_2 : 2 ^ w2 ≤ 3 ^ w2 := pow2_le_pow3 w2
  have hp2a1 : 2 ^ a1 ≥ 1 := pow2_pos_nat a1
  have hp2a2 : 2 ^ a2 ≥ 1 := pow2_pos_nat a2
  have hD_add : D + 3 ^ w1 * 3 ^ w2 = 2 ^ K := by
    dsimp [D, W, K]; rw [← Nat.pow_add 3 w1 w2]; omega
  have hid0 : 2 ^ w1 * H0 = D + (3 ^ w2 * C1 + 2 ^ (w1 + a1) * C2) := by
    have hlhs : 2 ^ w1 * H0 + 3 ^ w2 * 2 ^ w1 + 2 ^ (w1 + a1 + w2) =
        3 ^ w2 * 2 ^ (w1 + a1) + 2 ^ K := by
      dsimp [H0, twoBlockBroxCarry]
      have t1 : 2 ^ w1 * (3 ^ w2 * (2 ^ a1 - 1)) + 3 ^ w2 * 2 ^ w1 = 3 ^ w2 * 2 ^ (w1 + a1) := by
        calc
          2 ^ w1 * (3 ^ w2 * (2 ^ a1 - 1)) + 3 ^ w2 * 2 ^ w1
              = (3 ^ w2 * 2 ^ w1) * ((2 ^ a1 - 1) + 1) := by
                rw [← Nat.mul_assoc (2 ^ w1) (3 ^ w2), Nat.mul_comm (2 ^ w1) (3 ^ w2),
                    Nat.mul_add (3 ^ w2 * 2 ^ w1), Nat.mul_one]
          _ = 3 ^ w2 * 2 ^ (w1 + a1) := by
                rw [Nat.sub_add_cancel hp2a1, Nat.mul_assoc, ← Nat.pow_add]
      have t2 : 2 ^ w1 * (2 ^ (a1 + w2) * (2 ^ a2 - 1)) + 2 ^ (w1 + a1 + w2) = 2 ^ K := by
        calc
          2 ^ w1 * (2 ^ (a1 + w2) * (2 ^ a2 - 1)) + 2 ^ (w1 + a1 + w2)
              = 2 ^ (w1 + a1 + w2) * ((2 ^ a2 - 1) + 1) := by
                rw [← Nat.mul_assoc (2 ^ w1), ← Nat.pow_add 2 w1 (a1 + w2),
                    show w1 + (a1 + w2) = w1 + a1 + w2 by omega,
                    Nat.mul_add (2 ^ (w1 + a1 + w2)), Nat.mul_one]
          _ = 2 ^ K := by
                rw [Nat.sub_add_cancel hp2a2, ← Nat.pow_add]
      rw [Nat.mul_add (2 ^ w1)]; omega
    have hrhs : (D + (3 ^ w2 * C1 + 2 ^ (w1 + a1) * C2)) + 3 ^ w2 * 2 ^ w1 + 2 ^ (w1 + a1 + w2) =
        3 ^ w2 * 2 ^ (w1 + a1) + 2 ^ K := by
      have c1 : 3 ^ w2 * C1 + 3 ^ w2 * 2 ^ w1 = 3 ^ w1 * 3 ^ w2 := by
        dsimp [C1]
        rw [← Nat.mul_add, Nat.sub_add_cancel h2le3_1, Nat.mul_comm]
      have c2 : 2 ^ (w1 + a1) * C2 + 2 ^ (w1 + a1 + w2) = 3 ^ w2 * 2 ^ (w1 + a1) := by
        dsimp [C2]
        rw [Nat.pow_add 2 (w1 + a1) w2, ← Nat.mul_add, Nat.sub_add_cancel h2le3_2, Nat.mul_comm]
      omega
    omega
  have hid1 : 2 ^ w2 * H1 = D + (3 ^ w1 * C2 + 2 ^ (w2 + a2) * C1) := by
    have hlhs : 2 ^ w2 * H1 + 3 ^ w1 * 2 ^ w2 + 2 ^ (w2 + a2 + w1) =
        3 ^ w1 * 2 ^ (w2 + a2) + 2 ^ K := by
      dsimp [H1, twoBlockBroxCarry]
      have t1 : 2 ^ w2 * (3 ^ w1 * (2 ^ a2 - 1)) + 3 ^ w1 * 2 ^ w2 = 3 ^ w1 * 2 ^ (w2 + a2) := by
        calc
          2 ^ w2 * (3 ^ w1 * (2 ^ a2 - 1)) + 3 ^ w1 * 2 ^ w2
              = (3 ^ w1 * 2 ^ w2) * ((2 ^ a2 - 1) + 1) := by
                rw [← Nat.mul_assoc (2 ^ w2) (3 ^ w1), Nat.mul_comm (2 ^ w2) (3 ^ w1),
                    Nat.mul_add (3 ^ w1 * 2 ^ w2), Nat.mul_one]
          _ = 3 ^ w1 * 2 ^ (w2 + a2) := by
                rw [Nat.sub_add_cancel hp2a2, Nat.mul_assoc, ← Nat.pow_add]
      have t2 : 2 ^ w2 * (2 ^ (a2 + w1) * (2 ^ a1 - 1)) + 2 ^ (w2 + a2 + w1) = 2 ^ K := by
        calc
          2 ^ w2 * (2 ^ (a2 + w1) * (2 ^ a1 - 1)) + 2 ^ (w2 + a2 + w1)
              = 2 ^ (w2 + a2 + w1) * ((2 ^ a1 - 1) + 1) := by
                rw [← Nat.mul_assoc (2 ^ w2), ← Nat.pow_add 2 w2 (a2 + w1),
                    show w2 + (a2 + w1) = w2 + a2 + w1 by omega,
                    Nat.mul_add (2 ^ (w2 + a2 + w1)), Nat.mul_one]
          _ = 2 ^ K := by
                rw [Nat.sub_add_cancel hp2a1, ← Nat.pow_add]
                dsimp [K]; rw [show w2 + a2 + w1 + a1 = w1 + a1 + w2 + a2 by omega]
      rw [Nat.mul_add (2 ^ w2)]; omega
    have hrhs : (D + (3 ^ w1 * C2 + 2 ^ (w2 + a2) * C1)) + 3 ^ w1 * 2 ^ w2 + 2 ^ (w2 + a2 + w1) =
        3 ^ w1 * 2 ^ (w2 + a2) + 2 ^ K := by
      have c1 : 3 ^ w1 * C2 + 3 ^ w1 * 2 ^ w2 = 3 ^ w1 * 3 ^ w2 := by
        dsimp [C2]
        rw [← Nat.mul_add, Nat.sub_add_cancel h2le3_2]
      have c2 : 2 ^ (w2 + a2) * C1 + 2 ^ (w2 + a2 + w1) = 3 ^ w1 * 2 ^ (w2 + a2) := by
        dsimp [C1]
        rw [Nat.pow_add 2 (w2 + a2) w1, ← Nat.mul_add, Nat.sub_add_cancel h2le3_1, Nat.mul_comm]
      omega
    omega
  have hbridge : 3 ^ w1 * H0 - D = 2 ^ a1 * (2 ^ w2 * H1 - D) := by
    have hsub1 : 2 ^ w2 * H1 - D = 3 ^ w1 * C2 + 2 ^ (w2 + a2) * C1 := by omega
    rw [hsub1]
    have hlhs : 3 ^ w1 * H0 + 3 ^ w1 * 3 ^ w2 + 3 ^ w1 * 2 ^ (a1 + w2) =
        2 ^ a1 * (3 ^ w1 * 3 ^ w2) + 3 ^ w1 * 2 ^ (a1 + w2 + a2) := by
      dsimp [H0, twoBlockBroxCarry]
      have s1 : 3 ^ w1 * (3 ^ w2 * (2 ^ a1 - 1)) + 3 ^ w1 * 3 ^ w2 =
          2 ^ a1 * (3 ^ w1 * 3 ^ w2) := by
        calc
          3 ^ w1 * (3 ^ w2 * (2 ^ a1 - 1)) + 3 ^ w1 * 3 ^ w2
              = (3 ^ w1 * 3 ^ w2) * ((2 ^ a1 - 1) + 1) := by
                rw [← Nat.mul_assoc (3 ^ w1) (3 ^ w2), Nat.mul_add (3 ^ w1 * 3 ^ w2), Nat.mul_one]
          _ = 2 ^ a1 * (3 ^ w1 * 3 ^ w2) := by
                rw [Nat.sub_add_cancel hp2a1, Nat.mul_comm]
      have s2 : 3 ^ w1 * (2 ^ (a1 + w2) * (2 ^ a2 - 1)) + 3 ^ w1 * 2 ^ (a1 + w2) =
          3 ^ w1 * 2 ^ (a1 + w2 + a2) := by
        calc
          3 ^ w1 * (2 ^ (a1 + w2) * (2 ^ a2 - 1)) + 3 ^ w1 * 2 ^ (a1 + w2)
              = (3 ^ w1 * 2 ^ (a1 + w2)) * ((2 ^ a2 - 1) + 1) := by
                rw [← Nat.mul_assoc (3 ^ w1), Nat.mul_add (3 ^ w1 * 2 ^ (a1 + w2)), Nat.mul_one]
          _ = 3 ^ w1 * 2 ^ (a1 + w2 + a2) := by
                rw [Nat.sub_add_cancel hp2a2, Nat.mul_assoc, ← Nat.pow_add]
      rw [Nat.mul_add (3 ^ w1)]; omega
    have hrhs : (D + 2 ^ a1 * (3 ^ w1 * C2 + 2 ^ (w2 + a2) * C1)) +
        3 ^ w1 * 3 ^ w2 + 3 ^ w1 * 2 ^ (a1 + w2) =
        2 ^ a1 * (3 ^ w1 * 3 ^ w2) + 3 ^ w1 * 2 ^ (a1 + w2 + a2) := by
      have r1 : 2 ^ a1 * (3 ^ w1 * C2) + 3 ^ w1 * 2 ^ (a1 + w2) =
          2 ^ a1 * (3 ^ w1 * 3 ^ w2) := by
        dsimp [C2]
        have hrew : 3 ^ w1 * 2 ^ (a1 + w2) = 2 ^ a1 * (3 ^ w1 * 2 ^ w2) := by
          rw [Nat.pow_add 2 a1 w2, ← Nat.mul_assoc (3 ^ w1), Nat.mul_comm (3 ^ w1) (2 ^ a1),
              Nat.mul_assoc]
        rw [hrew, ← Nat.mul_add (2 ^ a1), ← Nat.mul_add (3 ^ w1), Nat.sub_add_cancel h2le3_2]
      have r2 : 2 ^ a1 * (2 ^ (w2 + a2) * C1) + 2 ^ K = 3 ^ w1 * 2 ^ (a1 + w2 + a2) := by
        dsimp [C1]
        have hrew1 : 2 ^ a1 * (2 ^ (w2 + a2) * (3 ^ w1 - 2 ^ w1)) =
            2 ^ (a1 + w2 + a2) * (3 ^ w1 - 2 ^ w1) := by
          rw [← Nat.mul_assoc (2 ^ a1), ← Nat.pow_add 2 a1 (w2 + a2),
              show a1 + (w2 + a2) = a1 + w2 + a2 by omega]
        have hrew2 : 2 ^ K = 2 ^ (a1 + w2 + a2) * 2 ^ w1 := by
          dsimp [K]
          rw [← Nat.pow_add 2 (a1 + w2 + a2) w1,
              show a1 + w2 + a2 + w1 = w1 + a1 + w2 + a2 by omega]
        rw [hrew1, hrew2, ← Nat.mul_add, Nat.sub_add_cancel h2le3_1, Nat.mul_comm]
      rw [Nat.mul_add (2 ^ a1)]; omega
    omega
  exact ⟨hid0, hid1, hbridge⟩

/--
  Theorem T10a (`two_block_reciprocal_and_cross_carry_identity`, `[]` axioms):
  Whenever `D * q0 = twoBlockBroxCarry w1 a1 w2 a2` (`3 ^ W < 2 ^ K`), `D` ALSO divides
  `twoBlockBroxCarry w2 a2 w1 a1` (`D * q1 = H1`), both Syracuse block equations hold
  (`3 ^ w1 * q0 - 1 = 2 ^ a1 * x1` and `3 ^ w2 * q1 - 1 = 2 ^ a2 * x0`), AND `(x0, x1)`
  satisfies the exact pure-`Nat` cleared-denominator 2-block reciprocal identity:
    `D * (x0 * x1) = 3 ^ w2 * (3 ^ w1 - 2 ^ w1) * x1 + 3 ^ w1 * (3 ^ w2 - 2 ^ w2) * x0
                     + (3 ^ w1 - 2 ^ w1) * (3 ^ w2 - 2 ^ w2)`.
-/
theorem two_block_reciprocal_and_cross_carry_identity (w1 a1 w2 a2 q0 : Nat)
    (hw1 : w1 ≥ 1) (ha1 : a1 ≥ 1) (hw2 : w2 ≥ 1) (ha2 : a2 ≥ 1)
    (hgt : 3 ^ (w1 + w2) < 2 ^ (w1 + a1 + w2 + a2))
    (hbrox0 : (2 ^ (w1 + a1 + w2 + a2) - 3 ^ (w1 + w2)) * q0 = twoBlockBroxCarry w1 a1 w2 a2) :
    let W := w1 + w2
    let K := w1 + a1 + w2 + a2
    let D := 2 ^ K - 3 ^ W
    let C1 := 3 ^ w1 - 2 ^ w1
    let C2 := 3 ^ w2 - 2 ^ w2
    let H1 := twoBlockBroxCarry w2 a2 w1 a1
    let x0 := 2 ^ w1 * q0 - 1
    ∃ q1 : Nat,
      q0 ≥ 1 ∧ q1 ≥ 1 ∧ q0 % 2 = 1 ∧ q1 % 2 = 1 ∧
      D * q1 = H1 ∧
      (let x1 := 2 ^ w2 * q1 - 1
       D * x0 = 3 ^ w2 * C1 + 2 ^ (w1 + a1) * C2 ∧
       D * x1 = 3 ^ w1 * C2 + 2 ^ (w2 + a2) * C1 ∧
       3 ^ w1 * q0 - 1 = 2 ^ a1 * x1 ∧
       3 ^ w2 * q1 - 1 = 2 ^ a2 * x0 ∧
       D * (x0 * x1) = 3 ^ w2 * C1 * x1 + 3 ^ w1 * C2 * x0 + C1 * C2) := by
  dsimp only
  let W := w1 + w2
  let K := w1 + a1 + w2 + a2
  let D := 2 ^ K - 3 ^ W
  let C1 := 3 ^ w1 - 2 ^ w1
  let C2 := 3 ^ w2 - 2 ^ w2
  let H0 := twoBlockBroxCarry w1 a1 w2 a2
  let H1 := twoBlockBroxCarry w2 a2 w1 a1
  change D * q0 = H0 at hbrox0
  have hD_pos : D > 0 := by dsimp [D, K, W]; omega
  have hD_odd : D % 2 = 1 := by
    have hp2 : 2 ^ K % 2 = 0 := by
      rw [show K = (K - 1) + 1 by dsimp [K]; omega, Nat.pow_succ]; omega
    have hp3 : 3 ^ W % 2 = 1 := pow3_odd_nat W
    have hgt_KW : 3 ^ W < 2 ^ K := hgt
    dsimp [D]
    generalize 2 ^ K = p2k, 3 ^ W = p3w at hp2 hp3 hgt_KW
    omega
  have hH0_odd : H0 % 2 = 1 := by
    dsimp [H0]; rw [← twoBlockBroxCarry_eq_broxOddCarry w1 a1 w2 a2 ha1]
    exact (broxOddCarry_odd_and_ge_pow3 _).1
  have hH1_odd : H1 % 2 = 1 := by
    dsimp [H1]; rw [← twoBlockBroxCarry_eq_broxOddCarry w2 a2 w1 a1 ha2]
    exact (broxOddCarry_odd_and_ge_pow3 _).1
  have hq0_ge1 : q0 ≥ 1 := by
    cases q0 with
    | zero => rw [Nat.mul_zero] at hbrox0; omega
    | succ _ => omega
  have hq0_odd : q0 % 2 = 1 := by
    by_cases ho : q0 % 2 = 1
    · exact ho
    · have hev : (D * q0) % 2 = 0 := by
        rw [Nat.mul_mod, show q0 % 2 = 0 by omega, Nat.mul_zero, Nat.zero_mod]
      rw [hbrox0] at hev; omega
  rcases two_block_numerator_identities w1 a1 w2 a2 hw1 ha1 hw2 ha2 hgt with
    ⟨hid0, hid1, hbridge⟩
  change 2 ^ w1 * H0 = D + (3 ^ w2 * C1 + 2 ^ (w1 + a1) * C2) at hid0
  change 2 ^ w2 * H1 = D + (3 ^ w1 * C2 + 2 ^ (w2 + a2) * C1) at hid1
  change 3 ^ w1 * H0 - D = 2 ^ a1 * (2 ^ w2 * H1 - D) at hbridge
  -- Prove `D ∣ H1` via `hbridge` and oddness of `D`:
  have hdvd_pow_cancel : ∀ (m X : Nat), D ∣ 2 ^ m * X -> D ∣ X := by
    intro m
    induction m with
    | zero => intro X h; simpa using h
    | succ m' ih =>
      intro X ⟨t, ht⟩
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ m') 2, Nat.mul_assoc] at ht
      have ht_ev : t % 2 = 0 := by
        have hm2 : (D * t) % 2 = 0 := by rw [← ht]; omega
        rw [Nat.mul_mod, hD_odd] at hm2; omega
      refine ih X ⟨t / 2, ?_⟩
      have ht2 : t = 2 * (t / 2) := by omega
      rw [ht2, ← Nat.mul_assoc D 2, Nat.mul_comm D 2, Nat.mul_assoc] at ht
      omega
  have h3q0_ge1 : 3 ^ w1 * q0 ≥ 1 := by
    simpa using Nat.mul_le_mul (pow3_pos_nat w1) hq0_ge1
  have hbridge_D : D * (3 ^ w1 * q0 - 1) = 2 ^ a1 * (2 ^ w2 * H1 - D) := by
    have h1 : D * (3 ^ w1 * q0 - 1) + D = 3 ^ w1 * H0 := by
      calc
        D * (3 ^ w1 * q0 - 1) + D = D * ((3 ^ w1 * q0 - 1) + 1) := by
          rw [Nat.mul_add, Nat.mul_one]
        _ = D * (3 ^ w1 * q0) := by rw [Nat.sub_add_cancel h3q0_ge1]
        _ = 3 ^ w1 * (D * q0) := by rw [← Nat.mul_assoc, Nat.mul_comm D, Nat.mul_assoc]
        _ = 3 ^ w1 * H0 := by rw [hbrox0]
    omega
  have hdvd_sub : D ∣ (2 ^ w2 * H1 - D) :=
    hdvd_pow_cancel a1 (2 ^ w2 * H1 - D) ⟨3 ^ w1 * q0 - 1, hbridge_D.symm⟩
  rcases hdvd_sub with ⟨x1_cand, hx1_cand⟩
  have hdvd_2w2H1 : D ∣ 2 ^ w2 * H1 := by
    refine ⟨x1_cand + 1, ?_⟩
    rw [Nat.mul_add, Nat.mul_one]
    omega
  rcases hdvd_pow_cancel w2 H1 hdvd_2w2H1 with ⟨q1, hq1_eq⟩
  have hbrox1 : D * q1 = H1 := hq1_eq.symm
  have hq1_ge1 : q1 ≥ 1 := by
    cases q1 with
    | zero => rw [Nat.mul_zero] at hbrox1; omega
    | succ _ => omega
  have hq1_odd : q1 % 2 = 1 := by
    by_cases ho : q1 % 2 = 1
    · exact ho
    · have hev : (D * q1) % 2 = 0 := by
        rw [Nat.mul_mod, show q1 % 2 = 0 by omega, Nat.mul_zero, Nat.zero_mod]
      rw [hbrox1] at hev; omega
  let x0 := 2 ^ w1 * q0 - 1
  let x1 := 2 ^ w2 * q1 - 1
  have hp2w1 : 2 ^ w1 ≥ 2 := by simpa using pow2_mono_nat hw1
  have hp2w2 : 2 ^ w2 ≥ 2 := by simpa using pow2_mono_nat hw2
  have hx0_p1 : x0 + 1 = 2 ^ w1 * q0 := by
    have hm := Nat.mul_le_mul hp2w1 hq0_ge1; dsimp [x0]; omega
  have hx1_p1 : x1 + 1 = 2 ^ w2 * q1 := by
    have hm := Nat.mul_le_mul hp2w2 hq1_ge1; dsimp [x1]; omega
  have hDx0 : D * x0 = 3 ^ w2 * C1 + 2 ^ (w1 + a1) * C2 := by
    have h1 : D * x0 + D = 2 ^ w1 * H0 := by
      calc
        D * x0 + D = D * (x0 + 1) := by rw [Nat.mul_add, Nat.mul_one]
        _ = D * (2 ^ w1 * q0) := by rw [hx0_p1]
        _ = 2 ^ w1 * (D * q0) := by rw [← Nat.mul_assoc, Nat.mul_comm D, Nat.mul_assoc]
        _ = 2 ^ w1 * H0 := by rw [hbrox0]
    omega
  have hDx1 : D * x1 = 3 ^ w1 * C2 + 2 ^ (w2 + a2) * C1 := by
    have h1 : D * x1 + D = 2 ^ w2 * H1 := by
      calc
        D * x1 + D = D * (x1 + 1) := by rw [Nat.mul_add, Nat.mul_one]
        _ = D * (2 ^ w2 * q1) := by rw [hx1_p1]
        _ = 2 ^ w2 * (D * q1) := by rw [← Nat.mul_assoc, Nat.mul_comm D, Nat.mul_assoc]
        _ = 2 ^ w2 * H1 := by rw [hbrox1]
    omega
  have hsyr1 : 3 ^ w1 * q0 - 1 = 2 ^ a1 * x1 := by
    apply nat_mul_left_cancel_pos D _ _ hD_pos
    calc
      D * (3 ^ w1 * q0 - 1) = 2 ^ a1 * (2 ^ w2 * H1 - D) := hbridge_D
      _ = 2 ^ a1 * (D * x1) := by rw [show 2 ^ w2 * H1 - D = D * x1 by omega]
      _ = D * (2 ^ a1 * x1) := by rw [← Nat.mul_assoc, Nat.mul_comm (2 ^ a1) D, Nat.mul_assoc]
  have hsyr2 : 3 ^ w2 * q1 - 1 = 2 ^ a2 * x0 := by
    have hgt_symm : 3 ^ (w2 + w1) < 2 ^ (w2 + a2 + w1 + a1) := by
      rw [Nat.add_comm w2 w1, show w2 + a2 + w1 + a1 = w1 + a1 + w2 + a2 by omega]
      exact hgt
    rcases two_block_numerator_identities w2 a2 w1 a1 hw2 ha2 hw1 ha1 hgt_symm with
      ⟨_, _, hbridge2⟩
    have hD_symm : 2 ^ (w2 + a2 + w1 + a1) - 3 ^ (w2 + w1) = D := by
      dsimp [D, K, W]
      rw [Nat.add_comm w2 w1, show w2 + a2 + w1 + a1 = w1 + a1 + w2 + a2 by omega]
    change 3 ^ w2 * H1 - (2 ^ (w2 + a2 + w1 + a1) - 3 ^ (w2 + w1)) =
      2 ^ a2 * (2 ^ w1 * H0 - (2 ^ (w2 + a2 + w1 + a1) - 3 ^ (w2 + w1))) at hbridge2
    rw [hD_symm] at hbridge2
    have h3q1_ge1 : 3 ^ w2 * q1 ≥ 1 := by
      simpa using Nat.mul_le_mul (pow3_pos_nat w2) hq1_ge1
    have h1 : D * (3 ^ w2 * q1 - 1) + D = 3 ^ w2 * H1 := by
      calc
        D * (3 ^ w2 * q1 - 1) + D = D * ((3 ^ w2 * q1 - 1) + 1) := by
          rw [Nat.mul_add, Nat.mul_one]
        _ = D * (3 ^ w2 * q1) := by rw [Nat.sub_add_cancel h3q1_ge1]
        _ = 3 ^ w2 * (D * q1) := by rw [← Nat.mul_assoc, Nat.mul_comm D, Nat.mul_assoc]
        _ = 3 ^ w2 * H1 := by rw [hbrox1]
    apply nat_mul_left_cancel_pos D _ _ hD_pos
    calc
      D * (3 ^ w2 * q1 - 1) = 3 ^ w2 * H1 - D := by omega
      _ = 2 ^ a2 * (2 ^ w1 * H0 - D) := hbridge2
      _ = 2 ^ a2 * (D * x0) := by rw [show 2 ^ w1 * H0 - D = D * x0 by omega]
      _ = D * (2 ^ a2 * x0) := by rw [← Nat.mul_assoc, Nat.mul_comm (2 ^ a2) D, Nat.mul_assoc]
  -- Cleared-denominator 2-block reciprocal identity:
  have hrecip : D * (x0 * x1) = 3 ^ w2 * C1 * x1 + 3 ^ w1 * C2 * x0 + C1 * C2 := by
    apply nat_mul_left_cancel_pos D _ _ hD_pos
    have hlhs : D * (D * (x0 * x1)) = (D * x0) * (D * x1) := by
      calc
        D * (D * (x0 * x1)) = D * ((D * x0) * x1) := by rw [Nat.mul_assoc D x0 x1]
        _ = (D * x0) * (D * x1) := by
              rw [← Nat.mul_assoc D (D * x0) x1, Nat.mul_comm D (D * x0), Nat.mul_assoc]
    have hrhs : D * (3 ^ w2 * C1 * x1 + 3 ^ w1 * C2 * x0 + C1 * C2) =
        3 ^ w2 * C1 * (D * x1) + 3 ^ w1 * C2 * (D * x0) + D * (C1 * C2) := by
      rw [Nat.mul_add, Nat.mul_add,
          ← Nat.mul_assoc D (3 ^ w2 * C1) x1, Nat.mul_comm D (3 ^ w2 * C1), Nat.mul_assoc (3 ^ w2 * C1) D x1,
          ← Nat.mul_assoc D (3 ^ w1 * C2) x0, Nat.mul_comm D (3 ^ w1 * C2), Nat.mul_assoc (3 ^ w1 * C2) D x0]
    rw [hlhs, hrhs, hDx0, hDx1]
    let P11 := (3 ^ w2 * C1) * (2 ^ (w2 + a2) * C1)
    let P22 := (2 ^ (w1 + a1) * C2) * (3 ^ w1 * C2)
    have hexp_l :
        (3 ^ w2 * C1 + 2 ^ (w1 + a1) * C2) * (3 ^ w1 * C2 + 2 ^ (w2 + a2) * C1) =
          3 ^ W * (C1 * C2) + P11 + P22 + 2 ^ K * (C1 * C2) := by
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
      have m1 : (3 ^ w2 * C1) * (3 ^ w1 * C2) = 3 ^ W * (C1 * C2) := by
        calc
          (3 ^ w2 * C1) * (3 ^ w1 * C2)
              = (3 ^ w1 * 3 ^ w2) * (C1 * C2) := by
                rw [Nat.mul_assoc (3 ^ w2) C1, ← Nat.mul_assoc C1 (3 ^ w1) C2,
                    Nat.mul_comm C1 (3 ^ w1), Nat.mul_assoc (3 ^ w1) C1 C2,
                    ← Nat.mul_assoc (3 ^ w2) (3 ^ w1), Nat.mul_comm (3 ^ w2) (3 ^ w1)]
          _ = 3 ^ W * (C1 * C2) := by dsimp [W]; rw [← Nat.pow_add]
      have m4 : (2 ^ (w1 + a1) * C2) * (2 ^ (w2 + a2) * C1) = 2 ^ K * (C1 * C2) := by
        calc
          (2 ^ (w1 + a1) * C2) * (2 ^ (w2 + a2) * C1)
              = (2 ^ (w1 + a1) * 2 ^ (w2 + a2)) * (C1 * C2) := by
                rw [Nat.mul_assoc (2 ^ (w1 + a1)) C2, ← Nat.mul_assoc C2 _ C1,
                    Nat.mul_comm C2 (2 ^ (w2 + a2)), Nat.mul_assoc (2 ^ (w2 + a2)) C2 C1,
                    Nat.mul_comm C2 C1, ← Nat.mul_assoc (2 ^ (w1 + a1)) (2 ^ (w2 + a2))]
          _ = 2 ^ K * (C1 * C2) := by
                dsimp [K]; rw [← Nat.pow_add, show (w1 + a1) + (w2 + a2) = w1 + a1 + w2 + a2 by omega]
      rw [m1, m4]
      dsimp [P11, P22]
      omega
    have hexp_r :
        3 ^ w2 * C1 * (3 ^ w1 * C2 + 2 ^ (w2 + a2) * C1) +
          3 ^ w1 * C2 * (3 ^ w2 * C1 + 2 ^ (w1 + a1) * C2) + D * (C1 * C2) =
          3 ^ W * (C1 * C2) + P11 + P22 + 2 ^ K * (C1 * C2) := by
      rw [Nat.mul_add (3 ^ w2 * C1), Nat.mul_add (3 ^ w1 * C2)]
      have m1 : (3 ^ w2 * C1) * (3 ^ w1 * C2) = 3 ^ W * (C1 * C2) := by
        calc
          (3 ^ w2 * C1) * (3 ^ w1 * C2)
              = (3 ^ w1 * 3 ^ w2) * (C1 * C2) := by
                rw [Nat.mul_assoc (3 ^ w2) C1, ← Nat.mul_assoc C1 (3 ^ w1) C2,
                    Nat.mul_comm C1 (3 ^ w1), Nat.mul_assoc (3 ^ w1) C1 C2,
                    ← Nat.mul_assoc (3 ^ w2) (3 ^ w1), Nat.mul_comm (3 ^ w2) (3 ^ w1)]
          _ = 3 ^ W * (C1 * C2) := by dsimp [W]; rw [← Nat.pow_add]
      have m2 : (3 ^ w1 * C2) * (3 ^ w2 * C1) = 3 ^ W * (C1 * C2) := by
        rw [Nat.mul_comm, m1]
      have m3 : (3 ^ w1 * C2) * (2 ^ (w1 + a1) * C2) = P22 := Nat.mul_comm _ _
      have mD : D * (C1 * C2) + 3 ^ W * (C1 * C2) = 2 ^ K * (C1 * C2) := by
        rw [← Nat.add_mul D (3 ^ W), show D + 3 ^ W = 2 ^ K by dsimp [D]; omega]
      rw [m1, m2, m3]
      dsimp [P11]
      omega
    rw [hexp_l, hexp_r]
  exact ⟨q1, hq0_ge1, hq1_ge1, hq0_odd, hq1_odd, hbrox1, hDx0, hDx1, hsyr1, hsyr2, hrecip⟩

-- ----------------------------------------------------------------------------
-- T10b: Unconditional 2-Block Mersenne Elimination (`q0 ≥ 3 ∧ q1 ≥ 3`),
--       `x0 ≥ 47`, `23 * D < 3 ^ W`, `W ≥ 8, K ≥ 13`, Dual Brox Cubic Squeeze,
--       & `M1 = Q_(2)^+` Potential-Obstruction Witnesses (`[]` Axioms)
-- ----------------------------------------------------------------------------

theorem pow2_sub1_nondiv3_imp_odd (w : Nat) (_hw : w ≥ 1)
    (hn3 : (2 ^ w - 1) % 3 ≠ 0) : w % 2 = 1 := by
  by_cases ho : w % 2 = 1
  · exact ho
  · exfalso
    have hev : w = 2 * (w / 2) := by omega
    have hm3 : 2 ^ w % 3 = 1 := by rw [hev]; exact pow2_even_mod3_local (w / 2)
    have hp2 : 2 ^ w ≥ 1 := pow2_pos_nat w
    have hadd : ((2 ^ w - 1) % 3 + 1) % 3 = 2 ^ w % 3 := by
      conv => rhs; rw [← Nat.sub_add_cancel hp2, Nat.add_mod]
    rw [hm3] at hadd
    have hlt : (2 ^ w - 1) % 3 < 3 := Nat.mod_lt _ (by decide)
    generalize (2 ^ w - 1) % 3 = r at hadd hlt hn3
    omega

theorem pow3_odd_sub1_mod4_eq2 (w : Nat) (hodd : w % 2 = 1) :
    (3 ^ w - 1) % 4 = 2 := by
  have hw_eq : w = 2 * (w / 2) + 1 := by omega
  have hm8 : 3 ^ w % 8 = 3 := by rw [hw_eq]; exact pow3_odd_mod8 (w / 2)
  have hm4 : 3 ^ w % 4 = 3 := by
    have hr := mod_mul_mod_eq (3 ^ w) 4 2
    rw [hm8] at hr; exact hr.symm
  have hp3 : 3 ^ w ≥ 1 := pow3_pos_nat w
  have hadd : ((3 ^ w - 1) % 4 + 1) % 4 = 3 ^ w % 4 := by
    conv => rhs; rw [← Nat.sub_add_cancel hp3, Nat.add_mod]
  rw [hm4] at hadd
  have hlt : (3 ^ w - 1) % 4 < 4 := Nat.mod_lt _ (by decide)
  generalize (3 ^ w - 1) % 4 = r at hadd hlt
  omega

theorem pow2_mul_odd_eq_mod4_two_imp_one (a z m : Nat)
    (hz_odd : z % 2 = 1) (hm4 : m % 4 = 2) (heq : m = 2 ^ a * z) :
    a = 1 := by
  cases a with
  | zero =>
    simp only [Nat.pow_zero, Nat.one_mul] at heq
    subst heq; omega
  | succ a' =>
    cases a' with
    | zero => rfl
    | succ a'' =>
      exfalso
      have h4 : 2 ^ (a'' + 2) * z = 4 * (2 ^ a'' * z) := by
        rw [show a'' + 2 = 2 + a'' by omega, Nat.pow_add, Nat.mul_assoc]
      rw [heq, h4] at hm4
      generalize 2 ^ a'' * z = t at hm4
      omega

theorem four_mul_succ_pow2_lt_pow3_succ : ∀ w : Nat,
    w ≥ 7 -> 4 * (w + 1) * 2 ^ w < 3 ^ (w + 1)
  | 0, hw => by omega
  | m + 1, hw => by
    by_cases hm6 : m = 6
    · subst hm6; decide
    · have ih := four_mul_succ_pow2_lt_pow3_succ m (by omega)
      have h2 : 4 * (m + 2) * 2 ^ (m + 1) = (8 * m + 16) * 2 ^ m := by
        rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm (4 * (m + 2) * 2 ^ m) 2]
        calc
          2 * (4 * (m + 2) * 2 ^ m) = (2 * (4 * (m + 2))) * 2 ^ m := (Nat.mul_assoc _ _ _).symm
          _ = (8 * m + 16) * 2 ^ m := by rw [show 2 * (4 * (m + 2)) = 8 * m + 16 by omega]
      have hle12 : (8 * m + 16) * 2 ^ m ≤ (12 * (m + 1)) * 2 ^ m :=
        Nat.mul_le_mul_right (2 ^ m) (by omega)
      have h12 : (12 * (m + 1)) * 2 ^ m = 3 * (4 * (m + 1) * 2 ^ m) := by
        rw [show 12 * (m + 1) = 3 * (4 * (m + 1)) by omega, Nat.mul_assoc 3]
      have h3_step : 3 * (4 * (m + 1) * 2 ^ m) < 3 ^ (m + 2) := by
        rw [Nat.pow_succ 3 (m + 1), Nat.mul_comm (3 ^ (m + 1)) 3]
        exact Nat.mul_lt_mul_of_pos_left ih (by decide)
      change 4 * (m + 2) * 2 ^ (m + 1) < 3 ^ (m + 2)
      rw [h2]
      exact Nat.lt_of_le_of_lt (by rw [← h12]; exact hle12) h3_step

theorem pow3_lt_pow2_two_mul : ∀ w : Nat, w ≥ 1 -> 3 ^ w < 2 ^ (2 * w)
  | 0, hw => by omega
  | 1, _ => by decide
  | w + 2, _ => by
    have ih := pow3_lt_pow2_two_mul (w + 1) (by omega)
    have h3 : 3 ^ (w + 2) = 3 * 3 ^ (w + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
    have h2 : 2 ^ (2 * (w + 2)) = 4 * 2 ^ (2 * (w + 1)) := by
      rw [show 2 * (w + 2) = 2 * (w + 1) + 2 by omega, Nat.pow_add, Nat.mul_comm]
    omega

theorem two_block_q1_ne_one (w2 a2 x0 q1 : Nat)
    (hw2 : w2 ≥ 1) (_ha2 : a2 ≥ 1)
    (h2nd : 3 ^ w2 < 2 ^ (w2 + a2))
    (hx0_odd : x0 % 2 = 1)
    (hx1_ge3 : 2 ^ w2 * q1 - 1 ≥ 3)
    (hx1_n3 : (2 ^ w2 * q1 - 1) % 3 ≠ 0)
    (hsyr2 : 3 ^ w2 * q1 - 1 = 2 ^ a2 * x0) :
    q1 ≠ 1 := by
  intro hq1
  subst hq1
  rw [Nat.mul_one] at hx1_ge3 hx1_n3 hsyr2
  have hw2_ge2 : w2 ≥ 2 := by
    cases w2 with
    | zero => omega
    | succ k =>
      cases k with
      | zero => simp at hx1_ge3
      | succ _ => omega
  have hw2_odd : w2 % 2 = 1 := pow2_sub1_nondiv3_imp_odd w2 hw2 hx1_n3
  have hm4 : (3 ^ w2 - 1) % 4 = 2 := pow3_odd_sub1_mod4_eq2 w2 hw2_odd
  have ha2_eq1 : a2 = 1 := pow2_mul_odd_eq_mod4_two_imp_one a2 x0 (3 ^ w2 - 1) hx0_odd hm4 hsyr2
  subst ha2_eq1
  have hlt := pow2_succ_lt_pow3 w2 hw2_ge2
  omega

theorem two_block_q0_ne_one (w1 a1 w2 a2 q0 q1 : Nat)
    (hw1 : w1 ≥ 2) (_ha1 : a1 ≥ 1) (hw2 : w2 ≥ 1) (_ha2 : a2 ≥ 1)
    (hW5 : w1 + w2 ≥ 5)
    (hgt : 3 ^ (w1 + w2) < 2 ^ (w1 + a1 + w2 + a2))
    (hx0_n3 : (2 ^ w1 * q0 - 1) % 3 ≠ 0)
    (hq1_ge1 : q1 ≥ 1) (hq1_odd : q1 % 2 = 1)
    (hsyr1 : 3 ^ w1 * q0 - 1 = 2 ^ a1 * (2 ^ w2 * q1 - 1))
    (hsyr2 : 3 ^ w2 * q1 - 1 = 2 ^ a2 * (2 ^ w1 * q0 - 1)) :
    q0 ≠ 1 := by
  intro hq0
  subst hq0
  rw [Nat.mul_one] at hx0_n3 hsyr1 hsyr2
  have hw1_odd : w1 % 2 = 1 := pow2_sub1_nondiv3_imp_odd w1 (by omega) hx0_n3
  have hm4 : (3 ^ w1 - 1) % 4 = 2 := pow3_odd_sub1_mod4_eq2 w1 hw1_odd
  have hp2w2 : 2 ^ w2 ≥ 2 := by simpa using pow2_mono_nat hw2
  have hx1_odd : (2 ^ w2 * q1 - 1) % 2 = 1 := by
    have hmul_ev : (2 ^ w2 * q1) % 2 = 0 := by
      rw [show w2 = (w2 - 1) + 1 by omega, Nat.pow_succ, Nat.mul_comm (2 ^ (w2 - 1)) 2,
          Nat.mul_assoc]; omega
    have hmul_ge2 : 2 ^ w2 * q1 ≥ 2 := Nat.mul_le_mul hp2w2 hq1_ge1
    generalize 2 ^ w2 * q1 = m at hmul_ev hmul_ge2
    omega
  have ha1_eq1 : a1 = 1 :=
    pow2_mul_odd_eq_mod4_two_imp_one a1 (2 ^ w2 * q1 - 1) (3 ^ w1 - 1) hx1_odd hm4 hsyr1
  subst ha1_eq1
  rw [Nat.pow_one] at hsyr1
  have h2_w2p1 : 2 ^ (w2 + 1) * q1 = 3 ^ w1 + 1 := by
    have hmul_ge2 : 2 ^ w2 * q1 ≥ 2 := Nat.mul_le_mul hp2w2 hq1_ge1
    have hp3_ge1 : 3 ^ w1 ≥ 1 := pow3_pos_nat w1
    have hstep : 2 * (2 ^ w2 * q1) = 2 ^ (w2 + 1) * q1 := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ w2) 2, Nat.mul_assoc]
    omega
  have hw2_eq1 : w2 = 1 := by
    by_cases hw2_1 : w2 = 1
    · exact hw2_1
    · exfalso
      have hw2_ge2 : w2 ≥ 2 := by omega
      have hm8_3 : (3 ^ w1 + 1) % 8 = 4 := by
        have ho : w1 = 2 * (w1 / 2) + 1 := by omega
        have h38 : 3 ^ w1 % 8 = 3 := by rw [ho]; exact pow3_odd_mod8 (w1 / 2)
        rw [Nat.add_mod, h38]
      have hm8_2 : (2 ^ (w2 + 1) * q1) % 8 = 0 := by
        have hsplit : w2 + 1 = 3 + (w2 - 2) := by omega
        rw [hsplit, Nat.pow_add, Nat.mul_assoc]
        change (8 * (2 ^ (w2 - 2) * q1)) % 8 = 0
        generalize 2 ^ (w2 - 2) * q1 = t
        omega
      rw [← h2_w2p1] at hm8_3
      omega
  subst hw2_eq1
  simp only [Nat.pow_one] at hsyr2
  change 4 * q1 = 3 ^ w1 + 1 at h2_w2p1
  have hfactor : 3 ^ (w1 + 1) - 1 = 2 ^ (a2 + 2) * (2 ^ w1 - 1) := by
    have h3succ : 3 ^ (w1 + 1) + 3 = 12 * q1 := by
      have h1 : 3 ^ (w1 + 1) + 3 = 3 * (3 ^ w1 + 1) := by
        rw [Nat.pow_succ, Nat.mul_comm (3 ^ w1) 3, Nat.mul_add, Nat.mul_one]
      rw [h1, ← h2_w2p1, ← Nat.mul_assoc]
    have h4syr : 12 * q1 = 4 * (2 ^ a2 * (2 ^ w1 - 1)) + 4 := by
      have hq : 3 * q1 = 2 ^ a2 * (2 ^ w1 - 1) + 1 := by omega
      calc
        12 * q1 = 4 * (3 * q1) := by rw [← Nat.mul_assoc]
        _ = 4 * (2 ^ a2 * (2 ^ w1 - 1) + 1) := by rw [hq]
        _ = 4 * (2 ^ a2 * (2 ^ w1 - 1)) + 4 := by rw [Nat.mul_add, Nat.mul_one]
    have h2a2 : 4 * (2 ^ a2 * (2 ^ w1 - 1)) = 2 ^ (a2 + 2) * (2 ^ w1 - 1) := by
      rw [Nat.pow_add 2 a2 2, show 2 ^ 2 = 4 from rfl, Nat.mul_comm (2 ^ a2) 4, Nat.mul_assoc]
    rw [h2a2] at h4syr
    omega
  have hlte := pow2_dvd_pow3_sub_one_le_four_mul (w1 + 1) (a2 + 2) (by omega) ⟨2 ^ w1 - 1, hfactor⟩
  by_cases hw1_le5 : w1 ≤ 5
  · have hw1_5 : w1 = 5 := by omega
    subst hw1_5
    have ha2_le2 : a2 ≤ 2 := by
      by_cases hle : a2 ≤ 2
      · exact hle
      · have hp32 : 32 ≤ 2 ^ (a2 + 2) := by simpa using pow2_mono_nat (by omega : 5 ≤ a2 + 2)
        omega
    have hk_le9 : 5 + 1 + 1 + a2 ≤ 9 := by omega
    have hp512 : 2 ^ (5 + 1 + 1 + a2) ≤ 2 ^ 9 := pow2_mono_nat hk_le9
    have h3_6 : (3 : Nat) ^ (5 + 1) = 729 := by decide
    have h2_9 : (2 : Nat) ^ 9 = 512 := by decide
    omega
  · have hw1_ge7 : w1 ≥ 7 := by omega
    have hp2w1 : 2 ^ w1 ≥ 4 := by simpa using pow2_mono_nat hw1
    have hprod_le : 2 ^ (a2 + 2) * (2 ^ w1 - 1) ≤ (4 * (w1 + 1)) * (2 ^ w1 - 1) :=
      Nat.mul_le_mul_right (2 ^ w1 - 1) hlte
    rw [← hfactor] at hprod_le
    have hexp : (4 * (w1 + 1)) * (2 ^ w1 - 1) + 4 * (w1 + 1) = 4 * (w1 + 1) * 2 ^ w1 := by
      calc
        (4 * (w1 + 1)) * (2 ^ w1 - 1) + 4 * (w1 + 1)
            = (4 * (w1 + 1)) * ((2 ^ w1 - 1) + 1) := by
              rw [Nat.mul_add (4 * (w1 + 1)), Nat.mul_one]
        _ = 4 * (w1 + 1) * 2 ^ w1 := by rw [Nat.sub_add_cancel (by omega)]
    have hlt_exp := four_mul_succ_pow2_lt_pow3_succ w1 hw1_ge7
    omega

theorem x0_ge_47_of_mod96_and_q0_ge3 (w1 q0 : Nat)
    (hw1 : w1 ≥ 2) (hq0_ge3 : q0 ≥ 3) (hq0_odd : q0 % 2 = 1)
    (hm96 : (2 ^ w1 * q0 - 1) % 96 = 7 ∨ (2 ^ w1 * q0 - 1) % 96 = 31 ∨
            (2 ^ w1 * q0 - 1) % 96 = 47 ∨ (2 ^ w1 * q0 - 1) % 96 = 59 ∨
            (2 ^ w1 * q0 - 1) % 96 = 71 ∨ (2 ^ w1 * q0 - 1) % 96 = 79 ∨
            (2 ^ w1 * q0 - 1) % 96 = 91 ∨ (2 ^ w1 * q0 - 1) % 96 = 95) :
    2 ^ w1 * q0 - 1 ≥ 47 := by
  by_cases hge : 2 ^ w1 * q0 - 1 ≥ 47
  · exact hge
  · exfalso
    have hp2w1 : 2 ^ w1 ≥ 4 := by simpa using pow2_mono_nat hw1
    have hlt96 : 2 ^ w1 * q0 - 1 < 96 := by omega
    rw [Nat.mod_eq_of_lt hlt96] at hm96
    have hx_cases : 2 ^ w1 * q0 = 8 ∨ 2 ^ w1 * q0 = 32 := by omega
    have hq_le8 : q0 ≤ 8 := by
      have hm := Nat.mul_le_mul_right q0 hp2w1
      omega
    have hq_cases : q0 = 3 ∨ q0 = 5 ∨ q0 = 7 := by omega
    rcases hq_cases with rfl | rfl | rfl <;> omega

theorem twenty_three_mul_det_lt_pow3_and_W_ge8
    (w1 w2 K D C1 C2 x0 x1 : Nat)
    (hw1 : w1 ≥ 2) (hw2 : w2 ≥ 1)
    (hW5 : w1 + w2 ≥ 5) (hK8 : K ≥ 8)
    (hgt : 3 ^ (w1 + w2) < 2 ^ K)
    (hband_hi : 7 ^ (w1 + w2) * 2 ^ K ≤ 22 ^ (w1 + w2))
    (hD : D = 2 ^ K - 3 ^ (w1 + w2))
    (hC1 : C1 = 3 ^ w1 - 2 ^ w1)
    (hC2 : C2 = 3 ^ w2 - 2 ^ w2)
    (hx0_47 : x0 ≥ 47) (hx1_49 : x1 ≥ 49)
    (hrecip : D * (x0 * x1) = 3 ^ w2 * C1 * x1 + 3 ^ w1 * C2 * x0 + C1 * C2) :
    23 * D < 3 ^ (w1 + w2) ∧ w1 + w2 ≥ 8 ∧ K ≥ 13 := by
  have hp2w1 : 2 ^ w1 ≥ 4 := by simpa using pow2_mono_nat hw1
  have hp2w2 : 2 ^ w2 ≥ 2 := by simpa using pow2_mono_nat hw2
  have hC1_lt : C1 < 3 ^ w1 := by have h := pow3_pos_nat w1; omega
  have hC2_lt : C2 < 3 ^ w2 := by have h := pow3_pos_nat w2; omega
  have h3W_split : 3 ^ w2 * 3 ^ w1 = 3 ^ (w1 + w2) := by
    rw [Nat.mul_comm, ← Nat.pow_add]
  have ht1 : 3 ^ w2 * C1 * x1 < 3 ^ (w1 + w2) * x1 := by
    rw [← h3W_split]
    have hm1 : 3 ^ w2 * C1 < 3 ^ w2 * 3 ^ w1 :=
      Nat.mul_lt_mul_of_pos_left hC1_lt (pow3_pos_nat w2)
    exact Nat.mul_lt_mul_of_pos_right hm1 (by omega)
  have ht2 : 3 ^ w1 * C2 * x0 < 3 ^ (w1 + w2) * x0 := by
    rw [← h3W_split, Nat.mul_comm (3 ^ w2) (3 ^ w1)]
    have hm1 : 3 ^ w1 * C2 < 3 ^ w1 * 3 ^ w2 :=
      Nat.mul_lt_mul_of_pos_left hC2_lt (pow3_pos_nat w1)
    exact Nat.mul_lt_mul_of_pos_right hm1 (by omega)
  have ht3 : C1 * C2 < 3 ^ (w1 + w2) := by
    rw [← h3W_split, Nat.mul_comm (3 ^ w2) (3 ^ w1)]
    have hm1 : C1 * C2 ≤ C1 * 3 ^ w2 := Nat.mul_le_mul_left C1 (Nat.le_of_lt hC2_lt)
    have hm2 : C1 * 3 ^ w2 < 3 ^ w1 * 3 ^ w2 :=
      Nat.mul_lt_mul_of_pos_right hC1_lt (pow3_pos_nat w2)
    omega
  have hDx0x1_lt : D * (x0 * x1) < 3 ^ (w1 + w2) * (x1 + x0 + 1) := by
    rw [hrecip, Nat.mul_add (3 ^ (w1 + w2)), Nat.mul_add (3 ^ (w1 + w2)), Nat.mul_one]
    omega
  have h23_sum_lt : 23 * (x1 + x0 + 1) < x0 * x1 := by
    let u := x0 - 47
    let v := x1 - 49
    have hx0_u : x0 = 47 + u := by dsimp [u]; omega
    have hx1_v : x1 = 49 + v := by dsimp [v]; omega
    rw [hx0_u, hx1_v, Nat.add_mul 47 u (49 + v), Nat.mul_add 47 49 v, Nat.mul_add u 49 v]
    have h47_49 : 47 * 49 = 2303 := rfl
    rw [h47_49, Nat.mul_comm u 49]
    have huv : u * v ≥ 0 := Nat.zero_le _
    generalize u * v = p at huv
    omega
  have h23D_lt : 23 * D < 3 ^ (w1 + w2) := by
    have hm : D * (23 * (x1 + x0 + 1)) ≤ D * (x0 * x1) :=
      Nat.mul_le_mul_left D (Nat.le_of_lt h23_sum_lt)
    have hassoc : (23 * D) * (x1 + x0 + 1) = D * (23 * (x1 + x0 + 1)) := by
      rw [Nat.mul_comm 23 D, Nat.mul_assoc D 23 (x1 + x0 + 1)]
    have hlt_mul : (23 * D) * (x1 + x0 + 1) < 3 ^ (w1 + w2) * (x1 + x0 + 1) := by omega
    by_cases h23 : 23 * D < 3 ^ (w1 + w2)
    · exact h23
    · exfalso
      have hge := Nat.mul_le_mul_right (x1 + x0 + 1) (by omega : 3 ^ (w1 + w2) ≤ 23 * D)
      omega
  have hW_ge8 : w1 + w2 ≥ 8 := by
    by_cases hw8 : w1 + w2 ≥ 8
    · exact hw8
    · exfalso
      have hw_cases : w1 + w2 = 5 ∨ w1 + w2 = 6 ∨ w1 + w2 = 7 := by omega
      rcases hw_cases with hw5 | hw6 | hw7
      · rw [hw5] at hgt hD h23D_lt
        have hp256 : 256 ≤ 2 ^ K := by simpa using pow2_mono_nat hK8
        have h3_5 : (3 : Nat) ^ 5 = 243 := rfl
        rw [h3_5] at hD h23D_lt
        omega
      · rw [hw6] at hgt hband_hi
        have hK10 : K ≥ 10 := by
          by_cases hk10 : K ≥ 10
          · exact hk10
          · have hp9 : 2 ^ K ≤ 2 ^ 9 := pow2_mono_nat (by omega)
            have h3_6 : (3 : Nat) ^ 6 = 729 := rfl
            have h2_9 : (2 : Nat) ^ 9 = 512 := rfl
            omega
        have hp10 : 2 ^ 10 ≤ 2 ^ K := pow2_mono_nat hK10
        have hm7 : 7 ^ 6 * 2 ^ 10 ≤ 7 ^ 6 * 2 ^ K := Nat.mul_le_mul_left (7 ^ 6) hp10
        have hbad : ¬ (7 ^ 6 * 2 ^ 10 ≤ 22 ^ 6) := by decide
        exact hbad (Nat.le_trans hm7 hband_hi)
      · rw [hw7] at hgt hband_hi
        have hK12 : K ≥ 12 := by
          by_cases hk12 : K ≥ 12
          · exact hk12
          · have hp11 : 2 ^ K ≤ 2 ^ 11 := pow2_mono_nat (by omega)
            have h3_7 : (3 : Nat) ^ 7 = 2187 := rfl
            have h2_11 : (2 : Nat) ^ 11 = 2048 := rfl
            omega
        have hp12 : 2 ^ 12 ≤ 2 ^ K := pow2_mono_nat hK12
        have hm7 : 7 ^ 7 * 2 ^ 12 ≤ 7 ^ 7 * 2 ^ K := Nat.mul_le_mul_left (7 ^ 7) hp12
        have hbad : ¬ (7 ^ 7 * 2 ^ 12 ≤ 22 ^ 7) := by decide
        exact hbad (Nat.le_trans hm7 hband_hi)
  have hK_ge13 : K ≥ 13 := by
    have h3_8 : 3 ^ 8 ≤ 3 ^ (w1 + w2) := by
      have hs : w1 + w2 = 8 + (w1 + w2 - 8) := by omega
      rw [hs, Nat.pow_add]
      have hp := pow3_pos_nat (w1 + w2 - 8)
      have hm := Nat.mul_le_mul_left (3 ^ 8) hp
      simpa using hm
    by_cases hk13 : K ≥ 13
    · exact hk13
    · have hp12 : 2 ^ K ≤ 2 ^ 12 := pow2_mono_nat (by omega)
      have h6561 : (3 : Nat) ^ 8 = 6561 := rfl
      have h4096 : (2 : Nat) ^ 12 = 4096 := rfl
      omega
  exact ⟨h23D_lt, hW_ge8, hK_ge13⟩

theorem dual_brox_cubic_squeeze (w1 a1 w2 a2 D q0 q1 : Nat)
    (hw1 : w1 ≥ 2) (ha1 : a1 ≥ 1) (hw2 : w2 ≥ 1) (_ha2 : a2 ≥ 1)
    (hgt : 3 ^ (w1 + w2) < 2 ^ (w1 + a1 + w2 + a2))
    (h1st : 2 ^ (w1 + a1) < 3 ^ w1)
    (hq0_ge3 : q0 ≥ 3) (hq1_ge3 : q1 ≥ 3)
    (hbrox0 : D * q0 = twoBlockBroxCarry w1 a1 w2 a2)
    (hbrox1 : D * q1 = twoBlockBroxCarry w2 a2 w1 a1) :
    27 * 2 ^ (w1 + w2 + a1 - 3) * D ^ 3 < 2 ^ (3 * (w1 + a1 + w2 + a2)) := by
  let W := w1 + w2
  let K := w1 + a1 + w2 + a2
  have hb0 : 3 * 2 ^ (w1 - 1) * D < 2 ^ K := by
    have hp2a1 : 2 ^ a1 - 1 < 2 ^ a1 := by have h := pow2_pos_nat a1; omega
    have hp2a2 : 2 ^ a2 - 1 < 2 ^ a2 := by have h := pow2_pos_nat a2; omega
    have ht1 : 2 ^ w1 * (3 ^ w2 * (2 ^ a1 - 1)) < 2 ^ K := by
      have hm1 : 3 ^ w2 * (2 ^ a1 - 1) < 3 ^ w2 * 2 ^ a1 :=
        Nat.mul_lt_mul_of_pos_left hp2a1 (pow3_pos_nat w2)
      have hm2 : 2 ^ w1 * (3 ^ w2 * (2 ^ a1 - 1)) < 2 ^ w1 * (3 ^ w2 * 2 ^ a1) :=
        Nat.mul_lt_mul_of_pos_left hm1 (pow2_pos_nat w1)
      have hrew : 2 ^ w1 * (3 ^ w2 * 2 ^ a1) = 3 ^ w2 * 2 ^ (w1 + a1) := by
        rw [← Nat.mul_assoc, Nat.mul_comm (2 ^ w1) (3 ^ w2), Nat.mul_assoc, ← Nat.pow_add]
      have hm3 : 3 ^ w2 * 2 ^ (w1 + a1) < 3 ^ (w1 + w2) := by
        rw [Nat.pow_add 3 w1 w2, Nat.mul_comm (3 ^ w1) (3 ^ w2)]
        exact Nat.mul_lt_mul_of_pos_left h1st (pow3_pos_nat w2)
      dsimp [K]; omega
    have ht2 : 2 ^ w1 * (2 ^ (a1 + w2) * (2 ^ a2 - 1)) < 2 ^ K := by
      have hm1 : 2 ^ (a1 + w2) * (2 ^ a2 - 1) < 2 ^ (a1 + w2) * 2 ^ a2 :=
        Nat.mul_lt_mul_of_pos_left hp2a2 (pow2_pos_nat _)
      have hm2 : 2 ^ w1 * (2 ^ (a1 + w2) * (2 ^ a2 - 1)) < 2 ^ w1 * (2 ^ (a1 + w2) * 2 ^ a2) :=
        Nat.mul_lt_mul_of_pos_left hm1 (pow2_pos_nat w1)
      have hrew : 2 ^ w1 * (2 ^ (a1 + w2) * 2 ^ a2) = 2 ^ K := by
        dsimp [K]
        rw [← Nat.pow_add 2 (a1 + w2) a2, ← Nat.pow_add 2 w1 (a1 + w2 + a2),
            show w1 + (a1 + w2 + a2) = w1 + a1 + w2 + a2 by omega]
      omega
    have h2H0 : 2 ^ w1 * (D * q0) < 2 * 2 ^ K := by
      rw [hbrox0]; unfold twoBlockBroxCarry; dsimp only
      rw [Nat.mul_add (2 ^ w1)]; omega
    have h3D_le : 2 * (3 * 2 ^ (w1 - 1) * D) ≤ 2 ^ w1 * (D * q0) := by
      have hm : 3 * D ≤ D * q0 := by
        rw [Nat.mul_comm D q0]; exact Nat.mul_le_mul_right D hq0_ge3
      have h2w : 2 ^ w1 = 2 * 2 ^ (w1 - 1) := by
        conv => lhs; rw [show w1 = (w1 - 1) + 1 by omega]
        rw [Nat.pow_succ, Nat.mul_comm]
      calc
        2 * (3 * 2 ^ (w1 - 1) * D)
            = (2 * 2 ^ (w1 - 1)) * (3 * D) := by
              rw [Nat.mul_comm 3 (2 ^ (w1 - 1)), Nat.mul_assoc (2 ^ (w1 - 1)) 3 D,
                  ← Nat.mul_assoc 2 (2 ^ (w1 - 1))]
        _ = 2 ^ w1 * (3 * D) := by rw [← h2w]
        _ ≤ 2 ^ w1 * (D * q0) := Nat.mul_le_mul_left (2 ^ w1) hm
    omega
  have hb1 : 3 * 2 ^ (W + a1 - 1) * D < 3 ^ w1 * 2 ^ K := by
    have hp2a1 : 2 ^ a1 - 1 < 2 ^ a1 := by have h := pow2_pos_nat a1; omega
    have hp2a2 : 2 ^ a2 - 1 < 2 ^ a2 := by have h := pow2_pos_nat a2; omega
    have ht1 : 2 ^ (W + a1) * (3 ^ w1 * (2 ^ a2 - 1)) < 3 ^ w1 * 2 ^ K := by
      have hm1 : 3 ^ w1 * (2 ^ a2 - 1) < 3 ^ w1 * 2 ^ a2 :=
        Nat.mul_lt_mul_of_pos_left hp2a2 (pow3_pos_nat w1)
      have hm2 : 2 ^ (W + a1) * (3 ^ w1 * (2 ^ a2 - 1)) < 2 ^ (W + a1) * (3 ^ w1 * 2 ^ a2) :=
        Nat.mul_lt_mul_of_pos_left hm1 (pow2_pos_nat _)
      have hrew : 2 ^ (W + a1) * (3 ^ w1 * 2 ^ a2) = 3 ^ w1 * 2 ^ K := by
        dsimp [W, K]
        rw [← Nat.mul_assoc, Nat.mul_comm (2 ^ (w1 + w2 + a1)) (3 ^ w1), Nat.mul_assoc,
            ← Nat.pow_add, show w1 + w2 + a1 + a2 = w1 + a1 + w2 + a2 by omega]
      omega
    have ht2 : 2 ^ (W + a1) * (2 ^ (a2 + w1) * (2 ^ a1 - 1)) < 3 ^ w1 * 2 ^ K := by
      have hm1 : 2 ^ (a2 + w1) * (2 ^ a1 - 1) < 2 ^ (a2 + w1) * 2 ^ a1 :=
        Nat.mul_lt_mul_of_pos_left hp2a1 (pow2_pos_nat _)
      have hm2 : 2 ^ (W + a1) * (2 ^ (a2 + w1) * (2 ^ a1 - 1)) <
          2 ^ (W + a1) * (2 ^ (a2 + w1) * 2 ^ a1) :=
        Nat.mul_lt_mul_of_pos_left hm1 (pow2_pos_nat _)
      have hrew : 2 ^ (W + a1) * (2 ^ (a2 + w1) * 2 ^ a1) = 2 ^ (w1 + a1) * 2 ^ K := by
        dsimp [W, K]
        rw [← Nat.pow_add 2 (a2 + w1) a1, ← Nat.pow_add 2 (w1 + w2 + a1),
            ← Nat.pow_add 2 (w1 + a1),
            show w1 + w2 + a1 + (a2 + w1 + a1) = w1 + a1 + (w1 + a1 + w2 + a2) by omega]
      have hm3 : 2 ^ (w1 + a1) * 2 ^ K < 3 ^ w1 * 2 ^ K :=
        Nat.mul_lt_mul_of_pos_right h1st (pow2_pos_nat K)
      omega
    have h2H1 : 2 ^ (W + a1) * (D * q1) < 2 * (3 ^ w1 * 2 ^ K) := by
      rw [hbrox1]; unfold twoBlockBroxCarry; dsimp only
      rw [Nat.mul_add (2 ^ (W + a1))]; omega
    have h3D_le : 2 * (3 * 2 ^ (W + a1 - 1) * D) ≤ 2 ^ (W + a1) * (D * q1) := by
      have hm : 3 * D ≤ D * q1 := by
        rw [Nat.mul_comm D q1]; exact Nat.mul_le_mul_right D hq1_ge3
      have h2wa : 2 ^ (W + a1) = 2 * 2 ^ (W + a1 - 1) := by
        conv => lhs; rw [show W + a1 = (W + a1 - 1) + 1 by dsimp [W]; omega]
        rw [Nat.pow_succ, Nat.mul_comm]
      calc
        2 * (3 * 2 ^ (W + a1 - 1) * D)
            = (2 * 2 ^ (W + a1 - 1)) * (3 * D) := by
              rw [Nat.mul_comm 3 (2 ^ (W + a1 - 1)), Nat.mul_assoc (2 ^ (W + a1 - 1)) 3 D,
                  ← Nat.mul_assoc 2 (2 ^ (W + a1 - 1))]
        _ = 2 ^ (W + a1) * (3 * D) := by rw [← h2wa]
        _ ≤ 2 ^ (W + a1) * (D * q1) := Nat.mul_le_mul_left (2 ^ (W + a1)) hm
    omega
  -- Multiply `hb0 * hb0 * hb1` and cancel `2 ^ (2 * w1)`:
  let A0 := 3 * 2 ^ (w1 - 1) * D
  let A1 := 3 * 2 ^ (W + a1 - 1) * D
  have hsq : A0 * A0 < 2 ^ K * 2 ^ K := by
    have hm1 : A0 * A0 ≤ A0 * 2 ^ K := Nat.mul_le_mul_left A0 (Nat.le_of_lt hb0)
    have hm2 : A0 * 2 ^ K < 2 ^ K * 2 ^ K := Nat.mul_lt_mul_of_pos_right hb0 (pow2_pos_nat K)
    omega
  have hcube : (A0 * A0) * A1 < (2 ^ K * 2 ^ K) * (3 ^ w1 * 2 ^ K) := by
    have hm1 : (A0 * A0) * A1 ≤ (A0 * A0) * (3 ^ w1 * 2 ^ K) :=
      Nat.mul_le_mul_left _ (Nat.le_of_lt hb1)
    have hm2 : (A0 * A0) * (3 ^ w1 * 2 ^ K) < (2 ^ K * 2 ^ K) * (3 ^ w1 * 2 ^ K) :=
      Nat.mul_lt_mul_of_pos_right hsq (Nat.mul_pos (pow3_pos_nat w1) (pow2_pos_nat K))
    omega
  have hrhs_lt : (2 ^ K * 2 ^ K) * (3 ^ w1 * 2 ^ K) < 2 ^ (2 * w1) * 2 ^ (3 * K) := by
    have h3_lt_4 := pow3_lt_pow2_two_mul w1 (by omega)
    have hrew : (2 ^ K * 2 ^ K) * (3 ^ w1 * 2 ^ K) = 3 ^ w1 * 2 ^ (3 * K) := by
      rw [← Nat.mul_assoc (2 ^ K * 2 ^ K), Nat.mul_comm (2 ^ K * 2 ^ K) (3 ^ w1),
          Nat.mul_assoc (3 ^ w1), ← Nat.pow_add 2 K K, ← Nat.pow_add 2 (K + K) K,
          show K + K + K = 3 * K by omega]
    rw [hrew]
    exact Nat.mul_lt_mul_of_pos_right h3_lt_4 (pow2_pos_nat (3 * K))
  have hlhs_eq : (A0 * A0) * A1 = 2 ^ (2 * w1) * (27 * 2 ^ (W + a1 - 3) * D ^ 3) := by
    dsimp [A0, A1]
    have hpow_sum :
        2 ^ (w1 - 1) * (2 ^ (w1 - 1) * 2 ^ (W + a1 - 1)) =
          2 ^ (2 * w1) * 2 ^ (W + a1 - 3) := by
      rw [← Nat.pow_add 2 (w1 - 1) (W + a1 - 1),
          ← Nat.pow_add 2 (w1 - 1),
          ← Nat.pow_add 2 (2 * w1),
          show (w1 - 1) + ((w1 - 1) + (W + a1 - 1)) = 2 * w1 + (W + a1 - 3) by dsimp [W]; omega]
    have hD3 : D ^ 3 = D * (D * D) := by
      rw [show (3 : Nat) = 2 + 1 from rfl, Nat.pow_succ, show (2 : Nat) = 1 + 1 from rfl,
          Nat.pow_succ, Nat.pow_one, Nat.mul_comm (D * D) D]
    rw [hD3]
    generalize 2 ^ (w1 - 1) = p1, 2 ^ (W + a1 - 1) = p2,
               2 ^ (2 * w1) = q1p, 2 ^ (W + a1 - 3) = q2p at hpow_sum
    calc
      (3 * p1 * D * (3 * p1 * D)) * (3 * p2 * D)
          = 27 * (p1 * (p1 * p2)) * (D * (D * D)) := by
            have hc1 : 3 * p1 * D * (3 * p1 * D) = 9 * (p1 * p1) * (D * D) := by
              calc
                (3 * p1 * D) * (3 * p1 * D)
                    = ((3 * p1) * (3 * p1)) * (D * D) := by
                      rw [Nat.mul_assoc (3 * p1) D, ← Nat.mul_assoc D (3 * p1) D,
                          Nat.mul_comm D (3 * p1), Nat.mul_assoc (3 * p1) D D,
                          ← Nat.mul_assoc (3 * p1) (3 * p1)]
                _ = 9 * (p1 * p1) * (D * D) := by
                      have h9 : (3 * p1) * (3 * p1) = 9 * (p1 * p1) := by
                        rw [Nat.mul_assoc 3 p1, ← Nat.mul_assoc p1 3 p1, Nat.mul_comm p1 3,
                            Nat.mul_assoc 3 p1 p1, ← Nat.mul_assoc 3 3]
                      rw [h9]
            rw [hc1]
            calc
              (9 * (p1 * p1) * (D * D)) * (3 * p2 * D)
                  = ((9 * (p1 * p1)) * (3 * p2)) * ((D * D) * D) := by
                    rw [Nat.mul_assoc (9 * (p1 * p1)) (D * D),
                        ← Nat.mul_assoc (D * D) (3 * p2) D,
                        Nat.mul_comm (D * D) (3 * p2),
                        Nat.mul_assoc (3 * p2) (D * D) D,
                        ← Nat.mul_assoc (9 * (p1 * p1)) (3 * p2)]
              _ = 27 * (p1 * (p1 * p2)) * (D * (D * D)) := by
                    have h27 : (9 * (p1 * p1)) * (3 * p2) = 27 * (p1 * (p1 * p2)) := by
                      rw [Nat.mul_assoc 9 (p1 * p1), ← Nat.mul_assoc (p1 * p1) 3 p2,
                          Nat.mul_comm (p1 * p1) 3, Nat.mul_assoc 3 (p1 * p1) p2,
                          ← Nat.mul_assoc 9 3, Nat.mul_assoc p1 p1 p2]
                    rw [h27, Nat.mul_assoc D D D]
      _ = 27 * (q1p * q2p) * (D * (D * D)) := by rw [hpow_sum]
      _ = q1p * (27 * q2p * (D * (D * D))) := by
            rw [← Nat.mul_assoc 27 q1p q2p, Nat.mul_comm 27 q1p,
                Nat.mul_assoc q1p 27 q2p, Nat.mul_assoc q1p (27 * q2p)]
  have hcomb : 2 ^ (2 * w1) * (27 * 2 ^ (W + a1 - 3) * D ^ 3) < 2 ^ (2 * w1) * 2 ^ (3 * K) := by
    omega
  by_cases hres : 27 * 2 ^ (W + a1 - 3) * D ^ 3 < 2 ^ (3 * K)
  · exact hres
  · exfalso
    have hge := Nat.mul_le_mul_left (2 ^ (2 * w1))
      (by omega : 2 ^ (3 * K) ≤ 27 * 2 ^ (W + a1 - 3) * D ^ 3)
    omega

/--
  Theorem T10b (`two_block_mersenne_elimination_and_cubic_squeeze`, `[]` axioms):
  Universal 2-Block Mersenne Elimination (`q0 ≥ 3 ∧ q1 ≥ 3`), `x0 ≥ 47`, `23 * D < 3 ^ W`,
  `W ≥ 8, K ≥ 13`, and Dual Brox Cubic Squeeze `27 * 2 ^ (W + a1 - 3) * D ^ 3 < 2 ^ (3 * K)`!
-/
theorem two_block_mersenne_elimination_and_cubic_squeeze
    (w1 a1 w2 a2 q0 : Nat)
    (hw1 : w1 ≥ 2) (ha1 : a1 ≥ 1) (hw2 : w2 ≥ 1) (ha2 : a2 ≥ 1)
    (hW5 : w1 + w2 ≥ 5) (hK8 : w1 + a1 + w2 + a2 ≥ 8)
    (hband_lo : 21 ^ (w1 + w2) < 7 ^ (w1 + w2) * 2 ^ (w1 + a1 + w2 + a2))
    (hband_hi : 7 ^ (w1 + w2) * 2 ^ (w1 + a1 + w2 + a2) ≤ 22 ^ (w1 + w2))
    (h1st : 2 ^ (w1 + a1) < 3 ^ w1)
    (hbrox0 : (2 ^ (w1 + a1 + w2 + a2) - 3 ^ (w1 + w2)) * q0 = twoBlockBroxCarry w1 a1 w2 a2)
    (hm96 : (2 ^ w1 * q0 - 1) % 96 = 7 ∨ (2 ^ w1 * q0 - 1) % 96 = 31 ∨
            (2 ^ w1 * q0 - 1) % 96 = 47 ∨ (2 ^ w1 * q0 - 1) % 96 = 59 ∨
            (2 ^ w1 * q0 - 1) % 96 = 71 ∨ (2 ^ w1 * q0 - 1) % 96 = 79 ∨
            (2 ^ w1 * q0 - 1) % 96 = 91 ∨ (2 ^ w1 * q0 - 1) % 96 = 95)
    (hx1_gt : ∀ q1 : Nat,
      (2 ^ (w1 + a1 + w2 + a2) - 3 ^ (w1 + w2)) * q1 = twoBlockBroxCarry w2 a2 w1 a1 ->
      2 ^ w2 * q1 - 1 ≥ (2 ^ w1 * q0 - 1) + 2 ∧ (2 ^ w2 * q1 - 1) % 3 ≠ 0) :
    ∃ q1 : Nat, IsPrimitiveTwoBlockBroxWitness w1 a1 w2 a2 q0 q1 := by
  have hgt : 3 ^ (w1 + w2) < 2 ^ (w1 + a1 + w2 + a2) := by
    have h21 : (21 : Nat) ^ (w1 + w2) = 7 ^ (w1 + w2) * 3 ^ (w1 + w2) :=
      mul_pow_nat 7 3 (w1 + w2)
    by_cases hlt : 3 ^ (w1 + w2) < 2 ^ (w1 + a1 + w2 + a2)
    · exact hlt
    · exfalso
      have hm := Nat.mul_le_mul_left (7 ^ (w1 + w2))
        (by omega : 2 ^ (w1 + a1 + w2 + a2) ≤ 3 ^ (w1 + w2))
      omega
  have h2nd : 3 ^ w2 < 2 ^ (w2 + a2) := by
    by_cases hlt : 3 ^ w2 < 2 ^ (w2 + a2)
    · exact hlt
    · exfalso
      have hm1 : 2 ^ (w1 + a1) * 2 ^ (w2 + a2) ≤ 2 ^ (w1 + a1) * 3 ^ w2 :=
        Nat.mul_le_mul_left _ (by omega)
      have hm2 : 2 ^ (w1 + a1) * 3 ^ w2 < 3 ^ w1 * 3 ^ w2 :=
        Nat.mul_lt_mul_of_pos_right h1st (pow3_pos_nat w2)
      rw [← Nat.pow_add 2 (w1 + a1) (w2 + a2),
          show (w1 + a1) + (w2 + a2) = w1 + a1 + w2 + a2 by omega] at hm1
      rw [← Nat.pow_add 3 w1 w2] at hm2
      omega
  rcases two_block_reciprocal_and_cross_carry_identity w1 a1 w2 a2 q0
      (by omega) ha1 hw2 ha2 hgt hbrox0 with
    ⟨q1, hq0_ge1, hq1_ge1, hq0_odd, hq1_odd, hbrox1, _, _, hsyr1, hsyr2, hrecip⟩
  rcases hx1_gt q1 hbrox1 with ⟨hx1_ge_x0p2, hx1_n3⟩
  rcases mod96_8classes_imp_mod16_and_mod3 (2 ^ w1 * q0 - 1) hm96 with ⟨hm16, hx0_n3⟩
  have hx0_odd : (2 ^ w1 * q0 - 1) % 2 = 1 := by omega
  have hx0_ge7 : 2 ^ w1 * q0 - 1 ≥ 7 := by omega
  have hq1_ne1 : q1 ≠ 1 :=
    two_block_q1_ne_one w2 a2 (2 ^ w1 * q0 - 1) q1 hw2 ha2 h2nd hx0_odd (by omega) hx1_n3 hsyr2
  have hq0_ne1 : q0 ≠ 1 :=
    two_block_q0_ne_one w1 a1 w2 a2 q0 q1 hw1 ha1 hw2 ha2 hW5 hgt hx0_n3 hq1_ge1 hq1_odd hsyr1 hsyr2
  have hq0_ge3 : q0 ≥ 3 := by omega
  have hq1_ge3 : q1 ≥ 3 := by omega
  have hx0_47 : 2 ^ w1 * q0 - 1 ≥ 47 :=
    x0_ge_47_of_mod96_and_q0_ge3 w1 q0 hw1 hq0_ge3 hq0_odd hm96
  rcases twenty_three_mul_det_lt_pow3_and_W_ge8 w1 w2 (w1 + a1 + w2 + a2)
      (2 ^ (w1 + a1 + w2 + a2) - 3 ^ (w1 + w2)) (3 ^ w1 - 2 ^ w1) (3 ^ w2 - 2 ^ w2)
      (2 ^ w1 * q0 - 1) (2 ^ w2 * q1 - 1)
      hw1 hw2 hW5 hK8 hgt hband_hi rfl rfl rfl hx0_47 (by omega) hrecip with
    ⟨h23D_lt, hW_ge8, hK_ge13⟩
  have hD24 := (det_mod24_and_ge5_constructive (w1 + a1 + w2 + a2) (w1 + w2)
    (by omega) (by omega) hgt).1
  have hcubic := dual_brox_cubic_squeeze w1 a1 w2 a2
    (2 ^ (w1 + a1 + w2 + a2) - 3 ^ (w1 + w2)) q0 q1
    hw1 ha1 hw2 ha2 hgt h1st hq0_ge3 hq1_ge3 hbrox0 hbrox1
  refine ⟨q1, ?_⟩
  unfold IsPrimitiveTwoBlockBroxWitness
  dsimp only
  exact ⟨hw1, ha1, hw2, ha2, hq0_ge3, hq1_ge3, hq0_odd, hq1_odd,
         hW_ge8, hK_ge13, hband_lo, hband_hi, h1st, h2nd, hD24,
         h23D_lt, hx0_47, hx1_ge_x0p2, hm96, hx1_n3, hbrox0, hbrox1, hcubic⟩

/--
  Kernel Certification of the Two `W = 5, K = 8, D = 13` `M1 = Q_(2)^+` 2-Block
  Obstruction Witnesses (`251/13 ↔ 439/13` and `287/13 ↔ 331/13`, `[]` axioms):
  Proves both satisfy `(21, 22)` band + `2^(w1+a1) < 3^w1 ∧ 3^w2 < 2^(w2+a2)` (and `v_B`
  EVEN satisfies `H0 ≥ 3*D`, `H1 ≥ 3*D`, AND the cubic squeeze `27 * 2^3 * 13^3 < 2^24`),
  yet BOTH are unconditionally separated from `Z^+` by `13 ∤ H0` and `23 * 13 > 3 ^ 5`!
-/
theorem two_block_m1_potential_obstruction_witnesses :
    let D := 2 ^ 8 - 3 ^ 5
    D = 13 ∧ 21 ^ 5 < 7 ^ 5 * 2 ^ 8 ∧ 7 ^ 5 * 2 ^ 8 ≤ 22 ^ 5 ∧
    -- Witness A `(3, 1, 2, 2)`: `251/13 <-> 439/13`, satisfies `Q_{>0}` potential bound `3*15*D < 4*3^5`:
    twoBlockBroxCarry 3 1 2 2 = 33 ∧ 3 * 15 * D < 4 * 3 ^ 5 ∧ 33 % D ≠ 0 ∧
    -- Witness B `(2, 1, 3, 2)`: `287/13 <-> 331/13`, satisfies `H0 ≥ 3*D, H1 ≥ 3*D` & cubic squeeze:
    twoBlockBroxCarry 2 1 3 2 = 75 ∧ twoBlockBroxCarry 3 2 2 1 = 43 ∧
    75 ≥ 3 * D ∧ 43 ≥ 3 * D ∧ 27 * 2 ^ (5 + 1 - 3) * D ^ 3 < 2 ^ 24 ∧
    75 % D ≠ 0 ∧ ¬ (23 * D < 3 ^ 5) := by
  decide

-- ----------------------------------------------------------------------------
-- T10c: Complete 2-Block Cycle Reduction (`NoTwoBlockPositiveCycles ↔ ...`) &
--       `SubexponentialCubicGapProp -> NoOneBlock ∧ NoTwoBlock`
-- ----------------------------------------------------------------------------

theorem parity_cons_true_imp_odd (k z : Nat) (rest : List Bool)
    (h : parityOfIter (k + 1) z = true :: rest) :
    z % 2 = 1 ∧ parityOfIter k (collatzStep z) = rest := by
  simp only [parityOfIter, List.cons.injEq] at h
  rcases h with ⟨hb, hrest⟩
  by_cases hev : z % 2 = 0
  · have ht : (z % 2 == 0) = true := decide_eq_true hev
    rw [ht] at hb; simp at hb
  · exact ⟨by omega, hrest⟩

theorem parity_cons_false_imp_even (k z : Nat) (rest : List Bool)
    (h : parityOfIter (k + 1) z = false :: rest) :
    z % 2 = 0 ∧ parityOfIter k (collatzStep z) = rest := by
  simp only [parityOfIter, List.cons.injEq] at h
  rcases h with ⟨hb, hrest⟩
  by_cases hev : z % 2 = 0
  · exact ⟨hev, hrest⟩
  · have hf : (z % 2 == 0) = false := decide_eq_false hev
    rw [hf] at hb; simp at hb

theorem odd_prefix_iter_ge : ∀ (w k z : Nat) (tail : List Bool),
    z > 0 -> parityOfIter (w + k) z = List.replicate w true ++ tail ->
    ∀ j : Nat, j ≤ w -> z ≤ collatzIter j z
  | 0, _, z, _, _, _, j, hj => by
    have hj0 : j = 0 := by omega
    subst hj0; simp [collatzIter]
  | w + 1, k, z, tail, hz, hv, j, hj => by
    rw [Nat.succ_add, List.replicate_succ, List.cons_append] at hv
    rcases parity_cons_true_imp_odd (w + k) z _ hv with ⟨hz_odd, hv_next⟩
    cases j with
    | zero => simp [collatzIter]
    | succ j' =>
      have hstep_gt : collatzStep z > z := by
        rw [collatzStep_of_odd_nat z hz_odd]; omega
      have ih := odd_prefix_iter_ge w k (collatzStep z) tail (by omega) hv_next j' (by omega)
      simp only [collatzIter]
      omega

theorem even_run_iter_ge_end : ∀ (a y : Nat),
    parityOfIter a y = List.replicate a false ->
    ∀ t : Nat, t ≤ a -> collatzIter a y ≤ collatzIter t y
  | 0, y, _, t, ht => by
    have ht0 : t = 0 := by omega
    subst ht0; simp [collatzIter]
  | a + 1, y, hv, t, ht => by
    rw [List.replicate_succ] at hv
    rcases parity_cons_false_imp_even a y _ hv with ⟨hy_ev, hv_next⟩
    have hstep_le : collatzStep y ≤ y := by
      rw [collatzStep_of_even_nat y hy_ev]; omega
    cases t with
    | zero =>
      have ih0 := even_run_iter_ge_end a (collatzStep y) hv_next 0 (Nat.zero_le _)
      simp only [collatzIter] at ih0 ⊢
      omega
    | succ t' =>
      simp only [collatzIter]
      exact even_run_iter_ge_end a (collatzStep y) hv_next t' (by omega)

theorem block_iter_ge_start_or_end (w a z : Nat) (hz : z > 0)
    (hv : parityOfIter (w + a) z = List.replicate w true ++ List.replicate a false)
    (j : Nat) (hj : j ≤ w + a) :
    z ≤ collatzIter j z ∨ collatzIter (w + a) z ≤ collatzIter j z := by
  by_cases hjw : j ≤ w
  · exact Or.inl (odd_prefix_iter_ge w a z (List.replicate a false) hz hv j hjw)
  · right
    have hsplit := parityOfIter_append_split w a z
    rw [hv] at hsplit
    have hlen : (List.replicate w true).length = (parityOfIter w z).length := by
      rw [List.length_replicate, parityOfIter_length]
    have hv_even : parityOfIter a (collatzIter w z) = List.replicate a false :=
      (list_append_inj_left_eq_len _ _ _ _ hlen hsplit).2.symm
    have hj_eq : j = w + (j - w) := by omega
    rw [collatzIter_add w a z, hj_eq, collatzIter_add w (j - w) z]
    exact even_run_iter_ge_end a (collatzIter w z) hv_even (j - w) (by omega)

theorem two_block_strict_min_extracts_primitive_witness
    (x0 w1 a1 w2 a2 : Nat)
    (hx0 : x0 > 2) (hw1 : w1 ≥ 1) (ha1 : a1 ≥ 1) (hw2 : w2 ≥ 1) (ha2 : a2 ≥ 1)
    (hv : parityOfIter (w1 + a1 + w2 + a2) x0 =
      List.replicate w1 true ++ List.replicate a1 false ++
      (List.replicate w2 true ++ List.replicate a2 false))
    (hcyc : collatzIter (w1 + a1 + w2 + a2) x0 = x0)
    (hlt_x1 : x0 < collatzIter (w1 + a1) x0) :
    ∃ q0 q1 : Nat,
      x0 = 2 ^ w1 * q0 - 1 ∧
      IsPrimitiveTwoBlockBroxWitness w1 a1 w2 a2 q0 q1 := by
  let K := w1 + a1 + w2 + a2
  let x1 := collatzIter (w1 + a1) x0
  have hK_pos : K > 0 := by dsimp [K]; omega
  -- Split `hv` into Block 1 (`x0 -> x1`) and Block 2 (`x1 -> x0`):
  have hK_split : K = (w1 + a1) + (w2 + a2) := by dsimp [K]; omega
  have happ := parityOfIter_append_split (w1 + a1) (w2 + a2) x0
  rw [← hK_split, hv] at happ
  have hlen1 : (List.replicate w1 true ++ List.replicate a1 false).length =
      (parityOfIter (w1 + a1) x0).length := by
    rw [parityOfIter_length, List.length_append, List.length_replicate, List.length_replicate]
  rcases list_append_inj_left_eq_len _ _ _ _ hlen1 happ with ⟨hv1_symm, hv2_symm⟩
  have hv1 : parityOfIter (w1 + a1) x0 = List.replicate w1 true ++ List.replicate a1 false :=
    hv1_symm.symm
  have hv2 : parityOfIter (w2 + a2) x1 = List.replicate w2 true ++ List.replicate a2 false :=
    hv2_symm.symm
  have hx1_to_x0 : collatzIter (w2 + a2) x1 = x0 := by
    dsimp [x1]; rw [← collatzIter_add (w1 + a1) (w2 + a2) x0, ← hK_split, hcyc]
  -- Prove `x0` is the global cycle minimum:
  have hmin_prefix : ∀ r : Nat, r < K -> x0 ≤ collatzIter r x0 := by
    intro r hr
    by_cases hr1 : r ≤ w1 + a1
    · rcases block_iter_ge_start_or_end w1 a1 x0 (by omega) hv1 r hr1 with h1 | h2
      · exact h1
      · change x1 ≤ collatzIter r x0 at h2; omega
    · have hr_eq : r = (w1 + a1) + (r - (w1 + a1)) := by omega
      rw [hr_eq, collatzIter_add (w1 + a1) (r - (w1 + a1)) x0]
      change x0 ≤ collatzIter (r - (w1 + a1)) x1
      rcases block_iter_ge_start_or_end w2 a2 x1 (by omega) hv2 (r - (w1 + a1)) (by omega) with h1 | h2
      · omega
      · rw [hx1_to_x0] at h2; exact h2
  have hmin : ∀ k : Nat, x0 ≤ collatzIter k x0 := by
    intro k
    have hdm : k = (k / K) * K + k % K := by
      have h := (Nat.div_add_mod k K).symm
      rw [Nat.mul_comm K (k / K)] at h; exact h
    rw [hdm, collatzIter_add ((k / K) * K) (k % K) x0,
        collatzIter_mul_period (k / K) K x0 hcyc]
    exact hmin_prefix (k % K) (Nat.mod_lt k hK_pos)
  -- Extract band `(21, 22)` and mod-96 class on `x0`:
  rcases nontrivial_cycle_min_mod48_and_band_21_22 x0 K (by omega) hK_pos hcyc (by omega) with
    ⟨x0', ⟨i', _, hi'_eq⟩, _, hmin', hm16', hx0'_n3, _, hW5, _, hband_lo, hband_hi, _⟩
  have hx0'_eq : x0' = x0 := by
    have h1 : x0 ≤ x0' := by rw [← hi'_eq]; exact hmin i'
    have h2 : x0' ≤ x0 := by
      have hm := hmin' (K - i')
      rw [← hi'_eq, ← collatzIter_add i' (K - i') x0,
          show i' + (K - i') = K by omega, hcyc, hi'_eq] at hm
      exact hm
    omega
  rw [hx0'_eq] at hm16' hx0'_n3 hW5 hband_lo hband_hi
  have hW_eq : parityWeight (parityOfIter K x0) = w1 + w2 := by
    dsimp [K]
    rw [hv, parityWeight_append, parityWeight_append, parityWeight_append,
        parityWeight_replicate_true_local, parityWeight_replicate_false,
        parityWeight_replicate_true_local, parityWeight_replicate_false]
    omega
  rw [hW_eq] at hW5 hband_lo hband_hi
  have hnoDesc : ∀ m : Nat, ¬ (0 < collatzIter m x0 ∧ collatzIter m x0 < x0) := by
    intro m ⟨_, hlt⟩; have hge := hmin m; omega
  have hne11 : x0 % 32 ≠ 11 := fun h11 =>
    dyadic_descent_exclusion x0 5 11 27 10 hnoDesc h11
      (by decide) (by decide) (by decide) (by decide) (by decide)
  have hne23 : x0 % 32 ≠ 23 := fun h23 =>
    dyadic_descent_exclusion x0 5 23 27 20 hnoDesc h23
      (by decide) (by decide) (by decide) (by decide) (by decide)
  have hm96 := mod32_mod3_to_mod96_8classes x0 hm16' hne11 hne23 hx0'_n3
  have hw1_ge2 : w1 ≥ 2 := by
    by_cases hw2_ok : w1 ≥ 2
    · exact hw2_ok
    · exfalso
      have hw1_1 : w1 = 1 := by omega
      subst hw1_1
      have ha1_pos : a1 = (a1 - 1) + 1 := by omega
      rw [ha1_pos, List.replicate_succ, show 1 + ((a1 - 1) + 1) = (a1 - 1) + 2 by omega] at hv1
      simp only [List.replicate, List.singleton_append] at hv1
      rcases parity_cons_true_imp_odd ((a1 - 1) + 1) x0 _ hv1 with ⟨hx0_odd, hv1_step⟩
      rcases parity_cons_false_imp_even (a1 - 1) (collatzStep x0) _ hv1_step with ⟨hstep_ev, _⟩
      rw [collatzStep_of_odd_nat x0 hx0_odd] at hstep_ev
      omega
  -- First-block dichotomy gives `2 ^ (w1 + a1) < 3 ^ w1`:
  have h1st : 2 ^ (w1 + a1) < 3 ^ w1 := by
    rcases cycle_min_first_block_dichotomy x0 K w1 a1
        (List.replicate w2 true ++ List.replicate a2 false) hK_pos hcyc hmin hv with
      hcyc1 | hlt_b
    · omega
    · exact hlt_b
  -- Extract `q0` from `extract_brox_q0_from_min_cycle`:
  have hgt : 3 ^ (w1 + w2) < 2 ^ K := by
    rw [show (21 : Nat) ^ (w1 + w2) = 7 ^ (w1 + w2) * 3 ^ (w1 + w2) from
        mul_pow_nat 7 3 (w1 + w2)] at hband_lo
    by_cases hlt : 3 ^ (w1 + w2) < 2 ^ K
    · exact hlt
    · have hm := Nat.mul_le_mul_left (7 ^ (w1 + w2)) (by omega : 2 ^ K ≤ 3 ^ (w1 + w2)); omega
  let rest := List.replicate (a1 - 1) false ++ (List.replicate w2 true ++ List.replicate a2 false)
  have hv_brox : parityOfIter K x0 = List.replicate w1 true ++ (false :: rest) := by
    dsimp [K, rest]
    rw [hv, List.append_assoc, ← List.cons_append, ← List.replicate_succ,
        show a1 - 1 + 1 = a1 by omega]
  have hwt_rest : parityWeight rest = w2 := by
    dsimp [rest]
    rw [parityWeight_append, parityWeight_replicate_false, Nat.zero_add,
        parityWeight_append, parityWeight_replicate_true_local, parityWeight_replicate_false,
        Nat.add_zero]
  rcases extract_brox_q0_from_min_cycle x0 K w1 rest hw1_ge2
      (by rw [hwt_rest]; exact hgt) hcyc hv_brox with
    ⟨q0, _, _, hx0_eq, hbrox0⟩
  rw [hwt_rest, twoBlockBroxCarry_eq_broxOddCarry w1 a1 w2 a2 ha1] at hbrox0
  -- Show any `q1` solving `D * q1 = H1` has `2 ^ w2 * q1 - 1 = x1`, hence `≥ x0 + 2` and `% 3 ≠ 0`:
  have hx1_odd : x1 % 2 = 1 := by
    have hw2_pos : w2 + a2 = (w2 - 1 + a2) + 1 := by omega
    rw [hw2_pos, show w2 = (w2 - 1) + 1 by omega, List.replicate_succ, List.cons_append] at hv2
    exact (parity_cons_true_imp_odd (w2 - 1 + a2) x1 _ hv2).1
  have hx1_cyc : collatzIter K x1 = x1 := by
    dsimp [x1]
    rw [← collatzIter_add (w1 + a1) K x0, Nat.add_comm (w1 + a1) K,
        collatzIter_add K (w1 + a1) x0, hcyc]
  have hx1_n3 : x1 % 3 ≠ 0 :=
    periodic_pos_nondiv3_universal x1 K (by omega) hK_pos hx1_cyc
  have hx0_odd : x0 % 2 = 1 := by omega
  have hx1_ge_x0p2 : x1 ≥ x0 + 2 := by omega
  have hx1_prop : ∀ q1 : Nat,
      (2 ^ K - 3 ^ (w1 + w2)) * q1 = twoBlockBroxCarry w2 a2 w1 a1 ->
      2 ^ w2 * q1 - 1 ≥ (2 ^ w1 * q0 - 1) + 2 ∧ (2 ^ w2 * q1 - 1) % 3 ≠ 0 := by
    intro q1_c hbrox1_c
    rcases two_block_reciprocal_and_cross_carry_identity w1 a1 w2 a2 q0
        (by omega) ha1 hw2 ha2 hgt hbrox0 with
      ⟨q1_true, hq0_pos, _, _, _, hbrox1_true, _, _, hsyr1_true, _, _⟩
    have hD_pos : 2 ^ K - 3 ^ (w1 + w2) > 0 := by omega
    have hq1_eq : q1_c = q1_true :=
      nat_mul_left_cancel_pos (2 ^ K - 3 ^ (w1 + w2)) q1_c q1_true hD_pos
        (by rw [hbrox1_c, hbrox1_true])
    subst hq1_eq
    have hx0_p1 : x0 + 1 = 2 ^ w1 * q0 := by
      have hp2w : 2 ^ w1 ≥ 4 := by simpa using pow2_mono_nat hw1_ge2
      have hm := Nat.mul_le_mul hp2w hq0_pos
      omega
    have hx1_iter := syracuse_block_iter x0 (2 ^ w2 * q1_c - 1) w1 a1 q0
      hq0_pos hx0_p1 hsyr1_true
    change x1 = 2 ^ w2 * q1_c - 1 at hx1_iter
    rw [← hx1_iter, ← hx0_eq]
    exact ⟨hx1_ge_x0p2, hx1_n3⟩
  rw [hx0_eq] at hm96
  rcases two_block_mersenne_elimination_and_cubic_squeeze w1 a1 w2 a2 q0
      hw1_ge2 ha1 hw2 ha2 hW5 (by dsimp [K] at hgt ⊢; omega)
      hband_lo hband_hi h1st hbrox0 hm96 hx1_prop with
    ⟨q1, hprim⟩
  exact ⟨q0, q1, hx0_eq, hprim⟩

/--
  Theorem T10c (`no_two_block_cycles_iff_one_block_and_primitive_brox`):
  `NoTwoBlockPositiveCycles` holds IF AND ONLY IF `NoOneBlockPositiveCycles` holds AND
  no `(w1, a1, w2, a2, q0, q1)` satisfies `IsPrimitiveTwoBlockBroxWitness`!
-/
theorem no_two_block_cycles_iff_one_block_and_primitive_brox :
    NoTwoBlockPositiveCycles ↔
      (NoOneBlockPositiveCycles ∧
       ∀ (w1 a1 w2 a2 q0 q1 : Nat), ¬ IsPrimitiveTwoBlockBroxWitness w1 a1 w2 a2 q0 q1) := by
  constructor
  · intro hno2
    refine ⟨?_, ?_⟩
    · intro x0 w1 a1 hx0 hw1 ha1 hv1 hcyc1
      have hcyc2 : collatzIter (w1 + a1 + w1 + a1) x0 = x0 := by
        rw [show w1 + a1 + w1 + a1 = (w1 + a1) + (w1 + a1) by omega,
            collatzIter_add, hcyc1, hcyc1]
      have hv2 : parityOfIter (w1 + a1 + w1 + a1) x0 =
          List.replicate w1 true ++ List.replicate a1 false ++
          (List.replicate w1 true ++ List.replicate a1 false) := by
        rw [show w1 + a1 + w1 + a1 = (w1 + a1) + (w1 + a1) by omega,
            parityOfIter_append_split, hcyc1, hv1]
      exact hno2 x0 w1 a1 w1 a1 hx0 hw1 ha1 hw1 ha1 hv2 hcyc2
    · intro w1 a1 w2 a2 q0 q1 hprim
      rcases hprim with
        ⟨hw1, ha1, hw2, ha2, hq0_ge3, hq1_ge3, _, _, _, _, hband_lo, _, _, _, _,
         _, hx0_47, _, _, _, hbrox0, hbrox1, _⟩
      have hgt : 3 ^ (w1 + w2) < 2 ^ (w1 + a1 + w2 + a2) := by
        rw [show (21 : Nat) ^ (w1 + w2) = 7 ^ (w1 + w2) * 3 ^ (w1 + w2) from
            mul_pow_nat 7 3 (w1 + w2)] at hband_lo
        by_cases hlt : 3 ^ (w1 + w2) < 2 ^ (w1 + a1 + w2 + a2)
        · exact hlt
        · have hm := Nat.mul_le_mul_left (7 ^ (w1 + w2))
            (by omega : 2 ^ (w1 + a1 + w2 + a2) ≤ 3 ^ (w1 + w2)); omega
      rcases two_block_reciprocal_and_cross_carry_identity w1 a1 w2 a2 q0
          (by omega) ha1 hw2 ha2 hgt hbrox0 with
        ⟨q1', _, _, _, _, hbrox1', _, _, hsyr1, hsyr2, _⟩
      have hD_pos : 2 ^ (w1 + a1 + w2 + a2) - 3 ^ (w1 + w2) > 0 := by omega
      have hq1_eq : q1' = q1 :=
        nat_mul_left_cancel_pos (2 ^ (w1 + a1 + w2 + a2) - 3 ^ (w1 + w2)) q1' q1 hD_pos
          (by rw [hbrox1', hbrox1])
      subst hq1_eq
      let x0 := 2 ^ w1 * q0 - 1
      let x1 := 2 ^ w2 * q1' - 1
      have hp2w1 : 2 ^ w1 ≥ 4 := by simpa using pow2_mono_nat hw1
      have hp2w2 : 2 ^ w2 ≥ 2 := by simpa using pow2_mono_nat hw2
      have hx0_p1 : x0 + 1 = 2 ^ w1 * q0 := by
        have hm := Nat.mul_le_mul hp2w1 (by omega : 1 ≤ q0); dsimp [x0]; omega
      have hx1_p1 : x1 + 1 = 2 ^ w2 * q1' := by
        have hm := Nat.mul_le_mul hp2w2 (by omega : 1 ≤ q1'); dsimp [x1]; omega
      rcases syracuse_block_iter_and_parity x0 x1 w1 a1 q0 (by omega) hx0_p1 hsyr1 with
        ⟨hiter1, hv1⟩
      rcases syracuse_block_iter_and_parity x1 x0 w2 a2 q1' (by omega) hx1_p1 hsyr2 with
        ⟨hiter2, hv2⟩
      have hcyc2 : collatzIter (w1 + a1 + w2 + a2) x0 = x0 := by
        rw [show w1 + a1 + w2 + a2 = (w1 + a1) + (w2 + a2) by omega,
            collatzIter_add, hiter1, hiter2]
      have hv_full : parityOfIter (w1 + a1 + w2 + a2) x0 =
          List.replicate w1 true ++ List.replicate a1 false ++
          (List.replicate w2 true ++ List.replicate a2 false) := by
        rw [show w1 + a1 + w2 + a2 = (w1 + a1) + (w2 + a2) by omega,
            parityOfIter_append_split, hiter1, hv1, hv2]
      exact hno2 x0 w1 a1 w2 a2 (by dsimp [x0]; omega) (by omega) ha1 hw2 ha2 hv_full hcyc2
  · rintro ⟨hno1, hnoprim⟩ x0 w1 a1 w2 a2 hx0 hw1 ha1 hw2 ha2 hv hcyc
    let x1 := collatzIter (w1 + a1) x0
    have hK_split : w1 + a1 + w2 + a2 = (w1 + a1) + (w2 + a2) := by omega
    have happ := parityOfIter_append_split (w1 + a1) (w2 + a2) x0
    rw [← hK_split, hv] at happ
    have hlen1 : (List.replicate w1 true ++ List.replicate a1 false).length =
        (parityOfIter (w1 + a1) x0).length := by
      rw [parityOfIter_length, List.length_append, List.length_replicate, List.length_replicate]
    rcases list_append_inj_left_eq_len _ _ _ _ hlen1 happ with ⟨hv1_s, hv2_s⟩
    have hv1 := hv1_s.symm
    have hv2 : parityOfIter (w2 + a2) x1 = List.replicate w2 true ++ List.replicate a2 false :=
      hv2_s.symm
    have hx1_to_x0 : collatzIter (w2 + a2) x1 = x0 := by
      dsimp [x1]; rw [← collatzIter_add, ← hK_split, hcyc]
    by_cases heq : x1 = x0
    · exact hno1 x0 w1 a1 hx0 hw1 ha1 hv1 heq
    · by_cases hlt : x0 < x1
      · rcases two_block_strict_min_extracts_primitive_witness x0 w1 a1 w2 a2
            hx0 hw1 ha1 hw2 ha2 hv hcyc hlt with
          ⟨q0, q1, _, hprim⟩
        exact hnoprim w1 a1 w2 a2 q0 q1 hprim
      · -- Rotate 1 block to `(x1, w2, a2, w1, a1)` where `x1 < x0 = collatzIter (w2 + a2) x1`:
        have hx1_pos : x1 > 0 := collatzIter_pos (w1 + a1) x0 (by omega)
        have hx1_gt2 : x1 > 2 := by
          by_cases hx1_le2 : x1 ≤ 2
          · exfalso
            have htriv := collatzIter_trivial_cycle (w2 + a2) x1 (by omega)
            rw [hx1_to_x0] at htriv; omega
          · omega
        have hcyc_rot : collatzIter (w2 + a2 + w1 + a1) x1 = x1 := by
          rw [show w2 + a2 + w1 + a1 = (w2 + a2) + (w1 + a1) by omega,
              collatzIter_add, hx1_to_x0]
        have hv_rot : parityOfIter (w2 + a2 + w1 + a1) x1 =
            List.replicate w2 true ++ List.replicate a2 false ++
            (List.replicate w1 true ++ List.replicate a1 false) := by
          rw [show w2 + a2 + w1 + a1 = (w2 + a2) + (w1 + a1) by omega,
              parityOfIter_append_split, hx1_to_x0, hv2, hv1]
        have hlt_rot : x1 < collatzIter (w2 + a2) x1 := by rw [hx1_to_x0]; omega
        rcases two_block_strict_min_extracts_primitive_witness x1 w2 a2 w1 a1
            hx1_gt2 hw2 ha2 hw1 ha1 hv_rot hcyc_rot hlt_rot with
          ⟨q1, q0, _, hprim⟩
        exact hnoprim w2 a2 w1 a1 q1 q0 hprim

/--
  Corollary T10c' (`subexponential_cubic_gap_eliminates_1_and_2_block_cycles`):
  The purely elementary polynomial-vs-exponential gap `SubexponentialCubicGapProp`
  (`∀ K W, W ≥ 6 -> 3 ^ W < 2 ^ K -> 27 * 2 ^ (W - 2) * (2 ^ K - 3 ^ W) ^ 3 ≥ 2 ^ (3 * K)`)
  unconditionally implies BOTH `NoOneBlockPositiveCycles` AND `NoTwoBlockPositiveCycles`!
-/
theorem subexponential_cubic_gap_eliminates_1_and_2_block_cycles
    (hgap : SubexponentialCubicGapProp) :
    NoOneBlockPositiveCycles ∧ NoTwoBlockPositiveCycles := by
  have hno1 : NoOneBlockPositiveCycles := by
    rw [no_one_block_cycles_iff_sharpened_gcd_mod24]
    intro w1 a1 q0 ⟨hw13, _, hq17, hgt, hbrox, _, _, _, _⟩
    let K := w1 + a1
    let D := 2 ^ K - 3 ^ w1
    change D * q0 = 2 ^ a1 - 1 at hbrox
    have h17D_lt : 17 * D < 2 ^ a1 := by
      have hm : 17 * D ≤ q0 * D := Nat.mul_le_mul_right D hq17
      rw [Nat.mul_comm q0 D, hbrox] at hm
      have hp2a : 2 ^ a1 ≥ 1 := pow2_pos_nat a1
      omega
    have hlin : 3 * 2 ^ (w1 - 1) * D < 2 ^ K := by
      have hm1 : 2 ^ w1 * (17 * D) < 2 ^ w1 * 2 ^ a1 :=
        Nat.mul_lt_mul_of_pos_left h17D_lt (pow2_pos_nat w1)
      rw [← Nat.pow_add 2 w1 a1] at hm1
      have h2w : 2 ^ w1 = 2 * 2 ^ (w1 - 1) := by
        conv => lhs; rw [show w1 = (w1 - 1) + 1 by omega]
        rw [Nat.pow_succ, Nat.mul_comm]
      have hm2 : 3 * 2 ^ (w1 - 1) * D ≤ 2 ^ w1 * (17 * D) := by
        rw [h2w]
        calc
          3 * 2 ^ (w1 - 1) * D ≤ 34 * 2 ^ (w1 - 1) * D :=
            Nat.mul_le_mul_right D (Nat.mul_le_mul_right _ (by decide))
          _ = (2 * 2 ^ (w1 - 1)) * (17 * D) := by
            rw [show (34 : Nat) = 2 * 17 from rfl, Nat.mul_assoc 2 17,
                Nat.mul_comm 17 (2 ^ (w1 - 1)), ← Nat.mul_assoc 2 (2 ^ (w1 - 1)),
                Nat.mul_assoc (2 * 2 ^ (w1 - 1)) 17 D]
      dsimp [K]; omega
    -- Cube `3 * 2 ^ (w1 - 1) * D < 2 ^ K`:
    let A := 3 * 2 ^ (w1 - 1) * D
    have hsq : A * A < 2 ^ K * 2 ^ K := by
      have hm1 : A * A ≤ A * 2 ^ K := Nat.mul_le_mul_left A (Nat.le_of_lt hlin)
      have hm2 : A * 2 ^ K < 2 ^ K * 2 ^ K := Nat.mul_lt_mul_of_pos_right hlin (pow2_pos_nat K)
      omega
    have hcube : (A * A) * A < (2 ^ K * 2 ^ K) * 2 ^ K := by
      have hm1 : (A * A) * A ≤ (A * A) * 2 ^ K :=
        Nat.mul_le_mul_left _ (Nat.le_of_lt hlin)
      have hm2 : (A * A) * 2 ^ K < (2 ^ K * 2 ^ K) * 2 ^ K :=
        Nat.mul_lt_mul_of_pos_right hsq (pow2_pos_nat K)
      omega
    have hrhs_eq : (2 ^ K * 2 ^ K) * 2 ^ K = 2 ^ (3 * K) := by
      rw [← Nat.pow_add 2 K K, ← Nat.pow_add 2 (K + K) K,
          show K + K + K = 3 * K by omega]
    have hge_gap := hgap K w1 (by omega) hgt
    change 27 * 2 ^ (w1 - 2) * D ^ 3 ≥ 2 ^ (3 * K) at hge_gap
    have hle_A3 : 27 * 2 ^ (w1 - 2) * D ^ 3 ≤ (A * A) * A := by
      dsimp [A]
      have hpow_le : 2 ^ (w1 - 2) ≤ 2 ^ (w1 - 1) * (2 ^ (w1 - 1) * 2 ^ (w1 - 1)) := by
        rw [← Nat.pow_add, ← Nat.pow_add]
        exact pow2_mono_nat (by omega)
      have hD3 : D ^ 3 = D * (D * D) := by
        rw [show (3 : Nat) = 2 + 1 from rfl, Nat.pow_succ, show (2 : Nat) = 1 + 1 from rfl,
            Nat.pow_succ, Nat.pow_one, Nat.mul_comm (D * D) D]
      rw [hD3]
      generalize 2 ^ (w1 - 1) = p, 2 ^ (w1 - 2) = q at hpow_le
      have heq_p : (3 * p * D * (3 * p * D)) * (3 * p * D) =
          27 * (p * (p * p)) * (D * (D * D)) := by
        have hc1 : (3 * p * D) * (3 * p * D) = 9 * (p * p) * (D * D) := by
          calc
            (3 * p * D) * (3 * p * D) = ((3 * p) * (3 * p)) * (D * D) := by
              rw [Nat.mul_assoc (3 * p) D, ← Nat.mul_assoc D (3 * p) D,
                  Nat.mul_comm D (3 * p), Nat.mul_assoc (3 * p) D D,
                  ← Nat.mul_assoc (3 * p) (3 * p)]
            _ = 9 * (p * p) * (D * D) := by
              have h9 : (3 * p) * (3 * p) = 9 * (p * p) := by
                rw [Nat.mul_assoc 3 p, ← Nat.mul_assoc p 3 p, Nat.mul_comm p 3,
                    Nat.mul_assoc 3 p p, ← Nat.mul_assoc 3 3]
              rw [h9]
        rw [hc1]
        calc
          (9 * (p * p) * (D * D)) * (3 * p * D)
              = ((9 * (p * p)) * (3 * p)) * ((D * D) * D) := by
                rw [Nat.mul_assoc (9 * (p * p)) (D * D),
                    ← Nat.mul_assoc (D * D) (3 * p) D,
                    Nat.mul_comm (D * D) (3 * p),
                    Nat.mul_assoc (3 * p) (D * D) D,
                    ← Nat.mul_assoc (9 * (p * p)) (3 * p)]
          _ = 27 * (p * (p * p)) * (D * (D * D)) := by
                have h27 : (9 * (p * p)) * (3 * p) = 27 * (p * (p * p)) := by
                  rw [Nat.mul_assoc 9 (p * p), ← Nat.mul_assoc (p * p) 3 p,
                      Nat.mul_comm (p * p) 3, Nat.mul_assoc 3 (p * p) p,
                      ← Nat.mul_assoc 9 3, Nat.mul_assoc p p p]
                rw [h27, Nat.mul_assoc D D D]
      rw [heq_p]
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 27 hpow_le)
    omega
  refine ⟨hno1, no_two_block_cycles_iff_one_block_and_primitive_brox.mpr ⟨hno1, ?_⟩⟩
  intro w1 a1 w2 a2 q0 q1 hprim
  rcases hprim with
    ⟨_, ha1, _, _, _, _, _, _, hW8, _, hband_lo, _, _, _, _, _, _, _, _, _, _, _, hcubic⟩
  have hgt : 3 ^ (w1 + w2) < 2 ^ (w1 + a1 + w2 + a2) := by
    rw [show (21 : Nat) ^ (w1 + w2) = 7 ^ (w1 + w2) * 3 ^ (w1 + w2) from
        mul_pow_nat 7 3 (w1 + w2)] at hband_lo
    by_cases hlt : 3 ^ (w1 + w2) < 2 ^ (w1 + a1 + w2 + a2)
    · exact hlt
    · have hm := Nat.mul_le_mul_left (7 ^ (w1 + w2))
        (by omega : 2 ^ (w1 + a1 + w2 + a2) ≤ 3 ^ (w1 + w2)); omega
  have hge_gap := hgap (w1 + a1 + w2 + a2) (w1 + w2) (by omega) hgt
  have hpow_le : 2 ^ (w1 + w2 - 2) ≤ 2 ^ (w1 + w2 + a1 - 3) := pow2_mono_nat (by omega)
  have hm_le :
      27 * 2 ^ (w1 + w2 - 2) * (2 ^ (w1 + a1 + w2 + a2) - 3 ^ (w1 + w2)) ^ 3 ≤
      27 * 2 ^ (w1 + w2 + a1 - 3) * (2 ^ (w1 + a1 + w2 + a2) - 3 ^ (w1 + w2)) ^ 3 :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 27 hpow_le)
  omega

-- ----------------------------------------------------------------------------
-- T11a & T11b: Hercher Sub-Double Merger Separation of 1-Block Cycles from `n_min`
--              & Unified Wave 3 Master Two-Barrier / Mod-373248 Equivalences
-- ----------------------------------------------------------------------------

/--
  Theorem T11a (`one_block_cycle_has_smaller_nonconvergent_partner`):
  Every positive 1-block cycle `x0 > 2` (`1^w1 ++ 0^a1`) has `nPrime := (x0 - 1) / 2`
  strictly smaller (`1 ≤ nPrime < x0`) merging into `x0` at step `w1 + a1 - 1` and
  NEVER reaching `1` — proving no minimal non-convergent counterexample `n_min` can ever
  lie on a 1-block cycle (strictly separating `(Z^+, 3x + 1)` from `M3 = (Z^+, 5x + 1)` at `13`)!
-/
theorem one_block_cycle_has_smaller_nonconvergent_partner (x0 w1 a1 : Nat)
    (hx0 : x0 > 2) (hw1 : w1 ≥ 1) (ha1 : a1 ≥ 1)
    (hv : parityOfIter (w1 + a1) x0 = List.replicate w1 true ++ List.replicate a1 false)
    (hcyc : collatzIter (w1 + a1) x0 = x0) :
    let nPrime := (x0 - 1) / 2
    1 ≤ nPrime ∧ nPrime < x0 ∧
    collatzIter (w1 + a1 - 1) nPrime = x0 ∧
    (∀ k : Nat, collatzIter k nPrime ≠ 1) := by
  dsimp only
  rcases extract_one_block_cycle_q0 x0 w1 a1 hx0 hw1 ha1 hv hcyc with
    ⟨q0, hw13, ha8, hq17, _, hgt, hx0_eq, hbrox⟩
  rcases one_block_gcd_and_congruence_lock w1 a1 q0 (by omega) (by omega) hgt hbrox with
    ⟨_, _, _, hsyr_eq, _, _, _⟩
  have hp2w : 2 ^ w1 ≥ 8192 := by simpa using pow2_mono_nat hw13
  have hx0_p1 : x0 + 1 = 2 ^ w1 * q0 := by
    have hm := Nat.mul_le_mul hp2w hq17; omega
  rw [← hx0_eq] at hsyr_eq
  have hmerge := subdouble_entry_block_merger x0 x0 w1 a1 q0
    (by omega) (by omega) (by omega) hx0_p1 hsyr_eq
  dsimp only at hmerge
  rw [show (w1 - 1) + (a1 - 2) + 2 = w1 + a1 - 1 by omega] at hmerge
  refine ⟨by omega, by omega, hmerge, ?_⟩
  intro k hk1
  by_cases hle : k ≤ w1 + a1 - 1
  · have hsplit : w1 + a1 - 1 = k + (w1 + a1 - 1 - k) := by omega
    rw [hsplit, collatzIter_add, hk1] at hmerge
    have htriv := collatzIter_trivial_cycle (w1 + a1 - 1 - k) 1 (Or.inl rfl)
    rw [hmerge] at htriv; omega
  · let t := k - (w1 + a1 - 1)
    have hk_eq : k = (w1 + a1 - 1) + t := by dsimp [t]; omega
    rw [hk_eq, collatzIter_add, hmerge] at hk1
    have hper := collatzIter_mul_period (t + 1) (w1 + a1) x0 hcyc
    have hgt_t : (t + 1) * (w1 + a1) ≥ t := by
      have hm := Nat.mul_le_mul_left (t + 1) (by omega : 1 ≤ w1 + a1)
      omega
    have hp_split : (t + 1) * (w1 + a1) = t + ((t + 1) * (w1 + a1) - t) := by omega
    rw [hp_split, collatzIter_add, hk1] at hper
    have htriv := collatzIter_trivial_cycle ((t + 1) * (w1 + a1) - t) 1 (Or.inl rfl)
    rw [hper] at htriv; omega

theorem parityWeight_zero_eq_replicate_false : ∀ u : List Bool,
    parityWeight u = 0 -> u = List.replicate u.length false
  | [], _ => rfl
  | true :: _, hw => by simp [parityWeight] at hw
  | false :: rest, hw => by
    simp only [parityWeight, List.length_cons, List.replicate_succ] at hw ⊢
    rw [← parityWeight_zero_eq_replicate_false rest (by omega)]

theorem leadingFalseCount_replicate_false_append_true : ∀ (b w2 : Nat) (tail : List Bool),
    w2 ≥ 1 ->
    leadingFalseCount (List.replicate b false ++ (List.replicate w2 true ++ tail)) = b
  | 0, w2, tail, hw2 => by
    rw [List.replicate_zero, List.nil_append,
        show w2 = (w2 - 1) + 1 by omega, List.replicate_succ, List.cons_append]
    rfl
  | b + 1, w2, tail, hw2 => by
    rw [List.replicate_succ, List.cons_append]
    simp only [leadingFalseCount]
    rw [leadingFalseCount_replicate_false_append_true b w2 tail hw2]
    omega

/--
  Theorem T11b (`no_nontrivial_cycles_iff_wave3_sharpened_brox_obstruction`):
  Upgraded Master Cycle Equivalence (`↔`): `NoNontrivialPositiveCycles` holds IF AND ONLY IF
  no `(w1, init, q0)` satisfies `IsWave3SharpenedBroxWitness w1 init q0` (enforcing BOTH
  the `T9` `q0 ≥ 17`, GCD & mod-24/mod-96 lock on `w_init = 0` AND the full `T10b`
  `IsPrimitiveTwoBlockBroxWitness` cubic squeeze on all 2-block words)!
-/
theorem no_nontrivial_cycles_iff_wave3_sharpened_brox_obstruction :
    NoNontrivialPositiveCycles ↔
      ∀ (w1 : Nat) (init : List Bool) (q0 : Nat), ¬ IsWave3SharpenedBroxWitness w1 init q0 := by
  constructor
  · intro hnocyc w1 init q0 hwit3
    exact (no_nontrivial_cycles_iff_sharpened_brox_obstruction.mp hnocyc) w1 init q0 hwit3.1
  · intro hnowit3 x p hx hp hcyc
    by_cases htriv : x = 1 ∨ x = 2
    · exact htriv
    · exfalso
      -- Start from a minimal-period or global-minimum cycle witness just as in `T8`:
      rcases nontrivial_cycle_min_mod48_and_band_21_22 x p hx hp hcyc htriv with
        ⟨x0, _, hx0_cyc, hmin, hm16, hx0_n3, _, hW5, hp8, hband_lo, hband_hi, hup_x0⟩
      have hnoDesc : ∀ m : Nat, ¬ (0 < collatzIter m x0 ∧ collatzIter m x0 < x0) := by
        intro m ⟨_, hlt⟩; have hge := hmin m; omega
      have hne11 : x0 % 32 ≠ 11 := fun h11 =>
        dyadic_descent_exclusion x0 5 11 27 10 hnoDesc h11
          (by decide) (by decide) (by decide) (by decide) (by decide)
      have hne23 : x0 % 32 ≠ 23 := fun h23 =>
        dyadic_descent_exclusion x0 5 23 27 20 hnoDesc h23
          (by decide) (by decide) (by decide) (by decide) (by decide)
      have hm96 := mod32_mod3_to_mod96_8classes x0 hm16 hne11 hne23 hx0_n3
      have hx0_ge7 : x0 ≥ 7 := by omega
      let v := parityOfIter p x0
      let W := parityWeight v
      have hv_len : v.length = p := parityOfIter_length p x0
      have h3W_lt_2p : 3 ^ W < 2 ^ p := by
        change 21 ^ W < 7 ^ W * 2 ^ p at hband_lo
        rw [show (21 : Nat) ^ W = 7 ^ W * 3 ^ W from mul_pow_nat 7 3 W] at hband_lo
        by_cases hlt : 3 ^ W < 2 ^ p
        · exact hlt
        · have hm := Nat.mul_le_mul_left (7 ^ W) (by omega : 2 ^ p ≤ 3 ^ W); omega
      have hsplit_v : ∃ (w1 : Nat) (rest : List Bool),
          v = List.replicate w1 true ++ (false :: rest) := by
        rcases split_at_first_false v with hall | hex
        · have hp23 := pow2_le_pow3 p
          change W = v.length at hall
          rw [hv_len] at hall; rw [hall] at h3W_lt_2p; omega
        · exact hex
      rcases hsplit_v with ⟨w1, rest, hv_eq⟩
      have hv_two_true : ∃ tail2 : List Bool, v = true :: true :: tail2 := by
        have hp_split : p = (p - 2) + 2 := by omega
        dsimp [v]
        rw [hp_split, show (p - 2) + 2 = ((p - 2) + 1) + 1 by omega]
        simp only [parityOfIter]
        have ho0 : (x0 % 2 == 0) = false := decide_eq_false (by omega)
        have hs0 : collatzStep x0 = (3 * x0 + 1) / 2 := by simp [collatzStep, ho0]
        have ho1 : (collatzStep x0 % 2 == 0) = false := by
          rw [hs0]; exact decide_eq_false (by omega)
        rw [ho0, ho1]
        exact ⟨parityOfIter (p - 2) (collatzStep (collatzStep x0)), rfl⟩
      rcases hv_two_true with ⟨tail2, hv_tt⟩
      have hw1_ge2 : w1 ≥ 2 := by
        cases w1 with
        | zero => rw [hv_eq] at hv_tt; simp at hv_tt
        | succ w1' =>
          cases w1' with
          | zero => rw [hv_eq] at hv_tt; simp at hv_tt
          | succ _ => omega
      rcases split_leading_false (false :: rest) with ⟨tail, hlead_eq, htail_cases⟩
      let a1 := leadingFalseCount (false :: rest)
      have ha1_ge1 : a1 ≥ 1 := by simp [a1, leadingFalseCount]
      have hv_block : v = List.replicate w1 true ++ List.replicate a1 false ++ tail := by
        rw [hv_eq, hlead_eq, List.append_assoc]
      rcases cycle_min_first_block_dichotomy x0 p w1 a1 tail hp hx0_cyc hmin hv_block with
        hcyc1 | hlt_block
      · -- Case A: 1-block cycle at `p1 := w1 + a1`:
        let p1 := w1 + a1
        have hp1_pos : p1 > 0 := by dsimp [p1]; omega
        have hp_split : p = p1 + tail.length := by
          rw [← hv_len, hv_block, List.length_append, List.length_append,
              List.length_replicate, List.length_replicate]
        have hv1_eq : parityOfIter p1 x0 = List.replicate w1 true ++ List.replicate a1 false := by
          have happ := parityOfIter_append_split p1 tail.length x0
          rw [← hp_split] at happ
          change v = parityOfIter p1 x0 ++ parityOfIter tail.length (collatzIter p1 x0) at happ
          rw [hv_block] at happ
          have hlen1 : (List.replicate w1 true ++ List.replicate a1 false).length =
              (parityOfIter p1 x0).length := by
            rw [parityOfIter_length, List.length_append, List.length_replicate, List.length_replicate]
          exact (list_append_inj_left_eq_len _ _ _ _ hlen1 happ).1.symm
        rcases nontrivial_cycle_min_mod48_and_band_21_22 x0 p1 (by omega) hp1_pos hcyc1 (by omega) with
          ⟨x0', ⟨i', _, hi'_eq⟩, _, hmin', _, _, _, hW1_5, hp1_8, hband1_lo, hband1_hi, hup1⟩
        have hx0'_eq : x0' = x0 := by
          have h1 : x0 ≤ x0' := by rw [← hi'_eq]; exact hmin i'
          have h2 : x0' ≤ x0 := by
            have hm := hmin' (p1 - i')
            rw [← hi'_eq, ← collatzIter_add i' (p1 - i') x0,
                show i' + (p1 - i') = p1 by omega, hcyc1, hi'_eq] at hm
            exact hm
          omega
        rw [hx0'_eq] at hW1_5 hband1_lo hband1_hi hup1
        have hW1_eq : parityWeight (parityOfIter p1 x0) = w1 := by
          rw [hv1_eq, parityWeight_append, parityWeight_replicate_true_local,
              parityWeight_replicate_false, Nat.add_zero]
        rw [hW1_eq] at hW1_5 hband1_lo hband1_hi hup1
        rcases extract_one_block_cycle_q0 x0 w1 a1 (by omega) (by omega) ha1_ge1 hv1_eq hcyc1 with
          ⟨q0, hw13, ha8, hq17, hq0_odd, h3w1_lt_2p1, hx0_q0, hbrox_a1⟩
        rcases one_block_gcd_and_congruence_lock w1 a1 q0 hw1_ge2 ha1_ge1 h3w1_lt_2p1 hbrox_a1 with
          ⟨_, _, _, _, hdvd_gcd, _, _⟩
        rcases one_block_no_pow3_quotient_and_q0_ge_17 w1 a1 q0 hw1_ge2 ha1_ge1 h3w1_lt_2p1 hbrox_a1 with
          ⟨_, _, _, hq24, _, _, hx96_2, hdiv17⟩
        let init := List.replicate (a1 - 2) false
        have hp1_K : p1 = w1 + 2 + init.length := by
          dsimp [p1, init]; rw [List.length_replicate]; omega
        have ha1_init : a1 = init.length + 2 := by
          dsimp [init]; rw [List.length_replicate]; omega
        have hwt_init : parityWeight init = 0 := parityWeight_replicate_false _
        rcases pow2_sub_pow3_mod24_in_4_classes p1 w1 (by omega) (by omega) h3w1_lt_2p1 with
          ⟨hD24, hD5⟩
        have hbrox_init : (2 ^ p1 - 3 ^ w1) * q0 = broxOddCarry init + 2 ^ (init.length + 1) := by
          rw [← broxOddCarry_append_false init]
          have hrep : init ++ [false] = List.replicate (a1 - 1) false := by
            dsimp [init]
            rw [← replicate_succ_append_local false (a1 - 2), show a1 - 2 + 1 = a1 - 1 by omega]
          rw [hrep, broxOddCarry_replicate_false (a1 - 1), show a1 - 1 + 1 = a1 by omega]
          exact hbrox_a1
        have hdiv_sq : (3 ^ w1) / (2 ^ (init.length + 2)) = 2 ^ w1 - 1 := by
          have hc_eq : p1 = w1 + 1 + (a1 - 1) := by dsimp [p1]; omega
          have hbrox_c : (2 ^ (w1 + 1 + (a1 - 1)) - 3 ^ w1) * q0 =
              broxOddCarry (List.replicate (a1 - 1) false) := by
            rw [← hc_eq, broxOddCarry_replicate_false (a1 - 1), show a1 - 1 + 1 = a1 by omega]
            exact hbrox_a1
          rcases one_block_cycle_binary_squeeze_and_q0_ge_three w1 (a1 - 1) q0
              hw1_ge2 (by omega) hq0_odd (by rw [← hc_eq]; exact h3w1_lt_2p1) hbrox_c with
            ⟨_, hsq, _, _, _⟩
          rw [show a1 - 1 + 1 = init.length + 2 by omega] at hsq
          exact hsq
        have hwit_base : IsSharpenedBroxCycleWitness w1 init q0 := by
          unfold IsSharpenedBroxCycleWitness
          dsimp only
          rw [← hp1_K, hwt_init, Nat.add_zero, ← hx0_q0]
          exact ⟨hw1_ge2, by omega, hq0_odd, hm96, hW1_5, hp1_8, hband1_lo, hband1_hi, hup1,
            hD24, hD5, hbrox_init, Or.inl ⟨rfl, by omega, hdiv_sq⟩⟩
        have hwit3 : IsWave3SharpenedBroxWitness w1 init q0 := by
          refine ⟨hwit_base, ?_, ?_⟩
          · intro _
            dsimp only
            rw [← ha1_init, ← hp1_K, hwt_init, Nat.add_zero]
            exact ⟨hw13, ha8, hq17, hq24, hx96_2, hdvd_gcd, hdiv17⟩
          · intro b_a1 w2 a2 _ hw2 _ h2blk
            exfalso
            have hwt_lhs : parityWeight (false :: (init ++ [false])) = 0 := by
              simp [parityWeight, parityWeight_append_false, hwt_init]
            rw [h2blk, parityWeight_append, parityWeight_replicate_false, Nat.zero_add,
                parityWeight_append, parityWeight_replicate_true_local,
                parityWeight_replicate_false, Nat.add_zero] at hwt_lhs
            omega
        exact hnowit3 w1 init q0 hwit3
      · -- Case B: Multi-block cycle (`collatzIter (w1 + a1) x0 ≠ x0` and `2 ^ (w1 + a1) < 3 ^ w1`):
        have htail_true : tail.head? = some true := by
          rcases htail_cases with hnil | htr
          · subst hnil
            rw [List.append_nil] at hv_block
            have hp_eq : p = w1 + a1 := by
              rw [← hv_len, hv_block, List.length_append,
                  List.length_replicate, List.length_replicate]
            have hW_w1 : W = w1 := by
              dsimp [W]
              rw [hv_block, parityWeight_append, parityWeight_replicate_true_local,
                  parityWeight_replicate_false, Nat.add_zero]
            rw [hp_eq, hW_w1] at h3W_lt_2p
            omega
          · exact htr
        let y := collatzIter (p - 1) x0
        have hy_ge : y ≥ x0 := hmin (p - 1)
        have hy_step : collatzStep y = x0 := by
          have hs : collatzIter p x0 = collatzStep (collatzIter (p - 1) x0) := by
            conv => lhs; rw [show p = (p - 1) + 1 by omega]
            exact collatzIter_add (p - 1) 1 x0
          dsimp [y]; rw [← hs, hx0_cyc]
        have hy_ev : y % 2 = 0 := by
          by_cases hev : y % 2 = 0
          · exact hev
          · rw [collatzStep_of_odd_nat y (by omega)] at hy_step; omega
        have hv_last_false : v = parityOfIter (p - 1) x0 ++ [false] := by
          dsimp [v]
          conv => lhs; rw [show p = (p - 1) + 1 by omega]
          rw [parityOfIter_append_split (p - 1) 1 x0]
          dsimp [y] at hy_ev
          have hb : (collatzIter (p - 1) x0 % 2 == 0) = true := decide_eq_true hy_ev
          simp [parityOfIter, hb]
        have hrest_nonempty : rest ≠ [] := by
          intro hnil; subst hnil
          simp [leadingFalseCount] at hlead_eq; subst hlead_eq; simp at htail_true
        have hv_rev_f : v.reverse.head? = some false := by
          rw [hv_last_false, List.reverse_append]; rfl
        have hrest_rev_f : rest.reverse.head? = some false := by
          rw [hv_eq, List.reverse_append, List.reverse_cons] at hv_rev_f
          cases hr : rest.reverse with
          | nil =>
            have h0 := congrArg List.reverse hr
            simp at h0; exact False.elim (hrest_nonempty h0)
          | cons lastBit revInit =>
            rw [hr] at hv_rev_f; simp at hv_rev_f; exact congrArg some hv_rev_f
        obtain ⟨init, hrest_init⟩ : ∃ init : List Bool, rest = init ++ [false] := by
          cases hr : rest.reverse with
          | nil => simp [hr] at hrest_rev_f
          | cons lastBit revInit =>
            rw [hr] at hrest_rev_f; simp at hrest_rev_f; subst hrest_rev_f
            refine ⟨revInit.reverse, ?_⟩
            have h0 := congrArg List.reverse hr; simpa using h0
        have hp_K : p = w1 + 2 + init.length := by
          rw [← hv_len, hv_eq, hrest_init, List.length_append, List.length_replicate,
              List.length_cons, List.length_append]; simp; omega
        have hW_init : W = w1 + parityWeight init := by
          dsimp [W]
          rw [hv_eq, hrest_init, parityWeight_append, parityWeight_replicate_true_local]
          simp [parityWeight, parityWeight_append_false]
        have hwt_init_pos : parityWeight init ≥ 1 := by
          have hw_f : parityWeight (false :: rest) = parityWeight init := by
            rw [hrest_init]; simp [parityWeight, parityWeight_append_false]
          rw [hlead_eq, parityWeight_append, parityWeight_replicate_false, Nat.zero_add] at hw_f
          cases tail with
          | nil => simp at htail_true
          | cons b t =>
            simp at htail_true; subst htail_true; simp [parityWeight] at hw_f; omega
        rcases extract_brox_q0_from_min_cycle x0 p w1 rest hw1_ge2
            (by rw [hrest_init, parityWeight_append_false, ← hW_init]; exact h3W_lt_2p)
            hx0_cyc hv_eq with
          ⟨q0, hq0_ge1, hq0_odd, hx0_q0, hbrox_r⟩
        rw [hrest_init, parityWeight_append_false, ← hW_init, broxOddCarry_append_false] at hbrox_r
        rcases pow2_sub_pow3_mod24_in_4_classes p W (by omega) (by omega) h3W_lt_2p with
          ⟨hD24, hD5⟩
        have ha1_init_eq : leadingFalseCount (false :: (init ++ [false])) = a1 := by
          dsimp [a1]; rw [hrest_init]
        have hwit_base : IsSharpenedBroxCycleWitness w1 init q0 := by
          unfold IsSharpenedBroxCycleWitness
          dsimp only
          rw [← hp_K, ← hW_init, ← hx0_q0, ha1_init_eq]
          exact ⟨hw1_ge2, hq0_ge1, hq0_odd, hm96, hW5, hp8, hband_lo, hband_hi, hup_x0,
            hD24, hD5, hbrox_r, Or.inr ⟨hwt_init_pos, hlt_block⟩⟩
        have hwit3 : IsWave3SharpenedBroxWitness w1 init q0 := by
          refine ⟨hwit_base, ?_, ?_⟩
          · intro hw0; omega
          · intro b_a1 w2 a2 hb_a1 hw2 ha2 h2blk
            have hb_eq_a1 : b_a1 = a1 := by
              have hlfc := congrArg leadingFalseCount h2blk
              rw [ha1_init_eq, leadingFalseCount_replicate_false_append_true b_a1 w2
                  (List.replicate a2 false) hw2] at hlfc
              exact hlfc.symm
            have hp_2blk : p = w1 + b_a1 + w2 + a2 := by
              have hlen_f := congrArg List.length h2blk
              simp only [List.length_cons, List.length_nil, List.length_append,
                         List.length_replicate] at hlen_f
              omega
            have hv_2blk : parityOfIter (w1 + b_a1 + w2 + a2) x0 =
                List.replicate w1 true ++ List.replicate b_a1 false ++
                (List.replicate w2 true ++ List.replicate a2 false) := by
              rw [← hp_2blk]
              change v = _
              rw [hv_eq, hrest_init, h2blk, ← List.append_assoc]
            have hcyc_2blk : collatzIter (w1 + b_a1 + w2 + a2) x0 = x0 := by
              rwa [← hp_2blk]
            have hlt_x1 : x0 < collatzIter (w1 + b_a1) x0 := by
              have hge := hmin (w1 + b_a1)
              by_cases heq1 : collatzIter (w1 + b_a1) x0 = x0
              · exfalso
                have happ1 := parityOfIter_append_split (w1 + b_a1) (w2 + a2) x0
                rw [show (w1 + b_a1) + (w2 + a2) = w1 + b_a1 + w2 + a2 by omega, hv_2blk] at happ1
                have hlen1 : (List.replicate w1 true ++ List.replicate b_a1 false).length =
                    (parityOfIter (w1 + b_a1) x0).length := by
                  rw [parityOfIter_length, List.length_append, List.length_replicate,
                      List.length_replicate]
                have hv1_sub := (list_append_inj_left_eq_len _ _ _ _ hlen1 happ1).1.symm
                rcases extract_one_block_cycle_q0 x0 w1 b_a1 (by omega) (by omega) hb_a1
                    hv1_sub heq1 with ⟨_, _, _, _, _, hgt1, _, _⟩
                rw [hb_eq_a1] at hgt1; omega
              · omega
            rcases two_block_strict_min_extracts_primitive_witness x0 w1 b_a1 w2 a2
                (by omega) (by omega) hb_a1 hw2 ha2 hv_2blk hcyc_2blk hlt_x1 with
              ⟨q0', q1, hx0_q0', hprim⟩
            have hp2w : 2 ^ w1 ≥ 4 := by simpa using pow2_mono_nat hw1_ge2
            have hq0'_eq : q0' = q0 := by
              have hm1 : 2 ^ w1 * q0 ≥ 4 := by simpa using Nat.mul_le_mul hp2w hq0_ge1
              have hq0'_pos : q0' ≥ 1 := by rcases hprim with ⟨_, _, _, _, _, _, _, _, _⟩; omega
              have hm2 : 2 ^ w1 * q0' ≥ 4 := by simpa using Nat.mul_le_mul hp2w hq0'_pos
              have heq_mul : 2 ^ w1 * q0' = 2 ^ w1 * q0 := by omega
              exact nat_mul_left_cancel_pos (2 ^ w1) q0' q0 (pow2_pos_nat w1) heq_mul
            subst hq0'_eq
            exact ⟨q1, hprim⟩
        exact hnowit3 w1 init q0 hwit3

/--
  Theorem T11b' (`unified_wave3_master_collatz_equivalences`):
  Master Campaign Synthesis Theorem chaining the Wave 3 Two-Barrier Decomposition
  (`NoDivergentPositiveOrbits ∧ ¬ IsWave3SharpenedBroxWitness`), `Mod373248` Horizon-
  Supercritical Contraction (`T3.11b`), and Forward-Iteration-Free Unique First-Hit
  Generator Range (`T3.16b`) directly to `CollatzConjectureStandard`!
-/
theorem unified_wave3_master_collatz_equivalences :
    (CollatzConjectureStandard ↔
      (NoDivergentPositiveOrbits ∧
       ∀ (w1 : Nat) (init : List Bool) (q0 : Nat), ¬ IsWave3SharpenedBroxWitness w1 init q0)) ∧
    (CollatzConjectureStandard ↔ Mod373248HorizonSupercriticalContractionProp) ∧
    (CollatzConjectureStandard ↔ Mod373248UniqueFirstHitRangeProp) := by
  refine ⟨?_, collatz_standard_iff_mod373248_horizon_supercritical_contraction,
          collatz_standard_iff_mod373248_unique_first_hit_range⟩
  rw [collatz_iff_two_barriers, no_nontrivial_cycles_iff_wave3_sharpened_brox_obstruction]

end CollatzFormal
