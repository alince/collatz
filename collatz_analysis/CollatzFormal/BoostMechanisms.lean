/-
  CollatzFormal/BoostMechanisms.lean
  Sections 14-21: Multi-Block Minimal-Counterexample Rigidity, Unbounded Syracuse
  Predecessor Tree & Disjoint Forest, General (a, b)-Affine & Multi-Return Backward
  Mergers, Higher 2^a * 3^b Sieve, Character Discrepancy, & 2-Vertex Hensel Splits.
-/

import CollatzFormal.Core

namespace CollatzFormal

-- ============================================================================
-- SECTION 14: Multi-Block Minimal-Counterexample Rigidity & Coalescence Coupling
-- ============================================================================

/--
  Theorem 27.1a (Universal Sub-Double Entry Merger Along Any Multi-Block Orbit Step):
  If at compressed step `K`, `x = collatzIter K nMin` has `x + 1 = 2^w * u` (`w >= 2, u >= 1`),
  `x <= 2 * nMin`, and even-run `a >= 2` (`(3^w * u - 1) % 4 = 0`), then `nPrime = (x - 1) / 2`
  satisfies `1 <= nPrime < nMin` and merges identically:
    `collatzIter (w + 1) ((x - 1) / 2) = collatzIter (K + w + 2) nMin`.
-/
theorem subdouble_entry_merger_step (nMin K x w u : Nat)
    (hw : w ≥ 2) (hu : u ≥ 1)
    (hx_iter : collatzIter K nMin = x)
    (hx_sub2 : x ≤ 2 * nMin)
    (hx_form : x + 1 = 2 ^ w * u)
    (ha_ge2 : (3 ^ w * u - 1) % 4 = 0) :
    1 ≤ (x - 1) / 2 ∧ (x - 1) / 2 < nMin ∧
    collatzIter (w + 1) ((x - 1) / 2) = collatzIter (K + (w + 2)) nMin := by
  have hp2w2 : 2 ^ (w - 2) ≥ 1 := pow2_pos_nat (w - 2)
  have hp2w1 : 2 ^ (w - 1) ≥ 2 := by
    rw [show w - 1 = (w - 2) + 1 by omega, Nat.pow_succ]; omega
  have hXw1 : 2 ^ (w - 1) * u ≥ 2 := Nat.mul_le_mul hp2w1 hu
  have hXw : 2 ^ w * u = 2 * (2 ^ (w - 1) * u) := by
    rw [show w = (w - 1) + 1 by omega, Nat.pow_succ]
    calc
      2 ^ (w - 1) * 2 * u = 2 * 2 ^ (w - 1) * u := by rw [Nat.mul_comm _ 2]
      _ = 2 * (2 ^ (w - 1) * u) := by rw [Nat.mul_assoc]
  -- Note x is odd (x = 2 * 2^(w-1) * u - 1 >= 3), while 2 * nMin is even, so x <= 2 * nMin - 1!
  have hx_eq : x = 2 ^ w * u - 1 := by omega
  have hp_eq : (x - 1) / 2 = 2 ^ (w - 1) * u - 1 := by omega
  refine ⟨by omega, by omega, ?_⟩
  rw [collatzIter_add K (w + 2) nMin, hx_iter]
  let z := 3 ^ (w - 1) * u
  have hz_pos : z ≥ 1 := Nat.mul_pos (pow3_pos_nat (w - 1)) hu
  have h3z : 3 ^ w * u = 3 * z := by
    rw [show w = (w - 1) + 1 by omega, Nat.pow_succ]
    calc
      3 ^ (w - 1) * 3 * u = 3 * 3 ^ (w - 1) * u := by rw [Nat.mul_comm _ 3]
      _ = 3 * z := by rw [Nat.mul_assoc]
  rw [h3z] at ha_ge2
  rw [show w + 1 = (w - 1) + 2 by omega, collatzIter_add (w - 1) 2 ((x - 1) / 2),
      hp_eq, odd_run_iter (w - 1) u hu]
  rw [collatzIter_add w 2 x, hx_eq, odd_run_iter w u hu, h3z]
  have hz1_ev : ((z - 1) % 2 == 0) = true := decide_eq_true (by omega)
  have hz1_s1 : collatzStep (z - 1) = (z - 1) / 2 := by simp [collatzStep, hz1_ev]
  have hz1_odd : (((z - 1) / 2) % 2 == 0) = false := decide_eq_false (by omega)
  have hz1_s2 : collatzStep ((z - 1) / 2) = (3 * ((z - 1) / 2) + 1) / 2 := by
    simp [collatzStep, hz1_odd]
  have h3z_ev1 : ((3 * z - 1) % 2 == 0) = true := decide_eq_true (by omega)
  have h3z_s1 : collatzStep (3 * z - 1) = (3 * z - 1) / 2 := by simp [collatzStep, h3z_ev1]
  have h3z_ev2 : ((((3 * z - 1) / 2) % 2) == 0) = true := decide_eq_true (by omega)
  have h3z_s2 : collatzStep ((3 * z - 1) / 2) = ((3 * z - 1) / 2) / 2 := by
    simp [collatzStep, h3z_ev2]
  change collatzStep (collatzStep (z - 1)) = collatzStep (collatzStep (3 * z - 1))
  rw [hz1_s1, hz1_s2, h3z_s1, h3z_s2]
  omega

/--
  Theorem 27.1b (Universal Sub-Quadruple Exit-Tail Merger — Works Even at `w = 1`!):
  For ANY `xLast = collatzIter K nMin` with `xLast >= 5`, `xLast % 8 = 5` (which holds at the
  final odd step `xLast = 2 * 3^(w - 1) * u - 1` of EVERY odd block `w >= 1` with `a >= 2`!),
  and `xLast <= 4 * nMin`, the predecessor `nPrime = (xLast - 1) / 4 = 2 * q + 1` satisfies
  `1 <= nPrime < nMin` and merges in ONE compressed step:
    `collatzIter 1 ((xLast - 1) / 4) = collatzIter (K + 3) nMin`.
-/
theorem subquad_exit_tail_merger_step (nMin K xLast : Nat)
    (hx_ge5 : xLast ≥ 5)
    (hx_mod8 : xLast % 8 = 5)
    (hx_iter : collatzIter K nMin = xLast)
    (hx_sub4 : xLast ≤ 4 * nMin) :
    1 ≤ (xLast - 1) / 4 ∧ (xLast - 1) / 4 < nMin ∧
    collatzIter 1 ((xLast - 1) / 4) = collatzIter (K + 3) nMin := by
  -- Note xLast % 4 = 1 while 4 * nMin % 4 = 0, so xLast <= 4 * nMin => xLast + 3 <= 4 * nMin!
  refine ⟨by omega, by omega, ?_⟩
  rw [collatzIter_add K 3 nMin, hx_iter]
  let p := (xLast - 1) / 4
  have hp_odd : (p % 2 == 0) = false := decide_eq_false (by dsimp [p]; omega)
  have hp_s1 : collatzIter 1 p = (3 * p + 1) / 2 := by
    simp [collatzIter, collatzStep, hp_odd]
  have hx_odd : (xLast % 2 == 0) = false := decide_eq_false (by omega)
  have hx_s1 : collatzStep xLast = (3 * xLast + 1) / 2 := by simp [collatzStep, hx_odd]
  have hx_ev2 : (((3 * xLast + 1) / 2) % 2 == 0) = true := decide_eq_true (by omega)
  have hx_s2 : collatzStep ((3 * xLast + 1) / 2) = ((3 * xLast + 1) / 2) / 2 := by
    simp [collatzStep, hx_ev2]
  have hx_ev3 : ((((3 * xLast + 1) / 2) / 2) % 2 == 0) = true := decide_eq_true (by omega)
  have hx_s3 : collatzStep (((3 * xLast + 1) / 2) / 2) = (((3 * xLast + 1) / 2) / 2) / 2 := by
    simp [collatzStep, hx_ev3]
  change collatzIter 1 p = collatzStep (collatzStep (collatzStep xLast))
  rw [hp_s1, hx_s1, hx_s2, hx_s3]
  dsimp [p]
  omega


theorem pow3_mod4_nat : ∀ k : Nat, 3 ^ k % 4 = if k % 2 == 0 then 1 else 3
  | 0 => rfl
  | k + 1 => by
    have ih := pow3_mod4_nat k
    rw [Nat.pow_succ, Nat.mul_mod, ih]
    by_cases hev : k % 2 = 0
    · have hb1 : (k % 2 == 0) = true := decide_eq_true hev
      have hb2 : ((k + 1) % 2 == 0) = false := decide_eq_false (by omega)
      rw [hb1, hb2]; rfl
    · have hb1 : (k % 2 == 0) = false := decide_eq_false hev
      have hb2 : ((k + 1) % 2 == 0) = true := decide_eq_true (by omega)
      rw [hb1, hb2]; rfl

/-- Every odd block `w >= 1, u >= 1` (`u` odd) with `(3^w * u - 1) % 4 = 0` ends at `xLast % 8 = 5` -/
theorem block_exit_tail_mod8_eq_5 (w u : Nat)
    (hw : w ≥ 1) (hu_odd : u % 2 = 1)
    (ha_ge2 : (3 ^ w * u - 1) % 4 = 0) :
    (2 * 3 ^ (w - 1) * u - 1) % 8 = 5 := by
  have hp3 : 3 ^ w * u = 3 * (3 ^ (w - 1) * u) := by
    rw [show w = (w - 1) + 1 by omega, Nat.pow_succ]
    calc
      3 ^ (w - 1) * 3 * u = 3 * 3 ^ (w - 1) * u := by rw [Nat.mul_comm _ 3]
      _ = 3 * (3 ^ (w - 1) * u) := by rw [Nat.mul_assoc]
  have hm_odd : (3 ^ (w - 1) * u) % 2 = 1 := by
    rw [Nat.mul_mod, pow3_mod2_nat (w - 1), hu_odd]
  rw [hp3] at ha_ge2
  have hassoc : 2 * 3 ^ (w - 1) * u = 2 * (3 ^ (w - 1) * u) := Nat.mul_assoc 2 _ u
  rw [hassoc]
  omega

/--
  Theorem 27.1c (Block-1 Odd-Quotient Mod-4 Rigidity):
  On any minimal counterexample `nMin = 2^w1 * u1 - 1` (`w1 >= 2`, `u1` odd),
  exclusion of `a1 >= 2` forces `u1 % 4 = 3^(w1 + 1) % 4` (hence `nMin % 16 != 3`,
  `nMin % 32 != 23`, etc.).
-/
theorem block1_u1_mod4_rigidity (w1 u1 : Nat)
    (hu_odd : u1 % 2 = 1)
    (hna1_ge2 : (3 ^ w1 * u1 - 1) % 4 ≠ 0) :
    u1 % 4 = 3 ^ (w1 + 1) % 4 := by
  have hprod_pos : 3 ^ w1 * u1 ≥ 1 := Nat.mul_pos (pow3_pos_nat w1) (by omega)
  have hm_w1 := pow3_mod4_nat w1
  have hm_w1p := pow3_mod4_nat (w1 + 1)
  have hprod : (3 ^ w1 * u1) % 4 = ((3 ^ w1 % 4) * (u1 % 4)) % 4 := Nat.mul_mod _ _ 4
  by_cases hev : w1 % 2 = 0
  · have hb1 : (w1 % 2 == 0) = true := decide_eq_true hev
    have hb2 : ((w1 + 1) % 2 == 0) = false := decide_eq_false (by omega)
    rw [hb1] at hm_w1
    rw [hb2] at hm_w1p
    simp at hm_w1 hm_w1p
    rw [hm_w1] at hprod
    omega
  · have hb1 : (w1 % 2 == 0) = false := decide_eq_false hev
    have hb2 : ((w1 + 1) % 2 == 0) = true := decide_eq_true (by omega)
    rw [hb1] at hm_w1
    rw [hb2] at hm_w1p
    simp at hm_w1 hm_w1p
    rw [hm_w1] at hprod
    omega

/--
  Theorem 27.2a (Universal Block-2 `a_2 = 1` Forcing Across ALL `w_2 >= 1` When `w_1 in {2, 3}`):
  Whenever `nMin >= 7` has `w_1 in {2, 3}` and `a_1 = 1` (`x_2 = (3^w_1 * u_1 - 1) / 2`),
  `x_2` satisfies BOTH `x_2 <= 2 * nMin` (killing `a_2 >= 2` for all `w_2 >= 2` via Entry Merger)
  AND for `w_2 = 1`, `x_2 >= 5` and `x_2 <= 4 * nMin` (killing `a_2 >= 2` via Exit-Tail Merger)!
  Hence `a_2 = 1` (`(3^w_2 * u_2 - 1) % 4 = 2`) holds for EVERY `w_2 >= 1`!
-/
theorem block2_a2_eq_1_of_w1_2_or_3
    (nMin w1 u1 x2 w2 u2 : Nat)
    (hnMin : nMin ≥ 7)
    (hw1 : w1 = 2 ∨ w1 = 3)
    (_hu1 : u1 ≥ 1)
    (hn1 : nMin + 1 = 2 ^ w1 * u1)
    (hx2_val : 2 * x2 = 3 ^ w1 * u1 - 1)
    (hx2_iter : collatzIter (w1 + 1) nMin = x2)
    (hw2 : w2 ≥ 1) (hu2_odd : u2 % 2 = 1)
    (hx2_form : x2 + 1 = 2 ^ w2 * u2)
    (hnoMerger : ∀ nPrime K1 K2 : Nat,
      1 ≤ nPrime -> nPrime < nMin -> collatzIter K1 nPrime ≠ collatzIter K2 nMin) :
    (3 ^ w2 * u2 - 1) % 4 = 2 := by
  have hx2_bounds : x2 ≥ 5 ∧ x2 ≤ 2 * nMin := by
    rcases hw1 with rfl | rfl
    · change nMin + 1 = 4 * u1 at hn1
      change 2 * x2 = 9 * u1 - 1 at hx2_val
      omega
    · change nMin + 1 = 8 * u1 at hn1
      change 2 * x2 = 27 * u1 - 1 at hx2_val
      omega
  have hp3w2_odd : (3 ^ w2 * u2) % 2 = 1 := by
    rw [Nat.mul_mod, pow3_mod2_nat w2, hu2_odd]
  by_cases ha2_div4 : (3 ^ w2 * u2 - 1) % 4 = 0
  · by_cases hw2_ge2 : w2 ≥ 2
    · rcases subdouble_entry_merger_step nMin (w1 + 1) x2 w2 u2 hw2_ge2 (by omega)
        hx2_iter hx2_bounds.2 hx2_form ha2_div4 with ⟨hp_lo, hp_hi, hcoal⟩
      exact False.elim (hnoMerger ((x2 - 1) / 2) (w2 + 1) ((w1 + 1) + (w2 + 2)) hp_lo hp_hi hcoal)
    · have hw2_eq1 : w2 = 1 := by omega
      subst hw2_eq1
      have hmod8 := block_exit_tail_mod8_eq_5 1 u2 (by omega) hu2_odd ha2_div4
      simp at hmod8
      have hx2_eq : 2 * u2 - 1 = x2 := by change x2 + 1 = 2 * u2 at hx2_form; omega
      rw [hx2_eq] at hmod8
      rcases subquad_exit_tail_merger_step nMin (w1 + 1) x2 hx2_bounds.1 hmod8 hx2_iter
        (by omega) with ⟨hp_lo, hp_hi, hcoal⟩
      exact False.elim (hnoMerger ((x2 - 1) / 4) 1 ((w1 + 1) + 3) hp_lo hp_hi hcoal)
  · have hp3_ge1 : 3 ^ w2 * u2 ≥ 1 := Nat.mul_pos (pow3_pos_nat w2) (by omega)
    omega

/--
  Theorem 27.2b (Exact `-5` Eigenfunction Law for `(w = 2, a = 1)` Syracuse Blocks):
  Whenever `x + 1 = 4 * u` and `2 * xNext = 9 * u - 1` (`w = 2, a = 1`),
  `8 * (xNext + 5) = 9 * (x + 5)`! Iterating `5` consecutive `w = 2, a = 1` blocks gives
  `32768 * (x_6 + 5) = 59049 * (nMin + 5)`, so for ALL `nMin >= 21`, `x_6 <= 2 * nMin`
  (forcing `a_6 = 1` across a 6th consecutive block as well!).
-/
theorem w2_a1_eigenfunction_step (x xNext u : Nat)
    (hx : x + 1 = 4 * u)
    (hxNext : 2 * xNext = 9 * u - 1) :
    8 * (xNext + 5) = 9 * (x + 5) := by
  omega

theorem chain_8_9_step (a b c m1 m2 : Nat)
    (h1 : m1 * (b + 5) = m2 * (a + 5))
    (h2 : 8 * (c + 5) = 9 * (b + 5)) :
    (8 * m1) * (c + 5) = (9 * m2) * (a + 5) := by
  calc
    (8 * m1) * (c + 5) = m1 * (8 * (c + 5)) := by
      rw [Nat.mul_assoc 8 m1, Nat.mul_comm m1 (c + 5), ← Nat.mul_assoc 8 (c + 5) m1,
          Nat.mul_comm (8 * (c + 5)) m1]
    _ = m1 * (9 * (b + 5)) := by rw [h2]
    _ = 9 * (m1 * (b + 5)) := by rw [← Nat.mul_assoc, Nat.mul_comm m1 9, Nat.mul_assoc]
    _ = 9 * (m2 * (a + 5)) := by rw [h1]
    _ = (9 * m2) * (a + 5) := by rw [← Nat.mul_assoc]

theorem subdouble_of_eigen_ratio (q p nMin y : Nat)
    (hnMin : nMin ≥ 21)
    (hbound : 5 * p < (2 * q - p) * 21 + 6 * q ∧ p ≤ 2 * q)
    (heq : q * (y + 5) = p * (nMin + 5)) :
    y ≤ 2 * nMin := by
  apply Classical.byContradiction
  intro hgt
  have hlhs : q * (2 * nMin + 6) ≤ q * (y + 5) := Nat.mul_le_mul_left q (by omega)
  rw [heq, Nat.mul_add q (2 * nMin) 6, Nat.mul_add p nMin 5] at hlhs
  have h1 : q * (2 * nMin) = p * nMin + (2 * q - p) * nMin := by
    rw [← Nat.add_mul, show p + (2 * q - p) = 2 * q by omega,
        ← Nat.mul_assoc, Nat.mul_comm 2 q]
  rw [h1] at hlhs
  have h21 : (2 * q - p) * 21 ≤ (2 * q - p) * nMin := Nat.mul_le_mul_left (2 * q - p) hnMin
  have hp5 : p * 5 = 5 * p := Nat.mul_comm p 5
  have hq6 : q * 6 = 6 * q := Nat.mul_comm q 6
  omega

theorem six_block_w2_subdouble_bound (nMin x2 x3 x4 x5 x6 : Nat)
    (hnMin : nMin ≥ 21)
    (h1 : 8 * (x2 + 5) = 9 * (nMin + 5))
    (h2 : 8 * (x3 + 5) = 9 * (x2 + 5))
    (h3 : 8 * (x4 + 5) = 9 * (x3 + 5))
    (h4 : 8 * (x5 + 5) = 9 * (x4 + 5))
    (h5 : 8 * (x6 + 5) = 9 * (x5 + 5)) :
    32768 * (x6 + 5) = 59049 * (nMin + 5) ∧
    x2 ≤ 2 * nMin ∧ x3 ≤ 2 * nMin ∧ x4 ≤ 2 * nMin ∧ x5 ≤ 2 * nMin ∧ x6 ≤ 2 * nMin := by
  have c2 := chain_8_9_step nMin x2 x3 8 9 h1 h2
  rw [show 8 * 8 = 64 by decide, show 9 * 9 = 81 by decide] at c2
  have c3 := chain_8_9_step nMin x3 x4 64 81 c2 h3
  rw [show 8 * 64 = 512 by decide, show 9 * 81 = 729 by decide] at c3
  have c4 := chain_8_9_step nMin x4 x5 512 729 c3 h4
  rw [show 8 * 512 = 4096 by decide, show 9 * 729 = 6561 by decide] at c4
  have c5 := chain_8_9_step nMin x5 x6 4096 6561 c4 h5
  rw [show 8 * 4096 = 32768 by decide, show 9 * 6561 = 59049 by decide] at c5
  exact ⟨c5,
    subdouble_of_eigen_ratio 8 9 nMin x2 hnMin (by decide) h1,
    subdouble_of_eigen_ratio 64 81 nMin x3 hnMin (by decide) c2,
    subdouble_of_eigen_ratio 512 729 nMin x4 hnMin (by decide) c3,
    subdouble_of_eigen_ratio 4096 6561 nMin x5 hnMin (by decide) c4,
    subdouble_of_eigen_ratio 32768 59049 nMin x6 hnMin (by decide) c5⟩

/-- Inductive Beatty-Cantor cone prefix survival predicate `SurvivingFrom j w v` -/
def SurvivingFrom : Nat -> Nat -> List Bool -> Prop
  | _, _, [] => True
  | j, w, false :: rest => 2 ^ (j + 1) < 3 ^ w ∧ SurvivingFrom (j + 1) w rest
  | j, w, true :: rest => 2 ^ (j + 1) < 3 ^ (w + 1) ∧ SurvivingFrom (j + 1) (w + 1) rest

theorem surviving_carry_aux_bound :
    ∀ (v : List Bool) (j w acc : Nat),
      2 ^ j ≤ 3 ^ w ->
      SurvivingFrom j w v ->
      3 * acc ≤ w * 3 ^ w ->
      3 * affineCarryAux v j acc ≤ (w + parityWeight v) * 3 ^ (w + parityWeight v)
  | [], _, w, acc, _, _, hacc => by
    simp [affineCarryAux, parityWeight]
    exact hacc
  | false :: rest, j, w, acc, _, hsurv, hacc => by
    rcases hsurv with ⟨hlt, hrest⟩
    simp only [affineCarryAux, parityWeight]
    exact surviving_carry_aux_bound rest (j + 1) w acc (by omega) hrest hacc
  | true :: rest, j, w, acc, hjw, hsurv, hacc => by
    rcases hsurv with ⟨hlt, hrest⟩
    simp only [affineCarryAux, parityWeight]
    have hacc_next : 3 * (3 * acc + 2 ^ j) ≤ (w + 1) * 3 ^ (w + 1) := by
      have hm1 : 3 * (3 * acc) ≤ 3 * (w * 3 ^ w) := Nat.mul_le_mul_left 3 hacc
      have hm2 : 3 * 2 ^ j ≤ 3 * 3 ^ w := Nat.mul_le_mul_left 3 hjw
      have hrhs : (w + 1) * 3 ^ (w + 1) = 3 * (w * 3 ^ w) + 3 * 3 ^ w := by
        rw [Nat.pow_succ, Nat.add_mul, Nat.one_mul,
            ← Nat.mul_assoc w (3 ^ w) 3, Nat.mul_comm (w * 3 ^ w) 3, Nat.mul_comm (3 ^ w) 3]
      have hlhs : 3 * (3 * acc + 2 ^ j) = 3 * (3 * acc) + 3 * 2 ^ j := Nat.mul_add 3 _ _
      omega
    have hw_eq : w + (1 + parityWeight rest) = (w + 1) + parityWeight rest := by omega
    rw [hw_eq]
    exact surviving_carry_aux_bound rest (j + 1) (w + 1) (3 * acc + 2 ^ j)
      (by omega) hrest hacc_next

/--
  Theorem 27.3a (Universal Carry Upper Bound `3 * C(v) <= w(v) * 3^w(v)` on `S_infty` Prefixes):
  Every prefix-surviving word `v` (`SurvivingFrom 0 0 v`) satisfies `3 * C(v) <= w(v) * 3^w(v)`.
-/
theorem surviving_carry_three_mul_le_weight_pow3 (v : List Bool)
    (hsurv : SurvivingFrom 0 0 v) :
    3 * affineCarry v ≤ parityWeight v * 3 ^ parityWeight v := by
  have h := surviving_carry_aux_bound v 0 0 0 (by decide) hsurv (by decide)
  simpa [affineCarry] using h

/--
  Theorem 27.3b (3-Adic Fiber Quotient Bound `T^k(n) < 3^w(v)` on Positive Surviving Orbits):
  For ANY `v` with `SurvivingFrom 0 0 v` and ANY positive integer `n` with
  `2^|v| * y = 3^w(v) * n + C(v)` and `3 * n + w(v) < 3 * 2^|v|`,
  the `|v|`-th iterate satisfies `y < 3^w(v)` (so `y` is uniquely pinned to the
  3-adic residue `(2^(-|v|) * C(v)) mod 3^w(v)`!).
-/
theorem surviving_prefix_iter_lt_pow3 (v : List Bool) (n y : Nat)
    (hsurv : SurvivingFrom 0 0 v)
    (hdec : 2 ^ v.length * y = 3 ^ parityWeight v * n + affineCarry v)
    (harch : 3 * n + parityWeight v < 3 * 2 ^ v.length) :
    y < 3 ^ parityWeight v := by
  have hc := surviving_carry_three_mul_le_weight_pow3 v hsurv
  have h3dec : 3 * (2 ^ v.length * y) ≤ 3 ^ parityWeight v * (3 * n + parityWeight v) := by
    calc
      3 * (2 ^ v.length * y)
          = 3 * (3 ^ parityWeight v * n) + 3 * affineCarry v := by rw [hdec, Nat.mul_add]
      _ ≤ 3 ^ parityWeight v * (3 * n) + parityWeight v * 3 ^ parityWeight v := by
            have hm : 3 * (3 ^ parityWeight v * n) = 3 ^ parityWeight v * (3 * n) := by
              rw [← Nat.mul_assoc, Nat.mul_comm 3 (3 ^ parityWeight v), Nat.mul_assoc]
            rw [hm]
            exact Nat.add_le_add_left hc _
      _ = 3 ^ parityWeight v * (3 * n + parityWeight v) := by
            rw [Nat.mul_comm (parityWeight v) (3 ^ parityWeight v), ← Nat.mul_add]
  have hlt : 3 ^ parityWeight v * (3 * n + parityWeight v) < 3 ^ parityWeight v * (3 * 2 ^ v.length) :=
    Nat.mul_lt_mul_of_pos_left harch (pow3_pos_nat (parityWeight v))
  apply Classical.byContradiction
  intro hge
  have hy_ge : 3 ^ parityWeight v ≤ y := by omega
  have hm : (3 * 2 ^ v.length) * 3 ^ parityWeight v ≤ 3 * (2 ^ v.length * y) := by
    rw [Nat.mul_assoc 3 (2 ^ v.length) (3 ^ parityWeight v)]
    exact Nat.mul_le_mul_left 3 (Nat.mul_le_mul_left (2 ^ v.length) hy_ge)
  rw [Nat.mul_comm (3 * 2 ^ v.length) (3 ^ parityWeight v)] at hm
  omega

/--
  Theorem 27.2c (`(w_1 = 4, a_1 = 1, w_2 = 1)` Exit-Tail Merger Exclusion):
  When `w_1 = 4, a_1 = 1` (`nMin + 1 = 16 * u1`, `2 * x2 = 81 * u1 - 1`), `x2 / nMin ~ 81/32 = 2.53 > 2`
  (so sub-double Entry Merger fails), YET `x2 <= 4 * nMin` holds for ALL `nMin >= 15` (`u1 >= 1`)!
  Hence at `w_2 = 1` (`x2 + 1 = 2 * u2`), `subquad_exit_tail_merger_step` STILL eliminates `a_2 >= 2`
  and forces `(3 * u2 - 1) % 4 = 2` (`u2 % 4 = 1`)!
-/
theorem block2_w1_4_w2_1_a2_eq_1
    (nMin u1 x2 u2 : Nat)
    (hu1 : u1 ≥ 1)
    (hn1 : nMin + 1 = 16 * u1)
    (hx2_val : 2 * x2 = 81 * u1 - 1)
    (hx2_iter : collatzIter 5 nMin = x2)
    (hu2_odd : u2 % 2 = 1)
    (hx2_form : x2 + 1 = 2 * u2)
    (hnoMerger : ∀ nPrime K1 K2 : Nat,
      1 ≤ nPrime -> nPrime < nMin -> collatzIter K1 nPrime ≠ collatzIter K2 nMin) :
    (3 * u2 - 1) % 4 = 2 := by
  have hx2_bounds : x2 ≥ 5 ∧ x2 ≤ 4 * nMin := by omega
  by_cases ha2_div4 : (3 * u2 - 1) % 4 = 0
  · have ha2_pow : (3 ^ 1 * u2 - 1) % 4 = 0 := by simpa using ha2_div4
    have hmod8 := block_exit_tail_mod8_eq_5 1 u2 (by decide) hu2_odd ha2_pow
    simp at hmod8
    have hx2_eq : 2 * u2 - 1 = x2 := by omega
    rw [hx2_eq] at hmod8
    rcases subquad_exit_tail_merger_step nMin 5 x2 hx2_bounds.1 hmod8 hx2_iter
      hx2_bounds.2 with ⟨hp_lo, hp_hi, hcoal⟩
    exact False.elim (hnoMerger ((x2 - 1) / 4) 1 8 hp_lo hp_hi hcoal)
  · omega

theorem pow2_add2_lt_pow3_of_ge4 : ∀ w : Nat, w ≥ 4 -> 2 ^ (w + 2) < 3 ^ w
  | 0, hw => by omega
  | 1, hw => by omega
  | 2, hw => by omega
  | 3, hw => by omega
  | 4, _ => by decide
  | w + 5, _ => by
    have ih := pow2_add2_lt_pow3_of_ge4 (w + 4) (by omega)
    rw [show w + 5 + 2 = (w + 4 + 2) + 1 by omega, Nat.pow_succ 2 (w + 4 + 2),
        show w + 5 = (w + 4) + 1 by omega, Nat.pow_succ 3 (w + 4)]
    omega

theorem survivingFrom_replicate_true :
    ∀ (k j w : Nat) (tail : List Bool),
      (∀ t : Nat, t < k -> 2 ^ (j + t + 1) < 3 ^ (w + t + 1)) ->
      SurvivingFrom (j + k) (w + k) tail ->
      SurvivingFrom j w (List.replicate k true ++ tail)
  | 0, j, w, tail, _, htail => by simpa using htail
  | k + 1, j, w, tail, hlt, htail => by
    simp only [List.replicate_succ, List.cons_append, SurvivingFrom]
    refine ⟨?_, ?_⟩
    · have h0 := hlt 0 (by omega)
      simpa using h0
    · have hshift : SurvivingFrom ((j + 1) + k) ((w + 1) + k) tail := by
        rwa [show (j + 1) + k = j + (k + 1) by omega,
             show (w + 1) + k = w + (k + 1) by omega]
      exact survivingFrom_replicate_true k (j + 1) (w + 1) tail
        (fun t ht => by
          have ht1 := hlt (t + 1) (by omega)
          rwa [show j + (t + 1) + 1 = (j + 1) + t + 1 by omega,
               show w + (t + 1) + 1 = (w + 1) + t + 1 by omega] at ht1)
        hshift

theorem pow2_lt_pow3_succ : ∀ t : Nat, 2 ^ (t + 1) < 3 ^ (t + 1)
  | 0 => by decide
  | t + 1 => by
    have ih := pow2_lt_pow3_succ t
    rw [show t + 1 + 1 = (t + 1) + 1 by rfl, Nat.pow_succ 2 (t + 1), Nat.pow_succ 3 (t + 1)]
    omega

/--
  Theorem 27.3c (Multi-Parameter Beatty-Cantor `S_infty` Family `1^w 0^2 ++ tail` for `w >= 4`):
  For EVERY `w >= 4` and EVERY surviving suffix `tail` (`SurvivingFrom (w + 2) w tail`),
  `v = List.replicate w true ++ [false, false] ++ tail` lies inside the Beatty-Cantor
  survival cone `SurvivingFrom 0 0 v` (realized in `S_infty`, yet excluded on every
  minimal non-descending positive integer `nMin > 1` by `subdouble_entry_merger_step`)!
-/
theorem cantor_cone_family_1w_00_survives (w : Nat) (tail : List Bool)
    (hw : w ≥ 4)
    (htail : SurvivingFrom (w + 2) w tail) :
    SurvivingFrom 0 0 (List.replicate w true ++ ([false, false] ++ tail)) := by
  have hw2 : 2 ^ (w + 2) < 3 ^ w := pow2_add2_lt_pow3_of_ge4 w hw
  have hw1 : 2 ^ (w + 1) < 3 ^ w := by
    have hm := pow2_mono_nat (show w + 1 ≤ w + 2 by omega)
    omega
  have hmid : SurvivingFrom (0 + w) (0 + w) ([false, false] ++ tail) := by
    simp only [Nat.zero_add, List.cons_append, List.nil_append, SurvivingFrom]
    exact ⟨hw1, hw2, htail⟩
  exact survivingFrom_replicate_true w 0 0 ([false, false] ++ tail)
    (fun t _ => by simpa using pow2_lt_pow3_succ t) hmid


/--
  Theorem 27.4 (Coupled Minimal-Counterexample Coalescence, 3-Adic Fiber Quotient,
  & Quadratic Carry-Deficit Peak Obstruction):
  On ANY minimal non-descending counterexample `nMin > 1`:
  (1) Every surviving Beatty-Cantor prefix `1^w 0^2 ++ tail` (`w >= 4`, realized in `S_infty`
      by `cantor_cone_family_1w_00_survives`) is strictly excluded on `nMin` via
      `subdouble_entry_merger_step` + `strict_descent_minimal_counterexample_coalescence_contradiction`;
  (2) Every surviving prefix `v` with `2^|v| * y = 3^w(v) * nMin + C(v)` and
      `3 * nMin + w(v) < 3 * 2^|v|` simultaneously forces the 3-adic fractional proximity
      ceiling `y < 3^w(v)` (`surviving_prefix_iter_lt_pow3`) AND, under `3 * (mPeak - nMin) * mPeak > nMin * w(v)`,
      the quadratic peak floor `3 * (2 * mPeak - nMin)^2 > 3 * nMin^2 + 4 * nMin * w(v)`!
-/
theorem minimal_counterexample_archimedean_coalescence_exclusion
    (nMin : Nat)
    (hnMin : nMin > 1)
    (hnoDesc : ∀ K : Nat, ¬ (0 < collatzIter K nMin ∧ collatzIter K nMin < nMin))
    (hminReach : ∀ m : Nat, 1 ≤ m -> m < nMin -> ∃ k1 : Nat, collatzIter k1 m = 1) :
    (∀ w u : Nat, w ≥ 4 -> u ≥ 1 -> nMin + 1 = 2 ^ w * u -> (3 ^ w * u - 1) % 4 = 0 -> False) ∧
    (∀ (v : List Bool) (y : Nat) (mPeak : Int),
      SurvivingFrom 0 0 v ->
      2 ^ v.length * y = 3 ^ parityWeight v * nMin + affineCarry v ->
      3 * nMin + parityWeight v < 3 * 2 ^ v.length ->
      3 * ((mPeak - (nMin : Int)) * mPeak) > (nMin : Int) * (parityWeight v : Int) ->
      y < 3 ^ parityWeight v ∧
      3 * ((2 * mPeak - (nMin : Int)) * (2 * mPeak - (nMin : Int))) >
        3 * ((nMin : Int) * (nMin : Int)) + 4 * ((nMin : Int) * (parityWeight v : Int))) := by
  refine ⟨?_, ?_⟩
  · intro w u hw hu hform ha_ge2
    rcases subdouble_entry_merger_step nMin 0 nMin w u (by omega) hu rfl (by omega) hform ha_ge2 with
      ⟨hp_lo, hp_lt, hcoal⟩
    exact strict_descent_minimal_counterexample_coalescence_contradiction
      nMin ((nMin - 1) / 2) (0 + (w + 2)) (w + 1) hnMin hp_lo hp_lt hnoDesc
      (hminReach ((nMin - 1) / 2) hp_lo hp_lt) hcoal.symm
  · intro v y mPeak hsurv hdec harch hunc
    exact ⟨surviving_prefix_iter_lt_pow3 v nMin y hsurv hdec harch,
           quadratic_peak_floor_cleared_square (nMin : Int) (parityWeight v : Int) mPeak hunc⟩


-- ============================================================================
-- SECTION 15: Unbounded-Weight Inverse Predecessor Tree & 3-Adic Branching Density
-- ============================================================================

theorem syracuse_step_unique : ∀ (d1 d2 y1 y2 : Nat),
    y1 % 2 = 1 -> y2 % 2 = 1 ->
    2 ^ d1 * y1 = 2 ^ d2 * y2 ->
    d1 = d2 ∧ y1 = y2
  | 0, 0, y1, y2, _, _, h => ⟨rfl, by simpa using h⟩
  | 0, d2 + 1, y1, y2, hy1, _, h => by
    simp only [Nat.pow_zero, Nat.one_mul] at h
    have hp : 2 ^ (d2 + 1) * y2 = 2 * (2 ^ d2 * y2) := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ d2) 2, Nat.mul_assoc]
    rw [hp] at h
    omega
  | d1 + 1, 0, y1, y2, _, hy2, h => by
    simp only [Nat.pow_zero, Nat.one_mul] at h
    have hp : 2 ^ (d1 + 1) * y1 = 2 * (2 ^ d1 * y1) := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ d1) 2, Nat.mul_assoc]
    rw [hp] at h
    omega
  | d1 + 1, d2 + 1, y1, y2, hy1, hy2, h => by
    have hp1 : 2 ^ (d1 + 1) * y1 = 2 * (2 ^ d1 * y1) := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ d1) 2, Nat.mul_assoc]
    have hp2 : 2 ^ (d2 + 1) * y2 = 2 * (2 ^ d2 * y2) := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ d2) 2, Nat.mul_assoc]
    rw [hp1, hp2] at h
    rcases syracuse_step_unique d1 d2 y1 y2 hy1 hy2 (by omega) with ⟨hd, hy⟩
    exact ⟨by omega, hy⟩

/--
  Explicit 2-of-6 Garden-of-Eden-Bypassing Syracuse Exponent Table:
  For every odd `y >= 5` with `y % 3 != 0`, selects `d in {1, ..., 6}` such that
  `2^d * y ≡ 4 or 7 (mod 9)`, guaranteeing `x = (2^d * y - 1) / 3` is an ODD integer
  `>= 5` with `x % 3 != 0`!
-/
def syracuseValidExp (y : Nat) (choice : Bool) : Nat :=
  let r := y % 9
  if r == 1 then (if choice then 4 else 2)
  else if r == 2 then (if choice then 3 else 1)
  else if r == 4 then (if choice then 6 else 2)
  else if r == 5 then (if choice then 5 else 3)
  else if r == 7 then (if choice then 6 else 4)
  else (if choice then 5 else 1)

def syracuseChild (y : Nat) (choice : Bool) : Nat :=
  (2 ^ syracuseValidExp y choice * y - 1) / 3

theorem syracuseChild_props (y : Nat) (choice : Bool)
    (hy_ge5 : y ≥ 5) (hy_odd : y % 2 = 1) (hy_non3 : y % 3 ≠ 0) :
    let d := syracuseValidExp y choice
    let x := syracuseChild y choice
    1 ≤ d ∧ d ≤ 6 ∧
    3 * x + 1 = 2 ^ d * y ∧
    x ≥ 5 ∧ x % 2 = 1 ∧ x % 3 ≠ 0 := by
  dsimp only
  unfold syracuseChild syracuseValidExp
  have hm9 : y % 9 = 1 ∨ y % 9 = 2 ∨ y % 9 = 4 ∨ y % 9 = 5 ∨ y % 9 = 7 ∨ y % 9 = 8 := by omega
  rcases hm9 with h | h | h | h | h | h <;> rw [h] <;> cases choice <;> simp <;> omega

theorem syracuseValidExp_lt (y : Nat) :
    syracuseValidExp y false < syracuseValidExp y true := by
  unfold syracuseValidExp
  by_cases h1 : y % 9 == 1
  · simp [h1]
  · by_cases h2 : y % 9 == 2
    · simp [h1, h2]
    · by_cases h4 : y % 9 == 4
      · simp [h1, h2, h4]
      · by_cases h5 : y % 9 == 5
        · simp [h1, h2, h4, h5]
        · by_cases h7 : y % 9 == 7
          · simp [h1, h2, h4, h5, h7]
          · simp [h1, h2, h4, h5, h7]

/-- Unbounded-weight binary Syracuse predecessor tree rooted at `y_0 = 5` -/
def syracuseTreeVal : List Bool -> Nat
  | [] => 5
  | b :: rest => syracuseChild (syracuseTreeVal rest) b

def syracuseTreeWord : List Bool -> List Bool
  | [] => [true, false, false, false]
  | b :: rest =>
    let y := syracuseTreeVal rest
    let d := syracuseValidExp y b
    true :: (List.replicate (d - 1) false ++ syracuseTreeWord rest)

theorem syracuseTreeVal_invariant : ∀ (cs : List Bool),
    syracuseTreeVal cs ≥ 5 ∧ syracuseTreeVal cs % 2 = 1 ∧ syracuseTreeVal cs % 3 ≠ 0
  | [] => by simp [syracuseTreeVal]
  | b :: rest => by
    rcases syracuseTreeVal_invariant rest with ⟨hge, hodd, hnon3⟩
    have hp := syracuseChild_props (syracuseTreeVal rest) b hge hodd hnon3
    simp only [syracuseTreeVal]
    exact ⟨hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2⟩

/--
  Theorem 28.3 (Global Injectivity of the Unbounded-Weight Binary Predecessor Tree):
  `syracuseTreeVal` is 100% injective across ALL `List Bool` of ALL weights simultaneously!
-/
theorem syracuseTreeVal_injective : ∀ (cs1 cs2 : List Bool),
    syracuseTreeVal cs1 = syracuseTreeVal cs2 -> cs1 = cs2
  | [], [], _ => rfl
  | [], b2 :: rest2, heq => by
    rcases syracuseTreeVal_invariant rest2 with ⟨hge2, hodd2, hnon3_2⟩
    have hp2 := syracuseChild_props (syracuseTreeVal rest2) b2 hge2 hodd2 hnon3_2
    simp only [syracuseTreeVal] at heq
    have h5 : 2 ^ 4 * 1 = 2 ^ syracuseValidExp (syracuseTreeVal rest2) b2 * syracuseTreeVal rest2 := by
      have h3x := hp2.2.2.1
      rw [← heq] at h3x
      omega
    rcases syracuse_step_unique 4 (syracuseValidExp (syracuseTreeVal rest2) b2)
      1 (syracuseTreeVal rest2) (by decide) hodd2 h5 with ⟨_, hy⟩
    omega
  | b1 :: rest1, [], heq => by
    rcases syracuseTreeVal_invariant rest1 with ⟨hge1, hodd1, hnon3_1⟩
    have hp1 := syracuseChild_props (syracuseTreeVal rest1) b1 hge1 hodd1 hnon3_1
    simp only [syracuseTreeVal] at heq
    have h5 : 2 ^ syracuseValidExp (syracuseTreeVal rest1) b1 * syracuseTreeVal rest1 = 2 ^ 4 * 1 := by
      have h3x := hp1.2.2.1
      rw [heq] at h3x
      omega
    rcases syracuse_step_unique (syracuseValidExp (syracuseTreeVal rest1) b1) 4
      (syracuseTreeVal rest1) 1 hodd1 (by decide) h5 with ⟨_, hy⟩
    omega
  | b1 :: rest1, b2 :: rest2, heq => by
    rcases syracuseTreeVal_invariant rest1 with ⟨hge1, hodd1, hnon3_1⟩
    rcases syracuseTreeVal_invariant rest2 with ⟨hge2, hodd2, hnon3_2⟩
    have hp1 := syracuseChild_props (syracuseTreeVal rest1) b1 hge1 hodd1 hnon3_1
    have hp2 := syracuseChild_props (syracuseTreeVal rest2) b2 hge2 hodd2 hnon3_2
    simp only [syracuseTreeVal] at heq
    have h2eq : 2 ^ syracuseValidExp (syracuseTreeVal rest1) b1 * syracuseTreeVal rest1 =
                2 ^ syracuseValidExp (syracuseTreeVal rest2) b2 * syracuseTreeVal rest2 := by
      have h3x1 := hp1.2.2.1
      have h3x2 := hp2.2.2.1
      rw [heq] at h3x1
      omega
    rcases syracuse_step_unique
      (syracuseValidExp (syracuseTreeVal rest1) b1)
      (syracuseValidExp (syracuseTreeVal rest2) b2)
      (syracuseTreeVal rest1) (syracuseTreeVal rest2)
      hodd1 hodd2 h2eq with ⟨hd_eq, hy_eq⟩
    have hrest_eq : rest1 = rest2 := syracuseTreeVal_injective rest1 rest2 hy_eq
    subst hrest_eq
    have hb_eq : b1 = b2 := by
      have hlt := syracuseValidExp_lt (syracuseTreeVal rest1)
      cases b1 <;> cases b2 <;> simp at hd_eq ⊢ <;> omega
    rw [hb_eq]

/--
  Theorem 28.4 (Exponential `2^w` Growth Bound `3^(w + 1) * x < 2^(4 + 6*w)`):
  Every tree node `syracuseTreeVal cs` at depth `w = cs.length` satisfies
  `3^(w + 1) * syracuseTreeVal cs < 2^(4 + 6 * w)`!
-/
theorem syracuseTreeVal_upper_bound : ∀ (cs : List Bool),
    3 ^ (cs.length + 1) * syracuseTreeVal cs < 2 ^ (4 + 6 * cs.length)
  | [] => by decide
  | b :: rest => by
    have ih := syracuseTreeVal_upper_bound rest
    rcases syracuseTreeVal_invariant rest with ⟨hge, hodd, hnon3⟩
    have hp := syracuseChild_props (syracuseTreeVal rest) b hge hodd hnon3
    simp only [syracuseTreeVal, List.length_cons]
    let d := syracuseValidExp (syracuseTreeVal rest) b
    let x := syracuseChild (syracuseTreeVal rest) b
    have hd_le6 : d ≤ 6 := hp.2.1
    have h3x : 3 * x + 1 = 2 ^ d * syracuseTreeVal rest := hp.2.2.1
    have hp2d : 2 ^ d ≤ 64 := by
      have hm := pow2_mono_nat hd_le6
      simpa using hm
    have hstep : 3 ^ ((rest.length + 1) + 1) * x <
        64 * (3 ^ (rest.length + 1) * syracuseTreeVal rest) := by
      rw [Nat.pow_succ, Nat.mul_assoc]
      have h1 : 3 * x < 64 * syracuseTreeVal rest := by
        have hm := Nat.mul_le_mul_right (syracuseTreeVal rest) hp2d
        omega
      have hm3 := Nat.mul_lt_mul_of_pos_left h1 (pow3_pos_nat (rest.length + 1))
      rw [← Nat.mul_assoc (3 ^ (rest.length + 1)) 64 (syracuseTreeVal rest),
          Nat.mul_comm (3 ^ (rest.length + 1)) 64,
          Nat.mul_assoc 64 (3 ^ (rest.length + 1)) (syracuseTreeVal rest)] at hm3
      exact hm3
    have hrhs : 64 * 2 ^ (4 + 6 * rest.length) = 2 ^ (4 + 6 * (rest.length + 1)) := by
      have heq : 4 + 6 * (rest.length + 1) = (4 + 6 * rest.length) + 6 := by omega
      have h26 : 2 ^ 6 = 64 := rfl
      rw [heq, Nat.pow_add 2 (4 + 6 * rest.length) 6, h26, Nat.mul_comm]
    have hm64 := Nat.mul_lt_mul_of_pos_left ih (by decide : 0 < 64)
    rw [hrhs] at hm64
    exact Nat.lt_trans hstep hm64


/--
  Theorem 28.1a (`a`-Fold Even Doubling Closure `x -> 2^a * x`, `v -> 0^a ++ v`):
  Iterating `one_equation_even_double_closure` `a` times lifts any solution `(v, x)`
  to `(List.replicate a false ++ v, 2^a * x)` with unchanged parity weight.
-/
theorem one_equation_even_replicate_closure : ∀ (a : Nat) (v : List Bool) (x : Int),
    (2 : Int) ^ v.length = (3 : Int) ^ parityWeight v * x + affineCarryInt v ->
    (2 : Int) ^ (List.replicate a false ++ v).length =
      (3 : Int) ^ parityWeight (List.replicate a false ++ v) * ((2 : Int) ^ a * x) +
      affineCarryInt (List.replicate a false ++ v)
  | 0, v, x, heq => by simpa using heq
  | a + 1, v, x, heq => by
    have ih := one_equation_even_replicate_closure a v x heq
    have hstep := one_equation_even_double_closure (List.replicate a false ++ v) ((2 : Int) ^ a * x) ih
    simp only [List.replicate_succ, List.cons_append]
    have hp : (2 : Int) ^ (a + 1) * x = 2 * ((2 : Int) ^ a * x) := by
      rw [Int.pow_succ, Int.mul_comm ((2 : Int) ^ a) 2, Int.mul_assoc]
    rwa [hp]

/--
  Theorem 28.1b (General Multi-Exponent Odd Syracuse Lift `3 * x + 1 = 2^d * y`):
  Whenever `v` solves `2^|v| = 3^w(v) * y + C(v)` and `x` is an odd integer (`x % 2 = 1`)
  satisfying `3 * x + 1 = 2^d * y` (`d >= 1`), `v' = true :: (replicate (d - 1) false ++ v)`
  has `w(v') = w(v) + 1`, `|v'| = |v| + d`, and solves `2^|v'| = 3^w(v') * x + C(v')`!
-/
theorem one_equation_syracuse_general_lift (d : Nat) (v : List Bool) (x y : Int)
    (hd : d ≥ 1)
    (hx_odd : x % 2 = 1)
    (hsyr : 3 * x + 1 = (2 : Int) ^ d * y)
    (heq : (2 : Int) ^ v.length = (3 : Int) ^ parityWeight v * y + affineCarryInt v) :
    let v' := true :: (List.replicate (d - 1) false ++ v)
    (2 : Int) ^ v'.length = (3 : Int) ^ parityWeight v' * x + affineCarryInt v' := by
  dsimp only
  let m : Int := (x - 1) / 2
  have hx_eq : x = 2 * m + 1 := by dsimp [m]; omega
  have hd_eq : (2 : Int) ^ d * y = 2 * ((2 : Int) ^ (d - 1) * y) := by
    conv => lhs; rw [show d = (d - 1) + 1 by omega]
    rw [Int.pow_succ, Int.mul_comm ((2 : Int) ^ (d - 1)) 2, Int.mul_assoc]
  have hm_eq : (2 : Int) ^ (d - 1) * y = 3 * m + 2 := by omega
  have hev := one_equation_even_replicate_closure (d - 1) v y heq
  rw [hm_eq] at hev
  rw [hx_eq]
  exact one_equation_odd_predecessor_lift (List.replicate (d - 1) false ++ v) m hev

theorem parityWeight_replicate_false_append : ∀ (a : Nat) (v : List Bool),
    parityWeight (List.replicate a false ++ v) = parityWeight v
  | 0, _ => rfl
  | a + 1, v => parityWeight_replicate_false_append a v

theorem syracuseTreeWord_weight : ∀ (cs : List Bool),
    parityWeight (syracuseTreeWord cs) = cs.length + 1
  | [] => rfl
  | b :: rest => by
    simp only [syracuseTreeWord, parityWeight, List.length_cons]
    rw [parityWeight_replicate_false_append, syracuseTreeWord_weight rest]
    omega


/--
  Theorem 28.2 (Every Unbounded-Weight Binary Tree Node Solves the One-Equation Identity):
  For EVERY binary choice sequence `cs : List Bool` of arbitrary length `w = cs.length`,
  `v = syracuseTreeWord cs` has exact weight `w + 1` and solves
  `2^|v| = 3^(w + 1) * syracuseTreeVal cs + C(v)`!
-/
theorem syracuseTreeWord_solves_one_equation : ∀ (cs : List Bool),
    let v := syracuseTreeWord cs
    (2 : Int) ^ v.length =
      (3 : Int) ^ parityWeight v * (syracuseTreeVal cs : Int) + affineCarryInt v
  | [] => by decide
  | b :: rest => by
    have ih := syracuseTreeWord_solves_one_equation rest
    rcases syracuseTreeVal_invariant rest with ⟨hge, hodd, hnon3⟩
    have hp := syracuseChild_props (syracuseTreeVal rest) b hge hodd hnon3
    let y := syracuseTreeVal rest
    let d := syracuseValidExp y b
    let x := syracuseChild y b
    have hsyr_nat : 3 * x + 1 = 2 ^ d * y := hp.2.2.1
    have hsyr_int : 3 * (x : Int) + 1 = (2 : Int) ^ d * (y : Int) := by
      have hc : ((3 * x + 1 : Nat) : Int) = ((2 ^ d * y : Nat) : Int) :=
        congrArg Int.ofNat hsyr_nat
      rw [natCast_add, natCast_mul, natCast_mul, natCast_pow2] at hc
      simpa using hc
    have hx_odd_int : (x : Int) % 2 = 1 := by
      have hx_mod : x % 2 = 1 := hp.2.2.2.2.1
      omega
    exact one_equation_syracuse_general_lift d (syracuseTreeWord rest) (x : Int) (y : Int)
      hp.1 hx_odd_int hsyr_int ih

-- ============================================================================
-- SECTION 16: Theorem 29 — General `(a, b)`-Affine Backward Merger Sieve,
--             `0 mod 3` Carry Trap, Initial-Bit Exhaustion, & Bounded Cycles
-- ============================================================================

/--
  Theorem 29.1a (Universal `(a, b)`-Affine 2-Adic Hensel Converse over `Z`):
  For EVERY parity word `u : List Bool` and EVERY pair of integers `x, y : Int`
  (positive, zero, or negative, with zero side-conditions),
  if `2^|u| * y = 3^w(u) * x + C(u)`, then `x` AUTOMATICALLY realizes parity
  vector `u` step-by-step and reaches `collatzIterInt |u| x = y`!
-/
theorem general_affine_converse_universal : ∀ (u : List Bool) (x y : Int),
    (2 : Int) ^ u.length * y = (3 : Int) ^ parityWeight u * x + affineCarryInt u ->
    matchesParity u x ∧ collatzIterInt u.length x = y
  | [], x, y, heq => by
    simp [parityWeight, affineCarryInt, affineCarryAuxInt] at heq
    exact ⟨trivial, by simp [collatzIterInt]; omega⟩
  | false :: rest, x, y, heq => by
    have hc : affineCarryInt (false :: rest) = 2 * affineCarryInt rest := by
      unfold affineCarryInt
      simp only [affineCarryAuxInt]
      have h01 : 0 + 1 = 1 := rfl
      rw [h01]
      have hs := affineCarryAuxInt_shift rest 1 0
      omega
    have hp2 : (2 : Int) ^ (false :: rest).length * y = 2 * ((2 : Int) ^ rest.length * y) := by
      simp only [List.length_cons, Int.pow_succ]
      rw [Int.mul_comm ((2 : Int) ^ rest.length) 2, Int.mul_assoc]
    simp only [parityWeight] at heq
    rw [hc, hp2] at heq
    have hprod_ev : ((3 : Int) ^ parityWeight rest * x) % 2 = 0 := by omega
    have hx_ev : x % 2 = 0 :=
      odd_mul_even_iff ((3 : Int) ^ parityWeight rest) x (pow3_mod2 _) hprod_ev
    have hstep : 2 * collatzStepInt x = x := collatzStepInt_even x hx_ev
    have hmul : (3 : Int) ^ parityWeight rest * x =
        2 * ((3 : Int) ^ parityWeight rest * collatzStepInt x) := by
      have h1 := congrArg (fun t => (3 : Int) ^ parityWeight rest * t) hstep.symm
      rw [h1, ← Int.mul_assoc, Int.mul_comm ((3 : Int) ^ parityWeight rest) 2, Int.mul_assoc]
    rw [hmul] at heq
    have hnext : (2 : Int) ^ rest.length * y =
        (3 : Int) ^ parityWeight rest * collatzStepInt x + affineCarryInt rest := by
      omega
    rcases general_affine_converse_universal rest (collatzStepInt x) y hnext with ⟨hm, hi⟩
    exact ⟨⟨hx_ev, hm⟩, hi⟩
  | true :: rest, x, y, heq => by
    have hc : affineCarryInt (true :: rest) =
        (3 : Int) ^ parityWeight rest + 2 * affineCarryInt rest := by
      unfold affineCarryInt
      simp only [affineCarryAuxInt]
      have h10 : 3 * (0 : Int) + (2 : Int) ^ 0 = 1 := rfl
      have h01 : 0 + 1 = 1 := rfl
      rw [h01, h10]
      have hs := affineCarryAuxInt_shift rest 1 1
      omega
    have hp2 : (2 : Int) ^ (true :: rest).length * y = 2 * ((2 : Int) ^ rest.length * y) := by
      simp only [List.length_cons, Int.pow_succ]
      rw [Int.mul_comm ((2 : Int) ^ rest.length) 2, Int.mul_assoc]
    have _hp3 : (3 : Int) ^ parityWeight (true :: rest) * x + (3 : Int) ^ parityWeight rest =
        (3 : Int) ^ parityWeight rest * (3 * x + 1) := by
      simp only [parityWeight]
      have hpw : 1 + parityWeight rest = parityWeight rest + 1 := by omega
      rw [hpw, Int.pow_succ, Int.mul_add, Int.mul_one, Int.mul_assoc]
    rw [hc, hp2] at heq
    have hcomb : 2 * ((2 : Int) ^ rest.length * y) =
        (3 : Int) ^ parityWeight rest * (3 * x + 1) + 2 * affineCarryInt rest := by
      omega
    have hprod_ev : ((3 : Int) ^ parityWeight rest * (3 * x + 1)) % 2 = 0 := by omega
    have h3x1_ev : (3 * x + 1) % 2 = 0 :=
      odd_mul_even_iff ((3 : Int) ^ parityWeight rest) (3 * x + 1) (pow3_mod2 _) hprod_ev
    have hx_odd : x % 2 = 1 := by omega
    have hstep : 2 * collatzStepInt x = 3 * x + 1 := collatzStepInt_odd x hx_odd
    have hmul : (3 : Int) ^ parityWeight rest * (3 * x + 1) =
        2 * ((3 : Int) ^ parityWeight rest * collatzStepInt x) := by
      have h1 := congrArg (fun t => (3 : Int) ^ parityWeight rest * t) hstep.symm
      rw [h1, ← Int.mul_assoc, Int.mul_comm ((3 : Int) ^ parityWeight rest) 2, Int.mul_assoc]
    rw [hmul] at hcomb
    have hnext : (2 : Int) ^ rest.length * y =
        (3 : Int) ^ parityWeight rest * collatzStepInt x + affineCarryInt rest := by
      omega
    rcases general_affine_converse_universal rest (collatzStepInt x) y hnext with ⟨hm, hi⟩
    exact ⟨⟨hx_odd, hm⟩, hi⟩

theorem affineCarryAuxInt_ofNat : ∀ (u : List Bool) (j acc : Nat),
    affineCarryAuxInt u j (acc : Int) = (affineCarryAux u j acc : Int)
  | [], _, _ => rfl
  | false :: rest, j, acc => affineCarryAuxInt_ofNat rest (j + 1) acc
  | true :: rest, j, acc => by
    simp only [affineCarryAuxInt, affineCarryAux]
    have hacc : 3 * (acc : Int) + (2 : Int) ^ j = ((3 * acc + 2 ^ j : Nat) : Int) := by
      rw [natCast_add, natCast_mul, natCast_pow2]
      rfl
    rw [hacc]
    exact affineCarryAuxInt_ofNat rest (j + 1) (3 * acc + 2 ^ j)

theorem affineCarryInt_ofNat (u : List Bool) :
    affineCarryInt u = (affineCarry u : Int) :=
  affineCarryAuxInt_ofNat u 0 0

/--
  Theorem 29.1b (General `(a, b)`-Affine Backward Merger Sieve Step):
  Whenever `collatzIter K n` satisfies the 3-adic backward congruence
    `(2^|u| * collatzIter K n - C(u)) % 3^w(u) = 0`
  and the Archimedean window
    `3^w(u) + C(u) <= 2^|u| * collatzIter K n < 3^w(u) * n + C(u)`,
  the strictly smaller positive integer `nPrime = (2^|u| * collatzIter K n - C(u)) / 3^w(u)`
  (`1 <= nPrime < n`) merges identically with `n` in `|u|` compressed steps:
    `collatzIter |u| nPrime = collatzIter K n`!
-/
theorem general_affine_backward_merger_step (n K : Nat) (u : List Bool)
    (hlo : 3 ^ parityWeight u + affineCarry u ≤ 2 ^ u.length * collatzIter K n)
    (hhi : 2 ^ u.length * collatzIter K n < 3 ^ parityWeight u * n + affineCarry u)
    (hdiv : (2 ^ u.length * collatzIter K n - affineCarry u) % 3 ^ parityWeight u = 0) :
    let nPrime := (2 ^ u.length * collatzIter K n - affineCarry u) / 3 ^ parityWeight u
    1 ≤ nPrime ∧ nPrime < n ∧ collatzIter u.length nPrime = collatzIter K n := by
  dsimp only
  let P3 := 3 ^ parityWeight u
  let Y := 2 ^ u.length * collatzIter K n
  let C := affineCarry u
  let nPrime := (Y - C) / P3
  have hP3_pos : P3 ≥ 1 := pow3_pos_nat (parityWeight u)
  have hd : P3 * nPrime = Y - C := by
    have hdm := Nat.div_add_mod (Y - C) P3
    rw [hdiv] at hdm
    dsimp [nPrime]
    omega
  have hp_pos : 1 ≤ nPrime := by
    cases hp : nPrime with
    | zero =>
      rw [hp, Nat.mul_zero] at hd
      dsimp [P3, Y, C] at hP3_pos hd
      omega
    | succ _ => omega
  have hp_lt : nPrime < n := by
    apply Classical.byContradiction
    intro hge
    have hm : P3 * n ≤ P3 * nPrime := Nat.mul_le_mul_left P3 (by omega)
    dsimp [P3, Y, C] at hm hd
    omega
  have heq_nat : 2 ^ u.length * collatzIter K n = 3 ^ parityWeight u * nPrime + affineCarry u := by
    dsimp [P3, Y, C] at hd
    omega
  have heq_int :
      (2 : Int) ^ u.length * (collatzIter K n : Int) =
        (3 : Int) ^ parityWeight u * (nPrime : Int) + affineCarryInt u := by
    have hc : ((2 ^ u.length * collatzIter K n : Nat) : Int) =
        ((3 ^ parityWeight u * nPrime + affineCarry u : Nat) : Int) :=
      congrArg Int.ofNat heq_nat
    rw [natCast_mul, natCast_pow2, natCast_add, natCast_mul, natCast_pow3,
        ← affineCarryInt_ofNat] at hc
    exact hc
  rcases general_affine_converse_universal u (nPrime : Int) (collatzIter K n : Int) heq_int with
    ⟨_, hiter⟩
  rw [collatzIterInt_ofNat] at hiter
  have hcoal : collatzIter u.length nPrime = collatzIter K n := by omega
  exact ⟨hp_pos, hp_lt, hcoal⟩

/--
  Theorem 29.1c (Minimal-Counterexample Exclusion for General `(a, b)`-Affine Mergers):
  No minimal non-descending counterexample `nMin > 1` can ever enter ANY backward merger
  congruence class `(2^|u| * T^K(nMin) - C(u)) % 3^w(u) = 0` inside `[3^w(u) + C(u), 3^w(u)*nMin + C(u))`!
-/
theorem minimal_counterexample_general_backward_merger_exclusion
    (nMin K : Nat) (u : List Bool)
    (hnMin : nMin > 1)
    (hnoDesc : ∀ k : Nat, ¬ (0 < collatzIter k nMin ∧ collatzIter k nMin < nMin))
    (hminReach : ∀ m : Nat, 1 ≤ m -> m < nMin -> ∃ k1 : Nat, collatzIter k1 m = 1)
    (hlo : 3 ^ parityWeight u + affineCarry u ≤ 2 ^ u.length * collatzIter K nMin)
    (hhi : 2 ^ u.length * collatzIter K nMin < 3 ^ parityWeight u * nMin + affineCarry u)
    (hdiv : (2 ^ u.length * collatzIter K nMin - affineCarry u) % 3 ^ parityWeight u = 0) :
    False := by
  rcases general_affine_backward_merger_step nMin K u hlo hhi hdiv with ⟨hp_lo, hp_lt, hcoal⟩
  let nPrime := (2 ^ u.length * collatzIter K nMin - affineCarry u) / 3 ^ parityWeight u
  exact strict_descent_minimal_counterexample_coalescence_contradiction
    nMin nPrime K u.length hnMin hp_lo hp_lt hnoDesc (hminReach nPrime hp_lo hp_lt) hcoal.symm

/--
  Theorem 29.2a (Mod-3 & Mod-12 Rigidity of `nMin`):
  Taking `K = 0` and `u = [true]` (`nPrime = (2 * nMin - 1) / 3`) eliminates `nMin % 3 = 2`,
  refining `nMin % 4 = 3` (`minimal_counterexample_mod4_eq_3`) to `nMin % 12 in {3, 7}`!
-/
theorem minimal_counterexample_mod3_ne_2 (nMin : Nat)
    (hnMin : nMin > 1)
    (hnoDesc : ∀ k : Nat, ¬ (0 < collatzIter k nMin ∧ collatzIter k nMin < nMin))
    (hminReach : ∀ m : Nat, 1 ≤ m -> m < nMin -> ∃ k1 : Nat, collatzIter k1 m = 1) :
    nMin % 3 ≠ 2 := by
  intro hmod
  have hlo : 3 ^ parityWeight [true] + affineCarry [true] ≤ 2 ^ [true].length * collatzIter 0 nMin := by
    simp [parityWeight, affineCarry, affineCarryAux, collatzIter]
    omega
  have hhi : 2 ^ [true].length * collatzIter 0 nMin < 3 ^ parityWeight [true] * nMin + affineCarry [true] := by
    simp [parityWeight, affineCarry, affineCarryAux, collatzIter]
    omega
  have hdiv : (2 ^ [true].length * collatzIter 0 nMin - affineCarry [true]) % 3 ^ parityWeight [true] = 0 := by
    simp [parityWeight, affineCarry, affineCarryAux, collatzIter]
    omega
  exact minimal_counterexample_general_backward_merger_exclusion
    nMin 0 [true] hnMin hnoDesc hminReach hlo hhi hdiv

theorem minimal_counterexample_mod12_in_3_or_7 (nMin : Nat)
    (hnMin : nMin > 1)
    (hnoDesc : ∀ k : Nat, ¬ (0 < collatzIter k nMin ∧ collatzIter k nMin < nMin))
    (hminReach : ∀ m : Nat, 1 ≤ m -> m < nMin -> ∃ k1 : Nat, collatzIter k1 m = 1) :
    nMin % 12 = 3 ∨ nMin % 12 = 7 := by
  have hp1 : collatzIter 1 nMin > 0 := collatzIter_pos 1 nMin (by omega)
  have hp2 : collatzIter 2 nMin > 0 := collatzIter_pos 2 nMin (by omega)
  have h1 : collatzIter 1 nMin ≥ nMin := by
    have hnd := hnoDesc 1
    omega
  have h2 : collatzIter 2 nMin ≥ nMin := by
    have hnd := hnoDesc 2
    omega
  have hm4 := minimal_counterexample_mod4_eq_3 nMin hnMin h1 h2
  have hm3 := minimal_counterexample_mod3_ne_2 nMin hnMin hnoDesc hminReach
  omega

/--
  Theorem 29.2b (Mod-9 Rigidity `nMin % 9 != 4`, Eliminating `31 mod 36`):
  Taking `K = 0` and `u = [true, true, false]` (`|u| = 3, w = 2, C(u) = 5`,
  `nPrime = (8 * nMin - 5) / 9`) eliminates `nMin % 9 = 4` across ALL `nMin > 1`!
-/
theorem minimal_counterexample_mod9_ne_4 (nMin : Nat)
    (hnMin : nMin > 1)
    (hnoDesc : ∀ k : Nat, ¬ (0 < collatzIter k nMin ∧ collatzIter k nMin < nMin))
    (hminReach : ∀ m : Nat, 1 ≤ m -> m < nMin -> ∃ k1 : Nat, collatzIter k1 m = 1) :
    nMin % 9 ≠ 4 := by
  intro hmod
  let u : List Bool := [true, true, false]
  have hu_w : parityWeight u = 2 := rfl
  have hu_l : u.length = 3 := rfl
  have hu_c : affineCarry u = 5 := rfl
  have hlo : 3 ^ parityWeight u + affineCarry u ≤ 2 ^ u.length * collatzIter 0 nMin := by
    rw [hu_w, hu_l, hu_c]
    simp only [collatzIter]
    omega
  have hhi : 2 ^ u.length * collatzIter 0 nMin < 3 ^ parityWeight u * nMin + affineCarry u := by
    rw [hu_w, hu_l, hu_c]
    simp only [collatzIter]
    omega
  have hdiv : (2 ^ u.length * collatzIter 0 nMin - affineCarry u) % 3 ^ parityWeight u = 0 := by
    rw [hu_w, hu_l, hu_c]
    simp only [collatzIter]
    omega
  exact minimal_counterexample_general_backward_merger_exclusion
    nMin 0 u hnMin hnoDesc hminReach hlo hhi hdiv

/--
  Theorem 29.2b' (Combined Mod-36 Rigidity — `5 / 36` Surviving Residue Classes):
  Combining `minimal_counterexample_mod12_in_3_or_7` (`nMin % 12 ∈ {3, 7}`) and
  `minimal_counterexample_mod9_ne_4` (`nMin % 9 ≠ 4`, eliminating `31 mod 36`),
  every minimal counterexample `nMin > 1` lies in `{3, 7, 15, 19, 27} mod 36`!
-/
theorem minimal_counterexample_mod36_in_5_classes (nMin : Nat)
    (hnMin : nMin > 1)
    (hnoDesc : ∀ k : Nat, ¬ (0 < collatzIter k nMin ∧ collatzIter k nMin < nMin))
    (hminReach : ∀ m : Nat, 1 ≤ m -> m < nMin -> ∃ k1 : Nat, collatzIter k1 m = 1) :
    nMin % 36 = 3 ∨ nMin % 36 = 7 ∨ nMin % 36 = 15 ∨ nMin % 36 = 19 ∨ nMin % 36 = 27 := by
  have hm12 := minimal_counterexample_mod12_in_3_or_7 nMin hnMin hnoDesc hminReach
  have hm9 := minimal_counterexample_mod9_ne_4 nMin hnMin hnoDesc hminReach
  omega

/--
  Theorem 29.2c (Sub-`3/2` & Sub-`9/4` Orbit-Return Backward Merger Steps):
  Along ANY step `K`, `x = collatzIter K nMin` merges strictly below `nMin` whenever:
  - `2 * x <= 3 * nMin` and `x % 3 = 2` (`u = [true]`, `nPrime = (2 * x - 1) / 3`), OR
  - `4 * x <= 9 * nMin` and `x % 9 = 8` (`u = [true, true]`, `nPrime = (4 * x - 5) / 9`)!
-/
theorem sub_3_2_backward_merger_step (nMin K : Nat)
    (hx_ge2 : collatzIter K nMin ≥ 2)
    (hx_mod3 : collatzIter K nMin % 3 = 2)
    (hx_sub : 2 * collatzIter K nMin ≤ 3 * nMin) :
    let nPrime := (2 * collatzIter K nMin - 1) / 3
    1 ≤ nPrime ∧ nPrime < nMin ∧ collatzIter 1 nPrime = collatzIter K nMin := by
  have h := general_affine_backward_merger_step nMin K [true]
    (by simp [parityWeight, affineCarry, affineCarryAux]; omega)
    (by simp [parityWeight, affineCarry, affineCarryAux]; omega)
    (by simp [parityWeight, affineCarry, affineCarryAux]; omega)
  simpa [parityWeight, affineCarry, affineCarryAux] using h

theorem sub_9_4_backward_merger_step (nMin K : Nat)
    (hx_mod9 : collatzIter K nMin % 9 = 8)
    (hx_sub : 4 * collatzIter K nMin ≤ 9 * nMin) :
    let nPrime := (4 * collatzIter K nMin - 5) / 9
    1 ≤ nPrime ∧ nPrime < nMin ∧ collatzIter 2 nPrime = collatzIter K nMin := by
  let u : List Bool := [true, true]
  have h := general_affine_backward_merger_step nMin K u
    (by change 9 + 5 ≤ 4 * collatzIter K nMin; omega)
    (by change 4 * collatzIter K nMin < 9 * nMin + 5; omega)
    (by change (4 * collatzIter K nMin - 5) % 9 = 0; omega)
  simpa [u, parityWeight, affineCarry, affineCarryAux] using h

theorem affineCarryInt_eq_zero_of_weight_zero : ∀ (u : List Bool),
    parityWeight u = 0 -> affineCarryInt u = 0
  | [], _ => rfl
  | false :: rest, hw => by
    have hc : affineCarryInt (false :: rest) = 2 * affineCarryInt rest := by
      unfold affineCarryInt
      simp only [affineCarryAuxInt]
      have h01 : 0 + 1 = 1 := rfl
      rw [h01, affineCarryAuxInt_shift rest 1 0]
      omega
    rw [hc, affineCarryInt_eq_zero_of_weight_zero rest hw]
    rfl
  | true :: rest, hw => by
    simp [parityWeight] at hw

/--
  Theorem 29.3 (The `0 mod 3` Garden-of-Eden Carry Trap):
  For EVERY parity word `u` of positive weight `parityWeight u >= 1`,
  `affineCarryInt u > 0` and `affineCarryInt u % 3 != 0`!
  Consequently, whenever `x % 3 = 0`, NO positive-weight backward merger word `u`
  can ever divide `2^|u| * x - C(u)` by `3^w(u)` (preventing single-return 3-adic
  merger survival density from decaying to `0`).
-/
theorem affineCarryInt_pos_nondiv3_of_weight_pos : ∀ (u : List Bool),
    parityWeight u ≥ 1 -> affineCarryInt u > 0 ∧ affineCarryInt u % 3 ≠ 0
  | [], hw => by simp [parityWeight] at hw
  | false :: rest, hw => by
    simp only [parityWeight] at hw
    rcases affineCarryInt_pos_nondiv3_of_weight_pos rest hw with ⟨hpos, hmod⟩
    have hc : affineCarryInt (false :: rest) = 2 * affineCarryInt rest := by
      unfold affineCarryInt
      simp only [affineCarryAuxInt]
      have h01 : 0 + 1 = 1 := rfl
      rw [h01, affineCarryAuxInt_shift rest 1 0]
      omega
    rw [hc]
    exact ⟨by omega, by omega⟩
  | true :: rest, _ => by
    have hc : affineCarryInt (true :: rest) =
        (3 : Int) ^ parityWeight rest + 2 * affineCarryInt rest := by
      unfold affineCarryInt
      simp only [affineCarryAuxInt]
      have h10 : 3 * (0 : Int) + (2 : Int) ^ 0 = 1 := rfl
      have h01 : 0 + 1 = 1 := rfl
      rw [h01, h10, affineCarryAuxInt_shift rest 1 1]
      omega
    rw [hc]
    cases hw_rest : parityWeight rest with
    | zero =>
      have hz := affineCarryInt_eq_zero_of_weight_zero rest hw_rest
      rw [hz]
      exact ⟨by decide, by decide⟩
    | succ w' =>
      rcases affineCarryInt_pos_nondiv3_of_weight_pos rest (by omega) with ⟨hpos, hmod⟩
      have hp3_pos : (3 : Int) ^ (w' + 1) ≥ 3 := by
        have hp_nat : 3 ^ w' ≥ 1 := pow3_pos_nat w'
        have hp_int : (3 : Int) ^ w' ≥ 1 := by
          rw [← natCast_pow3 w']
          omega
        rw [Int.pow_succ]
        omega
      have hp3_div3 : ((3 : Int) ^ (w' + 1)) % 3 = 0 := by
        rw [Int.pow_succ]
        omega
      exact ⟨by omega, by omega⟩

theorem garden_of_eden_div3_unmergeable (x : Nat) (u : List Bool)
    (hx_div3 : x % 3 = 0)
    (hw : parityWeight u ≥ 1)
    (hle : affineCarry u ≤ 2 ^ u.length * x) :
    (2 ^ u.length * x - affineCarry u) % 3 ^ parityWeight u ≠ 0 := by
  intro hdiv
  rcases affineCarryInt_pos_nondiv3_of_weight_pos u hw with ⟨_, hc_mod3⟩
  rw [affineCarryInt_ofNat] at hc_mod3
  have hc_nat_mod3 : affineCarry u % 3 ≠ 0 := by omega
  have hP3_eq : 3 ^ parityWeight u = 3 * 3 ^ (parityWeight u - 1) := by
    conv => lhs; rw [show parityWeight u = (parityWeight u - 1) + 1 by omega]
    rw [Nat.pow_succ, Nat.mul_comm]
  have hdm := Nat.div_add_mod (2 ^ u.length * x - affineCarry u) (3 ^ parityWeight u)
  rw [hdiv, Nat.add_zero, hP3_eq, Nat.mul_assoc] at hdm
  have hdiff_mod3 : (2 ^ u.length * x - affineCarry u) % 3 = 0 := by
    rw [← hdm]
    omega
  have hx_mul3 : (2 ^ u.length * x) % 3 = 0 := by
    rw [Nat.mul_mod, hx_div3]
    simp
  omega

theorem parityWeight_le_length : ∀ (v : List Bool), parityWeight v ≤ v.length
  | [] => Nat.le_refl 0
  | false :: rest => by
    have ih := parityWeight_le_length rest
    simp only [parityWeight, List.length_cons]
    omega
  | true :: rest => by
    have ih := parityWeight_le_length rest
    simp only [parityWeight, List.length_cons]
    omega

theorem nat_lt_pow2 : ∀ (k : Nat), k < 2 ^ k
  | 0 => by decide
  | k + 1 => by
    have ih := nat_lt_pow2 k
    have hp := pow2_pos_nat k
    rw [Nat.pow_succ]
    omega

/--
  Theorem 29.4a (Initial-Bit Exhaustion Forces `T^|v|(nMin) < 3^w(v)`):
  Once step count `|v|` exhausts the initial binary bits of `nMin` (`2 * nMin <= 2^|v|`,
  i.e., `|v| >= floor(log_2 nMin) + 2`), EVERY surviving prefix `v` (`SurvivingFrom 0 0 v`)
  automatically satisfies `3 * nMin + w(v) < 3 * 2^|v|` and hence `y < 3^w(v)`!
-/
theorem initial_bit_exhaustion_iter_lt_pow3 (v : List Bool) (nMin y : Nat)
    (hsurv : SurvivingFrom 0 0 v)
    (hbit : 2 * nMin ≤ 2 ^ v.length)
    (hdec : 2 ^ v.length * y = 3 ^ parityWeight v * nMin + affineCarry v) :
    y < 3 ^ parityWeight v := by
  have hw_le : parityWeight v ≤ v.length := parityWeight_le_length v
  have hk_lt : v.length < 2 ^ v.length := nat_lt_pow2 v.length
  have harch : 3 * nMin + parityWeight v < 3 * 2 ^ v.length := by omega
  exact surviving_prefix_iter_lt_pow3 v nMin y hsurv hdec harch

/--
  Theorem 29.4b (Bounded Minimal Counterexample Yields a Non-Trivial Positive Cycle):
  Any minimal non-descending counterexample `nMin > 1` whose compressed forward trajectory
  is bounded above by `B` (`∀ k, collatzIter k nMin <= B`) necessarily enters a non-trivial
  positive cycle `x >= nMin > 2` (`collatzIter p x = x`, `p >= 1`, `x != 1`, `x != 2`),
  directly contradicting `NoNontrivialPositiveCycles`!
-/
theorem minimal_counterexample_gt_two (nMin : Nat)
    (hnMin : nMin > 1)
    (hnoDesc : ∀ K : Nat, ¬ (0 < collatzIter K nMin ∧ collatzIter K nMin < nMin)) :
    nMin > 2 := by
  by_cases heq2 : nMin = 2
  · subst heq2
    exact False.elim (hnoDesc 1 ⟨by decide, by decide⟩)
  · omega

theorem bounded_minimal_counterexample_implies_nontrivial_cycle (nMin B : Nat)
    (hnMin : nMin > 1)
    (hnoDesc : ∀ K : Nat, ¬ (0 < collatzIter K nMin ∧ collatzIter K nMin < nMin))
    (hbdd : ∀ k : Nat, collatzIter k nMin ≤ B) :
    ∃ x p : Nat, x ≥ nMin ∧ x ≤ B ∧ p ≥ 1 ∧ collatzIter p x = x ∧ x ≠ 1 ∧ x ≠ 2 := by
  have hgt2 : nMin > 2 := minimal_counterexample_gt_two nMin hnMin hnoDesc
  rcases bounded_seq_repeats B (fun k => collatzIter k nMin) hbdd with ⟨i, j, hij, heq⟩
  let x := collatzIter i nMin
  let p := j - i
  have hsplit : j = i + p := by dsimp [p]; omega
  rw [hsplit, collatzIter_add] at heq
  have hx_pos : x > 0 := collatzIter_pos i nMin (by omega)
  have hx_ge : x ≥ nMin := by
    have hnd := hnoDesc i
    dsimp [x]
    omega
  exact ⟨x, p, hx_ge, hbdd i, by dsimp [p]; omega, heq.symm, by omega, by omega⟩


-- ============================================================================
-- SECTION 17: Theorem 30 — Multi-Root Disjoint Inverse Syracuse Forest on
--             `[5, nMin - 1]` & Carry Collision Sufficiency for Collatz
-- ============================================================================

/--
  Coordinator Trap 1 Falsification Witness (`syracuseTree_overlap_witnesses`):
  Naively rooting inverse Syracuse trees at ALL odd `y_0 >= 5` with `y_0 % 3 != 0`
  violates tree disjointness (`13 = syracuseChild 5 false`, `7 = syracuseChild 11 false`)!
-/
theorem syracuseTree_overlap_witnesses :
    syracuseChild 5 false = 13 ∧ syracuseChild 11 false = 7 := by
  decide

/--
  Exact In-Degree-`0` Root Predicate for the Disjoint Multi-Root Inverse Syracuse Forest:
  Among odd non-multiples of `3` in `[5, infty)`, `r` has ZERO `syracuseChild` parents in
  `[5, infty)` IF AND ONLY IF `r = 5` (whose parent is `1 < 5`) OR `(3 * r + 1) % 128 = 0`
  (requiring 2-adic valuation `d >= 7 > 6`)!
-/
def IsSyracuseForestRoot (r : Nat) : Prop :=
  r ≥ 5 ∧ r % 2 = 1 ∧ r % 3 ≠ 0 ∧ (r = 5 ∨ (3 * r + 1) % 128 = 0)

theorem syracuseChild_of_step (x y d : Nat)
    (hx_ge5 : x ≥ 5) (hx_non3 : x % 3 ≠ 0)
    (hd_lo : 1 ≤ d) (hd_hi : d ≤ 6)
    (hy_odd : y % 2 = 1)
    (hsyr : 3 * x + 1 = 2 ^ d * y)
    (hne5 : x ≠ 5) :
    ∃ b : Bool, y ≥ 5 ∧ y % 3 ≠ 0 ∧ syracuseChild y b = x := by
  have hy_non3 : y % 3 ≠ 0 := by
    intro hy3
    rcases (by omega : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6) with
      rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have hy_ge5 : y ≥ 5 := by
    apply Classical.byContradiction
    intro hlt5
    have hy1 : y = 1 := by
      rcases (by omega : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6) with
        rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    subst hy1
    rcases (by omega : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6) with
      rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have hd_match : syracuseValidExp y false = d ∨ syracuseValidExp y true = d := by
    have hm9 : y % 9 = 1 ∨ y % 9 = 2 ∨ y % 9 = 4 ∨ y % 9 = 5 ∨ y % 9 = 7 ∨ y % 9 = 8 := by omega
    rcases hm9 with h9 | h9 | h9 | h9 | h9 | h9
    · have hf : syracuseValidExp y false = 2 := by unfold syracuseValidExp; rw [h9]; decide
      have ht : syracuseValidExp y true = 4 := by unfold syracuseValidExp; rw [h9]; decide
      rw [hf, ht]
      rcases (by omega : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6) with
        rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    · have hf : syracuseValidExp y false = 1 := by unfold syracuseValidExp; rw [h9]; decide
      have ht : syracuseValidExp y true = 3 := by unfold syracuseValidExp; rw [h9]; decide
      rw [hf, ht]
      rcases (by omega : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6) with
        rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    · have hf : syracuseValidExp y false = 2 := by unfold syracuseValidExp; rw [h9]; decide
      have ht : syracuseValidExp y true = 6 := by unfold syracuseValidExp; rw [h9]; decide
      rw [hf, ht]
      rcases (by omega : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6) with
        rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    · have hf : syracuseValidExp y false = 3 := by unfold syracuseValidExp; rw [h9]; decide
      have ht : syracuseValidExp y true = 5 := by unfold syracuseValidExp; rw [h9]; decide
      rw [hf, ht]
      rcases (by omega : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6) with
        rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    · have hf : syracuseValidExp y false = 4 := by unfold syracuseValidExp; rw [h9]; decide
      have ht : syracuseValidExp y true = 6 := by unfold syracuseValidExp; rw [h9]; decide
      rw [hf, ht]
      rcases (by omega : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6) with
        rfl | rfl | rfl | rfl | rfl | rfl <;> omega
    · have hf : syracuseValidExp y false = 1 := by unfold syracuseValidExp; rw [h9]; decide
      have ht : syracuseValidExp y true = 5 := by unfold syracuseValidExp; rw [h9]; decide
      rw [hf, ht]
      rcases (by omega : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6) with
        rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  rcases hd_match with hf | ht
  · exact ⟨false, hy_ge5, hy_non3, by unfold syracuseChild; rw [hf]; omega⟩
  · exact ⟨true, hy_ge5, hy_non3, by unfold syracuseChild; rw [ht]; omega⟩

theorem even_not_div128_factor (n : Nat) (heven : n % 2 = 0) (hn128 : n % 128 ≠ 0) :
    ∃ d y : Nat, 1 ≤ d ∧ d ≤ 6 ∧ y % 2 = 1 ∧ n = 2 ^ d * y := by
  have hm1 : n = 2 * (n / 2) := by omega
  generalize n / 2 = m1 at hm1
  clear heven
  by_cases h1 : m1 % 2 = 1
  · exact ⟨1, m1, by decide, by decide, h1, by simpa using hm1⟩
  · have hm2 : n = 4 * (m1 / 2) := by omega
    generalize m1 / 2 = m2 at hm2
    clear hm1 h1
    by_cases h2 : m2 % 2 = 1
    · exact ⟨2, m2, by decide, by decide, h2, by simpa using hm2⟩
    · have hm3 : n = 8 * (m2 / 2) := by omega
      generalize m2 / 2 = m3 at hm3
      clear hm2 h2
      by_cases h3 : m3 % 2 = 1
      · exact ⟨3, m3, by decide, by decide, h3, by simpa using hm3⟩
      · have hm4 : n = 16 * (m3 / 2) := by omega
        generalize m3 / 2 = m4 at hm4
        clear hm3 h3
        by_cases h4 : m4 % 2 = 1
        · exact ⟨4, m4, by decide, by decide, h4, by simpa using hm4⟩
        · have hm5 : n = 32 * (m4 / 2) := by omega
          generalize m4 / 2 = m5 at hm5
          clear hm4 h4
          by_cases h5 : m5 % 2 = 1
          · exact ⟨5, m5, by decide, by decide, h5, by simpa using hm5⟩
          · have hm6 : n = 64 * (m5 / 2) := by omega
            generalize m5 / 2 = m6 at hm6
            clear hm5 h5
            have h6 : m6 % 2 = 1 := by omega
            exact ⟨6, m6, by decide, by decide, h6, by simpa using hm6⟩

/--
  Theorem 30.1a (Exact Bijective Characterization of In-Degree-`0` Forest Roots):
  For ANY `x >= 5` with `x % 2 = 1` and `x % 3 != 0`, `IsSyracuseForestRoot x` holds
  IF AND ONLY IF `x` is NEVER `syracuseChild y b` for any `y >= 5, y % 2 = 1, y % 3 != 0`!
-/
theorem syracuseForestRoot_iff_not_child (x : Nat)
    (hx_ge5 : x ≥ 5) (hx_odd : x % 2 = 1) (hx_non3 : x % 3 ≠ 0) :
    IsSyracuseForestRoot x ↔
      ∀ (y : Nat) (b : Bool), y ≥ 5 -> y % 2 = 1 -> y % 3 ≠ 0 -> syracuseChild y b ≠ x := by
  constructor
  · intro hroot y b hy_ge5 hy_odd hy_non3 hchild
    rcases hroot with ⟨_, _, _, hr_cases⟩
    have hp := syracuseChild_props y b hy_ge5 hy_odd hy_non3
    have hd_lo : 1 ≤ syracuseValidExp y b := hp.1
    have hd_hi : syracuseValidExp y b ≤ 6 := hp.2.1
    have hsyr : 3 * x + 1 = 2 ^ syracuseValidExp y b * y := by
      have h3 := hp.2.2.1
      rw [hchild] at h3
      exact h3
    rcases hr_cases with rfl | h128
    · have h5 : 2 ^ 4 * 1 = 2 ^ syracuseValidExp y b * y := by omega
      rcases syracuse_step_unique 4 (syracuseValidExp y b) 1 y (by decide) hy_odd h5 with ⟨_, hy1⟩
      omega
    · rcases (by omega :
          syracuseValidExp y b = 1 ∨ syracuseValidExp y b = 2 ∨ syracuseValidExp y b = 3 ∨
          syracuseValidExp y b = 4 ∨ syracuseValidExp y b = 5 ∨ syracuseValidExp y b = 6) with
        hd | hd | hd | hd | hd | hd <;> rw [hd] at hsyr <;> omega
  · intro hnot
    refine ⟨hx_ge5, hx_odd, hx_non3, ?_⟩
    apply Classical.byContradiction
    intro hnor
    have hne5 : x ≠ 5 := fun h5 => hnor (Or.inl h5)
    have hn128 : (3 * x + 1) % 128 ≠ 0 := fun h128 => hnor (Or.inr h128)
    rcases even_not_div128_factor (3 * x + 1) (by omega) hn128 with
      ⟨d, y, hd_lo, hd_hi, hy_odd, hsyr⟩
    rcases syracuseChild_of_step x y d hx_ge5 hx_non3 hd_lo hd_hi hy_odd hsyr hne5 with
      ⟨b, hy5, hyn3, hc⟩
    exact hnot y b hy5 hy_odd hyn3 hc

/-- Multi-root inverse Syracuse forest node at root `r` and binary choice sequence `cs` -/
def syracuseForestVal (r : Nat) : List Bool -> Nat
  | [] => r
  | b :: rest => syracuseChild (syracuseForestVal r rest) b

theorem syracuseForestVal_invariant (r : Nat) (hr : IsSyracuseForestRoot r) :
    ∀ (cs : List Bool),
      syracuseForestVal r cs ≥ 5 ∧
      syracuseForestVal r cs % 2 = 1 ∧
      syracuseForestVal r cs % 3 ≠ 0
  | [] => ⟨hr.1, hr.2.1, hr.2.2.1⟩
  | b :: rest => by
    rcases syracuseForestVal_invariant r hr rest with ⟨hge, hodd, hnon3⟩
    have hp := syracuseChild_props (syracuseForestVal r rest) b hge hodd hnon3
    simp only [syracuseForestVal]
    exact ⟨hp.2.2.2.1, hp.2.2.2.2.1, hp.2.2.2.2.2⟩

/--
  Theorem 30.1b (Global Pairwise-Disjoint Multi-Root Forest Injectivity):
  Across ALL roots `r1, r2` satisfying `IsSyracuseForestRoot` and ALL unbounded-depth
  binary choice words `cs1, cs2 : List Bool`, `syracuseForestVal r1 cs1 = syracuseForestVal r2 cs2`
  forces BOTH `r1 = r2` AND `cs1 = cs2`!
-/
theorem syracuseForestVal_injective :
    ∀ (cs1 cs2 : List Bool) (r1 r2 : Nat),
      IsSyracuseForestRoot r1 -> IsSyracuseForestRoot r2 ->
      syracuseForestVal r1 cs1 = syracuseForestVal r2 cs2 ->
      r1 = r2 ∧ cs1 = cs2
  | [], [], r1, r2, _, _, heq => ⟨heq, rfl⟩
  | [], b2 :: rest2, r1, r2, hr1, hr2, heq => by
    rcases syracuseForestVal_invariant r2 hr2 rest2 with ⟨hge2, hodd2, hnon3_2⟩
    have hnot := (syracuseForestRoot_iff_not_child r1 hr1.1 hr1.2.1 hr1.2.2.1).mp hr1
    exact False.elim (hnot (syracuseForestVal r2 rest2) b2 hge2 hodd2 hnon3_2 heq.symm)
  | b1 :: rest1, [], r1, r2, hr1, hr2, heq => by
    rcases syracuseForestVal_invariant r1 hr1 rest1 with ⟨hge1, hodd1, hnon3_1⟩
    have hnot := (syracuseForestRoot_iff_not_child r2 hr2.1 hr2.2.1 hr2.2.2.1).mp hr2
    exact False.elim (hnot (syracuseForestVal r1 rest1) b1 hge1 hodd1 hnon3_1 heq)
  | b1 :: rest1, b2 :: rest2, r1, r2, hr1, hr2, heq => by
    rcases syracuseForestVal_invariant r1 hr1 rest1 with ⟨hge1, hodd1, hnon3_1⟩
    rcases syracuseForestVal_invariant r2 hr2 rest2 with ⟨hge2, hodd2, hnon3_2⟩
    have hp1 := syracuseChild_props (syracuseForestVal r1 rest1) b1 hge1 hodd1 hnon3_1
    have hp2 := syracuseChild_props (syracuseForestVal r2 rest2) b2 hge2 hodd2 hnon3_2
    simp only [syracuseForestVal] at heq
    have h2eq :
        2 ^ syracuseValidExp (syracuseForestVal r1 rest1) b1 * syracuseForestVal r1 rest1 =
        2 ^ syracuseValidExp (syracuseForestVal r2 rest2) b2 * syracuseForestVal r2 rest2 := by
      have h3x1 := hp1.2.2.1
      have h3x2 := hp2.2.2.1
      rw [heq] at h3x1
      omega
    rcases syracuse_step_unique
      (syracuseValidExp (syracuseForestVal r1 rest1) b1)
      (syracuseValidExp (syracuseForestVal r2 rest2) b2)
      (syracuseForestVal r1 rest1) (syracuseForestVal r2 rest2)
      hodd1 hodd2 h2eq with ⟨hd_eq, hy_eq⟩
    rcases syracuseForestVal_injective rest1 rest2 r1 r2 hr1 hr2 hy_eq with ⟨hr_eq, hcs_eq⟩
    subst hr_eq
    subst hcs_eq
    have hb_eq : b1 = b2 := by
      have hlt := syracuseValidExp_lt (syracuseForestVal r1 rest1)
      cases b1 <;> cases b2 <;> simp at hd_eq ⊢ <;> omega
    exact ⟨rfl, by rw [hb_eq]⟩

/--
  Theorem 30.1c (Coordinator Trap 2 Corrected Multi-Root Scaling Bound):
  Every forest node at root `r` (`IsSyracuseForestRoot r`) and depth `w = cs.length`
  satisfies `3^w * syracuseForestVal r cs <= 2^(6 * w) * r` (scaling in `X / r`,
  resolving the Pigeonhole violation at `X = nMin` where `2^w <= (X / r)^{1/(6 - log_2 3)}`).
-/
theorem syracuseForestVal_upper_bound (r : Nat) (hr : IsSyracuseForestRoot r) :
    ∀ (cs : List Bool),
      3 ^ cs.length * syracuseForestVal r cs ≤ 2 ^ (6 * cs.length) * r
  | [] => by simp [syracuseForestVal]
  | b :: rest => by
    have ih := syracuseForestVal_upper_bound r hr rest
    rcases syracuseForestVal_invariant r hr rest with ⟨hge, hodd, hnon3⟩
    have hp := syracuseChild_props (syracuseForestVal r rest) b hge hodd hnon3
    simp only [syracuseForestVal, List.length_cons]
    have hp2d : 2 ^ syracuseValidExp (syracuseForestVal r rest) b ≤ 64 := by
      have hm := pow2_mono_nat hp.2.1
      simpa using hm
    have h3x : 3 * syracuseChild (syracuseForestVal r rest) b ≤ 64 * syracuseForestVal r rest := by
      have hm := Nat.mul_le_mul_right (syracuseForestVal r rest) hp2d
      have hs := hp.2.2.1
      omega
    have hstep :
        3 ^ (rest.length + 1) * syracuseChild (syracuseForestVal r rest) b ≤
          64 * (3 ^ rest.length * syracuseForestVal r rest) := by
      rw [Nat.pow_succ, Nat.mul_assoc]
      have hm3 := Nat.mul_le_mul_left (3 ^ rest.length) h3x
      rw [← Nat.mul_assoc (3 ^ rest.length) 64, Nat.mul_comm (3 ^ rest.length) 64,
          Nat.mul_assoc 64] at hm3
      exact hm3
    have hrhs : 64 * (2 ^ (6 * rest.length) * r) = 2 ^ (6 * (rest.length + 1)) * r := by
      rw [show 6 * (rest.length + 1) = 6 * rest.length + 6 by omega,
          Nat.pow_add 2 (6 * rest.length) 6]
      have h26 : 2 ^ 6 = 64 := rfl
      rw [h26, Nat.mul_comm (2 ^ (6 * rest.length)) 64, Nat.mul_assoc]
    have hm64 := Nat.mul_le_mul_left 64 ih
    rw [hrhs] at hm64
    exact Nat.le_trans hstep hm64

theorem even_mul_pow2_iter : ∀ (k y : Nat), collatzIter k (2 ^ k * y) = y
  | 0, y => by simp [collatzIter]
  | k + 1, y => by
    have hmul : 2 ^ (k + 1) * y = 2 * (2 ^ k * y) := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2, Nat.mul_assoc]
    have hev : ((2 ^ (k + 1) * y) % 2 == 0) = true := decide_eq_true (by omega)
    have hstep : collatzStep (2 ^ (k + 1) * y) = 2 ^ k * y := by
      simp only [collatzStep, hev]
      simp
      omega
    simp only [collatzIter, hstep]
    exact even_mul_pow2_iter k y

theorem syracuse_child_reaches_parent (x y d : Nat)
    (hd : d ≥ 1) (hx_odd : x % 2 = 1) (hsyr : 3 * x + 1 = 2 ^ d * y) :
    collatzIter d x = y := by
  have hd_split : d = (d - 1) + 1 := by omega
  have hp2 : 2 ^ d * y = 2 * (2 ^ (d - 1) * y) := by
    conv => lhs; rw [hd_split]
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ (d - 1)) 2, Nat.mul_assoc]
  have hx_odd_b : (x % 2 == 0) = false := decide_eq_false (by omega)
  have hstep : collatzStep x = 2 ^ (d - 1) * y := by
    simp only [collatzStep, hx_odd_b]
    simp
    omega
  rw [hd_split, show (d - 1) + 1 = 1 + (d - 1) by omega, collatzIter_add]
  have h1 : collatzIter 1 x = 2 ^ (d - 1) * y := by simpa [collatzIter] using hstep
  rw [h1]
  exact even_mul_pow2_iter (d - 1) y

theorem syracuseForestVal_reaches_root (r : Nat) (hr : IsSyracuseForestRoot r) :
    ∀ (cs : List Bool),
      ∃ k : Nat, k ≤ 6 * cs.length ∧ collatzIter k (syracuseForestVal r cs) = r
  | [] => ⟨0, by simp, rfl⟩
  | b :: rest => by
    rcases syracuseForestVal_reaches_root r hr rest with ⟨kRest, hk_le, hk_eq⟩
    rcases syracuseForestVal_invariant r hr rest with ⟨hge, hodd, hnon3⟩
    have hp := syracuseChild_props (syracuseForestVal r rest) b hge hodd hnon3
    let d := syracuseValidExp (syracuseForestVal r rest) b
    have hstep := syracuse_child_reaches_parent
      (syracuseChild (syracuseForestVal r rest) b) (syracuseForestVal r rest) d
      hp.1 hp.2.2.2.2.1 hp.2.2.1
    refine ⟨d + kRest, ?_, ?_⟩
    · simp only [List.length_cons]
      have hd6 : d ≤ 6 := hp.2.1
      omega
    · simp only [syracuseForestVal]
      rw [collatzIter_add, hstep, hk_eq]

theorem coalescence_reaches_one (n z K kp kz : Nat)
    (hcoal : collatzIter K n = collatzIter kp z)
    (hz1 : collatzIter kz z = 1) :
    ∃ kn : Nat, collatzIter kn n = 1 := by
  by_cases hle : kp ≤ kz
  · refine ⟨K + (kz - kp), ?_⟩
    rw [collatzIter_add, hcoal, ← collatzIter_add, show kp + (kz - kp) = kz by omega, hz1]
  · have hsplit : kp = kz + (kp - kz) := by omega
    have htriv : collatzIter kp z = 1 ∨ collatzIter kp z = 2 := by
      rw [hsplit, collatzIter_add, hz1]
      exact collatzIter_trivial_cycle (kp - kz) 1 (Or.inl rfl)
    rcases htriv with h1 | h2
    · exact ⟨K, by rw [hcoal, h1]⟩
    · refine ⟨K + 1, ?_⟩
      rw [collatzIter_add, hcoal, h2]
      rfl

/--
  Open Mixing Hypothesis 30.2a (`BackwardCarryContractionWindowProp`):
  For every integer `n > 1`, some forward iterate `collatzIter K n` hits a 3-adic
  backward carry congruence `(2^|u| * T^K(n) - C(u)) % 3^w(u) = 0` inside the
  strictly contracting window `[3^w(u) + C(u), 3^w(u) * n + C(u))`.
  Falsified on `Q_(2)^+` (`19/5`), `Z^-` (`-17`), and `5n + 1` (`5`, `13`).
-/
def BackwardCarryContractionWindowProp : Prop :=
  ∀ n : Nat, n > 1 ->
    ∃ (K : Nat) (u : List Bool),
      3 ^ parityWeight u + affineCarry u ≤ 2 ^ u.length * collatzIter K n ∧
      2 ^ u.length * collatzIter K n < 3 ^ parityWeight u * n + affineCarry u ∧
      (2 ^ u.length * collatzIter K n - affineCarry u) % 3 ^ parityWeight u = 0

theorem backward_carry_window_reaches_one_aux : ∀ (fuel n : Nat),
    BackwardCarryContractionWindowProp -> 1 ≤ n -> n ≤ fuel + 1 ->
    ∃ kn : Nat, collatzIter kn n = 1
  | 0, n, _, hn1, hle => by
    have hn_eq : n = 1 := by omega
    subst hn_eq
    exact ⟨0, rfl⟩
  | fuel + 1, n, hprop, hn1, hle => by
    by_cases hn_eq1 : n = 1
    · subst hn_eq1
      exact ⟨0, rfl⟩
    · rcases hprop n (by omega) with ⟨K, u, hlo, hhi, hdiv⟩
      rcases general_affine_backward_merger_step n K u hlo hhi hdiv with ⟨hp_lo, hp_lt, hcoal⟩
      let nPrime := (2 ^ u.length * collatzIter K n - affineCarry u) / 3 ^ parityWeight u
      rcases backward_carry_window_reaches_one_aux fuel nPrime hprop hp_lo (by omega) with ⟨kz, hkz⟩
      exact coalescence_reaches_one n nPrime K u.length kz hcoal.symm hkz

/--
  Theorem 30.2a (`BackwardCarryContractionWindowProp -> CollatzConjectureStandard`):
  `BackwardCarryContractionWindowProp` unconditionally implies `CollatzConjectureStandard`!
-/
theorem backward_carry_window_mixing_implies_collatz_standard
    (hprop : BackwardCarryContractionWindowProp) :
    CollatzConjectureStandard := by
  rw [collatz_standard_iff_compressed]
  intro n hn
  exact backward_carry_window_reaches_one_aux n n hprop (by omega) (by omega)

/--
  Open Mixing Hypothesis 30.2b (`MultiRootForestCarryCollisionProp`):
  For every integer `n >= 6`, some forward iterate `collatzIter K n` collides via an
  affine backward word `u` with ANY node `z = syracuseForestVal r cs` (even `z >> n` of
  unbounded depth!) in the disjoint inverse Syracuse tree of SOME root `r in [5, n - 1]`.
  Falsified on `Q_(2)^+` (`19/5`), `Z^-` (`-17`), and `5n + 1` (`13`).
-/
def MultiRootForestCarryCollisionProp : Prop :=
  ∀ n : Nat, n ≥ 6 ->
    ∃ (K r : Nat) (cs u : List Bool),
      IsSyracuseForestRoot r ∧
      r < n ∧
      (2 : Int) ^ u.length * (collatzIter K n : Int) =
        (3 : Int) ^ parityWeight u * (syracuseForestVal r cs : Int) + affineCarryInt u

theorem small_n_le_5_reaches_one (n : Nat) (hn1 : 1 ≤ n) (hn5 : n ≤ 5) :
    ∃ k : Nat, collatzIter k n = 1 := by
  rcases (by omega : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5) with
    rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, by decide⟩
  · exact ⟨5, by decide⟩
  · exact ⟨2, by decide⟩
  · exact ⟨4, by decide⟩

theorem multi_root_forest_collision_reaches_one_aux : ∀ (fuel n : Nat),
    MultiRootForestCarryCollisionProp -> 1 ≤ n -> n ≤ fuel + 1 ->
    ∃ kn : Nat, collatzIter kn n = 1
  | 0, n, _, hn1, hle => by
    have hn_eq : n = 1 := by omega
    subst hn_eq
    exact ⟨0, rfl⟩
  | fuel + 1, n, hprop, hn1, hle => by
    by_cases hn5 : n ≤ 5
    · exact small_n_le_5_reaches_one n hn1 hn5
    · rcases hprop n (by omega) with ⟨K, r, cs, u, hr_root, hr_lt, heq_int⟩
      rcases general_affine_converse_universal u
        (syracuseForestVal r cs : Int) (collatzIter K n : Int) heq_int with ⟨_, hiter_int⟩
      rw [collatzIterInt_ofNat] at hiter_int
      have hcoal : collatzIter K n = collatzIter u.length (syracuseForestVal r cs) := by omega
      rcases syracuseForestVal_reaches_root r hr_root cs with ⟨kTree, _, hkTree⟩
      have hr_ge5 : r ≥ 5 := hr_root.1
      rcases multi_root_forest_collision_reaches_one_aux fuel r hprop (by omega) (by omega) with
        ⟨kr, hkr⟩
      have hz1 : collatzIter (kTree + kr) (syracuseForestVal r cs) = 1 := by
        rw [collatzIter_add, hkTree, hkr]
      exact coalescence_reaches_one n (syracuseForestVal r cs) K u.length (kTree + kr) hcoal hz1

/--
  Theorem 30.2b (`MultiRootForestCarryCollisionProp -> CollatzConjectureStandard`):
  Even allowing collisions with arbitrarily large inverse-forest nodes `z = syracuseForestVal r cs >> n`
  above smaller roots `r in [5, n - 1]`, `MultiRootForestCarryCollisionProp` unconditionally
  closes `CollatzConjectureStandard`!
-/
theorem multi_root_forest_collision_implies_collatz_standard
    (hprop : MultiRootForestCarryCollisionProp) :
    CollatzConjectureStandard := by
  rw [collatz_standard_iff_compressed]
  intro n hn
  exact multi_root_forest_collision_reaches_one_aux n n hprop (by omega) (by omega)

theorem collatz_standard_implies_backward_carry_window
    (hstd : CollatzConjectureStandard) :
    BackwardCarryContractionWindowProp := by
  have hcomp := collatz_standard_iff_compressed.mp hstd
  intro n hn
  rcases hcomp n (by omega) with ⟨kn, hkn⟩
  refine ⟨kn, [true, false], ?_, ?_, ?_⟩
  · rw [hkn]; decide
  · rw [hkn]
    have hw : 3 ^ parityWeight [true, false] = 3 := rfl
    have hl : 2 ^ [true, false].length * 1 = 4 := rfl
    have hc : affineCarry [true, false] = 1 := rfl
    rw [hw, hl, hc]
    omega
  · rw [hkn]; decide

/--
  Theorem 30.2c (Exact Logical Equivalence `CollatzConjectureStandard ↔ BackwardCarryContractionWindowProp`):
-/
theorem collatz_standard_iff_backward_carry_window :
    CollatzConjectureStandard ↔ BackwardCarryContractionWindowProp :=
  ⟨collatz_standard_implies_backward_carry_window,
   backward_carry_window_mixing_implies_collatz_standard⟩

theorem collatz_standard_implies_multi_root_forest_collision
    (hstd : CollatzConjectureStandard) :
    MultiRootForestCarryCollisionProp := by
  have hcomp := collatz_standard_iff_compressed.mp hstd
  intro n hn
  rcases hcomp n (by omega) with ⟨kn, hkn⟩
  refine ⟨kn, 5, [], [true, false, false, false], ?_, by omega, ?_⟩
  · unfold IsSyracuseForestRoot; decide
  · rw [hkn]; decide

/--
  Theorem 30.2d (Exact Logical Equivalence `CollatzConjectureStandard ↔ MultiRootForestCarryCollisionProp`):
-/
theorem collatz_standard_iff_multi_root_forest_collision :
    CollatzConjectureStandard ↔ MultiRootForestCarryCollisionProp :=
  ⟨collatz_standard_implies_multi_root_forest_collision,
   multi_root_forest_collision_implies_collatz_standard⟩

/--
  The `5` residue classes modulo `36` (`{3, 7, 15, 19, 27} mod 36`, density `5/36 ≈ 13.89%`)
  surviving Theorem 29's initial backward merger sieve (`minimal_counterexample_mod36_in_5_classes`).
-/
def IsSurvivingMod36Class (n : Nat) : Prop :=
  n % 36 = 3 ∨ n % 36 = 7 ∨ n % 36 = 15 ∨ n % 36 = 19 ∨ n % 36 = 27

/--
  Sieved Open Mixing Hypothesis 30.2e (`SievedBackwardCarryWindowProp`):
  Restricts `BackwardCarryContractionWindowProp` strictly to `n >= 7` in the `5` surviving
  residue classes `{3, 7, 15, 19, 27} mod 36`.
-/
def SievedBackwardCarryWindowProp : Prop :=
  ∀ n : Nat, n ≥ 7 -> IsSurvivingMod36Class n ->
    ∃ (K : Nat) (u : List Bool),
      3 ^ parityWeight u + affineCarry u ≤ 2 ^ u.length * collatzIter K n ∧
      2 ^ u.length * collatzIter K n < 3 ^ parityWeight u * n + affineCarry u ∧
      (2 ^ u.length * collatzIter K n - affineCarry u) % 3 ^ parityWeight u = 0

/--
  Sieved Open Mixing Hypothesis 30.2f (`SievedMultiRootForestCarryCollisionProp`):
  Restricts `MultiRootForestCarryCollisionProp` strictly to `n >= 7` in the `5` surviving
  residue classes `{3, 7, 15, 19, 27} mod 36`.
-/
def SievedMultiRootForestCarryCollisionProp : Prop :=
  ∀ n : Nat, n ≥ 7 -> IsSurvivingMod36Class n ->
    ∃ (K r : Nat) (cs u : List Bool),
      IsSyracuseForestRoot r ∧
      r < n ∧
      (2 : Int) ^ u.length * (collatzIter K n : Int) =
        (3 : Int) ^ parityWeight u * (syracuseForestVal r cs : Int) + affineCarryInt u

theorem sieved_backward_carry_window_reaches_one_aux : ∀ (fuel n : Nat),
    SievedBackwardCarryWindowProp -> 1 ≤ n -> n ≤ fuel + 1 ->
    ∃ kn : Nat, collatzIter kn n = 1
  | 0, n, _, hn1, hle => by
    have hn_eq : n = 1 := by omega
    subst hn_eq
    exact ⟨0, rfl⟩
  | fuel + 1, n, hprop, hn1, hle => by
    have hminReach : ∀ m : Nat, 1 ≤ m -> m < n -> ∃ k1 : Nat, collatzIter k1 m = 1 :=
      fun m hm1 hmlt => sieved_backward_carry_window_reaches_one_aux fuel m hprop hm1 (by omega)
    by_cases hn_eq1 : n = 1
    · subst hn_eq1
      exact ⟨0, rfl⟩
    · by_cases hdesc : ∃ k : Nat, 0 < collatzIter k n ∧ collatzIter k n < n
      · rcases hdesc with ⟨k, hk_pos, hk_lt⟩
        rcases hminReach (collatzIter k n) (by omega) hk_lt with ⟨km, hkm⟩
        exact ⟨k + km, by rw [collatzIter_add, hkm]⟩
      · have hnoDesc : ∀ k : Nat, ¬ (0 < collatzIter k n ∧ collatzIter k n < n) :=
          fun k hk => hdesc ⟨k, hk⟩
        have hm36 : IsSurvivingMod36Class n :=
          minimal_counterexample_mod36_in_5_classes n (by omega) hnoDesc hminReach
        have hn_ge7 : n ≥ 7 := by
          by_cases hn3 : n = 3
          · subst hn3
            exact False.elim (hnoDesc 5 ⟨by decide, by decide⟩)
          · unfold IsSurvivingMod36Class at hm36
            omega
        rcases hprop n hn_ge7 hm36 with ⟨K, u, hlo, hhi, hdiv⟩
        rcases general_affine_backward_merger_step n K u hlo hhi hdiv with ⟨hp_lo, hp_lt, hcoal⟩
        rcases hminReach ((2 ^ u.length * collatzIter K n - affineCarry u) / 3 ^ parityWeight u)
          hp_lo hp_lt with ⟨kz, hkz⟩
        exact coalescence_reaches_one n _ K u.length kz hcoal.symm hkz

/--
  Theorem 30.2e (Exact Equivalence `CollatzConjectureStandard ↔ SievedBackwardCarryWindowProp`):
  Coupling Theorem 29's mod-36 sieve with Theorem 30 shows it suffices to prove backward carry
  window hits ONLY for `n >= 7` in `{3, 7, 15, 19, 27} mod 36`!
-/
theorem collatz_standard_iff_sieved_backward_carry_window :
    CollatzConjectureStandard ↔ SievedBackwardCarryWindowProp := by
  constructor
  · intro hstd n hn _
    exact collatz_standard_implies_backward_carry_window hstd n (by omega)
  · intro hprop
    rw [collatz_standard_iff_compressed]
    intro n hn
    exact sieved_backward_carry_window_reaches_one_aux n n hprop (by omega) (by omega)

theorem sieved_forest_collision_reaches_one_aux : ∀ (fuel n : Nat),
    SievedMultiRootForestCarryCollisionProp -> 1 ≤ n -> n ≤ fuel + 1 ->
    ∃ kn : Nat, collatzIter kn n = 1
  | 0, n, _, hn1, hle => by
    have hn_eq : n = 1 := by omega
    subst hn_eq
    exact ⟨0, rfl⟩
  | fuel + 1, n, hprop, hn1, hle => by
    have hminReach : ∀ m : Nat, 1 ≤ m -> m < n -> ∃ k1 : Nat, collatzIter k1 m = 1 :=
      fun m hm1 hmlt => sieved_forest_collision_reaches_one_aux fuel m hprop hm1 (by omega)
    by_cases hn_eq1 : n = 1
    · subst hn_eq1
      exact ⟨0, rfl⟩
    · by_cases hdesc : ∃ k : Nat, 0 < collatzIter k n ∧ collatzIter k n < n
      · rcases hdesc with ⟨k, hk_pos, hk_lt⟩
        rcases hminReach (collatzIter k n) (by omega) hk_lt with ⟨km, hkm⟩
        exact ⟨k + km, by rw [collatzIter_add, hkm]⟩
      · have hnoDesc : ∀ k : Nat, ¬ (0 < collatzIter k n ∧ collatzIter k n < n) :=
          fun k hk => hdesc ⟨k, hk⟩
        have hm36 : IsSurvivingMod36Class n :=
          minimal_counterexample_mod36_in_5_classes n (by omega) hnoDesc hminReach
        have hn_ge7 : n ≥ 7 := by
          by_cases hn3 : n = 3
          · subst hn3
            exact False.elim (hnoDesc 5 ⟨by decide, by decide⟩)
          · unfold IsSurvivingMod36Class at hm36
            omega
        rcases hprop n hn_ge7 hm36 with ⟨K, r, cs, u, hr_root, hr_lt, heq_int⟩
        rcases general_affine_converse_universal u
          (syracuseForestVal r cs : Int) (collatzIter K n : Int) heq_int with ⟨_, hiter_int⟩
        rw [collatzIterInt_ofNat] at hiter_int
        have hcoal : collatzIter K n = collatzIter u.length (syracuseForestVal r cs) := by omega
        rcases syracuseForestVal_reaches_root r hr_root cs with ⟨kTree, _, hkTree⟩
        have hr_ge5 : r ≥ 5 := hr_root.1
        rcases hminReach r (by omega) hr_lt with ⟨kr, hkr⟩
        have hz1 : collatzIter (kTree + kr) (syracuseForestVal r cs) = 1 := by
          rw [collatzIter_add, hkTree, hkr]
        exact coalescence_reaches_one n (syracuseForestVal r cs) K u.length (kTree + kr) hcoal hz1

/--
  Theorem 30.2f (Exact Equivalence `CollatzConjectureStandard ↔ SievedMultiRootForestCarryCollisionProp`):
  Coupling Theorem 29's mod-36 sieve with Theorem 30 shows it suffices to prove multi-root forest
  carry collisions ONLY for `n >= 7` in `{3, 7, 15, 19, 27} mod 36`!
-/
theorem collatz_standard_iff_sieved_forest_collision :
    CollatzConjectureStandard ↔ SievedMultiRootForestCarryCollisionProp := by
  constructor
  · intro hstd n hn _
    exact collatz_standard_implies_multi_root_forest_collision hstd n (by omega)
  · intro hprop
    rw [collatz_standard_iff_compressed]
    intro n hn
    exact sieved_forest_collision_reaches_one_aux n n hprop (by omega) (by omega)


-- ============================================================================
-- SECTION 18: Theorem 31 — Prime-Denominator `D = 2^K - 3^W` Rigidity,
--             `p = 23` / `139` Falsifications, & 2-Vertex `(x_(1), x_(2))` Split
-- ============================================================================

theorem affineCarryInt_odd_of_true_cons (u : List Bool) :
    affineCarryInt (true :: u) % 2 = 1 := by
  have hc : affineCarryInt (true :: u) = (3 : Int) ^ parityWeight u + 2 * affineCarryInt u := by
    unfold affineCarryInt
    simp only [affineCarryAuxInt]
    have h10 : 3 * (0 : Int) + (2 : Int) ^ 0 = 1 := rfl
    have h01 : 0 + 1 = 1 := rfl
    rw [h01, h10, affineCarryAuxInt_shift u 1 1]
    omega
  have hp3 : (3 : Int) ^ parityWeight u % 2 = 1 := pow3_mod2 (parityWeight u)
  rw [hc]
  omega

theorem affineCarryInt_replicate_false_append : ∀ (a : Nat) (w : List Bool),
    affineCarryInt (List.replicate a false ++ w) = (2 : Int) ^ a * affineCarryInt w
  | 0, w => by simp
  | a + 1, w => by
    simp only [List.replicate_succ, List.cons_append]
    have hc : affineCarryInt (false :: (List.replicate a false ++ w)) =
        2 * affineCarryInt (List.replicate a false ++ w) := by
      unfold affineCarryInt
      simp only [affineCarryAuxInt]
      have h01 : 0 + 1 = 1 := rfl
      rw [h01, affineCarryAuxInt_shift (List.replicate a false ++ w) 1 0]
      omega
    rw [hc, affineCarryInt_replicate_false_append a w, Int.pow_succ,
        Int.mul_comm ((2 : Int) ^ a) 2, Int.mul_assoc]

theorem odd_mul_pow2_exact_factor : ∀ (a : Nat) (D x Q : Int),
    D % 2 = 1 -> Q % 2 = 1 -> D * x = (2 : Int) ^ a * Q ->
    ∃ q : Int, x = (2 : Int) ^ a * q ∧ q % 2 = 1
  | 0, D, x, Q, _, hQ, heq => by
    simp only [Int.pow_zero, Int.one_mul] at heq
    have hx_odd : x % 2 = 1 := by
      by_cases hx_ev : x % 2 = 0
      · have hm : (D * x) % 2 = 0 := by rw [Int.mul_emod, hx_ev]; simp
        omega
      · omega
    exact ⟨x, by simp, hx_odd⟩
  | a + 1, D, x, Q, hD, hQ, heq => by
    have hp2 : (2 : Int) ^ (a + 1) * Q = 2 * ((2 : Int) ^ a * Q) := by
      rw [Int.pow_succ, Int.mul_comm ((2 : Int) ^ a) 2, Int.mul_assoc]
    rw [hp2] at heq
    have hprod_ev : (D * x) % 2 = 0 := by omega
    have hx_ev : x % 2 = 0 := odd_mul_even_iff D x hD hprod_ev
    let x' : Int := x / 2
    have hx_eq : x = 2 * x' := by dsimp [x']; omega
    have hmul : D * (2 * x') = 2 * (D * x') := by
      rw [← Int.mul_assoc, Int.mul_comm D 2, Int.mul_assoc]
    rw [hx_eq, hmul] at heq
    rcases odd_mul_pow2_exact_factor a D x' Q hD hQ (by omega) with ⟨q, hq_eq, hq_odd⟩
    refine ⟨q, ?_, hq_odd⟩
    rw [hx_eq, hq_eq, Int.pow_succ, Int.mul_comm ((2 : Int) ^ a) 2, Int.mul_assoc]

/--
  Theorem 31.1 (Exact 2-Adic Cycle Valuation Lock `v_2(x_0) = a = v_2(C(0^a 1 u))`):
  For EVERY parity word `v = 0^a ++ (1 :: u)` (`a >= 0`) and EVERY integer `x_0 : Int`
  solving `(2^|v| - 3^w(v)) * x_0 = C(v)`, `C(v) = 2^a * C(1 :: u)` with `C(1 :: u)` odd,
  and `x_0 = 2^a * q` with `q` odd (holding identically over `Z^+` and `Z^-`, explaining why
  pure 2-adic valuation identities cannot separate positive cycles from `-17` or `19/5`).
-/
theorem cycle_2adic_valuation_lock_replicate_false (a : Nat) (u : List Bool) (x0 : Int)
    (hcyc : ((2 : Int) ^ (List.replicate a false ++ (true :: u)).length -
             (3 : Int) ^ parityWeight (List.replicate a false ++ (true :: u))) * x0 =
            affineCarryInt (List.replicate a false ++ (true :: u))) :
    affineCarryInt (List.replicate a false ++ (true :: u)) =
      (2 : Int) ^ a * affineCarryInt (true :: u) ∧
    affineCarryInt (true :: u) % 2 = 1 ∧
    ∃ q : Int, x0 = (2 : Int) ^ a * q ∧ q % 2 = 1 := by
  let v := List.replicate a false ++ (true :: u)
  have hc_eq : affineCarryInt v = (2 : Int) ^ a * affineCarryInt (true :: u) :=
    affineCarryInt_replicate_false_append a (true :: u)
  have hQ_odd : affineCarryInt (true :: u) % 2 = 1 := affineCarryInt_odd_of_true_cons u
  have hv_len : v.length = a + 1 + u.length := by
    dsimp [v]
    rw [List.length_append, List.length_replicate, List.length_cons]
    omega
  have hp2_ev : ((2 : Int) ^ v.length) % 2 = 0 := by
    rw [hv_len, show a + 1 + u.length = (a + u.length) + 1 by omega, Int.pow_succ]
    omega
  have hp3_odd : ((3 : Int) ^ parityWeight v) % 2 = 1 := pow3_mod2 (parityWeight v)
  have hD_odd : ((2 : Int) ^ v.length - (3 : Int) ^ parityWeight v) % 2 = 1 := by omega
  change ((2 : Int) ^ v.length - (3 : Int) ^ parityWeight v) * x0 = affineCarryInt v at hcyc
  rw [hc_eq] at hcyc
  exact ⟨hc_eq, hQ_odd,
    odd_mul_pow2_exact_factor a ((2 : Int) ^ v.length - (3 : Int) ^ parityWeight v)
      x0 (affineCarryInt (true :: u)) hD_odd hQ_odd hcyc⟩

theorem pow2_mod23_in_subgroup : ∀ (k : Nat),
    let r := (2 : Int) ^ k % 23
    r = 1 ∨ r = 2 ∨ r = 4 ∨ r = 8 ∨ r = 16 ∨ r = 9 ∨
    r = 18 ∨ r = 13 ∨ r = 3 ∨ r = 6 ∨ r = 12
  | 0 => by decide
  | k + 1 => by
    have ih := pow2_mod23_in_subgroup k
    dsimp only at ih ⊢
    rw [Int.pow_succ, Int.mul_emod]
    rcases ih with h | h | h | h | h | h | h | h | h | h | h <;> rw [h] <;> decide

theorem mul_mod23_ne_zero (x y : Int)
    (hy : y % 23 ≠ 0)
    (hset : x % 23 = 1 ∨ x % 23 = 2 ∨ x % 23 = 4 ∨ x % 23 = 8 ∨ x % 23 = 16 ∨
            x % 23 = 9 ∨ x % 23 = 18 ∨ x % 23 = 13 ∨ x % 23 = 3 ∨ x % 23 = 6 ∨ x % 23 = 12) :
    (x * y) % 23 ≠ 0 := by
  rw [Int.mul_emod]
  rcases hset with h | h | h | h | h | h | h | h | h | h | h <;> rw [h] <;> omega

/--
  Theorem 31.2a (Universal Weight-2 Odd-`<2, 3>_23` Carry Obstruction):
  Because `<2, 3>_23 = <2>_23` has ODD order `11` (`-1 = 22 notin <2, 3>_23`),
  for ALL `a, b, c : Nat` (infinitely many weight-2 parity words `0^a 1 0^b 1 0^c`),
  `C(0^a 1 0^b 1 0^c) = 2^a * (3 + 2^(b + 1))` is NEVER divisible by `23`!
-/
theorem weight2_carry_mod23_never_zero (a b c : Nat) :
    let v := List.replicate a false ++
      (true :: (List.replicate b false ++ (true :: List.replicate c false)))
    parityWeight v = 2 ∧
    affineCarryInt v = (2 : Int) ^ a * (3 + (2 : Int) ^ (b + 1)) ∧
    affineCarryInt v % 23 ≠ 0 := by
  dsimp only
  let w0 := true :: List.replicate c false
  let w1 := List.replicate b false ++ w0
  let w2 := true :: w1
  let v := List.replicate a false ++ w2
  have hw0_wt : parityWeight w0 = 1 := by
    dsimp [w0]
    simp only [parityWeight]
    have hz : List.replicate c false = List.replicate c false ++ [] := by simp
    rw [hz, parityWeight_replicate_false_append, parityWeight]
  have hw1_wt : parityWeight w1 = 1 := by
    dsimp [w1]; rw [parityWeight_replicate_false_append, hw0_wt]
  have hw2_wt : parityWeight w2 = 2 := by
    dsimp [w2]; simp [parityWeight, hw1_wt]
  have hv_wt : parityWeight v = 2 := by
    dsimp [v]; rw [parityWeight_replicate_false_append, hw2_wt]
  have hw0_c : affineCarryInt w0 = 1 := by
    dsimp [w0]
    have hc : affineCarryInt (true :: List.replicate c false) =
        (3 : Int) ^ parityWeight (List.replicate c false) +
        2 * affineCarryInt (List.replicate c false) := by
      unfold affineCarryInt
      simp only [affineCarryAuxInt]
      have h10 : 3 * (0 : Int) + (2 : Int) ^ 0 = 1 := rfl
      have h01 : 0 + 1 = 1 := rfl
      rw [h01, h10, affineCarryAuxInt_shift (List.replicate c false) 1 1]
      omega
    have hz_wt : parityWeight (List.replicate c false) = 0 := by
      have hz : List.replicate c false = List.replicate c false ++ [] := by simp
      rw [hz, parityWeight_replicate_false_append, parityWeight]
    rw [hc, hz_wt, affineCarryInt_eq_zero_of_weight_zero _ hz_wt]
    rfl
  have hw1_c : affineCarryInt w1 = (2 : Int) ^ b := by
    dsimp [w1]; rw [affineCarryInt_replicate_false_append, hw0_c, Int.mul_one]
  have hw2_c : affineCarryInt w2 = 3 + (2 : Int) ^ (b + 1) := by
    dsimp [w2]
    have hc : affineCarryInt (true :: w1) = (3 : Int) ^ parityWeight w1 + 2 * affineCarryInt w1 := by
      unfold affineCarryInt
      simp only [affineCarryAuxInt]
      have h10 : 3 * (0 : Int) + (2 : Int) ^ 0 = 1 := rfl
      have h01 : 0 + 1 = 1 := rfl
      rw [h01, h10, affineCarryAuxInt_shift w1 1 1]
      omega
    have hp31 : (3 : Int) ^ 1 = 3 := rfl
    have hp2b : 2 * (2 : Int) ^ b = (2 : Int) ^ (b + 1) := by
      rw [Int.pow_succ, Int.mul_comm]
    rw [hc, hw1_wt, hp31, hw1_c, hp2b]
  have hv_c : affineCarryInt v = (2 : Int) ^ a * (3 + (2 : Int) ^ (b + 1)) := by
    dsimp [v]; rw [affineCarryInt_replicate_false_append, hw2_c]
  refine ⟨hv_wt, hv_c, ?_⟩
  rw [hv_c]
  have h2a := pow2_mod23_in_subgroup a
  have h2b := pow2_mod23_in_subgroup (b + 1)
  dsimp only at h2a h2b
  have hsum_mod : (3 + (2 : Int) ^ (b + 1)) % 23 ≠ 0 := by
    rw [Int.add_emod]
    rcases h2b with hb | hb | hb | hb | hb | hb | hb | hb | hb | hb | hb <;> rw [hb] <;> decide
  exact mul_mod23_ne_zero ((2 : Int) ^ a) (3 + (2 : Int) ^ (b + 1)) hsum_mod h2a

/--
  Theorem 31.2b (Weight-3 `p = 23` & `D = -139` (`-17` Cycle) Falsification Witnesses):
  At weight `W = 3`, `v = [true, true, false, true]` achieves `C(v) = 23 ≡ 0 (mod 23)` despite
  `|<2, 3>_23| = 11` being odd, and `-17` is a genuine `m = 2` cycle over `Z^-` with prime
  `|2^11 - 3^7| = 139` (`<2, 3>_139 = F_139^*`), falsifying naive subgroup coset obstructions for `W >= 3`!
-/
theorem weight3_mod23_and_neg17_mod139_falsification_witnesses :
    (parityWeight [true, true, false, true] = 3 ∧
     affineCarry [true, true, false, true] = 23 ∧
     affineCarry [true, true, false, true] % 23 = 0) ∧
    (collatzIterInt 11 (-17) = -17 ∧
     (2 : Int) ^ 11 - (3 : Int) ^ 7 = -139) := by
  decide

/--
  Theorem 31.3 (2-Vertex Ordered-Minimum `(x_(1), x_(2))` Budget Split Theorem):
  Suppose `s >= 1` low-`a` cycle vertices are ordered `x1 <= x2 <= ... <= x_s` so their
  reciprocal budget satisfies the cleared-denominator inequality
    `B * ((x1 + 1) * (x2 + 1)) <= D * (x2 + 1) + (s - 1) * D * (x1 + 1)`.
  Whenever `x1 >= A1` with `A1` strictly above the pole `D / B` (`D < B * (A1 + 1)`):
  (1) If `s = 1` (`s_low = 1`), NO solution exists (`False`);
  (2) For ALL `s >= 1` and ALL `x1 >= A1` (unbounded above!), `x2` is strictly capped by
      `(B * (A1 + 1) - D) * (x2 + 1) <= (s - 1) * D * (A1 + 1)`!
-/
theorem two_vertex_ordered_minimum_budget_split
    (x1 x2 A1 s B D : Nat)
    (hx1 : A1 ≤ x1)
    (hpole : D < B * (A1 + 1))
    (hbud : B * ((x1 + 1) * (x2 + 1)) ≤ D * (x2 + 1) + (s - 1) * D * (x1 + 1)) :
    (B * (A1 + 1) - D) * (x2 + 1) ≤ (s - 1) * D * (A1 + 1) ∧
    (s = 1 -> False) := by
  let T := x1 + 1
  let T0 := A1 + 1
  have hpole_T0 : D < B * T0 := hpole
  have hT0_le_T : T0 ≤ T := by dsimp [T, T0]; omega
  have hBT0_le_BT : B * T0 ≤ B * T := Nat.mul_le_mul_left B hT0_le_T
  have hD_lt_BT : D < B * T := by omega
  have hsub_T : (B * T - D) * (x2 + 1) + D * (x2 + 1) = B * (T * (x2 + 1)) := by
    rw [← Nat.add_mul, show B * T - D + D = B * T by omega, Nat.mul_assoc]
  have h1 : (B * T - D) * (x2 + 1) ≤ (s - 1) * D * T := by
    change B * (T * (x2 + 1)) ≤ D * (x2 + 1) + (s - 1) * D * T at hbud
    omega
  have hcross : T * (B * T0 - D) ≤ T0 * (B * T - D) := by
    have ha : T * (B * T0 - D) + T * D = T * (B * T0) := by
      rw [← Nat.mul_add, show B * T0 - D + D = B * T0 by omega]
    have hb : T0 * (B * T - D) + T0 * D = T0 * (B * T) := by
      rw [← Nat.mul_add, show B * T - D + D = B * T by omega]
    have hab_eq : T * (B * T0) = T0 * (B * T) := by
      rw [← Nat.mul_assoc, Nat.mul_comm T B, Nat.mul_assoc,
          ← Nat.mul_assoc T0 B T, Nat.mul_comm T0 B, Nat.mul_assoc, Nat.mul_comm T T0]
    have hTD : T0 * D ≤ T * D := Nat.mul_le_mul_right D hT0_le_T
    omega
  have hmul_x2 : (T * (B * T0 - D)) * (x2 + 1) ≤ (T0 * (B * T - D)) * (x2 + 1) :=
    Nat.mul_le_mul_right (x2 + 1) hcross
  have hmul_rhs : T0 * ((B * T - D) * (x2 + 1)) ≤ T0 * ((s - 1) * D * T) :=
    Nat.mul_le_mul_left T0 h1
  have hlhs_assoc : T * ((B * T0 - D) * (x2 + 1)) = (T * (B * T0 - D)) * (x2 + 1) :=
    (Nat.mul_assoc T _ _).symm
  have hmid_assoc : (T0 * (B * T - D)) * (x2 + 1) = T0 * ((B * T - D) * (x2 + 1)) :=
    Nat.mul_assoc T0 _ _
  have hrhs_comm : T0 * ((s - 1) * D * T) = T * ((s - 1) * D * T0) := by
    rw [Nat.mul_comm T0 ((s - 1) * D * T), Nat.mul_assoc ((s - 1) * D) T T0,
        Nat.mul_comm T T0, ← Nat.mul_assoc ((s - 1) * D) T0 T, Nat.mul_comm _ T]
  have hT_ineq : T * ((B * T0 - D) * (x2 + 1)) ≤ T * ((s - 1) * D * T0) := by
    rw [hlhs_assoc]
    exact Nat.le_trans hmul_x2 (by rw [hmid_assoc, ← hrhs_comm]; exact hmul_rhs)
  have hmain : (B * T0 - D) * (x2 + 1) ≤ (s - 1) * D * T0 := by
    apply Classical.byContradiction
    intro hgt
    have hge : (s - 1) * D * T0 + 1 ≤ (B * T0 - D) * (x2 + 1) := by omega
    have hm := Nat.mul_le_mul_left T hge
    rw [Nat.mul_add, Nat.mul_one] at hm
    have hT_pos : T ≥ 1 := by dsimp [T]; omega
    omega
  refine ⟨hmain, ?_⟩
  intro hs1
  subst hs1
  have hzero : (1 - 1) * D * T0 = 0 := by simp
  rw [hzero] at hmain
  have hpos_lhs : (B * T0 - D) * (x2 + 1) ≥ 1 :=
    Nat.mul_pos (by omega) (by omega)
  omega

/--
  Theorem 31.4 (Exact `s_low = s` Top-Strip Upper Bound Across All `1 ≤ s ≤ c`):
  Suppose `s` low-`a` cycle vertices lie in `[x1, bLow]` and the remaining `c - s`
  low-`a` vertices exceed `bLow`, yielding the cleared-denominator reciprocal budget
    `B * ((x1 + 1) * (bLow + 1)) <= s * D * (bLow + 1) + (c - s) * D * (x1 + 1)`.
  Whenever `(c - s) * D <= B * (bLow + 1)`, `x1` is bounded above by
    `(B * (bLow + 1) - (c - s) * D) * (x1 + 1) <= s * D * (bLow + 1)`,
  distinguishing `s = 2` (`0.870 / 0.851 / 0.833 bLow` at `m = 97..99, u = 1`) from
  `3 <= s <= c` (which increases monotonically to `c * D / B ≈ 0.9524 bLow` at `s = c`)!
-/
theorem s_low_top_strip_upper_bound
    (x1 bLow s c B D : Nat)
    (hrem : (c - s) * D ≤ B * (bLow + 1))
    (hbud : B * ((x1 + 1) * (bLow + 1)) ≤ s * D * (bLow + 1) + (c - s) * D * (x1 + 1)) :
    (B * (bLow + 1) - (c - s) * D) * (x1 + 1) ≤ s * D * (bLow + 1) := by
  have hsplit :
      (B * (bLow + 1) - (c - s) * D) * (x1 + 1) + (c - s) * D * (x1 + 1) =
        B * ((x1 + 1) * (bLow + 1)) := by
    rw [← Nat.add_mul,
        show B * (bLow + 1) - (c - s) * D + (c - s) * D = B * (bLow + 1) by omega,
        Nat.mul_assoc B (bLow + 1) (x1 + 1),
        Nat.mul_comm (bLow + 1) (x1 + 1)]
  omega


-- ============================================================================
-- SECTION 19: Theorem 32 — Concatenated Carry Law, Two-Return Garden-of-Eden
--             Escape, Complete Mod-1296 `(K, L)` Sieve, & `(Z / 81Z)^*` Shifting
-- ============================================================================

/--
  Theorem 32.1a (Exact Concatenation Law for `affineCarry` over `Nat`):
  For ALL parity words `u1, u2 : List Bool`,
    `affineCarry (u1 ++ u2) = 3 ^ parityWeight u2 * affineCarry u1 + 2 ^ u1.length * affineCarry u2`.
-/
theorem affineCarry_append (u1 u2 : List Bool) :
    affineCarry (u1 ++ u2) =
      3 ^ parityWeight u2 * affineCarry u1 + 2 ^ u1.length * affineCarry u2 := by
  have h := affineCarryInt_append u1 u2
  have hrhs :
      ((3 ^ parityWeight u2 * affineCarry u1 + 2 ^ u1.length * affineCarry u2 : Nat) : Int) =
        (3 : Int) ^ parityWeight u2 * affineCarryInt u1 +
          (2 : Int) ^ u1.length * affineCarryInt u2 := by
    rw [natCast_add, natCast_mul, natCast_pow3, natCast_mul, natCast_pow2,
        ← affineCarryInt_ofNat, ← affineCarryInt_ofNat]
  rw [affineCarryInt_ofNat (u1 ++ u2), ← hrhs] at h
  omega

theorem affineCarry_eq_zero_of_weight_zero (u : List Bool) (hw : parityWeight u = 0) :
    affineCarry u = 0 := by
  have h := affineCarryInt_eq_zero_of_weight_zero u hw
  rw [affineCarryInt_ofNat] at h
  omega

/--
  Right-appending `a` even (`false`) bits leaves BOTH `parityWeight` and `affineCarry`
  identically invariant while scaling `2 ^ u'.length` by `2 ^ a`.
-/
theorem affineCarry_append_replicate_false (u : List Bool) (a : Nat) :
    parityWeight (u ++ List.replicate a false) = parityWeight u ∧
    affineCarry (u ++ List.replicate a false) = affineCarry u := by
  have hw0 : parityWeight (List.replicate a false) = 0 := parityWeight_replicate_false a
  have hc0 : affineCarry (List.replicate a false) = 0 :=
    affineCarry_eq_zero_of_weight_zero (List.replicate a false) hw0
  refine ⟨?_, ?_⟩
  · rw [parityWeight_append, hw0, Nat.add_zero]
  · rw [affineCarry_append, hw0, hc0]
    simp

/--
  Theorem 32.1b (Two-Return Garden-of-Eden Escape Theorem):
  Suppose two trajectory points `x1` and `x2` are connected by intermediate parity word `vMid`:
    `2 ^ vMid.length * x2 = 3 ^ parityWeight vMid * x1 + affineCarry vMid`.
  Whereas a single return `x1` can evade all backward mergers via `x1 % 3 = 0` (Theorem 29.3),
  between `x1` and `x2`:
  (1) If `parityWeight vMid = 0`, then `2 ^ vMid.length * x2 = x1` (pure halving);
  (2) If `parityWeight vMid >= 1`, then `x2 % 3 != 0` UNCONDITIONALLY (even when `x1 % 3 = 0`!),
      completely escaping the `0 mod 3` Garden-of-Eden trap!
-/
theorem two_return_garden_of_eden_escape (vMid : List Bool) (x1 x2 : Nat)
    (hstep : 2 ^ vMid.length * x2 = 3 ^ parityWeight vMid * x1 + affineCarry vMid) :
    (parityWeight vMid = 0 -> 2 ^ vMid.length * x2 = x1) ∧
    (parityWeight vMid ≥ 1 -> x2 % 3 ≠ 0) := by
  refine ⟨?_, ?_⟩
  · intro hw0
    have hc0 : affineCarry vMid = 0 := affineCarry_eq_zero_of_weight_zero vMid hw0
    rw [hw0, hc0] at hstep
    simpa using hstep
  · intro hw1 hx2_div3
    rcases affineCarryInt_pos_nondiv3_of_weight_pos vMid hw1 with ⟨_, hc_mod3_int⟩
    rw [affineCarryInt_ofNat] at hc_mod3_int
    have hc_mod3 : affineCarry vMid % 3 ≠ 0 := by omega
    have hlhs_mod3 : (2 ^ vMid.length * x2) % 3 = 0 := by
      rw [Nat.mul_mod, hx2_div3]
      simp
    have hp3_split : 3 ^ parityWeight vMid * x1 = 3 * (3 ^ (parityWeight vMid - 1) * x1) := by
      conv => lhs; rw [show parityWeight vMid = (parityWeight vMid - 1) + 1 by omega]
      rw [Nat.pow_succ, Nat.mul_comm (3 ^ (parityWeight vMid - 1)) 3, Nat.mul_assoc]
    have hrhs_mod3 : (3 ^ parityWeight vMid * x1 + affineCarry vMid) % 3 = affineCarry vMid % 3 := by
      rw [hp3_split]
      omega
    rw [hstep, hrhs_mod3] at hlhs_mod3
    exact hc_mod3 hlhs_mod3

/--
  Theorem 32.1c (Two-Return Sub-`3/2` Residue Pinning `x2 % 3 = 1`):
  On any minimal counterexample `nMin > 1`, if a second return `x2 = collatzIter K2 nMin`
  follows an earlier iterate `x1` via `vMid` with `parityWeight vMid >= 1`, `x2 >= 2`,
  and `2 * x2 <= 3 * nMin`, then `x2 % 3 = 0` is blocked by Garden-of-Eden escape AND
  `x2 % 3 = 2` is blocked by `sub_3_2_backward_merger_step`, uniquely pinning `x2 % 3 = 1`!
-/
theorem two_return_sub_3_2_pin_mod3_eq_1
    (nMin K2 x1 x2 : Nat) (vMid : List Bool)
    (hnMin : nMin > 1)
    (hnoDesc : ∀ k : Nat, ¬ (0 < collatzIter k nMin ∧ collatzIter k nMin < nMin))
    (hminReach : ∀ m : Nat, 1 ≤ m -> m < nMin -> ∃ k1 : Nat, collatzIter k1 m = 1)
    (hx2_iter : collatzIter K2 nMin = x2)
    (hstep : 2 ^ vMid.length * x2 = 3 ^ parityWeight vMid * x1 + affineCarry vMid)
    (hw_pos : parityWeight vMid ≥ 1)
    (hx2_ge2 : x2 ≥ 2)
    (hx2_sub : 2 * x2 ≤ 3 * nMin) :
    x2 % 3 = 1 := by
  have hnon0 : x2 % 3 ≠ 0 := (two_return_garden_of_eden_escape vMid x1 x2 hstep).2 hw_pos
  have hnon2 : x2 % 3 ≠ 2 := by
    intro hm2
    have hge : collatzIter K2 nMin ≥ 2 := by omega
    have hmod : collatzIter K2 nMin % 3 = 2 := by omega
    have hsub : 2 * collatzIter K2 nMin ≤ 3 * nMin := by omega
    rcases sub_3_2_backward_merger_step nMin K2 hge hmod hsub with ⟨hp_lo, hp_lt, hcoal⟩
    exact strict_descent_minimal_counterexample_coalescence_contradiction
      nMin ((2 * collatzIter K2 nMin - 1) / 3) K2 1 hnMin hp_lo hp_lt hnoDesc
      (hminReach ((2 * collatzIter K2 nMin - 1) / 3) hp_lo hp_lt) hcoal.symm
  omega

/--
  Theorem 32.2a (2-Adic/3-Adic Fiber Constancy Law):
  Whenever `2 ^ v.length * y = 3 ^ parityWeight v * n + affineCarry v` and `b <= parityWeight v`,
  `(2 ^ v.length * y) % 3 ^ b = affineCarry v % 3 ^ b` (independent of `n`), and similarly
  `affineCarry (u1 ++ u2) % 3 ^ b = (2 ^ u1.length * affineCarry u2) % 3 ^ b` whenever
  `b <= parityWeight u2`.
-/
theorem forward_k_mod3_const_on_2adic_fiber (v : List Bool) (n y b : Nat)
    (hb : b ≤ parityWeight v)
    (hdec : 2 ^ v.length * y = 3 ^ parityWeight v * n + affineCarry v) :
    (2 ^ v.length * y) % 3 ^ b = affineCarry v % 3 ^ b := by
  have hp3 : 3 ^ parityWeight v * n = 3 ^ b * (3 ^ (parityWeight v - b) * n) := by
    conv => lhs; rw [show parityWeight v = b + (parityWeight v - b) by omega]
    rw [Nat.pow_add, Nat.mul_assoc]
  have hmul0 : (3 ^ b * (3 ^ (parityWeight v - b) * n)) % 3 ^ b = 0 := by
    rw [Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod]
  rw [hdec, hp3, Nat.add_mod, hmul0, Nat.zero_add, Nat.mod_mod]

theorem affineCarry_append_mod_pow3 (u1 u2 : List Bool) (b : Nat)
    (hb : b ≤ parityWeight u2) :
    affineCarry (u1 ++ u2) % 3 ^ b = (2 ^ u1.length * affineCarry u2) % 3 ^ b := by
  have hp3 : 3 ^ parityWeight u2 * affineCarry u1 =
      3 ^ b * (3 ^ (parityWeight u2 - b) * affineCarry u1) := by
    conv => lhs; rw [show parityWeight u2 = b + (parityWeight u2 - b) by omega]
    rw [Nat.pow_add, Nat.mul_assoc]
  have hmul0 : (3 ^ b * (3 ^ (parityWeight u2 - b) * affineCarry u1)) % 3 ^ b = 0 := by
    rw [Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod]
  rw [affineCarry_append, hp3, Nat.add_mod, hmul0, Nat.zero_add, Nat.mod_mod]

/--
  Theorem 32.2b (Non-Contractive `2^L > 3^b` Backward-Merger Falsification Witness):
  At `L = 5, b = 3` (`2^5 = 32 > 27 = 3^3`), `u = [true, true, true, false, false]` has
  `C(u) = 19`, and `n = 47` satisfies `(2^5 * 47 - 19) % 27 = 0`, YET the backward
  predecessor `(32 * 47 - 19) / 27 = 55 > 47` EXPANDS above `n`!
-/
theorem noncontractive_backward_word_falsification_L5_b3 :
    let u := [true, true, true, false, false]
    u.length = 5 ∧
    parityWeight u = 3 ∧
    affineCarry u = 19 ∧
    (2 ^ u.length * 47 - affineCarry u) % 3 ^ parityWeight u = 0 ∧
    (2 ^ u.length * 47 - affineCarry u) / 3 ^ parityWeight u = 55 ∧
    55 > 47 := by
  decide

/--
  Theorem 32.3a (Forward `K <= 4` Mod-16 Rigidity `nMin % 16 ∈ {7, 11, 15}`):
  Eliminates `nMin % 16 = 3` across ALL `nMin > 1` since `collatzIter 4 (16 * q + 3) = 9 * q + 2 < 16 * q + 3`.
-/
theorem collatzIter4_of_mod16_eq_3 (n : Nat) (h16 : n % 16 = 3) :
    collatzIter 4 n = 9 * (n / 16) + 2 := by
  let q := n / 16
  have hn_eq : n = 16 * q + 3 := by dsimp [q]; omega
  have ho1 : (n % 2 == 0) = false := decide_eq_false (by omega)
  have hs1 : collatzStep n = 24 * q + 5 := by simp [collatzStep, ho1]; omega
  have ho2 : ((24 * q + 5) % 2 == 0) = false := decide_eq_false (by omega)
  have hs2 : collatzStep (24 * q + 5) = 36 * q + 8 := by simp [collatzStep, ho2]; omega
  have he3 : ((36 * q + 8) % 2 == 0) = true := decide_eq_true (by omega)
  have hs3 : collatzStep (36 * q + 8) = 18 * q + 4 := by simp [collatzStep, he3]; omega
  have he4 : ((18 * q + 4) % 2 == 0) = true := decide_eq_true (by omega)
  have hs4 : collatzStep (18 * q + 4) = 9 * q + 2 := by simp [collatzStep, he4]; omega
  change collatzStep (collatzStep (collatzStep (collatzStep n))) = 9 * q + 2
  rw [hs1, hs2, hs3, hs4]

theorem minimal_counterexample_mod16_in_3_classes (nMin : Nat)
    (hnMin : nMin > 1)
    (hnoDesc : ∀ k : Nat, ¬ (0 < collatzIter k nMin ∧ collatzIter k nMin < nMin)) :
    nMin % 16 = 7 ∨ nMin % 16 = 11 ∨ nMin % 16 = 15 := by
  have hp1 : collatzIter 1 nMin > 0 := collatzIter_pos 1 nMin (by omega)
  have hp2 : collatzIter 2 nMin > 0 := collatzIter_pos 2 nMin (by omega)
  have h1 : collatzIter 1 nMin ≥ nMin := by have hnd := hnoDesc 1; omega
  have h2 : collatzIter 2 nMin ≥ nMin := by have hnd := hnoDesc 2; omega
  have hm4 := minimal_counterexample_mod4_eq_3 nMin hnMin h1 h2
  have hne3 : nMin % 16 ≠ 3 := by
    intro hm16
    have hi4 := collatzIter4_of_mod16_eq_3 nMin hm16
    exact hnoDesc 4 ⟨by omega, by omega⟩
  omega

/--
  Theorem 32.3b (`K = 0, L = 6, b = 4` Mod-81 Rigidity `nMin % 81 != 10`):
  Taking `u = [true, true, true, false, true, false]` (`|u| = 6, w = 4, C(u) = 73`,
  `2^6 = 64 < 81 = 3^4`) eliminates `nMin % 81 = 10` across ALL `nMin > 1`!
-/
theorem minimal_counterexample_mod81_ne_10 (nMin : Nat)
    (hnMin : nMin > 1)
    (hnoDesc : ∀ k : Nat, ¬ (0 < collatzIter k nMin ∧ collatzIter k nMin < nMin))
    (hminReach : ∀ m : Nat, 1 ≤ m -> m < nMin -> ∃ k1 : Nat, collatzIter k1 m = 1) :
    nMin % 81 ≠ 10 := by
  intro hmod
  let u : List Bool := [true, true, true, false, true, false]
  have hu_w : parityWeight u = 4 := rfl
  have hu_l : u.length = 6 := rfl
  have hu_c : affineCarry u = 73 := rfl
  have hlo : 3 ^ parityWeight u + affineCarry u ≤ 2 ^ u.length * collatzIter 0 nMin := by
    rw [hu_w, hu_l, hu_c]; simp only [collatzIter]; omega
  have hhi : 2 ^ u.length * collatzIter 0 nMin < 3 ^ parityWeight u * nMin + affineCarry u := by
    rw [hu_w, hu_l, hu_c]; simp only [collatzIter]; omega
  have hdiv : (2 ^ u.length * collatzIter 0 nMin - affineCarry u) % 3 ^ parityWeight u = 0 := by
    rw [hu_w, hu_l, hu_c]; simp only [collatzIter]; omega
  exact minimal_counterexample_general_backward_merger_exclusion
    nMin 0 u hnMin hnoDesc hminReach hlo hhi hdiv

/--
  Theorem 32.3c (Two-Stage `(K = 4, L = 10, b = 7)` Garden-of-Eden Escape Exclusion of `1275 mod 1296`):
  Although `1275 % 3 = 0` (`1275 % 36 = 15`), so ZERO `K = 0` backward mergers of ANY weight
  can ever apply (`garden_of_eden_div3_unmergeable`), advancing `K = 4` steps yields
  `collatzIter 4 (1296 * q + 1275) = 2187 * q + 2153` (`% 3 = 2 != 0`, escaping `0 mod 3`!),
  and backward word `u = [true, true, true, true, false, true, true, true, false, false]`
  (`L = 10, b = 7, 3^7 = 2187, C(u) = 2363`, `1024 * 27 = 27648 < 34992 = 16 * 2187`)
  merges `nMin` with `nPrime = 1024 * q + 1007 < 1296 * q + 1275` for EVERY `q >= 0`!
-/
theorem collatzIter4_of_mod16_eq_11 (n : Nat) (h16 : n % 16 = 11) :
    collatzIter 4 n = 27 * (n / 16) + 20 := by
  let q := n / 16
  have hn_eq : n = 16 * q + 11 := by dsimp [q]; omega
  have ho1 : (n % 2 == 0) = false := decide_eq_false (by omega)
  have hs1 : collatzStep n = 24 * q + 17 := by simp [collatzStep, ho1]; omega
  have ho2 : ((24 * q + 17) % 2 == 0) = false := decide_eq_false (by omega)
  have hs2 : collatzStep (24 * q + 17) = 36 * q + 26 := by simp [collatzStep, ho2]; omega
  have he3 : ((36 * q + 26) % 2 == 0) = true := decide_eq_true (by omega)
  have hs3 : collatzStep (36 * q + 26) = 18 * q + 13 := by simp [collatzStep, he3]; omega
  have ho4 : ((18 * q + 13) % 2 == 0) = false := decide_eq_false (by omega)
  have hs4 : collatzStep (18 * q + 13) = 27 * q + 20 := by simp [collatzStep, ho4]; omega
  change collatzStep (collatzStep (collatzStep (collatzStep n))) = 27 * q + 20
  rw [hs1, hs2, hs3, hs4]

theorem minimal_counterexample_mod1296_ne_1275 (nMin : Nat)
    (hnMin : nMin > 1)
    (hnoDesc : ∀ k : Nat, ¬ (0 < collatzIter k nMin ∧ collatzIter k nMin < nMin))
    (hminReach : ∀ m : Nat, 1 ≤ m -> m < nMin -> ∃ k1 : Nat, collatzIter k1 m = 1) :
    nMin % 1296 ≠ 1275 := by
  intro hmod
  have hm16 : nMin % 16 = 11 := by omega
  have hi4 := collatzIter4_of_mod16_eq_11 nMin hm16
  have hq : nMin / 16 = 81 * (nMin / 1296) + 79 := by omega
  have hi4_1296 : collatzIter 4 nMin = 2187 * (nMin / 1296) + 2153 := by omega
  let u : List Bool := [true, true, true, true, false, true, true, true, false, false]
  have hu_w : parityWeight u = 7 := rfl
  have hu_l : u.length = 10 := rfl
  have hu_c : affineCarry u = 2363 := rfl
  have hp3 : (3 : Nat) ^ 7 = 2187 := rfl
  have hp2 : (2 : Nat) ^ 10 = 1024 := rfl
  have hlo : 3 ^ parityWeight u + affineCarry u ≤ 2 ^ u.length * collatzIter 4 nMin := by
    rw [hu_w, hu_l, hu_c, hp3, hp2, hi4_1296]; omega
  have hhi : 2 ^ u.length * collatzIter 4 nMin < 3 ^ parityWeight u * nMin + affineCarry u := by
    rw [hu_w, hu_l, hu_c, hp3, hp2, hi4_1296]; omega
  have hdiv : (2 ^ u.length * collatzIter 4 nMin - affineCarry u) % 3 ^ parityWeight u = 0 := by
    rw [hu_w, hu_l, hu_c, hp3, hp2, hi4_1296]; omega
  exact minimal_counterexample_general_backward_merger_exclusion
    nMin 4 u hnMin hnoDesc hminReach hlo hhi hdiv

/--
  The exact `131` residue classes modulo `1296` (`131 / 1296 ≈ 10.108%`) surviving all
  universal `(K, L)` forward-backward merger laws determined modulo `1296 = 2^4 * 3^4`.
-/
def IsSurvivingMod1296Class (n : Nat) : Prop :=
  (n % 16 = 7 ∨ n % 16 = 11 ∨ n % 16 = 15) ∧
  n % 3 ≠ 2 ∧
  n % 9 ≠ 4 ∧
  n % 81 ≠ 10 ∧
  n % 1296 ≠ 1275

def isSurvivingMod1296Bool (n : Nat) : Bool :=
  (n % 16 == 7 || n % 16 == 11 || n % 16 == 15) &&
  !(n % 3 == 2) &&
  !(n % 9 == 4) &&
  !(n % 81 == 10) &&
  !(n % 1296 == 1275)

def countSurvivingMod1296Grid : Nat :=
  (List.range 36).foldl
    (fun acc i => acc + (List.range 36).countP (fun j => isSurvivingMod1296Bool (36 * i + j)))
    0

theorem survivingMod1296_count_eq_131 :
    countSurvivingMod1296Grid = 131 := by
  decide

/--
  Theorem 32.3d (Complete Mod-1296 Minimal-Counterexample Sieve):
  Every minimal non-descending counterexample `nMin > 1` lies strictly inside the `131`
  surviving residue classes modulo `1296` (`IsSurvivingMod1296Class nMin`), strictly refining
  `IsSurvivingMod36Class` (`180 / 1296 -> 131 / 1296`).
-/
theorem minimal_counterexample_mod1296_in_131_classes (nMin : Nat)
    (hnMin : nMin > 1)
    (hnoDesc : ∀ k : Nat, ¬ (0 < collatzIter k nMin ∧ collatzIter k nMin < nMin))
    (hminReach : ∀ m : Nat, 1 ≤ m -> m < nMin -> ∃ k1 : Nat, collatzIter k1 m = 1) :
    IsSurvivingMod1296Class nMin :=
  ⟨minimal_counterexample_mod16_in_3_classes nMin hnMin hnoDesc,
   minimal_counterexample_mod3_ne_2 nMin hnMin hnoDesc hminReach,
   minimal_counterexample_mod9_ne_4 nMin hnMin hnoDesc hminReach,
   minimal_counterexample_mod81_ne_10 nMin hnMin hnoDesc hminReach,
   minimal_counterexample_mod1296_ne_1275 nMin hnMin hnoDesc hminReach⟩

theorem survivingMod1296_implies_mod36 (n : Nat) (h : IsSurvivingMod1296Class n) :
    IsSurvivingMod36Class n := by
  rcases h with ⟨h16, h3, h9, h81, h1296⟩
  have hm4 : n % 4 = 3 := by omega
  clear h16 h81 h1296
  have hm12 : n % 12 = 3 ∨ n % 12 = 7 := by omega
  clear hm4 h3
  unfold IsSurvivingMod36Class
  omega

/--
  Sharpened Open Mixing Hypothesis 32.3e (`Mod1296SievedForestCarryCollisionProp`):
  Restricts `SievedMultiRootForestCarryCollisionProp` from `5 / 36` (`13.89%`) strictly down to
  `n >= 7` in the `131 / 1296` (`10.11%`) classes of `IsSurvivingMod1296Class`.
-/
def Mod1296SievedForestCarryCollisionProp : Prop :=
  ∀ n : Nat, n ≥ 7 -> IsSurvivingMod1296Class n ->
    ∃ (K r : Nat) (cs u : List Bool),
      IsSyracuseForestRoot r ∧
      r < n ∧
      (2 : Int) ^ u.length * (collatzIter K n : Int) =
        (3 : Int) ^ parityWeight u * (syracuseForestVal r cs : Int) + affineCarryInt u

theorem mod1296_sieved_forest_collision_reaches_one_aux : ∀ (fuel n : Nat),
    Mod1296SievedForestCarryCollisionProp -> 1 ≤ n -> n ≤ fuel + 1 ->
    ∃ kn : Nat, collatzIter kn n = 1
  | 0, n, _, hn1, hle => by
    have hn_eq : n = 1 := by omega
    subst hn_eq
    exact ⟨0, rfl⟩
  | fuel + 1, n, hprop, hn1, hle => by
    have hminReach : ∀ m : Nat, 1 ≤ m -> m < n -> ∃ k1 : Nat, collatzIter k1 m = 1 :=
      fun m hm1 hmlt => mod1296_sieved_forest_collision_reaches_one_aux fuel m hprop hm1 (by omega)
    by_cases hn_eq1 : n = 1
    · subst hn_eq1
      exact ⟨0, rfl⟩
    · by_cases hdesc : ∃ k : Nat, 0 < collatzIter k n ∧ collatzIter k n < n
      · rcases hdesc with ⟨k, hk_pos, hk_lt⟩
        rcases hminReach (collatzIter k n) (by omega) hk_lt with ⟨km, hkm⟩
        exact ⟨k + km, by rw [collatzIter_add, hkm]⟩
      · have hnoDesc : ∀ k : Nat, ¬ (0 < collatzIter k n ∧ collatzIter k n < n) :=
          fun k hk => hdesc ⟨k, hk⟩
        have hm1296 : IsSurvivingMod1296Class n :=
          minimal_counterexample_mod1296_in_131_classes n (by omega) hnoDesc hminReach
        have hn_ge7 : n ≥ 7 := by
          rcases hm1296 with ⟨h16, _, _, _, _⟩
          omega
        rcases hprop n hn_ge7 hm1296 with ⟨K, r, cs, u, hr_root, hr_lt, heq_int⟩
        rcases general_affine_converse_universal u
          (syracuseForestVal r cs : Int) (collatzIter K n : Int) heq_int with ⟨_, hiter_int⟩
        rw [collatzIterInt_ofNat] at hiter_int
        have hcoal : collatzIter K n = collatzIter u.length (syracuseForestVal r cs) := by omega
        rcases syracuseForestVal_reaches_root r hr_root cs with ⟨kTree, _, hkTree⟩
        have hr_ge5 : r ≥ 5 := hr_root.1
        rcases hminReach r (by omega) hr_lt with ⟨kr, hkr⟩
        have hz1 : collatzIter (kTree + kr) (syracuseForestVal r cs) = 1 := by
          rw [collatzIter_add, hkTree, hkr]
        exact coalescence_reaches_one n (syracuseForestVal r cs) K u.length (kTree + kr) hcoal hz1

/--
  Theorem 32.3e (Exact Equivalence `CollatzConjectureStandard ↔ Mod1296SievedForestCarryCollisionProp`):
-/
theorem collatz_standard_iff_mod1296_sieved_forest_collision :
    CollatzConjectureStandard ↔ Mod1296SievedForestCarryCollisionProp := by
  constructor
  · intro hstd n hn _
    exact collatz_standard_implies_multi_root_forest_collision hstd n (by omega)
  · intro hprop
    rw [collatz_standard_iff_compressed]
    intro n hn
    exact mod1296_sieved_forest_collision_reaches_one_aux n n hprop (by omega) (by omega)

/-- Discrete logarithm base `2` on `(Z / 81Z)^*` (`0 <= dlog2Mod81 r < 54` for `r % 3 != 0`) -/
def dlog2Mod81Table : List Nat :=
  [0, 0, 1, 0, 2, 23, 0, 16, 3, 0, 24, 13, 0, 8, 17, 0, 4, 33, 0, 48, 25, 0, 14, 11, 0, 46, 9,
   0, 18, 37, 0, 20, 5, 0, 34, 39, 0, 42, 49, 0, 26, 53, 0, 22, 15, 0, 12, 7, 0, 32, 47, 0, 10,
   45, 0, 36, 19, 0, 38, 41, 0, 52, 21, 0, 6, 31, 0, 44, 35, 0, 40, 51, 0, 30, 43, 0, 50, 29, 0,
   28, 27]

def dlog2Mod81 (r : Nat) : Nat :=
  dlog2Mod81Table.getD r 0

def checkDlog2Mod81All : Bool :=
  (List.range 81).all (fun r =>
    if r % 3 == 0 then true
    else decide (dlog2Mod81 r < 54) && (2 ^ dlog2Mod81 r % 81 == r))

theorem checkDlog2Mod81All_true : checkDlog2Mod81All = true := by
  decide

theorem pow2_54_mod81 : 2 ^ 54 % 81 = 1 := by
  decide

theorem dlog2Mod81_spec (r : Nat) (hr_lt : r < 81) (hr_non3 : r % 3 ≠ 0) :
    dlog2Mod81 r < 54 ∧ 2 ^ dlog2Mod81 r % 81 = r := by
  have hall := checkDlog2Mod81All_true
  unfold checkDlog2Mod81All at hall
  have hmem : r ∈ List.range 81 := List.mem_range.mpr hr_lt
  have hr_ok := List.all_eq_true.mp hall r hmem
  have hne : (r % 3 == 0) = false := decide_eq_false hr_non3
  rw [hne] at hr_ok
  simp at hr_ok
  exact hr_ok

theorem exists_pow2_mul_congr_mod81 (x c : Nat)
    (hx : x % 3 ≠ 0) (hc : c % 3 ≠ 0) :
    ∃ a : Nat, a < 54 ∧ (2 ^ a * x) % 81 = c % 81 := by
  have hx81_lt : x % 81 < 81 := Nat.mod_lt x (by decide)
  have hc81_lt : c % 81 < 81 := Nat.mod_lt c (by decide)
  have hx81_n3 : (x % 81) % 3 ≠ 0 := by omega
  have hc81_n3 : (c % 81) % 3 ≠ 0 := by omega
  rcases dlog2Mod81_spec (x % 81) hx81_lt hx81_n3 with ⟨he1_lt, he1_eq⟩
  rcases dlog2Mod81_spec (c % 81) hc81_lt hc81_n3 with ⟨he2_lt, he2_eq⟩
  let e1 := dlog2Mod81 (x % 81)
  let e2 := dlog2Mod81 (c % 81)
  change e1 < 54 at he1_lt
  change 2 ^ e1 % 81 = x % 81 at he1_eq
  change e2 < 54 at he2_lt
  change 2 ^ e2 % 81 = c % 81 at he2_eq
  by_cases hle : e1 ≤ e2
  · refine ⟨e2 - e1, by omega, ?_⟩
    calc
      (2 ^ (e2 - e1) * x) % 81
          = ((2 ^ (e2 - e1) % 81) * (x % 81)) % 81 := Nat.mul_mod _ _ 81
      _ = ((2 ^ (e2 - e1) % 81) * (2 ^ e1 % 81)) % 81 := by rw [he1_eq]
      _ = (2 ^ (e2 - e1) * 2 ^ e1) % 81 := (Nat.mul_mod _ _ 81).symm
      _ = 2 ^ e2 % 81 := by rw [← Nat.pow_add, show e2 - e1 + e1 = e2 by omega]
      _ = c % 81 := he2_eq
  · refine ⟨54 + e2 - e1, by omega, ?_⟩
    calc
      (2 ^ (54 + e2 - e1) * x) % 81
          = ((2 ^ (54 + e2 - e1) % 81) * (x % 81)) % 81 := Nat.mul_mod _ _ 81
      _ = ((2 ^ (54 + e2 - e1) % 81) * (2 ^ e1 % 81)) % 81 := by rw [he1_eq]
      _ = (2 ^ (54 + e2 - e1) * 2 ^ e1) % 81 := (Nat.mul_mod _ _ 81).symm
      _ = 2 ^ (54 + e2) % 81 := by rw [← Nat.pow_add, show 54 + e2 - e1 + e1 = 54 + e2 by omega]
      _ = (2 ^ 54 * 2 ^ e2) % 81 := by rw [Nat.pow_add]
      _ = ((2 ^ 54 % 81) * (2 ^ e2 % 81)) % 81 := Nat.mul_mod _ _ 81
      _ = (1 * (c % 81)) % 81 := by rw [pow2_54_mod81, he2_eq]
      _ = c % 81 := by rw [Nat.one_mul, Nat.mod_mod]

/--
  Theorem 32.4 (Two-Return Escape + `(Z / 81Z)^*` Suffix-Shift Surjectivity):
  At ANY positive-weight second return `x2` (`2 ^ vMid.length * x2 = 3 ^ parityWeight vMid * x1 + affineCarry vMid`,
  `parityWeight vMid >= 1`), `x2` escapes `0 mod 3`, so for EVERY weight-4 backward word `u`
  (`parityWeight u = 4`), there exists `a < 54` (`φ(81) = 54`) such that `u' = u ++ List.replicate a false`
  preserves `parityWeight u' = 4` and `affineCarry u' = affineCarry u` while solving the exact
  3-adic backward congruence `(2 ^ u'.length * x2) % 81 = affineCarry u' % 81`!
-/
theorem two_return_escape_suffix_congruence_mod81
    (vMid u : List Bool) (x1 x2 : Nat)
    (hstep : 2 ^ vMid.length * x2 = 3 ^ parityWeight vMid * x1 + affineCarry vMid)
    (hw_mid : parityWeight vMid ≥ 1)
    (hu_wt : parityWeight u = 4) :
    ∃ a : Nat,
      a < 54 ∧
      let u' := u ++ List.replicate a false
      parityWeight u' = 4 ∧
      affineCarry u' = affineCarry u ∧
      (2 ^ u'.length * x2) % 3 ^ parityWeight u' = affineCarry u' % 3 ^ parityWeight u' := by
  have hx2_n3 : x2 % 3 ≠ 0 := (two_return_garden_of_eden_escape vMid x1 x2 hstep).2 hw_mid
  have hp2_n3 : (2 ^ u.length * x2) % 3 ≠ 0 := by
    have hp2 : ∀ k : Nat, 2 ^ k % 3 = 1 ∨ 2 ^ k % 3 = 2 := by
      intro k
      induction k with
      | zero => exact Or.inl rfl
      | succ k' ih =>
        rw [Nat.pow_succ, Nat.mul_mod]
        rcases ih with h1 | h2
        · rw [h1]; decide
        · rw [h2]; decide
    rw [Nat.mul_mod]
    rcases hp2 u.length with h1 | h2
    · rw [h1]; omega
    · rw [h2]; omega
  rcases affineCarryInt_pos_nondiv3_of_weight_pos u (by omega) with ⟨_, hc_int⟩
  rw [affineCarryInt_ofNat] at hc_int
  have hc_n3 : affineCarry u % 3 ≠ 0 := by omega
  rcases exists_pow2_mul_congr_mod81 (2 ^ u.length * x2) (affineCarry u) hp2_n3 hc_n3 with
    ⟨a, ha_lt, ha_congr⟩
  refine ⟨a, ha_lt, ?_⟩
  dsimp only
  rcases affineCarry_append_replicate_false u a with ⟨hwt, hcar⟩
  rw [hu_wt] at hwt
  refine ⟨hwt, hcar, ?_⟩
  rw [hwt, hcar]
  have hp34 : (3 : Nat) ^ 4 = 81 := rfl
  have hlen : (u ++ List.replicate a false).length = a + u.length := by
    rw [List.length_append, List.length_replicate, Nat.add_comm]
  rw [hp34, hlen, Nat.pow_add, Nat.mul_assoc]
  exact ha_congr


end CollatzFormal
