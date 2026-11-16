/-
  CollatzFormal/CSFullConjecture.lean
  Universal CS & Algebraic Reductions, Obstruction Meta-Theorems, and All-Weight
  (Z / 3^w Z)^* Primitive-Root Backward Surjectivity for the Full Collatz Campaign.

  Zero external dependencies (pure Lean 4.35.0 Core), zero `sorry`,
  zero `native_decide`, zero custom `axiom`.
-/

import CollatzFormal.Core
import CollatzFormal.BoostMechanisms

namespace CollatzFormal

-- ============================================================================
-- SECTION 1: All-Weight (∀ w ≥ 1) 3-Adic Lifting-the-Exponent & Primitive Root
--            Surjectivity of 2 on (Z / 3^w Z)^*
-- ============================================================================

/--
  Constructive 3-adic Lifting-the-Exponent (LTE) quotient sequence `k_m` satisfying
    `2 ^ (2 * 3 ^ m) = 1 + 3 ^ (m + 1) * totient3Coeff m`
  with `totient3Coeff m % 3 = 1` for every `m : Nat`.
-/
def totient3Coeff : Nat -> Nat
  | 0 => 1
  | m + 1 =>
    let k := totient3Coeff m
    let X := 3 ^ (m + 1) * k
    k * (1 + X + 3 ^ m * k * X)

theorem cube_one_add_nat (X : Nat) :
    (1 + X) * (1 + X) * (1 + X) = 1 + 3 * X + 3 * (X * X) + X * (X * X) := by
  have h2 : (1 + X) * (1 + X) = 1 + 2 * X + X * X := by
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.mul_one]
    omega
  rw [h2, Nat.add_mul (1 + 2 * X) (X * X) (1 + X),
      Nat.mul_add (1 + 2 * X) 1 X, Nat.mul_one,
      Nat.add_mul 1 (2 * X) X, Nat.one_mul,
      Nat.mul_add (X * X) 1 X, Nat.mul_one,
      Nat.mul_assoc 2 X X, Nat.mul_assoc X X X]
  omega

/--
  Universal Inductive 3-Adic LTE Law (`∀ m : Nat`):
  `2 ^ (2 * 3 ^ m) = 1 + 3 ^ (m + 1) * totient3Coeff m` and `totient3Coeff m % 3 = 1`.
-/
theorem pow2_totient_3adic_lift : ∀ m : Nat,
    2 ^ (2 * 3 ^ m) = 1 + 3 ^ (m + 1) * totient3Coeff m ∧
    totient3Coeff m % 3 = 1
  | 0 => ⟨rfl, rfl⟩
  | m + 1 => by
    rcases pow2_totient_3adic_lift m with ⟨ih_eq, ih_mod⟩
    let k := totient3Coeff m
    let M0 := 3 ^ m
    let X := 3 ^ (m + 1) * k
    change 2 ^ (2 * M0) = 1 + X at ih_eq
    change k % 3 = 1 at ih_mod
    have hexp : 2 * 3 ^ (m + 1) = 2 * M0 + 2 * M0 + 2 * M0 := by
      dsimp [M0]
      rw [Nat.pow_succ]
      omega
    have hp3_m1 : 3 ^ (m + 1) = 3 * M0 := by
      dsimp [M0]
      rw [Nat.pow_succ, Nat.mul_comm]
    have hp3_m2 : 3 ^ (m + 2) = 3 * 3 ^ (m + 1) := by
      rw [Nat.pow_succ, Nat.mul_comm]
    have hX_eq : X = 3 * (M0 * k) := by
      dsimp [X]
      rw [hp3_m1, Nat.mul_assoc]
    have hpow_cube : 2 ^ (2 * 3 ^ (m + 1)) = (1 + X) * (1 + X) * (1 + X) := by
      rw [hexp, Nat.pow_add, Nat.pow_add, ih_eq]
    have hfact :
        3 ^ (m + 2) * (k * (1 + X + M0 * k * X)) =
          3 * X + 3 * (X * X) + X * (X * X) := by
      have h3k : 3 ^ (m + 2) * k = 3 * X := by
        dsimp [X]
        rw [hp3_m2, Nat.mul_assoc]
      calc
        3 ^ (m + 2) * (k * (1 + X + M0 * k * X))
            = (3 ^ (m + 2) * k) * (1 + X + M0 * k * X) := (Nat.mul_assoc _ _ _).symm
        _ = (3 * X) * (1 + X + M0 * k * X) := by rw [h3k]
        _ = (3 * X) * (1 + X) + (3 * X) * (M0 * k * X) := Nat.mul_add _ _ _
        _ = (3 * X) * 1 + (3 * X) * X + (3 * X) * (M0 * k * X) := by rw [Nat.mul_add]
        _ = 3 * X + 3 * (X * X) + (3 * X) * (M0 * k * X) := by
              rw [Nat.mul_one, Nat.mul_assoc 3 X X]
        _ = 3 * X + 3 * (X * X) + X * (X * X) := by
              have hlast : (3 * X) * (M0 * k * X) = X * (X * X) := by
                calc
                  (3 * X) * (M0 * k * X)
                      = (X * 3) * (M0 * k * X) := by rw [Nat.mul_comm 3 X]
                  _ = X * (3 * (M0 * k * X)) := Nat.mul_assoc X 3 _
                  _ = X * ((3 * (M0 * k)) * X) := by rw [Nat.mul_assoc 3 (M0 * k) X]
                  _ = X * (X * X) := by rw [← hX_eq]
              rw [hlast]
    refine ⟨?_, ?_⟩
    · simp only [totient3Coeff]
      change 2 ^ (2 * 3 ^ (m + 1)) = 1 + 3 ^ (m + 2) * (k * (1 + X + M0 * k * X))
      rw [hpow_cube, cube_one_add_nat X, hfact]
      omega
    · simp only [totient3Coeff]
      change (k * (1 + X + M0 * k * X)) % 3 = 1
      have hX_mod3 : X % 3 = 0 := by rw [hX_eq]; omega
      have hMKX_mod3 : (M0 * k * X) % 3 = 0 := by
        rw [Nat.mul_mod, hX_mod3, Nat.mul_zero, Nat.zero_mod]
      have hinner_mod3 : (1 + X + M0 * k * X) % 3 = 1 := by
        rw [Nat.add_mod (1 + X) (M0 * k * X) 3, hMKX_mod3, Nat.add_zero,
            Nat.mod_mod, Nat.add_mod 1 X 3, hX_mod3]
      rw [Nat.mul_mod, ih_mod, hinner_mod3]

/--
  Universal All-Weight Exact 3-Adic Valuation of `2 ^ (2 * 3 ^ (w - 1)) - 1` (`∀ w ≥ 1`):
  Eliminates finite-weight restrictions by proving for EVERY `w ≥ 1`:
  (1) `2 ^ (2 * 3 ^ (w - 1)) = 1 + 3 ^ w * totient3Coeff (w - 1)` with `totient3Coeff (w - 1) % 3 ≠ 0`,
  (2) `2 ^ (2 * 3 ^ (w - 1)) % 3 ^ w = 1`, and
  (3) `2 ^ (2 * 3 ^ (w - 1)) % 3 ^ (w + 1) = 1 + 3 ^ w` (exact 3-adic valuation `v_3 = w`).
-/
theorem pow2_totient_exact_valuation_all_weights (w : Nat) (hw : w ≥ 1) :
    2 ^ (2 * 3 ^ (w - 1)) = 1 + 3 ^ w * totient3Coeff (w - 1) ∧
    totient3Coeff (w - 1) % 3 ≠ 0 ∧
    2 ^ (2 * 3 ^ (w - 1)) % 3 ^ w = 1 ∧
    2 ^ (2 * 3 ^ (w - 1)) % 3 ^ (w + 1) = 1 + 3 ^ w := by
  rcases pow2_totient_3adic_lift (w - 1) with ⟨hlift, hmod1⟩
  have hw_eq : (w - 1) + 1 = w := by omega
  rw [hw_eq] at hlift
  have hp3w_gt1 : 3 ^ w > 1 := by
    rw [← hw_eq, Nat.pow_succ]
    have hp0 : 3 ^ (w - 1) ≥ 1 := pow3_pos_nat (w - 1)
    omega
  have hmod_pw : (1 + 3 ^ w * totient3Coeff (w - 1)) % 3 ^ w = 1 := by
    have hm0 : (3 ^ w * totient3Coeff (w - 1)) % 3 ^ w = 0 := by
      rw [Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod]
    rw [Nat.add_mod, hm0, Nat.add_zero, Nat.mod_mod, Nat.mod_eq_of_lt hp3w_gt1]
  have hmod_pw1 : (1 + 3 ^ w * totient3Coeff (w - 1)) % 3 ^ (w + 1) = 1 + 3 ^ w := by
    let q := totient3Coeff (w - 1) / 3
    have hk_decomp : totient3Coeff (w - 1) = 3 * q + 1 := by dsimp [q]; omega
    have hp3_succ : 3 ^ (w + 1) = 3 ^ w * 3 := Nat.pow_succ 3 w
    have hrew : 1 + 3 ^ w * totient3Coeff (w - 1) = (1 + 3 ^ w) + 3 ^ (w + 1) * q := by
      rw [hk_decomp, Nat.mul_add, Nat.mul_one, hp3_succ, ← Nat.mul_assoc (3 ^ w) 3 q]
      omega
    have hlt : 1 + 3 ^ w < 3 ^ (w + 1) := by
      rw [hp3_succ]
      omega
    have hm0 : (3 ^ (w + 1) * q) % 3 ^ (w + 1) = 0 := by
      rw [Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod]
    rw [hrew, Nat.add_mod, hm0, Nat.add_zero, Nat.mod_mod, Nat.mod_eq_of_lt hlt]
  refine ⟨hlift, by omega, ?_, ?_⟩
  · rw [hlift]; exact hmod_pw
  · rw [hlift]; exact hmod_pw1

theorem mod_three_mul_decomp (z M : Nat) (hM : M > 0) :
    z % (3 * M) = M * ((z / M) % 3) + z % M := by
  let q := z / M
  let rem := z % M
  have hrem_lt : rem < M := Nat.mod_lt z hM
  have hz_eq : z = M * q + rem := (Nat.div_add_mod z M).symm
  let q3 := q / 3
  let r3 := q % 3
  have hr3_lt : r3 < 3 := Nat.mod_lt q (by decide)
  have hq_eq : q = 3 * q3 + r3 := (Nat.div_add_mod q 3).symm
  have hlt_3M : M * r3 + rem < 3 * M := by
    have hm : M * r3 ≤ M * 2 := Nat.mul_le_mul_left M (by omega)
    omega
  have hz_3M : z = (M * r3 + rem) + (3 * M) * q3 := by
    calc
      z = M * (3 * q3 + r3) + rem := by rw [hz_eq, hq_eq]
      _ = M * (3 * q3) + M * r3 + rem := by rw [Nat.mul_add]
      _ = (3 * M) * q3 + M * r3 + rem := by
            rw [← Nat.mul_assoc M 3 q3, Nat.mul_comm M 3]
      _ = (M * r3 + rem) + (3 * M) * q3 := by omega
  have hm0 : ((3 * M) * q3) % (3 * M) = 0 := by
    rw [Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod]
  conv => lhs; rw [hz_3M]
  rw [Nat.add_mod, hm0, Nat.add_zero, Nat.mod_mod, Nat.mod_eq_of_lt hlt_3M]

theorem add_mul_mod_three_mul (z c M q rem : Nat)
    (hrem_lt : rem < M)
    (hz_mod : z % (3 * M) = M * q + rem) :
    (z + M * c) % (3 * M) = M * ((q + c % 3) % 3) + rem := by
  let Qz := z / (3 * M)
  have hz_eq : z = (3 * M) * Qz + (M * q + rem) := by
    have hdm := (Nat.div_add_mod z (3 * M)).symm
    rw [hz_mod] at hdm
    exact hdm
  let qc := c / 3
  let rc := c % 3
  have hc_eq : c = 3 * qc + rc := (Nat.div_add_mod c 3).symm
  let qs := (q + rc) / 3
  let rs := (q + rc) % 3
  have hrs_lt : rs < 3 := Nat.mod_lt (q + rc) (by decide)
  have hsum_eq : q + rc = 3 * qs + rs := (Nat.div_add_mod (q + rc) 3).symm
  have hlt_3M : M * rs + rem < 3 * M := by
    have hm : M * rs ≤ M * 2 := Nat.mul_le_mul_left M (by omega)
    omega
  have htot : z + M * c = (M * rs + rem) + (3 * M) * (Qz + qc + qs) := by
    calc
      z + M * c
          = (3 * M) * Qz + (M * q + rem) + M * (3 * qc + rc) := by rw [hz_eq, hc_eq]
      _ = (3 * M) * Qz + (M * (3 * qc) + M * (q + rc)) + rem := by
            rw [Nat.mul_add M (3 * qc) rc, Nat.mul_add M q rc]
            omega
      _ = (3 * M) * Qz + ((3 * M) * qc + M * (3 * qs + rs)) + rem := by
            rw [← Nat.mul_assoc M 3 qc, Nat.mul_comm M 3, hsum_eq]
      _ = (3 * M) * Qz + ((3 * M) * qc + ((3 * M) * qs + M * rs)) + rem := by
            rw [Nat.mul_add M (3 * qs) rs, ← Nat.mul_assoc M 3 qs, Nat.mul_comm M 3]
      _ = (M * rs + rem) + ((3 * M) * Qz + (3 * M) * qc + (3 * M) * qs) := by omega
      _ = (M * rs + rem) + (3 * M) * (Qz + qc + qs) := by
            rw [← Nat.mul_add (3 * M) Qz qc, ← Nat.mul_add (3 * M) (Qz + qc) qs]
  have hm0 : ((3 * M) * (Qz + qc + qs)) % (3 * M) = 0 := by
    rw [Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod]
  conv => lhs; rw [htot]
  rw [Nat.add_mod, hm0, Nat.add_zero, Nat.mod_mod, Nat.mod_eq_of_lt hlt_3M]

theorem pow2_mod3_one_or_two : ∀ k : Nat, 2 ^ k % 3 = 1 ∨ 2 ^ k % 3 = 2
  | 0 => Or.inl rfl
  | k + 1 => by
    rw [Nat.pow_succ, Nat.mul_mod]
    rcases pow2_mod3_one_or_two k with h1 | h2
    · rw [h1]; decide
    · rw [h2]; decide

/--
  Constructive Hensel-Lifted Discrete Logarithm Base `2` on `(Z / 3^(m+1) Z)^*`:
  Computes `0 <= e < 2 * 3 ^ m` satisfying `2 ^ e % 3 ^ (m + 1) = r % 3 ^ (m + 1)`
  for EVERY `m : Nat` and EVERY `r : Nat` with `r % 3 ≠ 0` (zero lookup tables!).
-/
def dlog2ModPow3Aux : Nat -> Nat -> Nat
  | 0, r => if r % 3 == 1 then 0 else 1
  | m + 1, r =>
    let e := dlog2ModPow3Aux m r
    let P := 2 * 3 ^ m
    let M3 := 3 ^ (m + 2)
    if 2 ^ e % M3 == r % M3 then e
    else if 2 ^ (e + P) % M3 == r % M3 then e + P
    else e + 2 * P

def dlog2ModPow3 (w r : Nat) : Nat :=
  dlog2ModPow3Aux (w - 1) r

theorem dlog2ModPow3Aux_spec : ∀ (m r : Nat),
    r % 3 ≠ 0 ->
    dlog2ModPow3Aux m r < 2 * 3 ^ m ∧
    2 ^ (dlog2ModPow3Aux m r) % 3 ^ (m + 1) = r % 3 ^ (m + 1)
  | 0, r, hr => by
    simp only [dlog2ModPow3Aux]
    by_cases h1 : r % 3 = 1
    · have hb : (r % 3 == 1) = true := decide_eq_true h1
      rw [hb]
      exact ⟨by decide, by simp [h1]⟩
    · have h2 : r % 3 = 2 := by omega
      have hb : (r % 3 == 1) = false := decide_eq_false h1
      rw [hb]
      exact ⟨by decide, by simp [h2]⟩
  | m + 1, r, hr => by
    rcases dlog2ModPow3Aux_spec m r hr with ⟨he_lt, he_mod⟩
    rcases pow2_totient_3adic_lift m with ⟨hlte, hk_mod3⟩
    let e := dlog2ModPow3Aux m r
    let P := 2 * 3 ^ m
    let M := 3 ^ (m + 1)
    let M3 := 3 ^ (m + 2)
    let k := totient3Coeff m
    change e < P at he_lt
    change 2 ^ e % M = r % M at he_mod
    change 2 ^ P = 1 + M * k at hlte
    change k % 3 = 1 at hk_mod3
    have hM_pos : M > 0 := pow3_pos_nat (m + 1)
    have hM3_eq : M3 = 3 * M := by dsimp [M3, M]; rw [Nat.pow_succ, Nat.mul_comm]
    have hP_next : 2 * 3 ^ (m + 1) = 3 * P := by dsimp [P]; rw [Nat.pow_succ]; omega
    let rem := r % M
    have hrem_lt : rem < M := Nat.mod_lt r hM_pos
    let q0 := (2 ^ e / M) % 3
    let qr := (r / M) % 3
    have hq0_lt : q0 < 3 := Nat.mod_lt _ (by decide)
    have hqr_lt : qr < 3 := Nat.mod_lt _ (by decide)
    have hz0_mod : 2 ^ e % (3 * M) = M * q0 + rem := by
      have hm := mod_three_mul_decomp (2 ^ e) M hM_pos
      rw [he_mod] at hm
      exact hm
    have hr_mod : r % (3 * M) = M * qr + rem := mod_three_mul_decomp r M hM_pos
    let z0 := 2 ^ e
    let z1 := 2 ^ (e + P)
    let z2 := 2 ^ (e + 2 * P)
    have hz1_step : z1 = z0 + M * (z0 * k) := by
      dsimp [z1, z0]
      rw [Nat.pow_add, hlte, Nat.mul_add, Nat.mul_one]
      have ha : 2 ^ e * (M * k) = M * (2 ^ e * k) := by
        rw [← Nat.mul_assoc, Nat.mul_comm (2 ^ e) M, Nat.mul_assoc]
      rw [ha]
    have hz2_step : z2 = z1 + M * (z1 * k) := by
      dsimp [z2, z1]
      rw [show e + 2 * P = (e + P) + P by omega, Nat.pow_add, hlte, Nat.mul_add, Nat.mul_one]
      have ha : 2 ^ (e + P) * (M * k) = M * (2 ^ (e + P) * k) := by
        rw [← Nat.mul_assoc, Nat.mul_comm (2 ^ (e + P)) M, Nat.mul_assoc]
      rw [ha]
    let s := z0 % 3
    have hs_12 : s = 1 ∨ s = 2 := pow2_mod3_one_or_two e
    have hM_div3 : M % 3 = 0 := by
      dsimp [M]
      rw [Nat.pow_succ, Nat.mul_mod]
      simp
    have hz0k_mod3 : (z0 * k) % 3 = s := by
      rw [Nat.mul_mod, hk_mod3, Nat.mul_one]
      dsimp [s]
      exact Nat.mod_mod z0 3
    have hz1_mod3 : z1 % 3 = s := by
      rw [hz1_step, Nat.add_mod, Nat.mul_mod, hM_div3, Nat.zero_mul, Nat.zero_mod,
          Nat.add_zero, Nat.mod_mod]
    have hz1k_mod3 : (z1 * k) % 3 = s := by
      rw [Nat.mul_mod, hz1_mod3, hk_mod3, Nat.mul_one]
      rcases hs_12 with hs | hs <;> rw [hs] <;> decide
    have hz1_mod : z1 % (3 * M) = M * ((q0 + s) % 3) + rem := by
      rw [hz1_step, add_mul_mod_three_mul z0 (z0 * k) M q0 rem hrem_lt hz0_mod, hz0k_mod3]
    have hz2_mod : z2 % (3 * M) = M * (((q0 + s) % 3 + s) % 3) + rem := by
      rw [hz2_step, add_mul_mod_three_mul z1 (z1 * k) M ((q0 + s) % 3) rem hrem_lt hz1_mod,
          hz1k_mod3]
    have hhit : z0 % M3 = r % M3 ∨ z1 % M3 = r % M3 ∨ z2 % M3 = r % M3 := by
      rw [hM3_eq, hz0_mod, hz1_mod, hz2_mod, hr_mod]
      have hq_cases :
          q0 = qr ∨ (q0 + s) % 3 = qr ∨ ((q0 + s) % 3 + s) % 3 = qr := by
        rcases hs_12 with hs | hs <;> omega
      rcases hq_cases with h0 | h1 | h2
      · exact Or.inl (by rw [h0])
      · exact Or.inr (Or.inl (by rw [h1]))
      · exact Or.inr (Or.inr (by rw [h2]))
    simp only [dlog2ModPow3Aux]
    change (let e0 := e; let P0 := P; let M30 := M3;
      if 2 ^ e0 % M30 == r % M30 then e0
      else if 2 ^ (e0 + P0) % M30 == r % M30 then e0 + P0
      else e0 + 2 * P0) < 2 * 3 ^ (m + 1) ∧
      2 ^ (let e0 := e; let P0 := P; let M30 := M3;
        if 2 ^ e0 % M30 == r % M30 then e0
        else if 2 ^ (e0 + P0) % M30 == r % M30 then e0 + P0
        else e0 + 2 * P0) % M3 = r % M3
    dsimp only
    by_cases hc0 : z0 % M3 = r % M3
    · have hb0 : (2 ^ e % M3 == r % M3) = true := decide_eq_true hc0
      rw [hb0]
      simp only [ite_true]
      exact ⟨by rw [hP_next]; omega, hc0⟩
    · have hb0 : (2 ^ e % M3 == r % M3) = false := decide_eq_false hc0
      rw [hb0]
      simp only [Bool.false_eq_true, ite_false]
      by_cases hc1 : z1 % M3 = r % M3
      · have hb1 : (2 ^ (e + P) % M3 == r % M3) = true := decide_eq_true hc1
        rw [hb1]
        simp only [ite_true]
        exact ⟨by rw [hP_next]; omega, hc1⟩
      · have hb1 : (2 ^ (e + P) % M3 == r % M3) = false := decide_eq_false hc1
        rw [hb1]
        simp only [Bool.false_eq_true, ite_false]
        have hc2 : z2 % M3 = r % M3 := by
          rcases hhit with h0 | h1 | h2
          · exact False.elim (hc0 h0)
          · exact False.elim (hc1 h1)
          · exact h2
        exact ⟨by rw [hP_next]; omega, hc2⟩

/--
  Universal All-Weight Discrete Logarithm Specification (`∀ w ≥ 1`):
  For EVERY weight `w ≥ 1` and EVERY `r : Nat` with `r % 3 ≠ 0`,
  `dlog2ModPow3 w r < 2 * 3 ^ (w - 1)` and `2 ^ (dlog2ModPow3 w r) % 3 ^ w = r % 3 ^ w`.
-/
theorem dlog2ModPow3_spec (w r : Nat) (hw : w ≥ 1) (hr : r % 3 ≠ 0) :
    dlog2ModPow3 w r < 2 * 3 ^ (w - 1) ∧
    2 ^ (dlog2ModPow3 w r) % 3 ^ w = r % 3 ^ w := by
  unfold dlog2ModPow3
  rcases dlog2ModPow3Aux_spec (w - 1) r hr with ⟨hlt, hmod⟩
  rw [show (w - 1) + 1 = w by omega] at hmod
  exact ⟨hlt, hmod⟩

theorem lt_three_cases (q : Nat) (hq : q < 3) : q = 0 ∨ q = 1 ∨ q = 2 := by
  omega

/--
  Universal Exact Multiplicative Order of `2` Modulo `3 ^ w` (`∀ w ≥ 1`):
  No positive exponent `0 < d < 2 * 3 ^ (w - 1)` ever satisfies `2 ^ d % 3 ^ w = 1`,
  proving `2` is a primitive root of `(Z / 3^w Z)^*` of exact order `φ(3^w) = 2 * 3^(w-1)`
  for EVERY `w ≥ 1`!
-/
theorem pow2_order_mod_pow3_aux : ∀ (m d : Nat),
    0 < d -> d < 2 * 3 ^ m -> 2 ^ d % 3 ^ (m + 1) ≠ 1
  | 0, d, hd_pos, hd_lt, h1 => by
    have hd1 : d = 1 := by omega
    subst hd1
    exact absurd h1 (by decide)
  | m + 1, d, hd_pos, hd_lt, h1 => by
    let P := 2 * 3 ^ m
    let M := 3 ^ (m + 1)
    let M3 := 3 ^ (m + 2)
    have hP_pos : P > 0 := by
      have hp : 3 ^ m ≥ 1 := pow3_pos_nat m
      dsimp [P]; omega
    have hM_gt1 : M > 1 := by
      dsimp [M]; rw [Nat.pow_succ]
      have hp : 3 ^ m ≥ 1 := pow3_pos_nat m
      omega
    have hM3_eq : M3 = M * 3 := Nat.pow_succ 3 (m + 1)
    have hd_lt_3P : d < 3 * P := by
      have h3 : 2 * 3 ^ (m + 1) = 3 * P := by dsimp [P]; rw [Nat.pow_succ]; omega
      omega
    -- First project `2^d % M3 = 1` down to `2^d % M = 1`:
    let Q3 := 2 ^ d / M3
    have hd_mod_M : 2 ^ d % M = 1 := by
      have hdm : 2 ^ d = M3 * Q3 + 2 ^ d % M3 := (Nat.div_add_mod (2 ^ d) M3).symm
      change 2 ^ d % M3 = 1 at h1
      rw [h1, hM3_eq, Nat.mul_assoc] at hdm
      have hm0 : (M * (3 * Q3)) % M = 0 := by
        rw [Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod]
      rw [hdm, Nat.add_mod, hm0, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hM_gt1]
    -- Divide `d = P * q + rem` with `rem < P` and `q < 3`:
    let q := d / P
    let rem := d % P
    have hrem_lt : rem < P := Nat.mod_lt d hP_pos
    have hd_decomp : d = P * q + rem := (Nat.div_add_mod d P).symm
    have hq_lt3 : q < 3 := by
      apply Classical.byContradiction
      intro hge3
      have hm : P * 3 ≤ P * q := Nat.mul_le_mul_left P (by omega)
      omega
    have hq_012 : q = 0 ∨ q = 1 ∨ q = 2 := lt_three_cases q hq_lt3
    rcases pow2_totient_3adic_lift m with ⟨hlte, _⟩
    change 2 ^ P = 1 + M * totient3Coeff m at hlte
    have h2P_mod_M : 2 ^ P % M = 1 := by
      rw [hlte]
      have hm0 : (M * totient3Coeff m) % M = 0 := by
        rw [Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod]
      rw [Nat.add_mod, hm0, Nat.add_zero, Nat.mod_mod, Nat.mod_eq_of_lt hM_gt1]
    have h2Pq_mod_M : 2 ^ (P * q) % M = 1 := by
      rcases hq_012 with hq0 | hq1 | hq2
      · rw [hq0, Nat.mul_zero, Nat.pow_zero, Nat.mod_eq_of_lt hM_gt1]
      · rw [hq1, Nat.mul_one]; exact h2P_mod_M
      · rw [hq2, show P * 2 = P + P by omega, Nat.pow_add, Nat.mul_mod, h2P_mod_M,
            Nat.one_mul, Nat.mod_eq_of_lt hM_gt1]
    have hrem_mod_M : 2 ^ rem % M = 1 := by
      rw [hd_decomp, Nat.pow_add, Nat.mul_mod, h2Pq_mod_M, Nat.one_mul, Nat.mod_mod] at hd_mod_M
      exact hd_mod_M
    have hrem_zero : rem = 0 := by
      by_cases hr0 : rem = 0
      · exact hr0
      · exact False.elim (pow2_order_mod_pow3_aux m rem (by omega) hrem_lt hrem_mod_M)
    rw [hrem_zero, Nat.add_zero] at hd_decomp
    have hq_12 : q = 1 ∨ q = 2 := by
      rcases hq_012 with hq0 | hq1 | hq2
      · rw [hq0, Nat.mul_zero] at hd_decomp; omega
      · exact Or.inl hq1
      · exact Or.inr hq2
    -- Check `q = 1` (`d = P`) and `q = 2` (`d = 2 * P`) modulo `M3 = 3 * M`:
    have hp1_val := (pow2_totient_exact_valuation_all_weights (m + 1) (by omega)).2.2.2
    change 2 ^ P % M3 = 1 + M at hp1_val
    rcases hq_12 with hq1 | hq2
    · rw [hq1, Nat.mul_one] at hd_decomp
      rw [hd_decomp] at h1
      change 2 ^ P % M3 = 1 at h1
      rw [hp1_val] at h1
      omega
    · rw [hq2, show P * 2 = P + P by omega] at hd_decomp
      rw [hd_decomp, Nat.pow_add, Nat.mul_mod, hp1_val] at h1
      change ((1 + M) * (1 + M)) % M3 = 1 at h1
      have hsq : (1 + M) * (1 + M) = (1 + 2 * M) + M3 * 3 ^ m := by
        have hM_split : M = 3 * 3 ^ m := by dsimp [M]; rw [Nat.pow_succ, Nat.mul_comm]
        have hMM : M * M = M3 * 3 ^ m := by
          calc
            M * M = M * (3 * 3 ^ m) := by rw [hM_split]
            _ = (M * 3) * 3 ^ m := (Nat.mul_assoc M 3 (3 ^ m)).symm
            _ = M3 * 3 ^ m := by rw [← hM3_eq]
        calc
          (1 + M) * (1 + M) = 1 + 2 * M + M * M := by
            rw [Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.mul_one]; omega
          _ = (1 + 2 * M) + M3 * 3 ^ m := by rw [hMM]
      have hlt_M3 : 1 + 2 * M < M3 := by rw [hM3_eq]; omega
      have hm0 : (M3 * 3 ^ m) % M3 = 0 := by
        rw [Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod]
      rw [hsq, Nat.add_mod, hm0, Nat.add_zero, Nat.mod_mod, Nat.mod_eq_of_lt hlt_M3] at h1
      omega

theorem pow2_order_mod_pow3_exact (w d : Nat)
    (hw : w ≥ 1) (hd_pos : 0 < d) (hd_lt : d < 2 * 3 ^ (w - 1)) :
    2 ^ d % 3 ^ w ≠ 1 := by
  have h := pow2_order_mod_pow3_aux (w - 1) d hd_pos hd_lt
  rwa [show (w - 1) + 1 = w by omega] at h

/--
  Universal All-Weight Multiplicative Shift Congruence Modulo `3 ^ w` (`∀ w ≥ 1`):
  For EVERY `w ≥ 1` and EVERY `x, c : Nat` coprime to `3` (`x % 3 ≠ 0`, `c % 3 ≠ 0`),
  there exists `a < 2 * 3 ^ (w - 1)` such that for EVERY period multiple `q : Nat`,
  `(2 ^ (a + q * (2 * 3 ^ (w - 1))) * x) % 3 ^ w = c % 3 ^ w`!
-/
theorem pow2_period_mul_mod_pow3 (w : Nat) (hw : w ≥ 1) :
    ∀ q : Nat, 2 ^ (q * (2 * 3 ^ (w - 1))) % 3 ^ w = 1
  | 0 => by
    have hp3_gt1 : 3 ^ w > 1 := by
      rw [show w = (w - 1) + 1 by omega, Nat.pow_succ]
      have hp : 3 ^ (w - 1) ≥ 1 := pow3_pos_nat (w - 1)
      omega
    simp [Nat.mod_eq_of_lt hp3_gt1]
  | q + 1 => by
    have ih := pow2_period_mul_mod_pow3 w hw q
    have hp1 := (pow2_totient_exact_valuation_all_weights w hw).2.2.1
    have hp3_gt1 : 3 ^ w > 1 := by
      rw [show w = (w - 1) + 1 by omega, Nat.pow_succ]
      have hp : 3 ^ (w - 1) ≥ 1 := pow3_pos_nat (w - 1)
      omega
    rw [Nat.succ_mul, Nat.pow_add, Nat.mul_mod, ih, hp1, Nat.one_mul,
        Nat.mod_eq_of_lt hp3_gt1]

theorem exists_pow2_mul_congr_mod_pow3 (w x c : Nat)
    (hw : w ≥ 1) (hx : x % 3 ≠ 0) (hc : c % 3 ≠ 0) :
    ∃ a : Nat,
      a < 2 * 3 ^ (w - 1) ∧
      ∀ q : Nat, (2 ^ (a + q * (2 * 3 ^ (w - 1))) * x) % 3 ^ w = c % 3 ^ w := by
  let P := 2 * 3 ^ (w - 1)
  let M := 3 ^ w
  rcases dlog2ModPow3_spec w x hw hx with ⟨he1_lt, he1_eq⟩
  rcases dlog2ModPow3_spec w c hw hc with ⟨he2_lt, he2_eq⟩
  let e1 := dlog2ModPow3 w x
  let e2 := dlog2ModPow3 w c
  change e1 < P at he1_lt
  change 2 ^ e1 % M = x % M at he1_eq
  change e2 < P at he2_lt
  change 2 ^ e2 % M = c % M at he2_eq
  have hbase : ∃ a : Nat, a < P ∧ (2 ^ a * x) % M = c % M := by
    by_cases hle : e1 ≤ e2
    · refine ⟨e2 - e1, by omega, ?_⟩
      calc
        (2 ^ (e2 - e1) * x) % M
            = ((2 ^ (e2 - e1) % M) * (x % M)) % M := Nat.mul_mod _ _ M
        _ = ((2 ^ (e2 - e1) % M) * (2 ^ e1 % M)) % M := by rw [he1_eq]
        _ = (2 ^ (e2 - e1) * 2 ^ e1) % M := (Nat.mul_mod _ _ M).symm
        _ = 2 ^ e2 % M := by rw [← Nat.pow_add, show e2 - e1 + e1 = e2 by omega]
        _ = c % M := he2_eq
    · refine ⟨P + e2 - e1, by omega, ?_⟩
      have hp1 : 2 ^ P % M = 1 := (pow2_totient_exact_valuation_all_weights w hw).2.2.1
      calc
        (2 ^ (P + e2 - e1) * x) % M
            = ((2 ^ (P + e2 - e1) % M) * (x % M)) % M := Nat.mul_mod _ _ M
        _ = ((2 ^ (P + e2 - e1) % M) * (2 ^ e1 % M)) % M := by rw [he1_eq]
        _ = (2 ^ (P + e2 - e1) * 2 ^ e1) % M := (Nat.mul_mod _ _ M).symm
        _ = 2 ^ (P + e2) % M := by rw [← Nat.pow_add, show P + e2 - e1 + e1 = P + e2 by omega]
        _ = (2 ^ P * 2 ^ e2) % M := by rw [Nat.pow_add]
        _ = ((2 ^ P % M) * (2 ^ e2 % M)) % M := Nat.mul_mod _ _ M
        _ = (1 * (c % M)) % M := by rw [hp1, he2_eq]
        _ = c % M := by rw [Nat.one_mul, Nat.mod_mod]
  rcases hbase with ⟨a, ha_lt, ha_congr⟩
  refine ⟨a, ha_lt, ?_⟩
  intro q
  have hpq : 2 ^ (q * P) % M = 1 := pow2_period_mul_mod_pow3 w hw q
  calc
    (2 ^ (a + q * P) * x) % M
        = (2 ^ (q * P) * (2 ^ a * x)) % M := by
            rw [Nat.pow_add, Nat.mul_comm (2 ^ a) (2 ^ (q * P)), Nat.mul_assoc]
    _ = ((2 ^ (q * P) % M) * ((2 ^ a * x) % M)) % M := Nat.mul_mod _ _ M
    _ = (1 * (c % M)) % M := by rw [hpq, ha_congr]
    _ = c % M := by rw [Nat.one_mul, Nat.mod_mod]

-- ============================================================================
-- SECTION 2: Universal Sign-Separation of General Affine Preimages &
--            All-Weight Two-Return Backward Exact Division (∀ w ≥ 1, ∀ q ≥ 0)
-- ============================================================================

/--
  Universal Sign-Separation of General `(2, 3)`-Affine Preimages over `Z`:
  Generalizing `one_equation_forces_pos` (`y = 1`) to ALL positive targets `y ≥ 1`:
  whenever `2 ^ |u| * y = 3 ^ w(u) * x + C(u)` with `y ≥ 1`, the integer preimage
  `x : Int` AUTOMATICALLY satisfies `x ≥ 1`!
  Conversely, on `M2 = Z^-` (`y ≤ 0`) with `w(u) ≥ 1`, `x` is strictly negative (`x ≤ -1`).
-/
theorem general_affine_forces_pos_of_target_pos (u : List Bool) (x y : Int)
    (hy_pos : y ≥ 1)
    (heq : (2 : Int) ^ u.length * y = (3 : Int) ^ parityWeight u * x + affineCarryInt u) :
    x ≥ 1 := by
  rcases general_affine_converse_universal u x y heq with ⟨_, hiter⟩
  apply Classical.byContradiction
  intro hnp
  have hle : x ≤ 0 := by omega
  have hiter_np := collatzIterInt_nonpos u.length x hle
  omega

theorem general_affine_forces_neg_of_target_nonpos (u : List Bool) (x y : Int)
    (hw : parityWeight u ≥ 1)
    (hy_np : y ≤ 0)
    (heq : (2 : Int) ^ u.length * y = (3 : Int) ^ parityWeight u * x + affineCarryInt u) :
    x ≤ -1 := by
  rcases affineCarryInt_pos_nondiv3_of_weight_pos u hw with ⟨hc_pos, _⟩
  have hp2_pos : (2 : Int) ^ u.length ≥ 1 := pow_pos_int 2 u.length (by omega)
  have hp3_pos : (3 : Int) ^ parityWeight u ≥ 1 := pow_pos_int 3 (parityWeight u) (by omega)
  have hlhs_np : (2 : Int) ^ u.length * y ≤ 0 := by
    have hm : (2 : Int) ^ u.length * (-y) ≥ 0 :=
      Int.mul_nonneg (by omega) (by omega)
    rw [Int.mul_neg] at hm
    omega
  apply Classical.byContradiction
  intro hge0
  have hx_nn : x ≥ 0 := by omega
  have hrhs_pos : (3 : Int) ^ parityWeight u * x + affineCarryInt u ≥ 1 := by
    have hm : (3 : Int) ^ parityWeight u * x ≥ 0 :=
      Int.mul_nonneg (by omega) hx_nn
    omega
  omega

/--
  Universal All-Weight Two-Return Escape + Exact Positive Backward Division (`∀ w ≥ 1, ∀ q ≥ 0`):
  Completely removes the `w = 4` (`mod 81`) finite-table restriction of
  `two_return_escape_suffix_congruence_mod81`!
  At EVERY positive-weight second return `x2` (`2^|vMid| * x2 = 3^w(vMid) * x1 + C(vMid)`,
  `w(vMid) ≥ 1`) and for EVERY positive-weight backward parity word `u` (`w = parityWeight u ≥ 1`),
  there exists a shift `a < 2 * 3 ^ (w - 1)` such that for EVERY period multiple `q : Nat`
  (including `q = 0`!), the zero-padded word `u' = u ++ List.replicate (a + q * (2 * 3 ^ (w - 1))) false`
  preserves `parityWeight u' = w` and `affineCarry u' = affineCarry u` AND solves the EXACT
  positive integer backward equation:
    `∃ y : Nat, y ≥ 1 ∧ 2 ^ u'.length * x2 = 3 ^ w * y + affineCarry u' ∧ collatzIter u'.length y = x2`!
-/
theorem two_return_escape_suffix_exact_division_all_weights
    (vMid u : List Bool) (x1 x2 : Nat)
    (hstep : 2 ^ vMid.length * x2 = 3 ^ parityWeight vMid * x1 + affineCarry vMid)
    (hw_mid : parityWeight vMid ≥ 1)
    (hu_pos : parityWeight u ≥ 1) :
    let w := parityWeight u
    ∃ a : Nat,
      a < 2 * 3 ^ (w - 1) ∧
      ∀ q : Nat,
        let u' := u ++ List.replicate (a + q * (2 * 3 ^ (w - 1))) false
        parityWeight u' = w ∧
        affineCarry u' = affineCarry u ∧
        (2 ^ u'.length * x2) % 3 ^ w = affineCarry u' % 3 ^ w ∧
        ∃ y : Nat,
          y ≥ 1 ∧
          2 ^ u'.length * x2 = 3 ^ w * y + affineCarry u' ∧
          collatzIter u'.length y = x2 := by
  dsimp only
  let w := parityWeight u
  have hx2_n3 : x2 % 3 ≠ 0 := (two_return_garden_of_eden_escape vMid x1 x2 hstep).2 hw_mid
  have hx2_pos : x2 ≥ 1 := by omega
  have hp2_n3 : (2 ^ u.length * x2) % 3 ≠ 0 := by
    rw [Nat.mul_mod]
    rcases pow2_mod3_one_or_two u.length with h1 | h2
    · rw [h1]; omega
    · rw [h2]; omega
  rcases affineCarryInt_pos_nondiv3_of_weight_pos u hu_pos with ⟨_, hc_int⟩
  rw [affineCarryInt_ofNat] at hc_int
  have hc_n3 : affineCarry u % 3 ≠ 0 := by omega
  rcases exists_pow2_mul_congr_mod_pow3 w (2 ^ u.length * x2) (affineCarry u)
      hu_pos hp2_n3 hc_n3 with ⟨a, ha_lt, ha_congr⟩
  refine ⟨a, ha_lt, ?_⟩
  intro q
  let shift := a + q * (2 * 3 ^ (w - 1))
  let u' := u ++ List.replicate shift false
  rcases affineCarry_append_replicate_false u shift with ⟨hwt, hcar⟩
  have hlen : u'.length = shift + u.length := by
    dsimp [u']
    rw [List.length_append, List.length_replicate, Nat.add_comm]
  have hcongr : (2 ^ u'.length * x2) % 3 ^ w = affineCarry u' % 3 ^ w := by
    change (2 ^ u'.length * x2) % 3 ^ w = affineCarry u' % 3 ^ w
    rw [hcar, hlen, Nat.pow_add, Nat.mul_assoc]
    exact ha_congr q
  -- Lift the exact congruence `(2^|u'| * x2) % 3^w = C(u') % 3^w` to `Int` and extract `y ≥ 1`:
  let M := 3 ^ w
  let LHS := 2 ^ u'.length * x2
  let C := affineCarry u'
  have hwt' : parityWeight u' = w := hwt
  have hL_dm : (LHS : Int) = (M : Int) * (LHS / M : Int) + (LHS % M : Int) := by
    have h := (Nat.div_add_mod LHS M).symm
    have hc := congrArg Int.ofNat h
    simpa [natCast_add, natCast_mul] using hc
  have hC_dm : (C : Int) = (M : Int) * (C / M : Int) + (C % M : Int) := by
    have h := (Nat.div_add_mod C M).symm
    have hc := congrArg Int.ofNat h
    simpa [natCast_add, natCast_mul] using hc
  have hrem_eq : (LHS % M : Int) = (C % M : Int) := congrArg Int.ofNat hcongr
  let yInt : Int := (LHS / M : Int) - (C / M : Int)
  have hyInt_eq : (M : Int) * yInt = (LHS : Int) - (C : Int) := by
    dsimp [yInt]
    rw [Int.mul_sub]
    omega
  have heq_int :
      (2 : Int) ^ u'.length * (x2 : Int) =
        (3 : Int) ^ parityWeight u' * yInt + affineCarryInt u' := by
    have hL_cast : (LHS : Int) = (2 : Int) ^ u'.length * (x2 : Int) := rfl
    have hM_cast : (M : Int) = (3 : Int) ^ parityWeight u' := by
      dsimp [M]
      rw [hwt']
    have hC_cast : (C : Int) = affineCarryInt u' := by
      dsimp [C]
      exact (affineCarryInt_ofNat u').symm
    rw [← hL_cast, ← hM_cast, ← hC_cast]
    omega
  have hyInt_pos : yInt ≥ 1 :=
    general_affine_forces_pos_of_target_pos u' yInt (x2 : Int) (by omega) heq_int
  let y : Nat := yInt.toNat
  have hy_cast : (y : Int) = yInt := Int.toNat_of_nonneg (by omega)
  have hy_ge1 : y ≥ 1 := by omega
  rw [← hy_cast] at heq_int
  rcases general_affine_converse_universal u' (y : Int) (x2 : Int) heq_int with ⟨_, hiter_int⟩
  rw [collatzIterInt_ofNat] at hiter_int
  have hiter_nat : collatzIter u'.length y = x2 := by omega
  have heq_nat : 2 ^ u'.length * x2 = 3 ^ w * y + affineCarry u' := by
    have h1 : ((2 ^ u'.length * x2 : Nat) : Int) =
        ((3 ^ w * y + affineCarry u' : Nat) : Int) := by
      rw [natCast_mul, natCast_add, natCast_mul, ← affineCarryInt_ofNat]
      rw [hwt'] at heq_int
      exact heq_int
    omega
  exact ⟨hwt, hcar, hcongr, y, hy_ge1, heq_nat, hiter_nat⟩

-- ============================================================================
-- SECTION 3: Track 3 Wave 1 — Constructive Suffix-Shift Quotient Operators,
--            Core-Word Reductions, Compressed Mod-1296 Equivalences, &
--            All-Weight Three-Coset Hensel Balance (T3.1 – T3.7)
-- ============================================================================

/--
  Unique constructive exponent shift `a ∈ [0, 2 * 3^(w - 1))` solving
  `(2 ^ a * x) % 3 ^ w = c % 3 ^ w` for all `w ≥ 1` and units `x, c` coprime to `3`.
-/
def dlog2ShiftModPow3 (w x c : Nat) : Nat :=
  let P := 2 * 3 ^ (w - 1)
  let e1 := dlog2ModPow3 w x
  let e2 := dlog2ModPow3 w c
  if e1 ≤ e2 then e2 - e1 else P + e2 - e1

/--
  Canonical minimal suffix zero-padding `a ∈ [0, 2 * 3^(w(u) - 1))` solving
  `(2 ^ (u.length + a) * x) % 3 ^ w(u) = affineCarry u % 3 ^ w(u)`.
-/
def canonicalSuffixShift (u : List Bool) (x : Nat) : Nat :=
  dlog2ShiftModPow3 (parityWeight u) (2 ^ u.length * x) (affineCarry u)

/--
  Total computable exact backward integer quotient
  `y = (2 ^ (u.length + shift) * x - affineCarry u) / 3 ^ w(u)`
  at period multiple `q : Nat`, where `shift = canonicalSuffixShift u x + q * (2 * 3^(w - 1))`.
-/
def exactBackwardQuotient (x : Nat) (u : List Bool) (q : Nat) : Nat :=
  let w := parityWeight u
  let shift := canonicalSuffixShift u x + q * (2 * 3 ^ (w - 1))
  (2 ^ (u.length + shift) * x - affineCarry u) / 3 ^ w

/--
  A parity word `u` is a **core parity word** iff it is non-empty and both begins
  and ends with an odd (`true`) step (`1...1`).
-/
def IsCoreParityWord (u : List Bool) : Prop :=
  u.head? = some true ∧ u.reverse.head? = some true

def dropLeadingFalse : List Bool -> List Bool
  | [] => []
  | false :: rest => dropLeadingFalse rest
  | true :: rest => true :: rest

def stripTrailingFalse : List Bool -> List Bool × Nat
  | [] => ([], 0)
  | b :: rest =>
    let res := stripTrailingFalse rest
    match res.1 with
    | [] => if b then ([true], res.2) else ([], res.2 + 1)
    | cHead :: cTail => (b :: cHead :: cTail, res.2)

def coreStripWord (u : List Bool) : List Bool :=
  (stripTrailingFalse (dropLeadingFalse u)).1

-- ----------------------------------------------------------------------------
-- T3.1: Universal Odd-Start Garden-of-Eden Escape (`∀ K ≥ 1`)
-- ----------------------------------------------------------------------------

theorem collatzStep_odd_mod3_eq_two (n : Nat) (hodd : n % 2 = 1) :
    collatzStep n % 3 = 2 := by
  have hb : (n % 2 == 0) = false := decide_eq_false (by omega)
  simp only [collatzStep, hb]
  simp
  omega

theorem collatzStep_mod3_ne_zero (x : Nat) (hx : x % 3 ≠ 0) :
    collatzStep x % 3 ≠ 0 := by
  unfold collatzStep
  cases h : (x % 2 == 0) with
  | true =>
    have hev : x % 2 = 0 := of_decide_eq_true h
    simp
    omega
  | false =>
    have hodd : x % 2 ≠ 0 := of_decide_eq_false h
    simp
    omega

theorem collatzIter_mod3_ne_zero : ∀ (k x : Nat),
    x % 3 ≠ 0 -> collatzIter k x % 3 ≠ 0
  | 0, _, hx => hx
  | k + 1, x, hx =>
    collatzIter_mod3_ne_zero k (collatzStep x) (collatzStep_mod3_ne_zero x hx)

/--
  Theorem T3.1a (Universal Odd-Start Garden-of-Eden Escape):
  For EVERY odd integer `n` (`n % 2 = 1`) and EVERY positive step count `K ≥ 1`,
  `collatzIter K n` escapes `0 mod 3` (`collatzIter K n % 3 ≠ 0`).
-/
theorem collatzIter_pos_step_mod3_ne_zero (K n : Nat) (hK : K ≥ 1) (hodd : n % 2 = 1) :
    collatzIter K n % 3 ≠ 0 := by
  have hsplit : K = 1 + (K - 1) := by omega
  rw [hsplit, collatzIter_add 1 (K - 1) n]
  have hs1 : collatzIter 1 n % 3 ≠ 0 := by
    have h2 := collatzStep_odd_mod3_eq_two n hodd
    change collatzStep n % 3 ≠ 0
    omega
  exact collatzIter_mod3_ne_zero (K - 1) (collatzIter 1 n) hs1

/--
  Theorem T3.1b (Universal Escape on All `131 / 1296` Surviving Classes):
  Every `n` in `IsSurvivingMod1296Class` has `collatzIter K n % 3 ≠ 0` for all `K ≥ 1`.
-/
theorem surviving_mod1296_iter_mod3_ne_zero (K n : Nat)
    (hK : K ≥ 1) (hs : IsSurvivingMod1296Class n) :
    collatzIter K n % 3 ≠ 0 := by
  have hodd : n % 2 = 1 := by
    rcases hs with ⟨h16, _, _, _, _⟩
    omega
  exact collatzIter_pos_step_mod3_ne_zero K n hK hodd

-- ----------------------------------------------------------------------------
-- T3.2: Total Specification, Uniqueness, Oddness & Exact Sign-Dichotomy
-- ----------------------------------------------------------------------------

theorem pow2_mul_cancel_unique_lt_period (w x a a' : Nat)
    (hw : w ≥ 1) (hx : x % 3 ≠ 0)
    (ha : a < 2 * 3 ^ (w - 1)) (ha' : a' < 2 * 3 ^ (w - 1))
    (heq : (2 ^ a' * x) % 3 ^ w = (2 ^ a * x) % 3 ^ w) :
    a' = a := by
  let P := 2 * 3 ^ (w - 1)
  let M := 3 ^ w
  rcases dlog2ModPow3_spec w x hw hx with ⟨he1_lt, he1_eq⟩
  let e1 := dlog2ModPow3 w x
  change e1 < P at he1_lt
  change 2 ^ e1 % M = x % M at he1_eq
  have hp1 : 2 ^ P % M = 1 := (pow2_totient_exact_valuation_all_weights w hw).2.2.1
  have hp3_gt1 : M > 1 := by
    dsimp [M]
    rw [show w = (w - 1) + 1 by omega, Nat.pow_succ]
    have hp0 : 3 ^ (w - 1) ≥ 1 := pow3_pos_nat (w - 1)
    omega
  have hhalf : ∀ b1 b2 : Nat,
      b1 < b2 -> b2 < P -> (2 ^ b2 * x) % M = (2 ^ b1 * x) % M -> False := by
    intro b1 b2 hlt hb2 hmod
    let inv := 2 ^ (P - b1) * 2 ^ (P - e1)
    have hmul_mod : (inv * (2 ^ b2 * x)) % M = (inv * (2 ^ b1 * x)) % M := by
      rw [Nat.mul_mod inv (2 ^ b2 * x) M, hmod, ← Nat.mul_mod]
    have hrhs_one : (inv * (2 ^ b1 * x)) % M = 1 := by
      calc
        (inv * (2 ^ b1 * x)) % M
            = ((inv % M) * (((2 ^ b1 % M) * (x % M)) % M)) % M := by
                rw [Nat.mul_mod inv, Nat.mul_mod (2 ^ b1) x M]
        _ = ((inv % M) * (((2 ^ b1 % M) * (2 ^ e1 % M)) % M)) % M := by rw [he1_eq]
        _ = (inv * (2 ^ b1 * 2 ^ e1)) % M := by
              rw [← Nat.mul_mod (2 ^ b1) (2 ^ e1) M, ← Nat.mul_mod]
        _ = (2 ^ P * 2 ^ P) % M := by
              dsimp [inv]
              have hrearrange :
                  2 ^ (P - b1) * 2 ^ (P - e1) * (2 ^ b1 * 2 ^ e1) =
                    (2 ^ (P - b1) * 2 ^ b1) * (2 ^ (P - e1) * 2 ^ e1) := by
                calc
                  2 ^ (P - b1) * 2 ^ (P - e1) * (2 ^ b1 * 2 ^ e1)
                      = 2 ^ (P - b1) * (2 ^ (P - e1) * (2 ^ b1 * 2 ^ e1)) := Nat.mul_assoc _ _ _
                  _ = 2 ^ (P - b1) * (2 ^ b1 * (2 ^ (P - e1) * 2 ^ e1)) := by
                        rw [← Nat.mul_assoc (2 ^ (P - e1)) (2 ^ b1),
                            Nat.mul_comm (2 ^ (P - e1)) (2 ^ b1), Nat.mul_assoc]
                  _ = (2 ^ (P - b1) * 2 ^ b1) * (2 ^ (P - e1) * 2 ^ e1) :=
                        (Nat.mul_assoc _ _ _).symm
              rw [hrearrange]
              rw [← Nat.pow_add, ← Nat.pow_add,
                  show P - b1 + b1 = P by omega, show P - e1 + e1 = P by omega]
        _ = ((2 ^ P % M) * (2 ^ P % M)) % M := Nat.mul_mod _ _ M
        _ = 1 := by rw [hp1, Nat.one_mul, Nat.mod_eq_of_lt hp3_gt1]
    have hlhs_diff : (inv * (2 ^ b2 * x)) % M = 2 ^ (b2 - b1) % M := by
      have hb2_split : 2 ^ b2 = 2 ^ (b2 - b1) * 2 ^ b1 := by
        rw [← Nat.pow_add, show b2 - b1 + b1 = b2 by omega]
      calc
        (inv * (2 ^ b2 * x)) % M
            = (2 ^ (b2 - b1) * (inv * (2 ^ b1 * x))) % M := by
                rw [hb2_split, Nat.mul_assoc (2 ^ (b2 - b1)) (2 ^ b1) x,
                    ← Nat.mul_assoc inv (2 ^ (b2 - b1)),
                    Nat.mul_comm inv (2 ^ (b2 - b1)), Nat.mul_assoc]
        _ = ((2 ^ (b2 - b1) % M) * ((inv * (2 ^ b1 * x)) % M)) % M := Nat.mul_mod _ _ M
        _ = ((2 ^ (b2 - b1) % M) * 1) % M := by rw [hrhs_one]
        _ = 2 ^ (b2 - b1) % M := by rw [Nat.mul_one, Nat.mod_mod]
    rw [hlhs_diff, hrhs_one] at hmul_mod
    exact pow2_order_mod_pow3_exact w (b2 - b1) hw (by omega) (by omega) hmul_mod
  by_cases hlt1 : a < a'
  · exact False.elim (hhalf a a' hlt1 ha' heq)
  · by_cases hlt2 : a' < a
    · exact False.elim (hhalf a' a hlt2 ha heq.symm)
    · omega

theorem dlog2ShiftModPow3_spec_unique (w x c : Nat)
    (hw : w ≥ 1) (hx : x % 3 ≠ 0) (hc : c % 3 ≠ 0) :
    let P := 2 * 3 ^ (w - 1)
    let a := dlog2ShiftModPow3 w x c
    a < P ∧
    (2 ^ a * x) % 3 ^ w = c % 3 ^ w ∧
    (∀ q : Nat, (2 ^ (a + q * P) * x) % 3 ^ w = c % 3 ^ w) ∧
    (∀ a' : Nat, a' < P -> (2 ^ a' * x) % 3 ^ w = c % 3 ^ w -> a' = a) := by
  dsimp only
  let P := 2 * 3 ^ (w - 1)
  let M := 3 ^ w
  rcases dlog2ModPow3_spec w x hw hx with ⟨he1_lt, he1_eq⟩
  rcases dlog2ModPow3_spec w c hw hc with ⟨he2_lt, he2_eq⟩
  let e1 := dlog2ModPow3 w x
  let e2 := dlog2ModPow3 w c
  change e1 < P at he1_lt
  change 2 ^ e1 % M = x % M at he1_eq
  change e2 < P at he2_lt
  change 2 ^ e2 % M = c % M at he2_eq
  have hbase : dlog2ShiftModPow3 w x c < P ∧
      (2 ^ (dlog2ShiftModPow3 w x c) * x) % M = c % M := by
    unfold dlog2ShiftModPow3
    change (if e1 ≤ e2 then e2 - e1 else P + e2 - e1) < P ∧
      (2 ^ (if e1 ≤ e2 then e2 - e1 else P + e2 - e1) * x) % M = c % M
    by_cases hle : e1 ≤ e2
    · simp only [hle, ite_true]
      refine ⟨by omega, ?_⟩
      calc
        (2 ^ (e2 - e1) * x) % M
            = ((2 ^ (e2 - e1) % M) * (x % M)) % M := Nat.mul_mod _ _ M
        _ = ((2 ^ (e2 - e1) % M) * (2 ^ e1 % M)) % M := by rw [he1_eq]
        _ = (2 ^ (e2 - e1) * 2 ^ e1) % M := (Nat.mul_mod _ _ M).symm
        _ = 2 ^ e2 % M := by rw [← Nat.pow_add, show e2 - e1 + e1 = e2 by omega]
        _ = c % M := he2_eq
    · simp only [hle, ite_false]
      refine ⟨by omega, ?_⟩
      have hp1 : 2 ^ P % M = 1 := (pow2_totient_exact_valuation_all_weights w hw).2.2.1
      calc
        (2 ^ (P + e2 - e1) * x) % M
            = ((2 ^ (P + e2 - e1) % M) * (x % M)) % M := Nat.mul_mod _ _ M
        _ = ((2 ^ (P + e2 - e1) % M) * (2 ^ e1 % M)) % M := by rw [he1_eq]
        _ = (2 ^ (P + e2 - e1) * 2 ^ e1) % M := (Nat.mul_mod _ _ M).symm
        _ = 2 ^ (P + e2) % M := by rw [← Nat.pow_add, show P + e2 - e1 + e1 = P + e2 by omega]
        _ = (2 ^ P * 2 ^ e2) % M := by rw [Nat.pow_add]
        _ = ((2 ^ P % M) * (2 ^ e2 % M)) % M := Nat.mul_mod _ _ M
        _ = (1 * (c % M)) % M := by rw [hp1, he2_eq]
        _ = c % M := by rw [Nat.one_mul, Nat.mod_mod]
  rcases hbase with ⟨ha_lt, ha_congr⟩
  refine ⟨ha_lt, ha_congr, ?_, ?_⟩
  · intro q
    have hpq : 2 ^ (q * P) % M = 1 := pow2_period_mul_mod_pow3 w hw q
    calc
      (2 ^ (dlog2ShiftModPow3 w x c + q * P) * x) % M
          = (2 ^ (q * P) * (2 ^ (dlog2ShiftModPow3 w x c) * x)) % M := by
              rw [Nat.pow_add, Nat.mul_comm _ (2 ^ (q * P)), Nat.mul_assoc]
      _ = ((2 ^ (q * P) % M) * ((2 ^ (dlog2ShiftModPow3 w x c) * x) % M)) % M := Nat.mul_mod _ _ M
      _ = (1 * (c % M)) % M := by rw [hpq, ha_congr]
      _ = c % M := by rw [Nat.one_mul, Nat.mod_mod]
  · intro a' ha'_lt ha'_congr
    rw [← ha_congr] at ha'_congr
    exact pow2_mul_cancel_unique_lt_period w x (dlog2ShiftModPow3 w x c) a'
      hw hx ha_lt ha'_lt ha'_congr

/--
  Theorem T3.2a (Total Specification & Uniqueness of `canonicalSuffixShift`):
  For EVERY positive-weight parity word `u` (`parityWeight u ≥ 1`) and EVERY `x` coprime to `3`,
  `canonicalSuffixShift u x` is the UNIQUE exponent `a < 2 * 3 ^ (w - 1)` solving
  `(2 ^ (u.length + a) * x) % 3 ^ w = affineCarry u % 3 ^ w`.
-/
theorem canonicalSuffixShift_spec_unique (u : List Bool) (x : Nat)
    (hw : parityWeight u ≥ 1) (hx : x % 3 ≠ 0) :
    let w := parityWeight u
    let P := 2 * 3 ^ (w - 1)
    let a := canonicalSuffixShift u x
    a < P ∧
    (2 ^ (u.length + a) * x) % 3 ^ w = affineCarry u % 3 ^ w ∧
    (∀ a' : Nat, a' < P -> (2 ^ (u.length + a') * x) % 3 ^ w = affineCarry u % 3 ^ w -> a' = a) := by
  dsimp only
  have hp2x_n3 : (2 ^ u.length * x) % 3 ≠ 0 := by
    rw [Nat.mul_mod]
    rcases pow2_mod3_one_or_two u.length with h1 | h2
    · rw [h1]; omega
    · rw [h2]; omega
  rcases affineCarryInt_pos_nondiv3_of_weight_pos u hw with ⟨_, hc_int⟩
  rw [affineCarryInt_ofNat] at hc_int
  have hc_n3 : affineCarry u % 3 ≠ 0 := by omega
  rcases dlog2ShiftModPow3_spec_unique (parityWeight u) (2 ^ u.length * x) (affineCarry u)
      hw hp2x_n3 hc_n3 with ⟨ha_lt, ha_congr, _, ha_uniq⟩
  unfold canonicalSuffixShift
  refine ⟨ha_lt, ?_, ?_⟩
  · rw [Nat.add_comm u.length, Nat.pow_add, Nat.mul_assoc]
    exact ha_congr
  · intro a' ha'_lt ha'_congr
    rw [Nat.add_comm u.length, Nat.pow_add, Nat.mul_assoc] at ha'_congr
    exact ha_uniq a' ha'_lt ha'_congr

/--
  Theorem T3.2b (Total Specification, Positivity, Forward Return & Oddness of `exactBackwardQuotient`):
  Notice `hx : x % 3 ≠ 0` automatically implies `x ≥ 1` (`0 % 3 = 0`), so for EVERY `w ≥ 1`,
  EVERY `x` with `x % 3 ≠ 0`, and EVERY `q : Nat` (including `q = 0`), there is ZERO `Nat`
  subtraction underflow: `y = exactBackwardQuotient x u q ≥ 1`, `2^(|u|+shift)*x = 3^w*y + C(u)`,
  `collatzIter (|u|+shift) y = x`, and leading `true` forces `y % 2 = 1`!
-/
theorem exactBackwardQuotient_spec (x : Nat) (u : List Bool) (q : Nat)
    (hw : parityWeight u ≥ 1) (hx : x % 3 ≠ 0) :
    let w := parityWeight u
    let shift := canonicalSuffixShift u x + q * (2 * 3 ^ (w - 1))
    let y := exactBackwardQuotient x u q
    y ≥ 1 ∧
    2 ^ (u.length + shift) * x = 3 ^ w * y + affineCarry u ∧
    collatzIter (u.length + shift) y = x ∧
    (u.head? = some true -> y % 2 = 1) := by
  dsimp only
  let w := parityWeight u
  let P := 2 * 3 ^ (w - 1)
  let a := canonicalSuffixShift u x
  let shift := a + q * P
  let u' := u ++ List.replicate shift false
  have hx_pos : x ≥ 1 := by omega
  have hp2x_n3 : (2 ^ u.length * x) % 3 ≠ 0 := by
    rw [Nat.mul_mod]
    rcases pow2_mod3_one_or_two u.length with h1 | h2
    · rw [h1]; omega
    · rw [h2]; omega
  rcases affineCarryInt_pos_nondiv3_of_weight_pos u hw with ⟨_, hc_int⟩
  rw [affineCarryInt_ofNat] at hc_int
  have hc_n3 : affineCarry u % 3 ≠ 0 := by omega
  have hshift_congr : (2 ^ (u.length + shift) * x) % 3 ^ w = affineCarry u % 3 ^ w := by
    have hq_congr :=
      (dlog2ShiftModPow3_spec_unique w (2 ^ u.length * x) (affineCarry u) hw hp2x_n3 hc_n3).2.2.1 q
    change (2 ^ (u.length + shift) * x) % 3 ^ w = affineCarry u % 3 ^ w
    rw [Nat.add_comm u.length shift, Nat.pow_add, Nat.mul_assoc]
    exact hq_congr
  rcases affineCarry_append_replicate_false u shift with ⟨hwt, hcar⟩
  have hu'_len : u'.length = u.length + shift := by
    dsimp [u']
    rw [List.length_append, List.length_replicate]
  let M := 3 ^ w
  let LHS := 2 ^ (u.length + shift) * x
  let C := affineCarry u
  have hM_pos : M > 0 := pow3_pos_nat w
  have hL_dm : (LHS : Int) = (M : Int) * (LHS / M : Int) + (LHS % M : Int) := by
    have h := (Nat.div_add_mod LHS M).symm
    have hc := congrArg Int.ofNat h
    simpa [natCast_add, natCast_mul] using hc
  have hC_dm : (C : Int) = (M : Int) * (C / M : Int) + (C % M : Int) := by
    have h := (Nat.div_add_mod C M).symm
    have hc := congrArg Int.ofNat h
    simpa [natCast_add, natCast_mul] using hc
  have hrem_eq : (LHS % M : Int) = (C % M : Int) := congrArg Int.ofNat hshift_congr
  let yInt : Int := (LHS / M : Int) - (C / M : Int)
  have hyInt_mul : (M : Int) * yInt = (LHS : Int) - (C : Int) := by
    dsimp [yInt]
    rw [Int.mul_sub]
    omega
  have heq_int :
      (2 : Int) ^ u'.length * (x : Int) =
        (3 : Int) ^ parityWeight u' * yInt + affineCarryInt u' := by
    have hL_cast : (LHS : Int) = (2 : Int) ^ u'.length * (x : Int) := by
      dsimp [LHS]
      rw [hu'_len]
    have hM_cast : (M : Int) = (3 : Int) ^ parityWeight u' := by
      dsimp [M, w]
      rw [hwt]
    have hC_cast : (C : Int) = affineCarryInt u' := by
      dsimp [C]
      rw [← hcar]
      exact (affineCarryInt_ofNat u').symm
    rw [← hL_cast, ← hM_cast, ← hC_cast]
    omega
  have hyInt_pos : yInt ≥ 1 :=
    general_affine_forces_pos_of_target_pos u' yInt (x : Int) (by omega) heq_int
  let y0 : Nat := yInt.toNat
  have hy0_cast : (y0 : Int) = yInt := Int.toNat_of_nonneg (by omega)
  have hy0_ge1 : y0 ≥ 1 := by omega
  rw [← hy0_cast] at heq_int
  have heq_nat0 : LHS = M * y0 + C := by
    have h1 : (LHS : Int) = (M : Int) * (y0 : Int) + (C : Int) := by
      rw [hy0_cast]
      omega
    have h2 : ((M * y0 + C : Nat) : Int) = (M : Int) * (y0 : Int) + (C : Int) := by
      rw [natCast_add, natCast_mul]
    omega
  have hy_eq_y0 : exactBackwardQuotient x u q = y0 := by
    unfold exactBackwardQuotient
    change (LHS - C) / M = y0
    have hsub : LHS - C = M * y0 := by omega
    rw [hsub, Nat.mul_comm M y0, Nat.mul_div_cancel y0 hM_pos]
  rw [hy_eq_y0]
  rcases general_affine_converse_universal u' (y0 : Int) (x : Int) heq_int with ⟨hpar, hiter_int⟩
  rw [collatzIterInt_ofNat, hu'_len] at hiter_int
  have hiter_nat : collatzIter (u.length + shift) y0 = x := by omega
  refine ⟨hy0_ge1, heq_nat0, hiter_nat, ?_⟩
  intro hhead
  cases u with
  | nil => simp at hhead
  | cons b rest =>
    simp at hhead
    subst hhead
    dsimp [u', matchesParity] at hpar
    have hy0_odd_int : (y0 : Int) % 2 = 1 := hpar.1
    omega

/--
  Theorem T3.2c (Exact Sign-Orientation Dichotomy Separating `Z^+` from `M2 = Z^-`):
  For EVERY positive-weight parity word `u` (`parityWeight u ≥ 1`) and EVERY integer solution
  `2 ^ |u| * x = 3 ^ w(u) * y + C(u)` over `Int`, `x ≥ 1 ↔ y ≥ 1` and `x ≤ 0 ↔ y ≤ -1`.
-/
theorem affine_quotient_sign_dichotomy (u : List Bool) (x y : Int)
    (hw : parityWeight u ≥ 1)
    (heq : (2 : Int) ^ u.length * x = (3 : Int) ^ parityWeight u * y + affineCarryInt u) :
    (x ≥ 1 ↔ y ≥ 1) ∧ (x ≤ 0 ↔ y ≤ -1) := by
  have hpos : x ≥ 1 -> y ≥ 1 :=
    fun hx => general_affine_forces_pos_of_target_pos u y x hx heq
  have hneg : x ≤ 0 -> y ≤ -1 :=
    fun hx => general_affine_forces_neg_of_target_nonpos u y x hw hx heq
  refine ⟨⟨hpos, ?_⟩, ⟨hneg, ?_⟩⟩
  · intro hy
    by_cases hx1 : x ≥ 1
    · exact hx1
    · have hle : y ≤ -1 := hneg (by omega)
      omega
  · intro hy
    by_cases hx0 : x ≤ 0
    · exact hx0
    · have hge : y ≥ 1 := hpos (by omega)
      omega

-- ----------------------------------------------------------------------------
-- T3.3 & T3.4: Period-Shift Recurrence, Mod-3 Cyclicity, & Core-Word Reduction
-- ----------------------------------------------------------------------------

/--
  Theorem T3.3 (Exact `q -> q + 1` Period-Shift Recurrence, `y ≥ 5`, & Mod-3 Cyclicity):
  Shifting `q ↦ q + 1` satisfies the exact closed recurrence
    `y_{q+1} = y_q + totient3Coeff (w - 1) * (affineCarry u + 3 ^ w * y_q)`,
  forcing `y_{q+1} ≥ 5` and cycling `y_q % 3` through all 3 residues `{0, 1, 2}` across `q, q+1, q+2`!
-/
theorem exactBackwardQuotient_period_recurrence_and_mod3 (x : Nat) (u : List Bool) (q : Nat)
    (hw : parityWeight u ≥ 1) (hx : x % 3 ≠ 0) :
    let w := parityWeight u
    let y0 := exactBackwardQuotient x u q
    let y1 := exactBackwardQuotient x u (q + 1)
    let y2 := exactBackwardQuotient x u (q + 2)
    y1 = y0 + totient3Coeff (w - 1) * (affineCarry u + 3 ^ w * y0) ∧
    y1 ≥ 5 ∧
    y0 % 3 ≠ y1 % 3 ∧ y1 % 3 ≠ y2 % 3 ∧ y0 % 3 ≠ y2 % 3 ∧
    y0 % 3 + y1 % 3 + y2 % 3 = 3 := by
  dsimp only
  let w := parityWeight u
  let P := 2 * 3 ^ (w - 1)
  let M := 3 ^ w
  have hM_pos : M > 0 := pow3_pos_nat w
  have hrec : ∀ t : Nat,
      exactBackwardQuotient x u (t + 1) =
        exactBackwardQuotient x u t +
          totient3Coeff (w - 1) * (affineCarry u + M * exactBackwardQuotient x u t) := by
    intro t
    rcases exactBackwardQuotient_spec x u t hw hx with ⟨_, heq_t, _, _⟩
    rcases exactBackwardQuotient_spec x u (t + 1) hw hx with ⟨_, heq_t1, _, _⟩
    rcases pow2_totient_exact_valuation_all_weights w hw with ⟨hlte, _, _, _⟩
    let yt := exactBackwardQuotient x u t
    let yt1 := exactBackwardQuotient x u (t + 1)
    let k := totient3Coeff (w - 1)
    let a := canonicalSuffixShift u x
    change 2 ^ (u.length + (a + t * P)) * x = M * yt + affineCarry u at heq_t
    change 2 ^ (u.length + (a + (t + 1) * P)) * x = M * yt1 + affineCarry u at heq_t1
    change 2 ^ P = 1 + M * k at hlte
    have hexp : u.length + (a + (t + 1) * P) = P + (u.length + (a + t * P)) := by
      rw [Nat.succ_mul]
      omega
    have hlhs : 2 ^ (u.length + (a + (t + 1) * P)) * x =
        M * (yt + k * (affineCarry u + M * yt)) + affineCarry u := by
      calc
        2 ^ (u.length + (a + (t + 1) * P)) * x
            = 2 ^ P * (2 ^ (u.length + (a + t * P)) * x) := by rw [hexp, Nat.pow_add, Nat.mul_assoc]
        _ = (1 + M * k) * (M * yt + affineCarry u) := by rw [hlte, heq_t]
        _ = 1 * (M * yt + affineCarry u) + (M * k) * (M * yt + affineCarry u) := Nat.add_mul _ _ _
        _ = M * yt + affineCarry u + M * (k * (affineCarry u + M * yt)) := by
              rw [Nat.one_mul, Nat.mul_assoc M k, Nat.add_comm (M * yt) (affineCarry u)]
        _ = M * (yt + k * (affineCarry u + M * yt)) + affineCarry u := by
              rw [Nat.mul_add M yt]
              omega
    rw [hlhs] at heq_t1
    have hmul_eq : M * yt1 = M * (yt + k * (affineCarry u + M * yt)) := by omega
    have h1 := congrArg (fun z => z / M) hmul_eq
    simpa [Nat.mul_comm M, Nat.mul_div_cancel _ hM_pos] using h1
  have hr0 := hrec q
  have hr1 := hrec (q + 1)
  rcases pow2_totient_3adic_lift (w - 1) with ⟨_, hk_mod3⟩
  have hk_ge1 : totient3Coeff (w - 1) ≥ 1 := by omega
  rcases exactBackwardQuotient_spec x u q hw hx with ⟨hy0_ge1, _, _, _⟩
  rcases affineCarryInt_pos_nondiv3_of_weight_pos u hw with ⟨hc_pos_int, hc_n3_int⟩
  rw [affineCarryInt_ofNat] at hc_pos_int hc_n3_int
  have hc_ge1 : affineCarry u ≥ 1 := by omega
  have hc_n3 : affineCarry u % 3 ≠ 0 := by omega
  have hM_ge3 : M ≥ 3 := by
    dsimp [M]
    rw [show w = (w - 1) + 1 by omega, Nat.pow_succ]
    have hp0 : 3 ^ (w - 1) ≥ 1 := pow3_pos_nat (w - 1)
    omega
  have hM_mod3 : M % 3 = 0 := by
    dsimp [M]
    rw [show w = (w - 1) + 1 by omega, Nat.pow_succ, Nat.mul_mod]
    simp
  have hy1_ge5 : exactBackwardQuotient x u (q + 1) ≥ 5 := by
    rw [hr0]
    have hin : affineCarry u + M * exactBackwardQuotient x u q ≥ 4 := by
      have hm : M * exactBackwardQuotient x u q ≥ 3 * 1 := Nat.mul_le_mul hM_ge3 hy0_ge1
      omega
    have hkm : totient3Coeff (w - 1) * (affineCarry u + M * exactBackwardQuotient x u q) ≥ 1 * 4 :=
      Nat.mul_le_mul hk_ge1 hin
    omega
  have hstep_mod3 : ∀ z : Nat,
      (z + totient3Coeff (w - 1) * (affineCarry u + M * z)) % 3 = (z + affineCarry u) % 3 := by
    intro z
    have hMz : (M * z) % 3 = 0 := by rw [Nat.mul_mod, hM_mod3, Nat.zero_mul, Nat.zero_mod]
    have hin : (affineCarry u + M * z) % 3 = affineCarry u % 3 := by
      rw [Nat.add_mod, hMz, Nat.add_zero, Nat.mod_mod]
    have hprod : (totient3Coeff (w - 1) * (affineCarry u + M * z)) % 3 = affineCarry u % 3 := by
      rw [Nat.mul_mod, hk_mod3, hin, Nat.one_mul, Nat.mod_mod]
    rw [Nat.add_mod z, hprod, ← Nat.add_mod]
  have hm1 : exactBackwardQuotient x u (q + 1) % 3 =
      (exactBackwardQuotient x u q + affineCarry u) % 3 := by
    rw [hr0]; exact hstep_mod3 _
  have hm2 : exactBackwardQuotient x u (q + 2) % 3 =
      (exactBackwardQuotient x u q + 2 * affineCarry u) % 3 := by
    have hstep2 : exactBackwardQuotient x u (q + 2) % 3 =
        (exactBackwardQuotient x u (q + 1) + affineCarry u) % 3 := by
      rw [show q + 2 = (q + 1) + 1 by omega, hr1]; exact hstep_mod3 _
    rw [hstep2, Nat.add_mod (exactBackwardQuotient x u (q + 1)), hm1, ← Nat.add_mod,
        Nat.add_assoc, ← Nat.two_mul]
  let r0 := exactBackwardQuotient x u q % 3
  let rc := affineCarry u % 3
  have hr0_lt : r0 < 3 := Nat.mod_lt _ (by decide)
  have hrc_12 : rc = 1 ∨ rc = 2 := by dsimp [rc]; omega
  have hm1' : exactBackwardQuotient x u (q + 1) % 3 = (r0 + rc) % 3 := by
    rw [hm1, Nat.add_mod]
  have hm2' : exactBackwardQuotient x u (q + 2) % 3 = (r0 + 2 * rc) % 3 := by
    rw [hm2]
    calc
      (exactBackwardQuotient x u q + 2 * affineCarry u) % 3
          = (r0 + (2 * affineCarry u) % 3) % 3 := Nat.add_mod _ _ 3
      _ = (r0 + (2 * rc) % 3) % 3 := by rw [Nat.mul_mod 2, show 2 % 3 = 2 from rfl]
      _ = (r0 % 3 + (2 * rc) % 3) % 3 := by rw [Nat.mod_eq_of_lt hr0_lt]
      _ = (r0 + 2 * rc) % 3 := (Nat.add_mod r0 (2 * rc) 3).symm
  refine ⟨hr0, hy1_ge5, ?_⟩
  rw [hm1', hm2']
  change r0 ≠ (r0 + rc) % 3 ∧ (r0 + rc) % 3 ≠ (r0 + 2 * rc) % 3 ∧
    r0 ≠ (r0 + 2 * rc) % 3 ∧ r0 + (r0 + rc) % 3 + (r0 + 2 * rc) % 3 = 3
  rcases (by omega : r0 = 0 ∨ r0 = 1 ∨ r0 = 2) with h0 | h0 | h0 <;>
    rcases hrc_12 with hc | hc <;> rw [h0, hc] <;> decide

theorem affineCarry_false_cons (u : List Bool) :
    affineCarry (false :: u) = 2 * affineCarry u := by
  have h : (affineCarry (false :: u) : Int) = ((2 * affineCarry u : Nat) : Int) := by
    rw [natCast_mul, ← affineCarryInt_ofNat, ← affineCarryInt_ofNat]
    unfold affineCarryInt
    simp only [affineCarryAuxInt]
    have h01 : 0 + 1 = 1 := rfl
    rw [h01, affineCarryAuxInt_shift u 1 0]
    omega
  omega

/--
  Theorem T3.4a (Core-Word Reduction Step Identities — Leading & Trailing `false`):
  - Prepending `false` doubles the exact backward quotient (`2 * y_q`) for EVERY `q : Nat`.
  - Appending `false` leaves `y_0` unchanged when `canonicalSuffixShift u x ≥ 1` and advances
    to `y_1 ≥ y_0` when `canonicalSuffixShift u x = 0`, so stripping `false` from either end
    never increases `exactBackwardQuotient x · 0`!
-/
theorem exactBackwardQuotient_false_cons_and_snoc (x : Nat) (u : List Bool)
    (hw : parityWeight u ≥ 1) (hx : x % 3 ≠ 0) :
    (∀ q : Nat, exactBackwardQuotient x (false :: u) q = 2 * exactBackwardQuotient x u q) ∧
    exactBackwardQuotient x (u ++ [false]) 0 =
      (if canonicalSuffixShift u x ≥ 1 then exactBackwardQuotient x u 0
       else exactBackwardQuotient x u 1) ∧
    exactBackwardQuotient x u 0 ≤ exactBackwardQuotient x (u ++ [false]) 0 := by
  let w := parityWeight u
  let P := 2 * 3 ^ (w - 1)
  let M := 3 ^ w
  have hM_pos : M > 0 := pow3_pos_nat w
  rcases canonicalSuffixShift_spec_unique u x hw hx with ⟨ha_lt, ha_congr, _⟩
  let a := canonicalSuffixShift u x
  change a < P at ha_lt
  change (2 ^ (u.length + a) * x) % M = affineCarry u % M at ha_congr
  -- Part 1: Leading `false :: u` has identical `canonicalSuffixShift` and doubled quotient:
  have hwt_f : parityWeight (false :: u) = w := rfl
  rcases canonicalSuffixShift_spec_unique (false :: u) x (by rw [hwt_f]; exact hw) hx with
    ⟨_, _, huniq_f⟩
  have hshift_f : canonicalSuffixShift (false :: u) x = a := by
    symm
    apply huniq_f a (by rw [hwt_f]; exact ha_lt)
    rw [hwt_f, affineCarry_false_cons]
    have hlen_f : (false :: u).length + a = (u.length + a) + 1 := by simp; omega
    rw [hlen_f, Nat.pow_succ, Nat.mul_comm (2 ^ (u.length + a)) 2, Nat.mul_assoc]
    rw [Nat.mul_mod 2, ha_congr, ← Nat.mul_mod]
  have hpart1 : ∀ q : Nat,
      exactBackwardQuotient x (false :: u) q = 2 * exactBackwardQuotient x u q := by
    intro q
    rcases exactBackwardQuotient_spec x u q hw hx with ⟨_, heq_q, _, _⟩
    rcases exactBackwardQuotient_spec x (false :: u) q (by rw [hwt_f]; exact hw) hx with
      ⟨_, heq_fq, _, _⟩
    let shift := a + q * P
    change 2 ^ (u.length + shift) * x = M * exactBackwardQuotient x u q + affineCarry u at heq_q
    rw [hwt_f, hshift_f, affineCarry_false_cons] at heq_fq
    change 2 ^ ((false :: u).length + shift) * x =
      M * exactBackwardQuotient x (false :: u) q + 2 * affineCarry u at heq_fq
    have hlen_fq : (false :: u).length + shift = (u.length + shift) + 1 := by simp; omega
    rw [hlen_fq, Nat.pow_succ, Nat.mul_comm (2 ^ (u.length + shift)) 2, Nat.mul_assoc, heq_q] at heq_fq
    have hmul : M * exactBackwardQuotient x (false :: u) q =
        M * (2 * exactBackwardQuotient x u q) := by
      have hd : 2 * (M * exactBackwardQuotient x u q + affineCarry u) =
          M * (2 * exactBackwardQuotient x u q) + 2 * affineCarry u := by
        rw [Nat.mul_add, ← Nat.mul_assoc 2 M, Nat.mul_comm 2 M, Nat.mul_assoc]
      omega
    have hdiv := congrArg (fun z => z / M) hmul
    rw [Nat.mul_comm M (exactBackwardQuotient x (false :: u) q), Nat.mul_div_cancel _ hM_pos,
        Nat.mul_comm M (2 * exactBackwardQuotient x u q), Nat.mul_div_cancel _ hM_pos] at hdiv
    exact hdiv
  -- Part 2: Trailing `u ++ [false]`:
  have hsnoc_rep : u ++ [false] = u ++ List.replicate 1 false := rfl
  rcases affineCarry_append_replicate_false u 1 with ⟨hwt_s, hcar_s⟩
  rw [← hsnoc_rep] at hwt_s hcar_s
  have hlen_s : (u ++ [false]).length = u.length + 1 := by simp
  rcases canonicalSuffixShift_spec_unique (u ++ [false]) x (by rw [hwt_s]; exact hw) hx with
    ⟨_, _, huniq_s⟩
  have hpart2 : exactBackwardQuotient x (u ++ [false]) 0 =
      (if a ≥ 1 then exactBackwardQuotient x u 0 else exactBackwardQuotient x u 1) := by
    by_cases ha1 : a ≥ 1
    · simp only [ha1, ite_true]
      have hshift_s : canonicalSuffixShift (u ++ [false]) x = a - 1 := by
        symm
        apply huniq_s (a - 1) (by rw [hwt_s]; dsimp only [P, w] at ha_lt ⊢; omega)
        rw [hwt_s, hcar_s, hlen_s, show u.length + 1 + (a - 1) = u.length + a by omega]
        exact ha_congr
      unfold exactBackwardQuotient
      rw [hwt_s, hcar_s, hlen_s, hshift_s]
      simp only [Nat.zero_mul, Nat.add_zero]
      dsimp only [a]
      rw [show u.length + 1 + (canonicalSuffixShift u x - 1) =
            u.length + canonicalSuffixShift u x by dsimp only [a] at ha1; omega]
    · simp only [ha1, ite_false]
      have ha0 : a = 0 := by omega
      have hP_ge2 : P ≥ 2 := by
        dsimp [P]
        have hp0 : 3 ^ (w - 1) ≥ 1 := pow3_pos_nat (w - 1)
        omega
      have hshift_s : canonicalSuffixShift (u ++ [false]) x = P - 1 := by
        symm
        apply huniq_s (P - 1) (by rw [hwt_s]; dsimp only [P, w] at hP_ge2 ⊢; omega)
        rw [hwt_s, hcar_s, hlen_s, show u.length + 1 + (P - 1) = P + u.length by omega]
        have hp1 : 2 ^ P % M = 1 := (pow2_totient_exact_valuation_all_weights w hw).2.2.1
        have ha0_congr : (2 ^ u.length * x) % M = affineCarry u % M := by
          rw [ha0, Nat.add_zero] at ha_congr
          exact ha_congr
        calc
          (2 ^ (P + u.length) * x) % M
              = (2 ^ P * (2 ^ u.length * x)) % M := by rw [Nat.pow_add, Nat.mul_assoc]
          _ = ((2 ^ P % M) * ((2 ^ u.length * x) % M)) % M := Nat.mul_mod _ _ M
          _ = (1 * (affineCarry u % M)) % M := by rw [hp1, ha0_congr]
          _ = affineCarry u % M := by rw [Nat.one_mul, Nat.mod_mod]
      unfold exactBackwardQuotient
      rw [hwt_s, hcar_s, hlen_s, hshift_s]
      simp only [Nat.zero_mul, Nat.add_zero, Nat.one_mul]
      have ha0_raw : canonicalSuffixShift u x = 0 := ha0
      rw [ha0_raw, Nat.zero_add]
      dsimp only [P, w] at hP_ge2 ⊢
      rw [show u.length + 1 + (2 * 3 ^ (parityWeight u - 1) - 1) =
            u.length + 2 * 3 ^ (parityWeight u - 1) by omega]
  have hpart3 : exactBackwardQuotient x u 0 ≤ exactBackwardQuotient x (u ++ [false]) 0 := by
    rw [hpart2]
    by_cases ha1 : a ≥ 1
    · simp only [ha1, ite_true]; exact Nat.le_refl _
    · simp only [ha1, ite_false]
      have hrec := (exactBackwardQuotient_period_recurrence_and_mod3 x u 0 hw hx).1
      rw [hrec]
      exact Nat.le_add_right _ _
  exact ⟨hpart1, hpart2, hpart3⟩

-- ----------------------------------------------------------------------------
-- T3.5 & T3.6: Core-Word Stripping & Compressed Mod-1296 Equivalences
-- ----------------------------------------------------------------------------

theorem head_append_of_some {α : Type} : ∀ (l1 l2 : List α) (a : α),
    l1.head? = some a -> (l1 ++ l2).head? = some a
  | [], _, _, h => by simp at h
  | x :: _, _, a, h => by simp at h ⊢; exact h

theorem stripTrailingFalse_spec : ∀ (u : List Bool),
    let res := stripTrailingFalse u
    res.1 ++ List.replicate res.2 false = u ∧
    ((res.1 = [] ∧ parityWeight u = 0) ∨
     (res.1 ≠ [] ∧ res.1.reverse.head? = some true)) ∧
    (u.head? = some true -> res.1.head? = some true)
  | [] => ⟨rfl, Or.inl ⟨rfl, rfl⟩, fun h => by simp at h⟩
  | b :: rest => by
    have ih := stripTrailingFalse_spec rest
    dsimp only at ih ⊢
    rcases ih with ⟨hrep, hcases, _⟩
    simp only [stripTrailingFalse]
    rcases hcases with ⟨hempty, hwt0⟩ | ⟨hnonempty, hlast⟩
    · rw [hempty]
      rw [hempty, List.nil_append] at hrep
      cases b with
      | false =>
        simp only [Bool.false_eq_true, ite_false, List.nil_append]
        refine ⟨?_, Or.inl ⟨trivial, by simp [parityWeight, hwt0]⟩, fun h => by simp at h⟩
        rw [List.replicate_succ, hrep]
      | true =>
        simp only [ite_true]
        refine ⟨?_, Or.inr ⟨by simp, rfl⟩, fun _ => rfl⟩
        simpa using congrArg (List.cons true) hrep
    · cases hc : (stripTrailingFalse rest).1 with
      | nil => exact False.elim (hnonempty hc)
      | cons cHead cTail =>
        rw [hc] at hrep hlast
        simp only
        refine ⟨?_, Or.inr ⟨by simp, ?_⟩, ?_⟩
        · simpa using congrArg (List.cons b) hrep
        · rw [List.reverse_cons]
          exact head_append_of_some (cHead :: cTail).reverse [b] true hlast
        · intro hh
          simp at hh
          subst hh
          rfl

/--
  Sharpened Open Mixing Hypothesis (`Mod1296CoreQuotientContractionProp`):
  Compresses `CollatzConjectureStandard` to core words `1...1` (`IsCoreParityWord u`),
  `K ≥ 1`, and period `q = 0`, with ZERO divisibility or lower-bound side-conditions!
-/
def Mod1296CoreQuotientContractionProp : Prop :=
  ∀ n : Nat, n ≥ 7 -> IsSurvivingMod1296Class n ->
    ∃ (K : Nat) (u : List Bool),
      K ≥ 1 ∧ IsCoreParityWord u ∧ exactBackwardQuotient (collatzIter K n) u 0 < n

/--
  Sharpened Open Mixing Hypothesis (`Mod1296CoreForestQuotientCollisionProp`):
  Compresses `Mod1296SievedForestCarryCollisionProp` strictly to core words `1...1`
  (`IsCoreParityWord u`) and total `exactBackwardQuotient` at `K ≥ 1`.
-/
def Mod1296CoreForestQuotientCollisionProp : Prop :=
  ∀ n : Nat, n ≥ 7 -> IsSurvivingMod1296Class n ->
    ∃ (K q r : Nat) (cs u : List Bool),
      K ≥ 1 ∧ IsCoreParityWord u ∧ IsSyracuseForestRoot r ∧ r < n ∧
      exactBackwardQuotient (collatzIter K n) u q = syracuseForestVal r cs

/--
  Theorem T3.5 (Pointwise Constructive Per-`n` Equivalence — Zero Circularity):
  For EVERY individual `n ≥ 7` in `IsSurvivingMod1296Class n`, a multi-root forest
  carry collision witness `(K, r, cs, u)` exists IF AND ONLY IF a core-word quotient
  collision witness `(K', q, r, cs, uCore)` (`K' ≥ 1`, `IsCoreParityWord uCore`) exists!
-/
theorem mod1296_forest_collision_at_n_iff_core_quotient_at_n (n : Nat)
    (_hn : n ≥ 7) (hs : IsSurvivingMod1296Class n) :
    (∃ (K r : Nat) (cs u : List Bool),
      IsSyracuseForestRoot r ∧ r < n ∧
      (2 : Int) ^ u.length * (collatzIter K n : Int) =
        (3 : Int) ^ parityWeight u * (syracuseForestVal r cs : Int) + affineCarryInt u) ↔
    (∃ (K q r : Nat) (cs u : List Bool),
      K ≥ 1 ∧ IsCoreParityWord u ∧ IsSyracuseForestRoot r ∧ r < n ∧
      exactBackwardQuotient (collatzIter K n) u q = syracuseForestVal r cs) := by
  constructor
  · rintro ⟨K, r, cs, u, hr_root, hr_lt, heq_int⟩
    let z := syracuseForestVal r cs
    rcases syracuseForestVal_invariant r hr_root cs with ⟨_, hz_odd, _⟩
    change z % 2 = 1 at hz_odd
    by_cases hw0 : parityWeight u = 0
    · -- Weight-0 witness: `2^|u| * T^K(n) = z` with `z` odd forces `u = []` and `T^K(n) = z`!
      have hc0 := affineCarryInt_eq_zero_of_weight_zero u hw0
      rw [hw0, hc0] at heq_int
      have heq_nat : 2 ^ u.length * collatzIter K n = z := by
        have h1 : ((2 ^ u.length * collatzIter K n : Nat) : Int) = (z : Int) := by
          rw [natCast_mul]
          simpa using heq_int
        omega
      have hlen0 : u.length = 0 := by
        cases hlen : u.length with
        | zero => rfl
        | succ m =>
          rw [hlen, Nat.pow_succ, Nat.mul_comm (2 ^ m) 2, Nat.mul_assoc] at heq_nat
          omega
      rw [hlen0] at heq_nat
      simp only [Nat.pow_zero, Nat.one_mul] at heq_nat
      have hxK_eq : collatzIter K n = z := heq_nat
      -- Advance 1 step to `K + 1 ≥ 1` with core word `[true]` (`q = 0`):
      have hxK1_eq : collatzIter (K + 1) n = collatzStep z := by
        rw [collatzIter_add K 1 n, hxK_eq]
        rfl
      have hz_odd_b : (z % 2 == 0) = false := decide_eq_false (by omega)
      have h2step : 2 * collatzStep z = 3 * z + 1 := by
        simp only [collatzStep, hz_odd_b]
        simp
        omega
      have hxK1_n3 : collatzStep z % 3 ≠ 0 := by
        have hm2 := collatzStep_odd_mod3_eq_two z hz_odd
        omega
      have hcore_t : IsCoreParityWord [true] := ⟨rfl, rfl⟩
      have hwt_t : parityWeight [true] = 1 := rfl
      have hcar_t : affineCarry [true] = 1 := rfl
      rcases canonicalSuffixShift_spec_unique [true] (collatzStep z) (by omega) hxK1_n3 with
        ⟨_, _, huniq_t⟩
      have hshift0 : canonicalSuffixShift [true] (collatzStep z) = 0 := by
        symm
        apply huniq_t 0 (by decide)
        change (2 ^ 1 * collatzStep z) % 3 = 1 % 3
        omega
      have hquot_z : exactBackwardQuotient (collatzStep z) [true] 0 = z := by
        unfold exactBackwardQuotient
        rw [hwt_t, hcar_t, hshift0]
        change (2 ^ 1 * collatzStep z - 1) / 3 = z
        omega
      refine ⟨K + 1, 0, r, cs, [true], by omega, hcore_t, hr_root, hr_lt, ?_⟩
      rw [hxK1_eq, hquot_z]
    · -- Positive-weight witness (`parityWeight u ≥ 1`):
      have hw_pos : parityWeight u ≥ 1 := by omega
      have heq_nat_u : 2 ^ u.length * collatzIter K n = 3 ^ parityWeight u * z + affineCarry u := by
        have h1 : ((2 ^ u.length * collatzIter K n : Nat) : Int) =
            ((3 ^ parityWeight u * z + affineCarry u : Nat) : Int) := by
          rw [natCast_mul, natCast_add, natCast_mul, ← affineCarryInt_ofNat]
          exact heq_int
        omega
      -- Ensure `K1 ≥ 1` (if `K = 0`, advance 1 odd step from `n` and append `[true]` to `u`):
      have hex_K1 : ∃ (K1 : Nat) (u1 : List Bool),
          K1 ≥ 1 ∧ parityWeight u1 ≥ 1 ∧
          2 ^ u1.length * collatzIter K1 n = 3 ^ parityWeight u1 * z + affineCarry u1 := by
        by_cases hK0 : K = 0
        · subst hK0
          simp only [collatzIter] at heq_nat_u
          have hn_odd : n % 2 = 1 := by rcases hs with ⟨h16, _, _, _, _⟩; omega
          have hn_odd_b : (n % 2 == 0) = false := decide_eq_false (by omega)
          have hstep_n : 2 * collatzIter 1 n = 3 * n + 1 := by
            change 2 * collatzStep n = 3 * n + 1
            simp only [collatzStep, hn_odd_b]
            simp
            omega
          let u1 := u ++ [true]
          have hu1_len : u1.length = u.length + 1 := by simp [u1]
          have hu1_wt : parityWeight u1 = parityWeight u + 1 := by
            simp [u1, parityWeight_append, parityWeight]
          have hu1_car : affineCarry u1 = 3 * affineCarry u + 2 ^ u.length := by
            dsimp [u1]
            rw [affineCarry_append]
            have hw_t : parityWeight [true] = 1 := rfl
            have hc_t : affineCarry [true] = 1 := rfl
            rw [hw_t, hc_t]
            omega
          refine ⟨1, u1, by omega, by omega, ?_⟩
          rw [hu1_len, hu1_wt, hu1_car]
          calc
            2 ^ (u.length + 1) * collatzIter 1 n
                = 2 ^ u.length * (2 * collatzIter 1 n) := by rw [Nat.pow_succ, Nat.mul_assoc]
            _ = 2 ^ u.length * (3 * n + 1) := by rw [hstep_n]
            _ = 3 * (2 ^ u.length * n) + 2 ^ u.length := by
                  rw [Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc,
                      Nat.mul_comm (2 ^ u.length) 3, Nat.mul_assoc]
            _ = 3 * (3 ^ parityWeight u * z + affineCarry u) + 2 ^ u.length := by rw [heq_nat_u]
            _ = 3 ^ (parityWeight u + 1) * z + (3 * affineCarry u + 2 ^ u.length) := by
                  rw [Nat.mul_add, ← Nat.mul_assoc 3 (3 ^ parityWeight u),
                      Nat.mul_comm 3 (3 ^ parityWeight u), ← Nat.pow_succ, Nat.add_assoc]
        · exact ⟨K, u, by omega, hw_pos, heq_nat_u⟩
      rcases hex_K1 with ⟨K1, u1, hK1_pos, hu1_wt_pos, heq_u1⟩
      -- Since `z` is odd and `parityWeight u1 ≥ 1`, `u1` MUST start with `true`:
      have hu1_head : u1.head? = some true := by
        cases u1 with
        | nil => simp [parityWeight] at hu1_wt_pos
        | cons b rest =>
          cases b with
          | true => rfl
          | false =>
            have hlen_c : (false :: rest).length = rest.length + 1 := rfl
            rw [hlen_c, Nat.pow_succ, Nat.mul_comm (2 ^ rest.length) 2,
                Nat.mul_assoc, affineCarry_false_cons] at heq_u1
            have hp3_odd : 3 ^ parityWeight (false :: rest) % 2 = 1 := by
              have hi := pow3_mod2 (parityWeight (false :: rest))
              have hn_cast : ((3 ^ parityWeight (false :: rest) : Nat) : Int) =
                  (3 : Int) ^ parityWeight (false :: rest) := rfl
              omega
            have hprod_odd : (3 ^ parityWeight (false :: rest) * z) % 2 = 1 := by
              rw [Nat.mul_mod, hp3_odd, hz_odd]
            omega
      -- Strip trailing `false`s from `u1` to obtain `uCore` (`IsCoreParityWord uCore`) and `trail`:
      rcases stripTrailingFalse_spec u1 with ⟨hrep, hcases, hhead_imp⟩
      let uCore := (stripTrailingFalse u1).1
      let trail := (stripTrailingFalse u1).2
      change uCore ++ List.replicate trail false = u1 at hrep
      have huCore_last : uCore.reverse.head? = some true := by
        rcases hcases with ⟨_, hwt0⟩ | ⟨_, hlast⟩
        · omega
        · exact hlast
      have huCore_core : IsCoreParityWord uCore := ⟨hhead_imp hu1_head, huCore_last⟩
      rcases affineCarry_append_replicate_false uCore trail with ⟨hwt_c, hcar_c⟩
      rw [hrep] at hwt_c hcar_c
      let w := parityWeight uCore
      have hw_c_pos : w ≥ 1 := by dsimp [w]; omega
      have hu1_len : u1.length = uCore.length + trail := by
        rw [← hrep, List.length_append, List.length_replicate]
      let P := 2 * 3 ^ (w - 1)
      let M := 3 ^ w
      have hP_pos : P > 0 := by
        dsimp [P]
        have hp0 : 3 ^ (w - 1) ≥ 1 := pow3_pos_nat (w - 1)
        omega
      have hM_pos : M > 0 := pow3_pos_nat w
      let q := trail / P
      let a' := trail % P
      have ha'_lt : a' < P := Nat.mod_lt trail hP_pos
      have htrail_eq : trail = a' + q * P := by
        have hdm := (Nat.div_add_mod trail P).symm
        dsimp [q, a']
        rw [Nat.mul_comm P (trail / P)] at hdm
        omega
      let xK := collatzIter K1 n
      have hxK_n3 : xK % 3 ≠ 0 := surviving_mod1296_iter_mod3_ne_zero K1 n hK1_pos hs
      have hcongr_trail : (2 ^ (uCore.length + trail) * xK) % M = affineCarry uCore % M := by
        have heq_c : 2 ^ (uCore.length + trail) * xK = M * z + affineCarry uCore := by
          rw [← hu1_len, heq_u1, hwt_c, hcar_c]
        have hm0 : (M * z) % M = 0 := by rw [Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod]
        rw [heq_c, Nat.add_mod, hm0, Nat.zero_add, Nat.mod_mod]
      have hcongr_a' : (2 ^ (uCore.length + a') * xK) % M = affineCarry uCore % M := by
        have hpq : 2 ^ (q * P) % M = 1 := pow2_period_mul_mod_pow3 w hw_c_pos q
        have hsplit_exp : uCore.length + trail = q * P + (uCore.length + a') := by omega
        rw [hsplit_exp, Nat.pow_add, Nat.mul_assoc, Nat.mul_mod, hpq, Nat.one_mul,
            Nat.mod_mod] at hcongr_trail
        exact hcongr_trail
      rcases canonicalSuffixShift_spec_unique uCore xK hw_c_pos hxK_n3 with ⟨_, _, huniq_c⟩
      have ha'_eq : a' = canonicalSuffixShift uCore xK := huniq_c a' ha'_lt hcongr_a'
      have hquot_eq : exactBackwardQuotient xK uCore q = z := by
        unfold exactBackwardQuotient
        change (2 ^ (uCore.length + (canonicalSuffixShift uCore xK + q * P)) * xK -
          affineCarry uCore) / M = z
        rw [← ha'_eq, ← htrail_eq, ← hu1_len, heq_u1, hwt_c, hcar_c]
        have hsub : M * z + affineCarry uCore - affineCarry uCore = M * z := by omega
        rw [hsub, Nat.mul_comm M z, Nat.mul_div_cancel z hM_pos]
      exact ⟨K1, q, r, cs, uCore, hK1_pos, huCore_core, hr_root, hr_lt, hquot_eq⟩
  · rintro ⟨K, q, r, cs, u, hK_pos, hu_core, hr_root, hr_lt, hquot⟩
    have hw_pos : parityWeight u ≥ 1 := by
      rcases hu_core with ⟨hhead, _⟩
      cases u with
      | nil => simp at hhead
      | cons b rest =>
        simp at hhead
        subst hhead
        simp [parityWeight]
    have hxK_n3 : collatzIter K n % 3 ≠ 0 := surviving_mod1296_iter_mod3_ne_zero K n hK_pos hs
    rcases exactBackwardQuotient_spec (collatzIter K n) u q hw_pos hxK_n3 with ⟨_, heq_nat, _, _⟩
    rw [hquot] at heq_nat
    let shift := canonicalSuffixShift u (collatzIter K n) + q * (2 * 3 ^ (parityWeight u - 1))
    let u' := u ++ List.replicate shift false
    rcases affineCarry_append_replicate_false u shift with ⟨hwt', hcar'⟩
    have hlen' : u'.length = u.length + shift := by
      dsimp [u']
      rw [List.length_append, List.length_replicate]
    refine ⟨K, r, cs, u', hr_root, hr_lt, ?_⟩
    have hcast : ((2 ^ (u.length + shift) * collatzIter K n : Nat) : Int) =
        ((3 ^ parityWeight u * syracuseForestVal r cs + affineCarry u : Nat) : Int) :=
      congrArg (fun t : Nat => (t : Int)) heq_nat
    rw [natCast_mul, natCast_pow2, natCast_add, natCast_mul, natCast_pow3,
        ← affineCarryInt_ofNat] at hcast
    rw [hlen', hwt']
    have hcar_int : affineCarryInt u' = affineCarryInt u := by
      rw [affineCarryInt_ofNat, affineCarryInt_ofNat, hcar']
    rw [hcar_int]
    exact hcast

theorem core_quotient_contraction_reaches_one_aux : ∀ (fuel n : Nat),
    Mod1296CoreQuotientContractionProp -> 1 ≤ n -> n ≤ fuel + 1 ->
    ∃ kn : Nat, collatzIter kn n = 1
  | 0, n, _, hn1, hle => by
    have hn_eq : n = 1 := by omega
    subst hn_eq
    exact ⟨0, rfl⟩
  | fuel + 1, n, hprop, hn1, hle => by
    have hminReach : ∀ m : Nat, 1 ≤ m -> m < n -> ∃ k1 : Nat, collatzIter k1 m = 1 :=
      fun m hm1 hmlt => core_quotient_contraction_reaches_one_aux fuel m hprop hm1 (by omega)
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
        have hn_ge7 : n ≥ 7 := by rcases hm1296 with ⟨h16, _, _, _, _⟩; omega
        rcases hprop n hn_ge7 hm1296 with ⟨K, u, hK_pos, hu_core, hy_lt⟩
        have hw_pos : parityWeight u ≥ 1 := by
          rcases hu_core with ⟨hhead, _⟩
          cases u with
          | nil => simp at hhead
          | cons b rest => simp at hhead; subst hhead; simp [parityWeight]
        have hxK_n3 : collatzIter K n % 3 ≠ 0 :=
          surviving_mod1296_iter_mod3_ne_zero K n hK_pos hm1296
        rcases exactBackwardQuotient_spec (collatzIter K n) u 0 hw_pos hxK_n3 with
          ⟨hy_ge1, _, hcoal, _⟩
        rcases hminReach (exactBackwardQuotient (collatzIter K n) u 0) hy_ge1 hy_lt with
          ⟨kz, hkz⟩
        exact coalescence_reaches_one n (exactBackwardQuotient (collatzIter K n) u 0)
          K (u.length + (canonicalSuffixShift u (collatzIter K n) + 0 * (2 * 3 ^ (parityWeight u - 1))))
          kz hcoal.symm hkz

/--
  Theorem T3.6a (Global Equivalence `CollatzConjectureStandard ↔ Mod1296CoreQuotientContractionProp`):
  Eliminates 100% of `3^w`-adic divisibility and lower-window side-conditions across all weights!
-/
theorem collatz_standard_iff_mod1296_core_quotient_contraction :
    CollatzConjectureStandard ↔ Mod1296CoreQuotientContractionProp := by
  constructor
  · intro hstd n hn _
    have hcomp := collatz_standard_iff_compressed.mp hstd
    rcases hcomp n (by omega) with ⟨kn, hkn⟩
    have hkn_pos : kn ≥ 1 := by
      by_cases hk0 : kn = 0
      · subst hk0; simp [collatzIter] at hkn; omega
      · omega
    refine ⟨kn, [true], hkn_pos, ⟨rfl, rfl⟩, ?_⟩
    rw [hkn]
    have hq1 : exactBackwardQuotient 1 [true] 0 = 1 := by decide
    rw [hq1]
    omega
  · intro hprop
    rw [collatz_standard_iff_compressed]
    intro n hn
    exact core_quotient_contraction_reaches_one_aux n n hprop (by omega) (by omega)

/--
  Theorem T3.6b (Global Equivalence `CollatzConjectureStandard ↔ Mod1296CoreForestQuotientCollisionProp`):
-/
theorem collatz_standard_iff_mod1296_core_forest_quotient_collision :
    CollatzConjectureStandard ↔ Mod1296CoreForestQuotientCollisionProp := by
  rw [collatz_standard_iff_mod1296_sieved_forest_collision]
  constructor
  · intro hprop n hn hs
    exact (mod1296_forest_collision_at_n_iff_core_quotient_at_n n hn hs).mp (hprop n hn hs)
  · intro hprop n hn hs
    exact (mod1296_forest_collision_at_n_iff_core_quotient_at_n n hn hs).mpr (hprop n hn hs)

-- ----------------------------------------------------------------------------
-- T3.7: All-Weight `(Z / 3^w Z)^*` Three-Coset Hensel Balance
-- ----------------------------------------------------------------------------

theorem div_mod_of_mul_add_lt (M q rem : Nat) (hrem : rem < M) :
    (M * q + rem) % M = rem ∧ (M * q + rem) / M = q := by
  have hM_pos : M > 0 := by omega
  have hm0 : (M * q) % M = 0 := by rw [Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod]
  have hmod : (M * q + rem) % M = rem := by
    rw [Nat.add_mod, hm0, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hrem]
  have hdm := (Nat.div_add_mod (M * q + rem) M).symm
  rw [hmod] at hdm
  let d := (M * q + rem) / M
  have hmul_eq : M * d = M * q := by dsimp [d]; omega
  have hdiv : d = q := by
    have h1 := congrArg (fun z => z / M) hmul_eq
    rw [Nat.mul_comm M d, Nat.mul_div_cancel d hM_pos,
        Nat.mul_comm M q, Nat.mul_div_cancel q hM_pos] at h1
    exact h1
  exact ⟨hmod, hdiv⟩

theorem mod3_coset_perm_digits (q0 s : Nat) (hq0 : q0 < 3) (hs : s = 1 ∨ s = 2) :
    let d1 := (q0 + s) % 3
    let d2 := (d1 + s) % 3
    q0 < 3 ∧ d1 < 3 ∧ d2 < 3 ∧
    q0 ≠ d1 ∧ d1 ≠ d2 ∧ q0 ≠ d2 ∧
    q0 + d1 + d2 = 3 := by
  rcases (by omega : q0 = 0 ∨ q0 = 1 ∨ q0 = 2) with rfl | rfl | rfl <;>
    rcases hs with rfl | rfl <;> decide

/--
  Theorem T3.7 (Universal All-Weight `(Z / 3^w Z)^*` Three-Coset Hensel Balance):
  For EVERY `m, a, c : Nat` with `c % 3 ≠ 0`, the three coset shifts `a, a + P, a + 2P`
  (`P = 2 * 3^m`, `M = 3^(m+1)`) share the identical mod-`M` residue while their upper
  ternary digits `r_t / M` form an exact permutation of `{0, 1, 2}` (`1 + ω + ω^2 = 0`,
  algebraic kernel of primitive character orthogonality `S_w(ξ; c) = 0` for all `w ≥ 2`).
-/
theorem pow2_orbit_three_coset_balance (m a c : Nat) (hc : c % 3 ≠ 0) :
    let M := 3 ^ (m + 1)
    let P := 2 * 3 ^ m
    let r0 := (2 ^ a * c) % (3 * M)
    let r1 := (2 ^ (a + P) * c) % (3 * M)
    let r2 := (2 ^ (a + 2 * P) * c) % (3 * M)
    r0 % M = r1 % M ∧ r1 % M = r2 % M ∧
    r0 / M < 3 ∧ r1 / M < 3 ∧ r2 / M < 3 ∧
    r0 / M ≠ r1 / M ∧ r1 / M ≠ r2 / M ∧ r0 / M ≠ r2 / M ∧
    r0 / M + r1 / M + r2 / M = 3 := by
  dsimp only
  let M := 3 ^ (m + 1)
  let P := 2 * 3 ^ m
  let k := totient3Coeff m
  rcases pow2_totient_3adic_lift m with ⟨hlte, hk_mod3⟩
  change 2 ^ P = 1 + M * k at hlte
  change k % 3 = 1 at hk_mod3
  have hM_pos : M > 0 := pow3_pos_nat (m + 1)
  have hM_mod3 : M % 3 = 0 := by
    dsimp [M]; rw [Nat.pow_succ, Nat.mul_mod]; simp
  let z0 := 2 ^ a * c
  let z1 := 2 ^ (a + P) * c
  let z2 := 2 ^ (a + 2 * P) * c
  have hz1_step : z1 = z0 + M * (z0 * k) := by
    dsimp [z1, z0]
    rw [Nat.pow_add, Nat.mul_comm (2 ^ a) (2 ^ P), Nat.mul_assoc, hlte,
        Nat.add_mul, Nat.one_mul, Nat.mul_assoc M k z0, Nat.mul_comm k z0]
  have hz2_step : z2 = z1 + M * (z1 * k) := by
    dsimp [z2, z1]
    rw [show a + 2 * P = (a + P) + P by omega, Nat.pow_add,
        Nat.mul_comm (2 ^ (a + P)) (2 ^ P), Nat.mul_assoc, hlte,
        Nat.add_mul, Nat.one_mul, Nat.mul_assoc M k _, Nat.mul_comm k _]
  let rem := z0 % M
  let q0 := (z0 / M) % 3
  have hrem_lt : rem < M := Nat.mod_lt z0 hM_pos
  have hq0_lt : q0 < 3 := Nat.mod_lt (z0 / M) (by decide)
  let s := z0 % 3
  have hs_12 : s = 1 ∨ s = 2 := by
    dsimp [s, z0]
    rw [Nat.mul_mod]
    rcases pow2_mod3_one_or_two a with h1 | h2
    · rw [h1]; omega
    · rw [h2]; omega
  have hz0k_mod3 : (z0 * k) % 3 = s := by
    rw [Nat.mul_mod, hk_mod3, Nat.mul_one]
    dsimp [s]
    exact Nat.mod_mod z0 3
  have hz1_mod3 : z1 % 3 = s := by
    rw [hz1_step, Nat.add_mod z0, Nat.mul_mod M (z0 * k) 3, hM_mod3,
        Nat.zero_mul, Nat.zero_mod, Nat.add_zero, Nat.mod_mod]
  have hz1k_mod3 : (z1 * k) % 3 = s := by
    rw [Nat.mul_mod, hz1_mod3, hk_mod3, Nat.mul_one]
    rcases hs_12 with hs | hs <;> rw [hs] <;> decide
  have hr0_eq : z0 % (3 * M) = M * q0 + rem := mod_three_mul_decomp z0 M hM_pos
  have hr1_eq : z1 % (3 * M) = M * ((q0 + s) % 3) + rem := by
    rw [hz1_step, add_mul_mod_three_mul z0 (z0 * k) M q0 rem hrem_lt hr0_eq, hz0k_mod3]
  have hr2_eq : z2 % (3 * M) = M * (((q0 + s) % 3 + s) % 3) + rem := by
    rw [hz2_step, add_mul_mod_three_mul z1 (z1 * k) M ((q0 + s) % 3) rem hrem_lt hr1_eq, hz1k_mod3]
  rcases div_mod_of_mul_add_lt M q0 rem hrem_lt with ⟨hm0, hd0⟩
  rcases div_mod_of_mul_add_lt M ((q0 + s) % 3) rem hrem_lt with ⟨hm1, hd1⟩
  rcases div_mod_of_mul_add_lt M (((q0 + s) % 3 + s) % 3) rem hrem_lt with ⟨hm2, hd2⟩
  change (z0 % (3 * M)) % M = _ ∧ _
  rw [hr0_eq, hr1_eq, hr2_eq, hm0, hm1, hm2, hd0, hd1, hd2]
  exact ⟨rfl, rfl, mod3_coset_perm_digits q0 s hq0_lt hs_12⟩

-- ============================================================================
-- SECTION 4: Track 1 Wave 1 — Universal Cycle Ratio Sandwich, Mod-48 / Mod-12 /
--            `(21, 22)` Band Rigidity, Pure-Nat Brox Equivalence, &
--            `(2^A * 3^B)` Bounded-Modulus Obstruction Meta-Theorem (T1 – T4)
-- ============================================================================

-- ----------------------------------------------------------------------------
-- T1: Trajectory & Cycle Multiplicative Ratio Sandwich, Peak Floor, & Rigidity
-- ----------------------------------------------------------------------------

/--
  Theorem T1a (Universal Trajectory Upper Ratio from Odd Lower Bound `m`):
  Along ANY `k`-step compressed trajectory from `n`, if every odd iterate in `[0, k)`
  is `≥ m`, then `2 ^ k * m ^ W * collatzIter k n ≤ (3 * m + 1) ^ W * n`.
-/
theorem iter_upper_ratio_of_odd_lower_bound :
    ∀ (k n m : Nat),
      (∀ j : Nat, j < k -> collatzIter j n % 2 = 1 -> m ≤ collatzIter j n) ->
      2 ^ k * m ^ parityWeight (parityOfIter k n) * collatzIter k n ≤
        (3 * m + 1) ^ parityWeight (parityOfIter k n) * n
  | 0, n, m, _ => by simp [collatzIter, parityOfIter, parityWeight]
  | k + 1, n, m, hm => by
    have hm_tail : ∀ j : Nat, j < k ->
        collatzIter j (collatzStep n) % 2 = 1 -> m ≤ collatzIter j (collatzStep n) :=
      fun j hj hodd => hm (j + 1) (by omega) hodd
    have ih := iter_upper_ratio_of_odd_lower_bound k (collatzStep n) m hm_tail
    let n' := collatzStep n
    let W' := parityWeight (parityOfIter k n')
    let y := collatzIter k n'
    change 2 ^ k * m ^ W' * y ≤ (3 * m + 1) ^ W' * n' at ih
    simp only [parityOfIter, collatzIter]
    cases hev : (n % 2 == 0) with
    | true =>
      have hn_ev : n % 2 = 0 := of_decide_eq_true hev
      have h2n' : 2 * n' = n := by dsimp [n']; simp [collatzStep, hev]; omega
      simp only [ite_true, parityWeight]
      change 2 ^ (k + 1) * m ^ W' * y ≤ (3 * m + 1) ^ W' * n
      have hlhs : 2 ^ (k + 1) * m ^ W' * y = 2 * (2 ^ k * m ^ W' * y) := by
        rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2,
            Nat.mul_assoc 2 (2 ^ k) (m ^ W'), Nat.mul_assoc 2 (2 ^ k * m ^ W') y]
      have hrhs : 2 * ((3 * m + 1) ^ W' * n') = (3 * m + 1) ^ W' * n := by
        rw [← Nat.mul_assoc, Nat.mul_comm 2 ((3 * m + 1) ^ W'), Nat.mul_assoc, h2n']
      rw [hlhs, ← hrhs]
      exact Nat.mul_le_mul_left 2 ih
    | false =>
      have hn_odd : n % 2 = 1 := by have hne := of_decide_eq_false hev; omega
      have hm_le_n : m ≤ n := hm 0 (by omega) hn_odd
      have h2n' : 2 * n' = 3 * n + 1 := by dsimp [n']; simp [collatzStep, hev]; omega
      have hcross : m * (3 * n + 1) ≤ (3 * m + 1) * n := by
        rw [Nat.mul_add, Nat.mul_one, Nat.add_mul, Nat.one_mul,
            ← Nat.mul_assoc m 3 n, Nat.mul_comm m 3, Nat.mul_assoc]
        omega
      simp only [Bool.false_eq_true, ite_false, parityWeight]
      rw [Nat.add_comm 1 W']
      change 2 ^ (k + 1) * m ^ (W' + 1) * y ≤ (3 * m + 1) ^ (W' + 1) * n
      have hlhs : 2 ^ (k + 1) * m ^ (W' + 1) * y = (2 * m) * (2 ^ k * m ^ W' * y) := by
        rw [Nat.pow_succ 2 k, Nat.pow_succ m W',
            Nat.mul_comm (2 ^ k) 2, Nat.mul_comm (m ^ W') m,
            Nat.mul_assoc 2 (2 ^ k), ← Nat.mul_assoc (2 ^ k) m,
            Nat.mul_comm (2 ^ k) m, Nat.mul_assoc m (2 ^ k) (m ^ W'),
            ← Nat.mul_assoc 2 m, Nat.mul_assoc (2 * m)]
      have hstep1 : (2 * m) * (2 ^ k * m ^ W' * y) ≤ (2 * m) * ((3 * m + 1) ^ W' * n') :=
        Nat.mul_le_mul_left (2 * m) ih
      have hmid : (2 * m) * ((3 * m + 1) ^ W' * n') = (3 * m + 1) ^ W' * (m * (3 * n + 1)) := by
        calc
          (2 * m) * ((3 * m + 1) ^ W' * n')
              = (3 * m + 1) ^ W' * ((2 * m) * n') := by
                rw [← Nat.mul_assoc, Nat.mul_comm (2 * m) ((3 * m + 1) ^ W'), Nat.mul_assoc]
          _ = (3 * m + 1) ^ W' * (m * (2 * n')) := by
                rw [Nat.mul_comm 2 m, Nat.mul_assoc m 2 n']
          _ = (3 * m + 1) ^ W' * (m * (3 * n + 1)) := by rw [h2n']
      have hstep2 : (3 * m + 1) ^ W' * (m * (3 * n + 1)) ≤
          (3 * m + 1) ^ W' * ((3 * m + 1) * n) :=
        Nat.mul_le_mul_left ((3 * m + 1) ^ W') hcross
      have hrhs : (3 * m + 1) ^ W' * ((3 * m + 1) * n) = (3 * m + 1) ^ (W' + 1) * n := by
        rw [← Nat.mul_assoc, ← Nat.pow_succ]
      rw [hlhs]
      exact Nat.le_trans hstep1 (by rw [hmid, ← hrhs]; exact hstep2)

/--
  Theorem T1b (Universal Trajectory Lower Ratio from Odd Upper Bound `M`):
  Along ANY `k`-step compressed trajectory from `n`, if every odd iterate in `[0, k)`
  is `≤ M`, then `(3 * M + 1) ^ W * n ≤ 2 ^ k * M ^ W * collatzIter k n`.
-/
theorem iter_lower_ratio_of_odd_upper_bound :
    ∀ (k n M : Nat),
      (∀ j : Nat, j < k -> collatzIter j n % 2 = 1 -> collatzIter j n ≤ M) ->
      (3 * M + 1) ^ parityWeight (parityOfIter k n) * n ≤
        2 ^ k * M ^ parityWeight (parityOfIter k n) * collatzIter k n
  | 0, n, M, _ => by simp [collatzIter, parityOfIter, parityWeight]
  | k + 1, n, M, hM => by
    have hM_tail : ∀ j : Nat, j < k ->
        collatzIter j (collatzStep n) % 2 = 1 -> collatzIter j (collatzStep n) ≤ M :=
      fun j hj hodd => hM (j + 1) (by omega) hodd
    have ih := iter_lower_ratio_of_odd_upper_bound k (collatzStep n) M hM_tail
    let n' := collatzStep n
    let W' := parityWeight (parityOfIter k n')
    let y := collatzIter k n'
    change (3 * M + 1) ^ W' * n' ≤ 2 ^ k * M ^ W' * y at ih
    simp only [parityOfIter, collatzIter]
    cases hev : (n % 2 == 0) with
    | true =>
      have hn_ev : n % 2 = 0 := of_decide_eq_true hev
      have h2n' : 2 * n' = n := by dsimp [n']; simp [collatzStep, hev]; omega
      simp only [ite_true, parityWeight]
      change (3 * M + 1) ^ W' * n ≤ 2 ^ (k + 1) * M ^ W' * y
      have hlhs : (3 * M + 1) ^ W' * n = 2 * ((3 * M + 1) ^ W' * n') := by
        rw [← h2n', ← Nat.mul_assoc, Nat.mul_comm ((3 * M + 1) ^ W') 2, Nat.mul_assoc]
      have hrhs : 2 ^ (k + 1) * M ^ W' * y = 2 * (2 ^ k * M ^ W' * y) := by
        rw [Nat.pow_succ, Nat.mul_comm (2 ^ k) 2,
            Nat.mul_assoc 2 (2 ^ k) (M ^ W'), Nat.mul_assoc 2 (2 ^ k * M ^ W') y]
      rw [hlhs, hrhs]
      exact Nat.mul_le_mul_left 2 ih
    | false =>
      have hn_odd : n % 2 = 1 := by have hne := of_decide_eq_false hev; omega
      have hn_le_M : n ≤ M := hM 0 (by omega) hn_odd
      have h2n' : 2 * n' = 3 * n + 1 := by dsimp [n']; simp [collatzStep, hev]; omega
      have hcross : (3 * M + 1) * n ≤ M * (3 * n + 1) := by
        rw [Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.mul_one,
            ← Nat.mul_assoc M 3 n, Nat.mul_comm M 3, Nat.mul_assoc]
        omega
      simp only [Bool.false_eq_true, ite_false, parityWeight]
      rw [Nat.add_comm 1 W']
      change (3 * M + 1) ^ (W' + 1) * n ≤ 2 ^ (k + 1) * M ^ (W' + 1) * y
      have hlhs : (3 * M + 1) ^ (W' + 1) * n = (3 * M + 1) ^ W' * ((3 * M + 1) * n) := by
        rw [Nat.pow_succ, Nat.mul_assoc]
      have hstep1 : (3 * M + 1) ^ W' * ((3 * M + 1) * n) ≤
          (3 * M + 1) ^ W' * (M * (3 * n + 1)) :=
        Nat.mul_le_mul_left ((3 * M + 1) ^ W') hcross
      have hmid : (3 * M + 1) ^ W' * (M * (3 * n + 1)) = (2 * M) * ((3 * M + 1) ^ W' * n') := by
        calc
          (3 * M + 1) ^ W' * (M * (3 * n + 1))
              = (3 * M + 1) ^ W' * (M * (2 * n')) := by rw [h2n']
          _ = (3 * M + 1) ^ W' * ((2 * M) * n') := by rw [← Nat.mul_assoc M 2 n', Nat.mul_comm M 2]
          _ = (2 * M) * ((3 * M + 1) ^ W' * n') := by
                rw [← Nat.mul_assoc, Nat.mul_comm ((3 * M + 1) ^ W') (2 * M), Nat.mul_assoc]
      have hstep2 : (2 * M) * ((3 * M + 1) ^ W' * n') ≤ (2 * M) * (2 ^ k * M ^ W' * y) :=
        Nat.mul_le_mul_left (2 * M) ih
      have hrhs : (2 * M) * (2 ^ k * M ^ W' * y) = 2 ^ (k + 1) * M ^ (W' + 1) * y := by
        rw [Nat.pow_succ 2 k, Nat.pow_succ M W',
            Nat.mul_comm (2 ^ k) 2, Nat.mul_comm (M ^ W') M,
            Nat.mul_assoc 2 (2 ^ k), ← Nat.mul_assoc (2 ^ k) M,
            Nat.mul_comm (2 ^ k) M, Nat.mul_assoc M (2 ^ k) (M ^ W'),
            ← Nat.mul_assoc 2 M, Nat.mul_assoc (2 * M)]
      rw [hlhs]
      exact Nat.le_trans hstep1 (by rw [hmid, ← hrhs]; exact hstep2)

theorem exists_odd_step_of_parityWeight_pos : ∀ (k n : Nat),
    parityWeight (parityOfIter k n) ≥ 1 ->
    ∃ j : Nat, j < k ∧ collatzIter j n % 2 = 1
  | 0, _, hw => by simp [parityOfIter, parityWeight] at hw
  | k + 1, n, hw => by
    simp only [parityOfIter] at hw
    cases hev : (n % 2 == 0) with
    | true =>
      rw [hev] at hw
      simp only [ite_true, parityWeight] at hw
      rcases exists_odd_step_of_parityWeight_pos k (collatzStep n) hw with ⟨j, hj, hodd⟩
      exact ⟨j + 1, by omega, hodd⟩
    | false =>
      have hn_odd : n % 2 = 1 := by have hne := of_decide_eq_false hev; omega
      exact ⟨0, by omega, hn_odd⟩

theorem mul_pow_nat : ∀ (a b w : Nat), (a * b) ^ w = a ^ w * b ^ w
  | _, _, 0 => by simp
  | a, b, w + 1 => by
    rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, mul_pow_nat a b w]
    calc
      a ^ w * b ^ w * (a * b)
          = a ^ w * (b ^ w * (a * b)) := Nat.mul_assoc _ _ _
      _ = a ^ w * (a * (b ^ w * b)) := by
            rw [← Nat.mul_assoc (b ^ w) a b, Nat.mul_comm (b ^ w) a, Nat.mul_assoc]
      _ = (a ^ w * a) * (b ^ w * b) := (Nat.mul_assoc _ _ _).symm

theorem pow_pos_nat_of_pos (a : Nat) (ha : a ≥ 1) : ∀ w : Nat, a ^ w ≥ 1
  | 0 => by simp
  | w + 1 => by
    rw [Nat.pow_succ]
    exact Nat.mul_pos (pow_pos_nat_of_pos a ha w) ha

theorem le_of_mul_le_mul_right_pos (a b c : Nat) (hc : c ≥ 1) (h : a * c ≤ b * c) :
    a ≤ b := by
  apply Classical.byContradiction
  intro hgt
  have hm : (b + 1) * c ≤ a * c := Nat.mul_le_mul_right c (by omega)
  rw [Nat.add_mul, Nat.one_mul] at hm
  omega

theorem binom_linear_floor : ∀ (m A : Nat),
    A ^ (m + 1) + (m + 1) * A ^ m ≤ (A + 1) ^ (m + 1)
  | 0, A => by simp
  | m + 1, A => by
    have ih := binom_linear_floor m A
    have hmul := Nat.mul_le_mul_right (A + 1) ih
    rw [← Nat.pow_succ (A + 1) (m + 1)] at hmul
    have hexp : (A ^ (m + 1) + (m + 1) * A ^ m) * (A + 1) =
        (A ^ (m + 2) + (m + 2) * A ^ (m + 1)) + (m + 1) * A ^ m := by
      calc
        (A ^ (m + 1) + (m + 1) * A ^ m) * (A + 1)
            = A ^ (m + 1) * A + A ^ (m + 1) + ((m + 1) * A ^ m * A + (m + 1) * A ^ m) := by
              rw [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.mul_add, Nat.mul_one]
        _ = A ^ (m + 2) + A ^ (m + 1) + ((m + 1) * A ^ (m + 1) + (m + 1) * A ^ m) := by
              rw [← Nat.pow_succ A (m + 1), Nat.mul_assoc (m + 1) (A ^ m) A, ← Nat.pow_succ A m]
        _ = A ^ (m + 2) + ((1 + (m + 1)) * A ^ (m + 1) + (m + 1) * A ^ m) := by
              rw [Nat.add_assoc, ← Nat.add_assoc (A ^ (m + 1)),
                  Nat.add_mul 1 (m + 1) (A ^ (m + 1)), Nat.one_mul]
        _ = (A ^ (m + 2) + (m + 2) * A ^ (m + 1)) + (m + 1) * A ^ m := by
              rw [show 1 + (m + 1) = m + 2 by omega, Nat.add_assoc]
    rw [hexp] at hmul
    exact Nat.le_trans (Nat.le_add_right _ _) hmul

/--
  Theorem T1c (Universal Cycle Ratio Sandwich & Pure-Nat Binomial Peak Floor):
  Every positive periodic point `collatzIter k n = n` (`n ≥ 1, k ≥ 1`) with odd lower/upper
  bounds `m, M` satisfies `W ≥ 1`, `3^W < 2^k`, `2^k * m^W ≤ (3*m + 1)^W`,
  `(3*M + 1)^W ≤ 2^k * M^W`, and `W * 3^(W - 1) ≤ (2^k - 3^W) * M`.
-/
theorem cycle_ratio_sandwich_and_peak_floor (n k m M : Nat)
    (hn : n ≥ 1) (hk : k ≥ 1) (hcyc : collatzIter k n = n)
    (hm : ∀ j : Nat, j < k -> collatzIter j n % 2 = 1 -> m ≤ collatzIter j n)
    (hM : ∀ j : Nat, j < k -> collatzIter j n % 2 = 1 -> collatzIter j n ≤ M) :
    let W := parityWeight (parityOfIter k n)
    W ≥ 1 ∧ 3 ^ W < 2 ^ k ∧
    2 ^ k * m ^ W ≤ (3 * m + 1) ^ W ∧
    (3 * M + 1) ^ W ≤ 2 ^ k * M ^ W ∧
    W * 3 ^ (W - 1) ≤ (2 ^ k - 3 ^ W) * M := by
  dsimp only
  let v := parityOfIter k n
  let W := parityWeight v
  have hv_len : v.length = k := parityOfIter_length k n
  have hv_par : matchesParity v (n : Int) := parityOfIter_matches k n
  have hcyc_int : collatzIterInt v.length (n : Int) = (n : Int) := by
    rw [hv_len, collatzIterInt_ofNat, hcyc]
  have hbs := bohm_sontacchi_cycle_equation_universal v (n : Int) hv_par hcyc_int
  rw [hv_len] at hbs
  have hW_pos : W ≥ 1 := by
    by_cases hW0 : W = 0
    · have hc0 := affineCarryInt_eq_zero_of_weight_zero v hW0
      change W = 0 at hW0
      rw [show parityWeight v = 0 from hW0, hc0] at hbs
      simp only [Int.pow_zero] at hbs
      have hp2_ge2 : (2 : Int) ^ k ≥ 2 := by
        rw [show k = (k - 1) + 1 by omega, Int.pow_succ]
        have hp0 : (2 : Int) ^ (k - 1) ≥ 1 := pow_pos_int 2 (k - 1) (by omega)
        omega
      have hprod_pos : 0 < ((2 : Int) ^ k - 1) * (n : Int) :=
        Int.mul_pos (by omega) (by omega)
      omega
    · omega
  rcases affineCarryInt_pos_nondiv3_of_weight_pos v hW_pos with ⟨hc_pos, _⟩
  change ((2 : Int) ^ k - (3 : Int) ^ W) * (n : Int) = affineCarryInt v at hbs
  have hdet_pos : (2 : Int) ^ k - (3 : Int) ^ W ≥ 1 := by
    apply Classical.byContradiction
    intro hle0
    have hm_np : (n : Int) * (- ((2 : Int) ^ k - (3 : Int) ^ W)) ≥ 0 :=
      Int.mul_nonneg (by omega) (by omega)
    rw [Int.mul_neg, Int.mul_comm (n : Int)] at hm_np
    omega
  have hp3_lt_p2 : 3 ^ W < 2 ^ k := by
    have hcast : ((3 ^ W : Nat) : Int) < ((2 ^ k : Nat) : Int) := by
      change (3 : Int) ^ W < (2 : Int) ^ k
      omega
    omega
  have hup_n := iter_upper_ratio_of_odd_lower_bound k n m hm
  rw [hcyc] at hup_n
  have hup := le_of_mul_le_mul_right_pos (2 ^ k * m ^ W) ((3 * m + 1) ^ W) n hn hup_n
  have hlo_n := iter_lower_ratio_of_odd_upper_bound k n M hM
  rw [hcyc] at hlo_n
  have hlo := le_of_mul_le_mul_right_pos ((3 * M + 1) ^ W) (2 ^ k * M ^ W) n hn hlo_n
  -- Binomial peak floor `W * 3^(W - 1) ≤ (2^k - 3^W) * M`:
  rcases exists_odd_step_of_parityWeight_pos k n hW_pos with ⟨j0, hj0_lt, hj0_odd⟩
  have hj0_pos : collatzIter j0 n ≥ 1 := collatzIter_pos j0 n hn
  have hM_ge1 : M ≥ 1 := Nat.le_trans hj0_pos (hM j0 hj0_lt hj0_odd)
  have hbin := binom_linear_floor (W - 1) (3 * M)
  rw [show (W - 1) + 1 = W by omega] at hbin
  have hcomb : (3 * M) ^ W + W * (3 * M) ^ (W - 1) ≤ 2 ^ k * M ^ W := Nat.le_trans hbin hlo
  have hMW_split : M ^ W = M * M ^ (W - 1) := by
    conv => lhs; rw [show W = (W - 1) + 1 by omega]
    rw [Nat.pow_succ, Nat.mul_comm]
  have hlhs_fact : (3 * M) ^ W + W * (3 * M) ^ (W - 1) =
      (3 ^ W * M + W * 3 ^ (W - 1)) * M ^ (W - 1) := by
    rw [mul_pow_nat 3 M W, mul_pow_nat 3 M (W - 1), hMW_split]
    rw [Nat.add_mul, Nat.mul_assoc (3 ^ W) M (M ^ (W - 1)),
        Nat.mul_assoc W (3 ^ (W - 1)) (M ^ (W - 1))]
  have hrhs_fact : 2 ^ k * M ^ W = (2 ^ k * M) * M ^ (W - 1) := by
    rw [hMW_split, Nat.mul_assoc]
  rw [hlhs_fact, hrhs_fact] at hcomb
  have hMW1_pos : M ^ (W - 1) ≥ 1 := pow_pos_nat_of_pos M hM_ge1 (W - 1)
  have hlin := le_of_mul_le_mul_right_pos _ _ (M ^ (W - 1)) hMW1_pos hcomb
  have hsub_mul : (2 ^ k - 3 ^ W) * M + 3 ^ W * M = 2 ^ k * M := by
    rw [← Nat.add_mul, Nat.sub_add_cancel (by omega)]
  have hpeak : W * 3 ^ (W - 1) ≤ (2 ^ k - 3 ^ W) * M := by omega
  exact ⟨hW_pos, hp3_lt_p2, hup, hlo, hpeak⟩

theorem pow_three_mul_add_one_mod : ∀ (m W : Nat), (3 * m + 1) ^ W % m = 1 % m
  | _, 0 => rfl
  | m, W + 1 => by
    rw [Nat.pow_succ, Nat.mul_mod, pow_three_mul_add_one_mod m W]
    have hm1 : (3 * m + 1) % m = 1 % m := by
      have hm0 : (3 * m) % m = 0 := by
        rw [Nat.mul_comm, Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod]
      rw [Nat.add_mod, hm0, Nat.zero_add, Nat.mod_mod]
    rw [hm1, ← Nat.mul_mod, Nat.one_mul]

/--
  Theorem T1d (Constant-Odd Cycle Rigidity — Unconditionally Eliminating `W = 1` for All `k`):
  If all odd elements on a positive cycle equal `m`, then `m = 1`, `2^k = 4^W`, and `n ∈ {1, 2}`!
-/
theorem cycle_constant_odd_implies_trivial (n k m : Nat)
    (hn : n ≥ 1) (hk : k ≥ 1) (hcyc : collatzIter k n = n)
    (hconst : ∀ j : Nat, j < k -> collatzIter j n % 2 = 1 -> collatzIter j n = m) :
    m = 1 ∧ 2 ^ k = 4 ^ parityWeight (parityOfIter k n) ∧ (n = 1 ∨ n = 2) := by
  have hm_lo : ∀ j : Nat, j < k -> collatzIter j n % 2 = 1 -> m ≤ collatzIter j n :=
    fun j hj ho => by rw [hconst j hj ho]; exact Nat.le_refl m
  have hm_hi : ∀ j : Nat, j < k -> collatzIter j n % 2 = 1 -> collatzIter j n ≤ m :=
    fun j hj ho => by rw [hconst j hj ho]; exact Nat.le_refl m
  rcases cycle_ratio_sandwich_and_peak_floor n k m m hn hk hcyc hm_lo hm_hi with
    ⟨hW_pos, _, hup, hlo, _⟩
  let W := parityWeight (parityOfIter k n)
  change 2 ^ k * m ^ W ≤ (3 * m + 1) ^ W at hup
  change (3 * m + 1) ^ W ≤ 2 ^ k * m ^ W at hlo
  have heq : (3 * m + 1) ^ W = 2 ^ k * m ^ W := by omega
  rcases exists_odd_step_of_parityWeight_pos k n hW_pos with ⟨j0, hj0_lt, hj0_odd⟩
  have hj0_eq : collatzIter j0 n = m := hconst j0 hj0_lt hj0_odd
  have hm_ge1 : m ≥ 1 := by have hp := collatzIter_pos j0 n hn; omega
  have hm_eq1 : m = 1 := by
    by_cases hm1 : m = 1
    · exact hm1
    · have hm_gt1 : m > 1 := by omega
      have hlhs_mod : (3 * m + 1) ^ W % m = 1 := by
        rw [pow_three_mul_add_one_mod m W, Nat.mod_eq_of_lt hm_gt1]
      have hrhs_mod : (2 ^ k * m ^ W) % m = 0 := by
        rw [show W = (W - 1) + 1 by omega, Nat.pow_succ, ← Nat.mul_assoc,
            Nat.mul_mod, Nat.mod_self, Nat.mul_zero, Nat.zero_mod]
      rw [heq, hrhs_mod] at hlhs_mod
      omega
  subst hm_eq1
  have hp4 : 2 ^ k = 4 ^ W := by simpa using heq.symm
  have hsplit : k = j0 + (k - j0) := by omega
  have hn_triv : n = 1 ∨ n = 2 := by
    have h1 : n = collatzIter (k - j0) 1 := by
      calc
        n = collatzIter k n := hcyc.symm
        _ = collatzIter (j0 + (k - j0)) n := by rw [← hsplit]
        _ = collatzIter (k - j0) (collatzIter j0 n) := collatzIter_add j0 (k - j0) n
        _ = collatzIter (k - j0) 1 := by rw [hj0_eq]
    rw [h1]
    exact collatzIter_trivial_cycle (k - j0) 1 (Or.inl rfl)
  exact ⟨rfl, hp4, hn_triv⟩

-- ----------------------------------------------------------------------------
-- T2: Periodic `x % 3 ≠ 0`, Odd Max Mod-12, Sharpened Mod-48 Min, & `(21, 22)` Band
-- ----------------------------------------------------------------------------

/--
  Theorem T2a (Universal `x % 3 ≠ 0` Periodic Invariance):
  Every positive periodic point `collatzIter p x = x` (`x > 0, p > 0`) satisfies `x % 3 ≠ 0`.
-/
theorem periodic_pos_nondiv3_universal (x p : Nat)
    (hx : x > 0) (hp : p > 0) (hcyc : collatzIter p x = x) :
    x % 3 ≠ 0 := by
  have hm0 : ∀ j : Nat, j < p -> collatzIter j x % 2 = 1 -> 0 ≤ collatzIter j x :=
    fun _ _ _ => Nat.zero_le _
  have hM0 : ∀ j : Nat, j < p -> collatzIter j x % 2 = 1 ->
      collatzIter j x ≤ prefixBoundIter p x :=
    fun j hj _ => le_prefixBoundIter p j x (by omega)
  have hW_pos := (cycle_ratio_sandwich_and_peak_floor x p 0 (prefixBoundIter p x) hx hp hcyc hm0 hM0).1
  rcases exists_odd_step_of_parityWeight_pos p x hW_pos with ⟨j0, hj0_lt, hj0_odd⟩
  have hsplit : p = j0 + (p - j0) := by omega
  have hx_eq : x = collatzIter (p - j0) (collatzIter j0 x) := by
    calc
      x = collatzIter p x := hcyc.symm
      _ = collatzIter (j0 + (p - j0)) x := by rw [← hsplit]
      _ = collatzIter (p - j0) (collatzIter j0 x) := collatzIter_add j0 (p - j0) x
  rw [hx_eq]
  exact collatzIter_pos_step_mod3_ne_zero (p - j0) (collatzIter j0 x) (by omega) hj0_odd

theorem exists_max_odd_on_prefix : ∀ (k : Nat) (f : Nat -> Nat),
    (∃ j : Nat, j < k ∧ f j % 2 = 1) ->
    ∃ i : Nat, i < k ∧ f i % 2 = 1 ∧ (∀ j : Nat, j < k -> f j % 2 = 1 -> f j ≤ f i)
  | 0, _, ⟨_, hj, _⟩ => by omega
  | k + 1, f, hex => by
    by_cases hex_k : ∃ j : Nat, j < k ∧ f j % 2 = 1
    · rcases exists_max_odd_on_prefix k f hex_k with ⟨i0, hi0_lt, hi0_odd, hi0_max⟩
      by_cases hfk : f k % 2 = 1 ∧ f i0 < f k
      · refine ⟨k, by omega, hfk.1, ?_⟩
        intro j hj hjo
        by_cases hjk : j = k
        · subst hjk; exact Nat.le_refl _
        · have hle := hi0_max j (by omega) hjo
          omega
      · refine ⟨i0, by omega, hi0_odd, ?_⟩
        intro j hj hjo
        by_cases hjk : j = k
        · subst hjk; omega
        · exact hi0_max j (by omega) hjo
    · rcases hex with ⟨j0, hj0_lt, hj0_odd⟩
      have hj0_eq : j0 = k := by
        by_cases hlt : j0 < k
        · exact False.elim (hex_k ⟨j0, hlt, hj0_odd⟩)
        · omega
      rw [hj0_eq] at hj0_odd
      refine ⟨k, by omega, hj0_odd, ?_⟩
      intro j hj hjo
      by_cases hlt : j < k
      · exact False.elim (hex_k ⟨j, hlt, hjo⟩)
      · have hjk : j = k := by omega
        subst hjk
        exact Nat.le_refl _

/--
  Theorem T2b (Universal Cycle Odd Maximum Mod-12 Rigidity `M % 12 ∈ {1, 5}`):
  On EVERY positive Collatz cycle (`collatzIter p x = x`), the maximum odd element `M`
  satisfies `M % 12 = 1 ∨ M % 12 = 5` (since `M % 3 ≠ 0` and `M % 4 = 3` would step to
  `(3*M + 1)/2 > M` which is STILL odd!).
-/
theorem cycle_odd_max_mod12_in_1_or_5 (x p : Nat)
    (hx : x > 0) (hp : p > 0) (hcyc : collatzIter p x = x) :
    ∃ M : Nat,
      (∃ i : Nat, i < p ∧ collatzIter i x = M) ∧
      (M % 12 = 1 ∨ M % 12 = 5) ∧
      (∀ j : Nat, j < p -> collatzIter j x % 2 = 1 -> collatzIter j x ≤ M) := by
  have hm0 : ∀ j : Nat, j < p -> collatzIter j x % 2 = 1 -> 0 ≤ collatzIter j x :=
    fun _ _ _ => Nat.zero_le _
  have hM0 : ∀ j : Nat, j < p -> collatzIter j x % 2 = 1 ->
      collatzIter j x ≤ prefixBoundIter p x :=
    fun j hj _ => le_prefixBoundIter p j x (by omega)
  have hW_pos := (cycle_ratio_sandwich_and_peak_floor x p 0 (prefixBoundIter p x) hx hp hcyc hm0 hM0).1
  have hex_odd := exists_odd_step_of_parityWeight_pos p x hW_pos
  rcases exists_max_odd_on_prefix p (fun j => collatzIter j x) hex_odd with
    ⟨i, hi_lt, hi_odd, hi_max⟩
  let M := collatzIter i x
  have hM_pos : M > 0 := collatzIter_pos i x hx
  have hM_cyc : collatzIter p M = M := by
    dsimp [M]
    rw [← collatzIter_add i p x, Nat.add_comm i p, collatzIter_add p i x, hcyc]
  have hM_n3 : M % 3 ≠ 0 := periodic_pos_nondiv3_universal M p hM_pos hp hM_cyc
  have hM_ne3_mod4 : M % 4 ≠ 3 := by
    intro hm4
    have hM_odd_b : (M % 2 == 0) = false := decide_eq_false (by omega)
    have hstep_val : collatzStep M = (3 * M + 1) / 2 := by simp [collatzStep, hM_odd_b]
    have hstep_odd : collatzStep M % 2 = 1 := by rw [hstep_val]; omega
    have hstep_gt : collatzStep M > M := by rw [hstep_val]; omega
    have hstep_iter : collatzIter (i + 1) x = collatzStep M := by
      rw [collatzIter_add i 1 x]
      rfl
    by_cases hi1 : i + 1 < p
    · have hle := hi_max (i + 1) hi1 (by rw [hstep_iter]; exact hstep_odd)
      rw [hstep_iter] at hle
      omega
    · have hip : i + 1 = p := by omega
      rw [hip, hcyc] at hstep_iter
      have hle := hi_max 0 hp (by simp [collatzIter]; rw [hstep_iter]; exact hstep_odd)
      simp only [collatzIter] at hle
      omega
  refine ⟨M, ⟨i, hi_lt, rfl⟩, by omega, hi_max⟩

theorem exists_min_on_prefix : ∀ (k : Nat) (f : Nat -> Nat),
    k > 0 -> ∃ i : Nat, i < k ∧ (∀ j : Nat, j < k -> f i ≤ f j)
  | 0, _, hk => by omega
  | 1, _, _ => ⟨0, by omega, fun j hj => by
      cases j with
      | zero => exact Nat.le_refl _
      | succ _ => omega⟩
  | k + 2, f, _ => by
    rcases exists_min_on_prefix (k + 1) f (by omega) with ⟨i0, hi0_lt, hi0_min⟩
    by_cases hfk : f (k + 1) < f i0
    · refine ⟨k + 1, by omega, ?_⟩
      intro j hj
      by_cases hjk : j = k + 1
      · subst hjk; exact Nat.le_refl _
      · have hle := hi0_min j (by omega)
        omega
    · refine ⟨i0, by omega, ?_⟩
      intro j hj
      by_cases hjk : j = k + 1
      · subst hjk; omega
      · exact hi0_min j (by omega)

theorem pow_le_pow_left_nat (a b : Nat) (hab : a ≤ b) : ∀ w : Nat, a ^ w ≤ b ^ w
  | 0 => by simp
  | w + 1 => by
    rw [Nat.pow_succ, Nat.pow_succ]
    exact Nat.mul_le_mul (pow_le_pow_left_nat a b hab w) hab

theorem band_21_22_forces_W_ge_5_and_p_ge_8 (W p : Nat)
    (hW : W ≥ 1)
    (hlo : 21 ^ W < 7 ^ W * 2 ^ p)
    (hhi : 7 ^ W * 2 ^ p ≤ 22 ^ W) :
    W ≥ 5 ∧ p ≥ 8 := by
  have hW_ge5 : W ≥ 5 := by
    apply Classical.byContradiction
    intro hlt5
    have hW_cases : W = 1 ∨ W = 2 ∨ W = 3 ∨ W = 4 := by omega
    by_cases hp8 : p ≥ 8
    · have hp2_256 : 2 ^ p ≥ 256 := by
        have h := pow2_mono_nat (a := 8) (b := p) hp8
        simpa using h
      have hm := Nat.mul_le_mul_left (7 ^ W) hp2_256
      rcases hW_cases with rfl | rfl | rfl | rfl <;> omega
    · have hp_cases : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨ p = 7 := by omega
      rcases hW_cases with rfl | rfl | rfl | rfl <;>
        rcases hp_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        omega
  have hp_ge8 : p ≥ 8 := by
    have h3W_lt_2p : 3 ^ W < 2 ^ p := by
      have h21 : 21 ^ W = 7 ^ W * 3 ^ W := mul_pow_nat 7 3 W
      rw [h21] at hlo
      apply Classical.byContradiction
      intro hge
      have hm := Nat.mul_le_mul_left (7 ^ W) (by omega : 2 ^ p ≤ 3 ^ W)
      omega
    have h3_243 : 3 ^ 5 ≤ 3 ^ W := by
      have hm := pow3_mono_nat_aux 5 (W - 5)
      rwa [show 5 + (W - 5) = W by omega] at hm
    have h2p_gt_243 : 2 ^ p > 243 := by
      have h243 : (3 : Nat) ^ 5 = 243 := rfl
      omega
    apply Classical.byContradiction
    intro hlt8
    have hp_le7 : 2 ^ p ≤ 2 ^ 7 := pow2_mono_nat (by omega)
    have h128 : (2 : Nat) ^ 7 = 128 := rfl
    omega
  exact ⟨hW_ge5, hp_ge8⟩

/--
  Theorem T2c (Sharpened Mod-48 6-Class Cycle Minimum & `(21, 22)` Exponent Band):
  Every non-trivial positive cycle (`collatzIter p x = x`, `¬ (x = 1 ∨ x = 2)`) has a global
  cycle minimum `x0 = collatzIter i x ≥ 7` satisfying:
  - `x0 % 16 ∈ {7, 11, 15}` and `x0 % 3 ≠ 0`, hence the sharpened 6-class mod-48 sieve
    `x0 % 48 ∈ {7, 11, 23, 31, 43, 47}`,
  - `21 ^ W < 7 ^ W * 2 ^ p ∧ 7 ^ W * 2 ^ p ≤ 22 ^ W`, and
  - `W ≥ 5 ∧ p ≥ 8` unconditionally (zero parity-word enumeration!).
-/
theorem nontrivial_cycle_min_mod48_and_band_21_22 (x p : Nat)
    (hx : x > 0) (hp : p > 0) (hcyc : collatzIter p x = x)
    (hnon : ¬ (x = 1 ∨ x = 2)) :
    ∃ x0 : Nat,
      (∃ i : Nat, i < p ∧ collatzIter i x = x0) ∧
      collatzIter p x0 = x0 ∧
      (∀ k : Nat, x0 ≤ collatzIter k x0) ∧
      (x0 % 16 = 7 ∨ x0 % 16 = 11 ∨ x0 % 16 = 15) ∧
      x0 % 3 ≠ 0 ∧
      (x0 % 48 = 7 ∨ x0 % 48 = 11 ∨ x0 % 48 = 23 ∨
       x0 % 48 = 31 ∨ x0 % 48 = 43 ∨ x0 % 48 = 47) ∧
      let W := parityWeight (parityOfIter p x0)
      W ≥ 5 ∧ p ≥ 8 ∧
      21 ^ W < 7 ^ W * 2 ^ p ∧ 7 ^ W * 2 ^ p ≤ 22 ^ W ∧
      2 ^ p * x0 ^ W ≤ (3 * x0 + 1) ^ W := by
  rcases exists_min_on_prefix p (fun j => collatzIter j x) hp with ⟨i, hi_lt, hi_min⟩
  let x0 := collatzIter i x
  have hx0_pos : x0 > 0 := collatzIter_pos i x hx
  have hx0_cyc : collatzIter p x0 = x0 := by
    dsimp [x0]
    rw [← collatzIter_add i p x, Nat.add_comm i p, collatzIter_add p i x, hcyc]
  have hx0_all_x : ∀ t : Nat, x0 ≤ collatzIter t x := by
    intro t
    have hdm : t = (t / p) * p + t % p := by
      have h := (Nat.div_add_mod t p).symm
      rw [Nat.mul_comm p (t / p)] at h
      exact h
    have hrem_lt : t % p < p := Nat.mod_lt t hp
    have hper := collatzIter_mul_period (t / p) p x hcyc
    rw [hdm, collatzIter_add ((t / p) * p) (t % p) x, hper]
    exact hi_min (t % p) hrem_lt
  have hx0_min : ∀ k : Nat, x0 ≤ collatzIter k x0 := by
    intro k
    dsimp [x0]
    rw [← collatzIter_add i k x]
    exact hx0_all_x (i + k)
  have hx0_gt1 : x0 > 1 := by
    by_cases hx0_1 : x0 = 1
    · have hback : x = collatzIter (p - i) x0 := by
        dsimp [x0]
        rw [← collatzIter_add i (p - i) x, show i + (p - i) = p by omega, hcyc]
      rw [hx0_1] at hback
      have htriv := collatzIter_trivial_cycle (p - i) 1 (Or.inl rfl)
      rw [← hback] at htriv
      exact False.elim (hnon htriv)
    · omega
  have hnoDesc : ∀ k : Nat, ¬ (0 < collatzIter k x0 ∧ collatzIter k x0 < x0) := by
    intro k ⟨_, hlt⟩
    have hge := hx0_min k
    omega
  have hm16 := minimal_counterexample_mod16_in_3_classes x0 hx0_gt1 hnoDesc
  have hx0_n3 := periodic_pos_nondiv3_universal x0 p hx0_pos hp hx0_cyc
  have hm48 : x0 % 48 = 7 ∨ x0 % 48 = 11 ∨ x0 % 48 = 23 ∨
      x0 % 48 = 31 ∨ x0 % 48 = 43 ∨ x0 % 48 = 47 := by omega
  have hx0_ge7 : x0 ≥ 7 := by omega
  have hm_odd : ∀ j : Nat, j < p -> collatzIter j x0 % 2 = 1 -> x0 ≤ collatzIter j x0 :=
    fun j _ _ => hx0_min j
  have hM_odd : ∀ j : Nat, j < p -> collatzIter j x0 % 2 = 1 ->
      collatzIter j x0 ≤ prefixBoundIter p x0 :=
    fun j hj _ => le_prefixBoundIter p j x0 (by omega)
  rcases cycle_ratio_sandwich_and_peak_floor x0 p x0 (prefixBoundIter p x0)
      (by omega) hp hx0_cyc hm_odd hM_odd with ⟨hW_pos, h3W_lt_2p, hup_x0, _, _⟩
  let W := parityWeight (parityOfIter p x0)
  have hband_lo : 21 ^ W < 7 ^ W * 2 ^ p := by
    rw [show (21 : Nat) ^ W = 7 ^ W * 3 ^ W from mul_pow_nat 7 3 W]
    exact Nat.mul_lt_mul_of_pos_left h3W_lt_2p (pow_pos_nat_of_pos 7 (by decide) W)
  have hband_hi : 7 ^ W * 2 ^ p ≤ 22 ^ W := by
    have hlin : 7 * (3 * x0 + 1) ≤ 22 * x0 := by omega
    have hpow := pow_le_pow_left_nat (7 * (3 * x0 + 1)) (22 * x0) hlin W
    rw [mul_pow_nat 7 (3 * x0 + 1) W, mul_pow_nat 22 x0 W] at hpow
    have h1 : (7 ^ W * 2 ^ p) * x0 ^ W ≤ 7 ^ W * (3 * x0 + 1) ^ W := by
      rw [Nat.mul_assoc]
      exact Nat.mul_le_mul_left (7 ^ W) hup_x0
    have h2 : (7 ^ W * 2 ^ p) * x0 ^ W ≤ 22 ^ W * x0 ^ W := Nat.le_trans h1 hpow
    exact le_of_mul_le_mul_right_pos (7 ^ W * 2 ^ p) (22 ^ W) (x0 ^ W)
      (pow_pos_nat_of_pos x0 (by omega) W) h2
  rcases band_21_22_forces_W_ge_5_and_p_ge_8 W p hW_pos hband_lo hband_hi with ⟨hW5, hp8⟩
  exact ⟨x0, ⟨i, hi_lt, rfl⟩, hx0_cyc, hx0_min, hm16, hx0_n3, hm48,
    hW5, hp8, hband_lo, hband_hi, hup_x0⟩

-- ----------------------------------------------------------------------------
-- T3: `[]`-Axiom Pure-Nat Brox Odd-Carry Equivalence for `NoNontrivialPositiveCycles`
-- ----------------------------------------------------------------------------

/--
  Pure-`Nat` strictly positive odd carry `broxOddCarry` for shifted `+1` cycles.
-/
def broxOddCarry : List Bool -> Nat
  | [] => 1
  | _ :: u => 2 * broxOddCarry u + 3 ^ parityWeight u

/--
  Certified Pure-`Nat` Brox Cycle-Minimum Witness Predicate (zero `Nat` truncation underflow,
  separating `M1 = Q_(2)^+`, `M2 = Z^-`, `M3 = 5x + 1`, and the trivial `{1, 2}` cycle).
-/
def IsBroxNatCycleMinWitness (w1 : Nat) (rest : List Bool) (q0 : Nat) : Prop :=
  let K := w1 + 1 + rest.length
  let W := w1 + parityWeight rest
  let x0 := 2 ^ w1 * q0 - 1
  w1 ≥ 2 ∧ q0 ≥ 1 ∧ q0 % 2 = 1 ∧
  (x0 % 16 = 7 ∨ x0 % 16 = 11 ∨ x0 % 16 = 15) ∧ x0 % 3 ≠ 0 ∧
  W ≥ 5 ∧ K ≥ 8 ∧
  21 ^ W < 7 ^ W * 2 ^ K ∧ 7 ^ W * 2 ^ K ≤ 22 ^ W ∧
  2 ^ K * x0 ^ W ≤ (3 * x0 + 1) ^ W ∧
  (2 ^ K - 3 ^ W) * q0 = broxOddCarry rest

theorem broxOddCarry_odd_and_ge_pow3 : ∀ (rest : List Bool),
    broxOddCarry rest % 2 = 1 ∧ broxOddCarry rest ≥ 3 ^ parityWeight rest
  | [] => ⟨rfl, by simp [broxOddCarry, parityWeight]⟩
  | b :: u => by
    rcases broxOddCarry_odd_and_ge_pow3 u with ⟨hodd, hge⟩
    have hp3_odd : 3 ^ parityWeight u % 2 = 1 := by
      have hi := pow3_mod2 (parityWeight u)
      have hn : ((3 ^ parityWeight u : Nat) : Int) = (3 : Int) ^ parityWeight u := rfl
      omega
    refine ⟨?_, ?_⟩
    · simp only [broxOddCarry]
      omega
    · cases b with
      | false =>
        simp only [broxOddCarry, parityWeight]
        omega
      | true =>
        simp only [broxOddCarry, parityWeight]
        rw [Nat.add_comm 1 (parityWeight u), Nat.pow_succ]
        omega

theorem broxOddCarry_int_closed_form : ∀ (rest : List Bool),
    (broxOddCarry rest : Int) =
      2 * affineCarryInt rest + (2 : Int) ^ (rest.length + 1) - (3 : Int) ^ parityWeight rest
  | [] => by simp [broxOddCarry, affineCarryInt, affineCarryAuxInt, parityWeight]
  | false :: u => by
    have ih := broxOddCarry_int_closed_form u
    have hc : affineCarryInt (false :: u) = 2 * affineCarryInt u := by
      unfold affineCarryInt
      simp only [affineCarryAuxInt]
      have h01 : 0 + 1 = 1 := rfl
      rw [h01, affineCarryAuxInt_shift u 1 0]
      omega
    have hp2 : (2 : Int) ^ ((false :: u).length + 1) = 2 * (2 : Int) ^ (u.length + 1) := by
      simp only [List.length_cons]
      rw [Int.pow_succ, Int.mul_comm]
    simp only [broxOddCarry, parityWeight]
    rw [natCast_add, natCast_mul, ih, hc, hp2]
    have hp3_cast : ((3 ^ parityWeight u : Nat) : Int) = (3 : Int) ^ parityWeight u := rfl
    rw [hp3_cast]
    omega
  | true :: u => by
    have ih := broxOddCarry_int_closed_form u
    have hc : affineCarryInt (true :: u) = (3 : Int) ^ parityWeight u + 2 * affineCarryInt u := by
      unfold affineCarryInt
      simp only [affineCarryAuxInt]
      have h10 : 3 * (0 : Int) + (2 : Int) ^ 0 = 1 := rfl
      have h01 : 0 + 1 = 1 := rfl
      rw [h01, h10, affineCarryAuxInt_shift u 1 1]
      omega
    have hp2 : (2 : Int) ^ ((true :: u).length + 1) = 2 * (2 : Int) ^ (u.length + 1) := by
      simp only [List.length_cons]
      rw [Int.pow_succ, Int.mul_comm]
    have hp3 : (3 : Int) ^ parityWeight (true :: u) = 3 * (3 : Int) ^ parityWeight u := by
      simp only [parityWeight]
      rw [Nat.add_comm 1, Int.pow_succ, Int.mul_comm]
    simp only [broxOddCarry]
    rw [natCast_add, natCast_mul, ih, hc, hp2, hp3]
    have hp3_cast : ((3 ^ parityWeight u : Nat) : Int) = (3 : Int) ^ parityWeight u := rfl
    rw [hp3_cast]
    omega

theorem brox_shift_carry_identity (w1 : Nat) (rest : List Bool) :
    let v := List.replicate w1 true ++ (false :: rest)
    affineCarryInt v + ((2 : Int) ^ v.length - (3 : Int) ^ parityWeight v) =
      (2 : Int) ^ w1 * (broxOddCarry rest : Int) := by
  dsimp only
  let u1 := List.replicate w1 true
  have hu1_len : u1.length = w1 := List.length_replicate
  have hu1_wt : parityWeight u1 = w1 := by
    have h : ∀ m : Nat, parityWeight (List.replicate m true) = m := by
      intro m; induction m with
      | zero => rfl
      | succ m' ih => simp [List.replicate_succ, parityWeight, ih]; omega
    exact h w1
  have hu1_car : affineCarryInt u1 = (3 : Int) ^ w1 - (2 : Int) ^ w1 := by
    have h := one_cycle_carry_closed_form_universal w1 0
    simpa [u1] using h
  have hfc_car : affineCarryInt (false :: rest) = 2 * affineCarryInt rest := by
    unfold affineCarryInt
    simp only [affineCarryAuxInt]
    have h01 : 0 + 1 = 1 := rfl
    rw [h01, affineCarryAuxInt_shift rest 1 0]
    omega
  rw [affineCarryInt_append u1 (false :: rest), List.length_append, parityWeight_append]
  rw [hu1_len, hu1_wt, hu1_car, hfc_car]
  simp only [List.length_cons, parityWeight]
  rw [broxOddCarry_int_closed_form rest]
  have hp2 : (2 : Int) ^ (w1 + (rest.length + 1)) =
      (2 : Int) ^ w1 * (2 : Int) ^ (rest.length + 1) := Int.pow_add 2 w1 (rest.length + 1)
  have hp3 : (3 : Int) ^ (w1 + parityWeight rest) =
      (3 : Int) ^ parityWeight rest * (3 : Int) ^ w1 := by
    rw [Int.pow_add, Int.mul_comm]
  rw [hp2, hp3, Int.mul_sub ((3 : Int) ^ parityWeight rest),
      Int.mul_sub ((2 : Int) ^ w1), Int.mul_add ((2 : Int) ^ w1)]
  have hcomm : (3 : Int) ^ parityWeight rest * (2 : Int) ^ w1 =
      (2 : Int) ^ w1 * (3 : Int) ^ parityWeight rest := Int.mul_comm _ _
  rw [hcomm]
  omega

theorem split_at_first_false : ∀ (v : List Bool),
    parityWeight v = v.length ∨
    ∃ (w1 : Nat) (rest : List Bool), v = List.replicate w1 true ++ (false :: rest)
  | [] => Or.inl rfl
  | false :: rest => Or.inr ⟨0, rest, rfl⟩
  | true :: u => by
    rcases split_at_first_false u with hall | ⟨w1, rest, heq⟩
    · left
      simp only [parityWeight, List.length_cons, hall]
      omega
    · right
      refine ⟨w1 + 1, rest, ?_⟩
      rw [List.replicate_succ, List.cons_append, heq]

/--
  Theorem T3 (`[]`-Axiom Sharp Pure-Nat Brox Equivalence for `NoNontrivialPositiveCycles`):
  `NoNontrivialPositiveCycles` holds IF AND ONLY IF no triple `(w1, rest, q0)` satisfies
  `IsBroxNatCycleMinWitness w1 rest q0`!
-/
theorem no_nontrivial_cycles_iff_brox_nat_obstruction :
    NoNontrivialPositiveCycles ↔
      ∀ (w1 : Nat) (rest : List Bool) (q0 : Nat), ¬ IsBroxNatCycleMinWitness w1 rest q0 := by
  constructor
  · intro hnocyc w1 rest q0 hwit
    rcases hwit with
      ⟨hw1_ge2, hq0_ge1, _, hm16, _, _, hK_ge8, hband_lo, _, _, hbrox_eq⟩
    let K := w1 + 1 + rest.length
    let W := w1 + parityWeight rest
    let x0 := 2 ^ w1 * q0 - 1
    let v := List.replicate w1 true ++ (false :: rest)
    have hv_len : v.length = K := by
      dsimp [v, K]
      rw [List.length_append, List.length_replicate, List.length_cons]
      omega
    have hv_wt : parityWeight v = W := by
      dsimp [v, W]
      rw [parityWeight_append]
      have h : ∀ m : Nat, parityWeight (List.replicate m true) = m := by
        intro m; induction m with
        | zero => rfl
        | succ m' ih => simp [List.replicate_succ, parityWeight, ih]; omega
      rw [h w1]
      rfl
    have h3W_lt_2K : 3 ^ W < 2 ^ K := by
      change 21 ^ W < 7 ^ W * 2 ^ K at hband_lo
      rw [show (21 : Nat) ^ W = 7 ^ W * 3 ^ W from mul_pow_nat 7 3 W] at hband_lo
      apply Classical.byContradiction
      intro hge
      have hm := Nat.mul_le_mul_left (7 ^ W) (by omega : 2 ^ K ≤ 3 ^ W)
      omega
    have hp2w1_ge4 : 2 ^ w1 ≥ 4 := by
      have hm := pow2_mono_nat hw1_ge2
      simpa using hm
    have hx0_ge7 : x0 ≥ 7 := by dsimp [x0] at hm16 ⊢; omega
    have hx0p1_nat : x0 + 1 = 2 ^ w1 * q0 := by
      dsimp [x0]
      have hm := Nat.mul_le_mul hp2w1_ge4 hq0_ge1
      omega
    have hbrox_int : ((2 : Int) ^ K - (3 : Int) ^ W) * (q0 : Int) = (broxOddCarry rest : Int) := by
      change (2 ^ K - 3 ^ W) * q0 = broxOddCarry rest at hbrox_eq
      have hc : (((2 ^ K - 3 ^ W) * q0 : Nat) : Int) = (broxOddCarry rest : Int) :=
        congrArg (fun t : Nat => (t : Int)) hbrox_eq
      rw [natCast_mul] at hc
      have hsub : ((2 ^ K - 3 ^ W : Nat) : Int) = (2 : Int) ^ K - (3 : Int) ^ W := by
        have hadd : (2 ^ K - 3 ^ W) + 3 ^ W = 2 ^ K := Nat.sub_add_cancel (by omega)
        have hc2 : (((2 ^ K - 3 ^ W) + 3 ^ W : Nat) : Int) = ((2 ^ K : Nat) : Int) :=
          congrArg (fun t : Nat => (t : Int)) hadd
        rw [natCast_add, natCast_pow3, natCast_pow2] at hc2
        omega
      rwa [hsub] at hc
    have hshift := brox_shift_carry_identity w1 rest
    change affineCarryInt v + ((2 : Int) ^ v.length - (3 : Int) ^ parityWeight v) =
      (2 : Int) ^ w1 * (broxOddCarry rest : Int) at hshift
    rw [hv_len, hv_wt] at hshift
    have hmul_w1 : ((2 : Int) ^ K - (3 : Int) ^ W) * ((x0 : Int) + 1) =
        (2 : Int) ^ w1 * (broxOddCarry rest : Int) := by
      have hx0p1_int : (x0 : Int) + 1 = (2 : Int) ^ w1 * (q0 : Int) := by
        have hc := congrArg Int.ofNat hx0p1_nat
        simpa [natCast_add, natCast_mul] using hc
      rw [hx0p1_int, ← Int.mul_assoc, Int.mul_comm ((2 : Int) ^ K - (3 : Int) ^ W) ((2 : Int) ^ w1),
          Int.mul_assoc, hbrox_int]
    have hcyc_aff : (2 : Int) ^ v.length * (x0 : Int) =
        (3 : Int) ^ parityWeight v * (x0 : Int) + affineCarryInt v := by
      rw [hv_len, hv_wt]
      rw [Int.mul_add, Int.mul_one] at hmul_w1
      rw [← hshift] at hmul_w1
      rw [Int.sub_mul] at hmul_w1
      omega
    rcases general_affine_converse_universal v (x0 : Int) (x0 : Int) hcyc_aff with ⟨_, hiter_int⟩
    rw [hv_len, collatzIterInt_ofNat] at hiter_int
    have hx0_cyc : collatzIter K x0 = x0 := by omega
    have htriv := hnocyc x0 K (by omega) (by omega) hx0_cyc
    omega
  · intro hnowit x p hx hp hcyc
    apply Classical.byContradiction
    intro hnon
    rcases nontrivial_cycle_min_mod48_and_band_21_22 x p hx hp hcyc hnon with
      ⟨x0, _, hx0_cyc, _, hm16, hx0_n3, _, hW5, hp8, hband_lo, hband_hi, hup_x0⟩
    let v := parityOfIter p x0
    let W := parityWeight v
    have hv_len : v.length = p := parityOfIter_length p x0
    have h3W_lt_2p : 3 ^ W < 2 ^ p := by
      change 21 ^ W < 7 ^ W * 2 ^ p at hband_lo
      rw [show (21 : Nat) ^ W = 7 ^ W * 3 ^ W from mul_pow_nat 7 3 W] at hband_lo
      apply Classical.byContradiction
      intro hge
      have hm := Nat.mul_le_mul_left (7 ^ W) (by omega : 2 ^ p ≤ 3 ^ W)
      omega
    -- Split `v` at its first `false` (`W < p` since `3^W < 2^p` vs `2^p ≤ 3^p`):
    have hsplit_v : ∃ (w1 : Nat) (rest : List Bool),
        v = List.replicate w1 true ++ (false :: rest) := by
      rcases split_at_first_false v with hall | hex
      · have hp23 := pow2_le_pow3 p
        change W = v.length at hall
        rw [hv_len] at hall
        rw [hall] at h3W_lt_2p
        omega
      · exact hex
    rcases hsplit_v with ⟨w1, rest, hv_eq⟩
    -- Since `p ≥ 8` and `x0 % 16 ∈ {7, 11, 15}`, the first two steps of `x0` are `true`:
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
      | zero =>
        rw [hv_eq] at hv_tt
        simp at hv_tt
      | succ w1' =>
        cases w1' with
        | zero =>
          rw [hv_eq] at hv_tt
          simp at hv_tt
        | succ _ => omega
    have hp_eq_K : p = w1 + 1 + rest.length := by
      rw [← hv_len, hv_eq, List.length_append, List.length_replicate, List.length_cons]
      omega
    have hW_eq : W = w1 + parityWeight rest := by
      dsimp [W]
      rw [hv_eq, parityWeight_append]
      have h : ∀ m : Nat, parityWeight (List.replicate m true) = m := by
        intro m; induction m with
        | zero => rfl
        | succ m' ih => simp [List.replicate_succ, parityWeight, ih]; omega
      rw [h w1]
      rfl
    -- Apply Bohm-Sontacchi + `brox_shift_carry_identity` + `odd_mul_pow2_exact_factor`:
    have hv_par : matchesParity v (x0 : Int) := parityOfIter_matches p x0
    have hcyc_int : collatzIterInt v.length (x0 : Int) = (x0 : Int) := by
      rw [hv_len, collatzIterInt_ofNat, hx0_cyc]
    have hbs := bohm_sontacchi_cycle_equation_universal v (x0 : Int) hv_par hcyc_int
    rw [hv_len] at hbs
    have hshift := brox_shift_carry_identity w1 rest
    dsimp only at hshift
    rw [← hv_eq, hv_len] at hshift
    have hmul_eq : ((2 : Int) ^ p - (3 : Int) ^ W) * ((x0 : Int) + 1) =
        (2 : Int) ^ w1 * (broxOddCarry rest : Int) := by
      rw [Int.mul_add, Int.mul_one, hbs]
      exact hshift
    have hD_odd : ((2 : Int) ^ p - (3 : Int) ^ W) % 2 = 1 := by
      have hp2_ev : ((2 : Int) ^ p) % 2 = 0 := by
        rw [show p = (p - 1) + 1 by omega, Int.pow_succ]
        omega
      have hp3_odd : ((3 : Int) ^ W) % 2 = 1 := pow3_mod2 W
      omega
    have hbrox_odd_int : (broxOddCarry rest : Int) % 2 = 1 := by
      have ho := (broxOddCarry_odd_and_ge_pow3 rest).1
      omega
    rcases odd_mul_pow2_exact_factor w1 ((2 : Int) ^ p - (3 : Int) ^ W)
        ((x0 : Int) + 1) (broxOddCarry rest : Int) hD_odd hbrox_odd_int hmul_eq with
      ⟨qInt, hqInt_eq, hqInt_odd⟩
    have hqInt_pos : qInt ≥ 1 := by
      have hp2w1_pos : (2 : Int) ^ w1 ≥ 1 := pow_pos_int 2 w1 (by omega)
      apply Classical.byContradiction
      intro hle0
      have hm_np : (2 : Int) ^ w1 * (-qInt) ≥ 0 := Int.mul_nonneg (by omega) (by omega)
      rw [Int.mul_neg] at hm_np
      omega
    let q0 : Nat := qInt.toNat
    have hq0_cast : (q0 : Int) = qInt := Int.toNat_of_nonneg (by omega)
    have hq0_ge1 : q0 ≥ 1 := by omega
    have hq0_odd : q0 % 2 = 1 := by omega
    have hx0_eq_q0 : x0 = 2 ^ w1 * q0 - 1 := by
      rw [← hq0_cast] at hqInt_eq
      have hnat : x0 + 1 = 2 ^ w1 * q0 := by
        have h1 : ((x0 + 1 : Nat) : Int) = ((2 ^ w1 * q0 : Nat) : Int) := by
          rw [natCast_add, natCast_mul]
          exact hqInt_eq
        omega
      omega
    have hbrox_q0_int : ((2 : Int) ^ p - (3 : Int) ^ W) * (q0 : Int) = (broxOddCarry rest : Int) := by
      apply mul_left_cancel_pow2_int w1
      calc
        (2 : Int) ^ w1 * (((2 : Int) ^ p - (3 : Int) ^ W) * (q0 : Int))
            = ((2 : Int) ^ p - (3 : Int) ^ W) * ((2 : Int) ^ w1 * (q0 : Int)) := by
              rw [← Int.mul_assoc, Int.mul_comm ((2 : Int) ^ w1), Int.mul_assoc]
        _ = ((2 : Int) ^ p - (3 : Int) ^ W) * ((x0 : Int) + 1) := by
              have hq_orig : (x0 : Int) + 1 = (2 : Int) ^ w1 * (q0 : Int) := by
                have hc := congrArg (fun t => t + 1) hx0_eq_q0
                have hp2w1_ge1 : 2 ^ w1 * q0 ≥ 1 := Nat.mul_pos (pow2_pos_nat w1) hq0_ge1
                have hadd : 2 ^ w1 * q0 - 1 + 1 = 2 ^ w1 * q0 := Nat.sub_add_cancel hp2w1_ge1
                rw [hadd] at hc
                have hci : ((x0 + 1 : Nat) : Int) = ((2 ^ w1 * q0 : Nat) : Int) :=
                  congrArg (fun t : Nat => (t : Int)) hc
                simpa [natCast_add, natCast_mul, natCast_pow2] using hci
              rw [hq_orig]
        _ = (2 : Int) ^ w1 * (broxOddCarry rest : Int) := hmul_eq
    have hbrox_q0_nat : (2 ^ p - 3 ^ W) * q0 = broxOddCarry rest := by
      have hsub : ((2 ^ p - 3 ^ W : Nat) : Int) = (2 : Int) ^ p - (3 : Int) ^ W := by
        have hadd : (2 ^ p - 3 ^ W) + 3 ^ W = 2 ^ p := Nat.sub_add_cancel (by omega)
        have hc2 : (((2 ^ p - 3 ^ W) + 3 ^ W : Nat) : Int) = ((2 ^ p : Nat) : Int) :=
          congrArg (fun t : Nat => (t : Int)) hadd
        rw [natCast_add, natCast_pow3, natCast_pow2] at hc2
        omega
      have h1 : (((2 ^ p - 3 ^ W) * q0 : Nat) : Int) = (broxOddCarry rest : Int) := by
        rw [natCast_mul, hsub]
        exact hbrox_q0_int
      omega
    have hwit : IsBroxNatCycleMinWitness w1 rest q0 := by
      unfold IsBroxNatCycleMinWitness
      dsimp only
      rw [← hp_eq_K, ← hW_eq, ← hx0_eq_q0]
      exact ⟨hw1_ge2, hq0_ge1, hq0_odd, hm16, hx0_n3, hW5, hp8,
        hband_lo, hband_hi, hup_x0, hbrox_q0_nat⟩
    exact hnowit w1 rest q0 hwit

-- ----------------------------------------------------------------------------
-- T4: Constructive Bezout Lifting & `(2^A * 3^B)` Bounded-Modulus Obstruction
-- ----------------------------------------------------------------------------

theorem bezout_product_lift_int (d m u1 v1 n u2 v2 : Int)
    (h1 : d * u1 + m * v1 = 1) (h2 : d * u2 + n * v2 = 1) :
    d * (u1 + m * v1 * u2) + (m * n) * (v1 * v2) = 1 := by
  calc
    d * (u1 + m * v1 * u2) + (m * n) * (v1 * v2)
        = d * u1 + (m * v1) * (d * u2 + n * v2) := by
          rw [Int.mul_add, Int.mul_add]
          have ha : d * (m * v1 * u2) = (m * v1) * (d * u2) := by
            rw [← Int.mul_assoc d (m * v1) u2, Int.mul_comm d (m * v1), Int.mul_assoc]
          have hb : (m * n) * (v1 * v2) = (m * v1) * (n * v2) := by
            rw [Int.mul_assoc m n (v1 * v2), ← Int.mul_assoc n v1 v2,
                Int.mul_comm n v1, Int.mul_assoc v1 n v2, ← Int.mul_assoc m v1 (n * v2)]
          rw [ha, hb, Int.add_assoc]
    _ = d * u1 + (m * v1) * 1 := by rw [h2]
    _ = 1 := by rw [Int.mul_one]; exact h1

theorem bezout_pow2_int (d : Int) (hd2 : d % 2 = 1) :
    ∀ A : Nat, ∃ u v : Int, d * u + (2 : Int) ^ A * v = 1
  | 0 => ⟨0, 1, by simp⟩
  | A + 1 => by
    rcases bezout_pow2_int d hd2 A with ⟨u1, v1, h1⟩
    let vStep : Int := - ((d - 1) / 2)
    have hstep : d * 1 + 2 * vStep = 1 := by dsimp [vStep]; omega
    refine ⟨u1 + (2 : Int) ^ A * v1 * 1, v1 * vStep, ?_⟩
    rw [Int.pow_succ]
    exact bezout_product_lift_int d ((2 : Int) ^ A) u1 v1 2 1 vStep h1 hstep

theorem bezout_pow3_int (d : Int) (hd3 : d % 3 ≠ 0) :
    ∀ B : Nat, ∃ u v : Int, d * u + (3 : Int) ^ B * v = 1
  | 0 => ⟨0, 1, by simp⟩
  | B + 1 => by
    rcases bezout_pow3_int d hd3 B with ⟨u1, v1, h1⟩
    have hbase3 : ∃ u2 v2 : Int, d * u2 + 3 * v2 = 1 := by
      by_cases hm1 : d % 3 = 1
      · exact ⟨1, - ((d - 1) / 3), by omega⟩
      · exact ⟨2, - ((2 * d - 1) / 3), by omega⟩
    rcases hbase3 with ⟨u2, v2, h2⟩
    refine ⟨u1 + (3 : Int) ^ B * v1 * u2, v1 * v2, ?_⟩
    rw [Int.pow_succ]
    exact bezout_product_lift_int d ((3 : Int) ^ B) u1 v1 3 u2 v2 h1 h2

/--
  Theorem T4a (Constructive All-Exponent `(2^A * 3^B)` Bezout Lifting over `Int`):
  For EVERY `d : Int` coprime to `6` (`d % 2 = 1`, `d % 3 ≠ 0`) and ALL `A, B : Nat`,
  there exist `U, V : Int` solving `d * U + (2^A * 3^B) * V = 1`.
-/
theorem bezout_coprime_pow2_pow3_universal (d : Int) (A B : Nat)
    (hd2 : d % 2 = 1) (hd3 : d % 3 ≠ 0) :
    ∃ U V : Int, d * U + ((2 : Int) ^ A * (3 : Int) ^ B) * V = 1 := by
  rcases bezout_pow2_int d hd2 A with ⟨u1, v1, h1⟩
  rcases bezout_pow3_int d hd3 B with ⟨u2, v2, h2⟩
  exact ⟨u1 + (2 : Int) ^ A * v1 * u2, v1 * v2,
    bezout_product_lift_int d ((2 : Int) ^ A) u1 v1 ((3 : Int) ^ B) u2 v2 h1 h2⟩

theorem rotateLeft_length : ∀ (j : Nat) (v : List Bool), (rotateLeft j v).length = v.length
  | 0, _ => rfl
  | j + 1, v => by simp [rotateLeft, rotateLeft_length j (rotateLeft1 v), rotateLeft1_length]

theorem rotateLeft_weight : ∀ (j : Nat) (v : List Bool),
    parityWeight (rotateLeft j v) = parityWeight v
  | 0, _ => rfl
  | j + 1, v => by simp [rotateLeft, rotateLeft_weight j (rotateLeft1 v), rotateLeft1_weight]

theorem rotateLeft_comm_rotateLeft1 : ∀ (j : Nat) (v : List Bool),
    rotateLeft j (rotateLeft1 v) = rotateLeft1 (rotateLeft j v)
  | 0, _ => rfl
  | j + 1, v => by simp [rotateLeft, rotateLeft_comm_rotateLeft1 j (rotateLeft1 v)]

theorem rotateLeft_append_prefix : ∀ (u w : List Bool),
    rotateLeft u.length (u ++ w) = w ++ u
  | [], w => by simp [rotateLeft]
  | b :: rest, w => by
    simp only [List.length_cons, List.cons_append]
    change rotateLeft rest.length (rotateLeft1 (b :: (rest ++ w))) = w ++ b :: rest
    simp only [rotateLeft1, List.append_assoc]
    rw [rotateLeft_append_prefix rest (w ++ [b])]
    simp

theorem rotateLeft_full_period (v : List Bool) : rotateLeft v.length v = v := by
  have h := rotateLeft_append_prefix v []
  simpa using h

/--
  Theorem T4b (Universal `(2^A * 3^B)` Bounded-Modulus Cycle Obstruction Meta-Theorem):
  For EVERY `(A, B : Nat)` and EVERY parity word `v` with `w(v) ≥ 1` and `3^w(v) < 2^|v|`,
  the rational periodic orbit `P_j / D` in `Q_(2)^+ ∩ Q_(3)^+` projects to an EXACT closed
  compressed Collatz pseudo-cycle `(r_0, ..., r_{|v|-1})` modulo `M = 2^A * 3^B`!
  Hence NO bounded-modulus graph or rational/modular vertex potential over `(Z / 2^A * 3^B Z)`
  can ever certify `NoNontrivialPositiveCycles` without global `Z`-integrality `D ∣ C(v)`!
-/
theorem universal_bounded_modulus_cycle_obstruction
    (v : List Bool) (A B : Nat)
    (hw : parityWeight v ≥ 1)
    (hdet : (3 : Int) ^ parityWeight v < (2 : Int) ^ v.length) :
    let D : Int := (2 : Int) ^ v.length - (3 : Int) ^ parityWeight v
    let M : Int := (2 : Int) ^ A * (3 : Int) ^ B
    D > 0 ∧ D % 2 = 1 ∧ D % 3 ≠ 0 ∧
    ∃ U : Int,
      (D * U) % M = 1 % M ∧
      let P := fun j : Nat => affineCarryInt (rotateLeft j v)
      let r := fun j : Nat => (P j * U) % M
      P v.length = P 0 ∧ r v.length = r 0 ∧
      (∀ j : Nat, P j > 0 ∧ P j % 3 ≠ 0) ∧
      (∀ j : Nat, B ≥ 1 -> r j % 3 ≠ 0) ∧
      (∀ j : Nat, ∀ u : List Bool, rotateLeft j v = false :: u ->
        P j = 2 * P (j + 1) ∧ (2 * r (j + 1) - r j) % M = 0) ∧
      (∀ j : Nat, ∀ u : List Bool, rotateLeft j v = true :: u ->
        2 * P (j + 1) = 3 * P j + D ∧ (2 * r (j + 1) - (3 * r j + 1)) % M = 0) := by
  dsimp only
  let D : Int := (2 : Int) ^ v.length - (3 : Int) ^ parityWeight v
  let M : Int := (2 : Int) ^ A * (3 : Int) ^ B
  have hv_len_pos : v.length ≥ 1 := by
    cases v with
    | nil => simp [parityWeight] at hw
    | cons _ _ => simp
  have hD_pos : D > 0 := by omega
  have hD_odd : D % 2 = 1 := by
    dsimp [D]
    have hp2_ev : ((2 : Int) ^ v.length) % 2 = 0 := by
      rw [show v.length = (v.length - 1) + 1 by omega, Int.pow_succ]
      omega
    have hp3_odd : ((3 : Int) ^ parityWeight v) % 2 = 1 := pow3_mod2 (parityWeight v)
    omega
  have hD_n3 : D % 3 ≠ 0 := by
    dsimp [D]
    have hp3_0 : ((3 : Int) ^ parityWeight v) % 3 = 0 := by
      rw [show parityWeight v = (parityWeight v - 1) + 1 by omega, Int.pow_succ]
      omega
    have hp2_n3 : ((2 : Int) ^ v.length) % 3 ≠ 0 := by
      have hn : ((2 ^ v.length : Nat) : Int) = (2 : Int) ^ v.length := rfl
      rcases pow2_mod3_one_or_two v.length with h1 | h2 <;> omega
    omega
  rcases bezout_coprime_pow2_pow3_universal D A B hD_odd hD_n3 with ⟨U, V, hbez⟩
  change D * U + M * V = 1 at hbez
  have hDU_mod : (D * U) % M = 1 % M := by
    have hDU_eq : D * U = 1 + M * (-V) := by rw [Int.mul_neg]; omega
    rw [hDU_eq, Int.add_mul_emod_self_left]
  refine ⟨hD_pos, hD_odd, hD_n3, U, hDU_mod, ?_⟩
  let P := fun j : Nat => affineCarryInt (rotateLeft j v)
  let r := fun j : Nat => (P j * U) % M
  have hP_per : P v.length = P 0 := by dsimp [P]; rw [rotateLeft_full_period]; rfl
  have hr_per : r v.length = r 0 := by dsimp [r]; rw [hP_per]
  have hP_props : ∀ j : Nat, P j > 0 ∧ P j % 3 ≠ 0 := by
    intro j
    have hwj : parityWeight (rotateLeft j v) ≥ 1 := by rw [rotateLeft_weight]; exact hw
    rcases affineCarryInt_pos_nondiv3_of_weight_pos (rotateLeft j v) hwj with ⟨hp, hn3⟩
    exact ⟨by omega, hn3⟩
  have hr_n3 : ∀ j : Nat, B ≥ 1 -> r j % 3 ≠ 0 := by
    intro j hB1
    have hM_div3 : M % 3 = 0 := by
      dsimp [M]
      rw [show B = (B - 1) + 1 by omega, Int.pow_succ, ← Int.mul_assoc]
      omega
    have hU_n3 : U % 3 ≠ 0 := by
      intro hU0
      have h1 : (D * U + M * V) % 3 = 0 := by
        rw [Int.add_emod, Int.mul_emod D U 3, hU0, Int.mul_emod M V 3, hM_div3]
        simp
      rw [hbez] at h1
      omega
    have hPU_n3 : (P j * U) % 3 ≠ 0 := by
      have hp_n3 := (hP_props j).2
      rcases (by omega : P j % 3 = 1 ∨ P j % 3 = 2) with hp3 | hp3 <;>
        rcases (by omega : U % 3 = 1 ∨ U % 3 = 2) with hu3 | hu3 <;>
        rw [Int.mul_emod, hp3, hu3] <;> decide
    have hdm : P j * U = M * ((P j * U) / M) + (P j * U) % M := by
      have h := Int.emod_def (P j * U) M
      omega
    have hM_mul_0 : (M * ((P j * U) / M)) % 3 = 0 := by
      rw [Int.mul_emod, hM_div3]
      simp
    have hmod_eq : (P j * U) % 3 = r j % 3 := by
      dsimp [r]
      conv => lhs; rw [hdm]
      rw [Int.add_emod, hM_mul_0, Int.zero_add, Int.emod_emod]
    omega
  refine ⟨hP_per, hr_per, hP_props, hr_n3, ?_, ?_⟩
  · intro j u hrot
    have hrot1 : rotateLeft (j + 1) v = u ++ [false] := by
      simp only [rotateLeft]
      rw [rotateLeft_comm_rotateLeft1 j v, hrot]
      rfl
    have hPj : P j = 2 * P (j + 1) := by
      dsimp [P]
      rw [hrot, hrot1]
      exact affineCarryInt_rotate_false u
    refine ⟨hPj, ?_⟩
    let X := P (j + 1) * U
    let Y := P j * U
    have hYX : Y = 2 * X := by
      dsimp [Y, X]
      rw [hPj, Int.mul_assoc]
    have hX_dm : X = M * (X / M) + X % M := by have h := Int.emod_def X M; omega
    have hY_dm : Y = M * (Y / M) + Y % M := by have h := Int.emod_def Y M; omega
    have hdiff : 2 * (X % M) - Y % M = M * (Y / M - 2 * (X / M)) := by
      rw [Int.mul_sub, ← Int.mul_assoc M 2 (X / M), Int.mul_comm M 2, Int.mul_assoc 2 M (X / M)]
      omega
    change (2 * (X % M) - Y % M) % M = 0
    rw [hdiff, Int.mul_emod_right]
  · intro j u hrot
    have hrot1 : rotateLeft (j + 1) v = u ++ [true] := by
      simp only [rotateLeft]
      rw [rotateLeft_comm_rotateLeft1 j v, hrot]
      rfl
    have hlen_u : u.length + 1 = v.length := by
      have hl := rotateLeft_length j v
      rw [hrot] at hl
      simpa using hl
    have hwt_u : parityWeight u + 1 = parityWeight v := by
      have hwj := rotateLeft_weight j v
      rw [hrot] at hwj
      simp only [parityWeight] at hwj
      omega
    have hPj : 2 * P (j + 1) = 3 * P j + D := by
      dsimp [P, D]
      rw [hrot, hrot1]
      have hrt := affineCarryInt_rotate_true u
      rw [hlen_u, hwt_u] at hrt
      omega
    refine ⟨hPj, ?_⟩
    let X := P (j + 1) * U
    let Y := P j * U
    have hlin_XY : 2 * X - (3 * Y + 1) = M * (-V) := by
      have h2X : 2 * X = (3 * P j + D) * U := by
        dsimp [X]
        rw [← Int.mul_assoc 2 (P (j + 1)) U, hPj]
      have hexp : (3 * P j + D) * U = 3 * Y + D * U := by
        dsimp [Y]
        rw [Int.add_mul, Int.mul_assoc]
      rw [h2X, hexp, Int.mul_neg]
      omega
    have hX_dm : X = M * (X / M) + X % M := by have h := Int.emod_def X M; omega
    have hY_dm : Y = M * (Y / M) + Y % M := by have h := Int.emod_def Y M; omega
    have hdiff : 2 * (X % M) - (3 * (Y % M) + 1) = M * (-V - 2 * (X / M) + 3 * (Y / M)) := by
      have hm1 : M * (-V - 2 * (X / M) + 3 * (Y / M)) =
          M * (-V) - 2 * (M * (X / M)) + 3 * (M * (Y / M)) := by
        rw [Int.mul_add, Int.mul_sub,
            ← Int.mul_assoc M 2 (X / M), Int.mul_comm M 2, Int.mul_assoc 2 M (X / M),
            ← Int.mul_assoc M 3 (Y / M), Int.mul_comm M 3, Int.mul_assoc 3 M (Y / M)]
      rw [hm1]
      omega
    change (2 * (X % M) - (3 * (Y % M) + 1)) % M = 0
    rw [hdiff, Int.mul_emod_right]

/--
  Theorem T4c (High-Floor `319 / 13 > 24` Positive Rational Cycle Obstruction Witness):
  `v = [true, true, false, true, true, false, true, false]` (`K = 8, W = 5, D = 2^8 - 3^5 = 13`)
  satisfies BOTH the `(21, 22)` band (`21^5 < 7^5 * 2^8 ≤ 22^5`) AND the sharpened 6-class
  mod-48 minimum sieve (`r_0 = 43 ∈ {7, 11, 23, 31, 43, 47}`) AND exceeds floor `n_0 = 24`
  at EVERY orbit vertex (`P_j ≥ 319 > 24 * 13 = 312` for all `j < 8`), yet is cleanly refuted
  by `Z`-integrality `13 ∤ 83 = broxOddCarry [true, true, false, true, false]`!
-/
theorem high_floor_319_over_13_obstruction_witness :
    let v := [true, true, false, true, true, false, true, false]
    v.length = 8 ∧
    parityWeight v = 5 ∧
    2 ^ v.length - 3 ^ parityWeight v = 13 ∧
    21 ^ 5 < 7 ^ 5 * 2 ^ 8 ∧ 7 ^ 5 * 2 ^ 8 ≤ 22 ^ 5 ∧
    affineCarry v = 319 ∧
    319 > 24 * 13 ∧
    (319 * 37) % 48 = 43 ∧ (13 * 37) % 48 = 1 ∧
    broxOddCarry [true, true, false, true, false] = 83 ∧
    83 % 13 ≠ 0 := by
  decide

-- ============================================================================
-- SECTION 5: Track 2 — Mixed `(2, 3)` Collatz SRS Halting Equivalence,
--            Natural / Arctic / Upper-Triangular Matrix Impossibility Theorems,
--            Self-Congruent Syracuse Pumping Obstruction, & Universal All-Weight
--            Minimal-Counterexample Sieves (`Mod-5184`, `Mod-46656`, `Mod-373248`)
-- ============================================================================

-- ----------------------------------------------------------------------------
-- T2.1 & T2.4: Mixed `(2, 3)` Binary-Ternary Collatz SRS & Matrix Obstructions
-- ----------------------------------------------------------------------------

/--
  7-symbol alphabet `{L, R, B0, B1, T0, T1, T2}` for the 11-rule mixed binary-ternary
  Collatz string rewriting system (`MixedSRSBaseRule`).
-/
inductive MixedSRSSym where
  | L | R | B0 | B1 | T0 | T1 | T2
  deriving DecidableEq, Repr

def isBinaryInteriorSym : MixedSRSSym -> Bool
  | .B0 => true
  | .B1 => true
  | _ => false

/--
  Right-to-left (MSB `+1` to LSB) mixed `(2, 3)` evaluation of interior words,
  mapping empty interior `[]` (`[L, R]`) to `1` so `1` is the unique normal form.
-/
def srsEvalInterior : List MixedSRSSym -> Nat
  | [] => 1
  | .B0 :: u => 2 * srsEvalInterior u
  | .B1 :: u => 2 * srsEvalInterior u + 1
  | .T0 :: u => 3 * srsEvalInterior u
  | .T1 :: u => 3 * srsEvalInterior u + 1
  | .T2 :: u => 3 * srsEvalInterior u + 2
  | .L :: u => srsEvalInterior u
  | .R :: u => srsEvalInterior u

theorem srsEvalInterior_pos : ∀ (u : List MixedSRSSym), srsEvalInterior u ≥ 1
  | [] => by simp [srsEvalInterior]
  | s :: u => by
    have ih := srsEvalInterior_pos u
    cases s <;> simp [srsEvalInterior] <;> omega

def encodePosBinAux : Nat -> Nat -> List MixedSRSSym
  | 0, _ => []
  | fuel + 1, n =>
    if n ≤ 1 then []
    else (if n % 2 == 1 then MixedSRSSym.B1 else MixedSRSSym.B0) :: encodePosBinAux fuel (n / 2)

/--
  Canonical LSB-first binary interior encoding `u ∈ {B0, B1}*` of `n ≥ 1`
  (`encodePosBin 1 = []`, so `1 ↔ [L, R]`).
-/
def encodePosBin (n : Nat) : List MixedSRSSym :=
  encodePosBinAux n n

theorem encodePosBinAux_spec : ∀ (fuel n : Nat),
    1 ≤ n -> n ≤ fuel + 1 ->
    srsEvalInterior (encodePosBinAux fuel n) = n ∧
    (∀ s, s ∈ encodePosBinAux fuel n -> isBinaryInteriorSym s = true)
  | 0, n, hn1, hle => by
    have hn : n = 1 := by omega
    subst hn
    refine ⟨rfl, ?_⟩
    intro s hs; simp [encodePosBinAux] at hs
  | fuel + 1, n, hn1, hle => by
    unfold encodePosBinAux
    by_cases h1 : n ≤ 1
    · have hn : n = 1 := by omega
      subst hn
      simp [srsEvalInterior]
    · simp only [h1, ite_false]
      rcases encodePosBinAux_spec fuel (n / 2) (by omega) (by omega) with ⟨heval, hbin⟩
      by_cases hodd : (n % 2 == 1) = true
      · have hm1 : n % 2 = 1 := of_decide_eq_true hodd
        simp only [hodd, ite_true, srsEvalInterior, heval]
        refine ⟨by omega, ?_⟩
        intro s hs
        rcases List.mem_cons.mp hs with rfl | hmem
        · rfl
        · exact hbin s hmem
      · have hm0 : n % 2 = 0 := by
          have hne : ¬ (n % 2 = 1) := fun h => hodd (decide_eq_true h)
          omega
        have hbf : (n % 2 == 1) = false := decide_eq_false (by omega)
        simp only [hbf, Bool.false_eq_true, ite_false, srsEvalInterior, heval]
        refine ⟨by omega, ?_⟩
        intro s hs
        rcases List.mem_cons.mp hs with rfl | hmem
        · rfl
        · exact hbin s hmem

theorem encodePosBin_spec (n : Nat) (hn : 1 ≤ n) :
    srsEvalInterior (encodePosBin n) = n ∧
    (∀ s, s ∈ encodePosBin n -> isBinaryInteriorSym s = true) :=
  encodePosBinAux_spec n n hn (by omega)

theorem binary_interior_unique : ∀ (u v : List MixedSRSSym),
    (∀ s, s ∈ u -> isBinaryInteriorSym s = true) ->
    (∀ s, s ∈ v -> isBinaryInteriorSym s = true) ->
    srsEvalInterior u = srsEvalInterior v -> u = v
  | [], [], _, _, _ => rfl
  | [], s :: v, _, hv, heq => by
    have hs := hv s List.mem_cons_self
    have hp := srsEvalInterior_pos v
    cases s <;> simp [isBinaryInteriorSym] at hs <;> simp [srsEvalInterior] at heq <;> omega
  | s :: u, [], hu, _, heq => by
    have hs := hu s List.mem_cons_self
    have hp := srsEvalInterior_pos u
    cases s <;> simp [isBinaryInteriorSym] at hs <;> simp [srsEvalInterior] at heq <;> omega
  | s1 :: u, s2 :: v, hu, hv, heq => by
    have hs1 := hu s1 List.mem_cons_self
    have hs2 := hv s2 List.mem_cons_self
    have hu' : ∀ x, x ∈ u -> isBinaryInteriorSym x = true :=
      fun x hx => hu x (List.mem_cons_of_mem s1 hx)
    have hv' : ∀ x, x ∈ v -> isBinaryInteriorSym x = true :=
      fun x hx => hv x (List.mem_cons_of_mem s2 hx)
    cases s1 <;> simp [isBinaryInteriorSym] at hs1 <;>
    cases s2 <;> simp [isBinaryInteriorSym] at hs2 <;>
    simp [srsEvalInterior] at heq
    · rw [binary_interior_unique u v hu' hv' (by omega)]
    · omega
    · omega
    · rw [binary_interior_unique u v hu' hv' (by omega)]

/--
  11-rule mixed `(2, 3)` Collatz string rewriting system (`R1`–`R11`).
-/
inductive MixedSRSBaseRule : List MixedSRSSym -> List MixedSRSSym -> Prop where
  | r1_even : MixedSRSBaseRule [.L, .B0] [.L]
  | r2_odd  : MixedSRSBaseRule [.L, .B1] [.L, .T2]
  | r3_t0b0 : MixedSRSBaseRule [.T0, .B0] [.B0, .T0]
  | r4_t0b1 : MixedSRSBaseRule [.T0, .B1] [.B1, .T1]
  | r5_t1b0 : MixedSRSBaseRule [.T1, .B0] [.B1, .T0]
  | r6_t1b1 : MixedSRSBaseRule [.T1, .B1] [.B0, .T2]
  | r7_t2b0 : MixedSRSBaseRule [.T2, .B0] [.B0, .T1]
  | r8_t2b1 : MixedSRSBaseRule [.T2, .B1] [.B1, .T2]
  | r9_t0R  : MixedSRSBaseRule [.T0, .R] [.B1, .R]
  | r10_t1R : MixedSRSBaseRule [.T1, .R] [.B0, .B0, .R]
  | r11_t2R : MixedSRSBaseRule [.T2, .R] [.B1, .B0, .R]

def MixedCollatzStep (w1 w2 : List MixedSRSSym) : Prop :=
  ∃ p l r q : List MixedSRSSym,
    MixedSRSBaseRule l r ∧ w1 = p ++ l ++ q ∧ w2 = p ++ r ++ q

inductive MixedSRSReaches : List MixedSRSSym -> List MixedSRSSym -> Prop where
  | refl (w : List MixedSRSSym) : MixedSRSReaches w w
  | step {w1 w2 w3 : List MixedSRSSym} :
      MixedCollatzStep w1 w2 -> MixedSRSReaches w2 w3 -> MixedSRSReaches w1 w3

theorem mixedSRSReaches_trans {w1 w2 w3 : List MixedSRSSym}
    (h12 : MixedSRSReaches w1 w2) (h23 : MixedSRSReaches w2 w3) :
    MixedSRSReaches w1 w3 := by
  induction h12 with
  | refl _ => exact h23
  | step hs _ ih => exact MixedSRSReaches.step hs (ih h23)

theorem mixedSRS_prepend_context (p : List MixedSRSSym) {w1 w2 : List MixedSRSSym}
    (h : MixedSRSReaches w1 w2) : MixedSRSReaches (p ++ w1) (p ++ w2) := by
  induction h with
  | refl _ => exact MixedSRSReaches.refl _
  | step hs _ ih =>
    rcases hs with ⟨p0, l, r, q0, hrule, heq1, heq2⟩
    refine MixedSRSReaches.step ⟨p ++ p0, l, r, q0, hrule, ?_, ?_⟩ ih
    · simp [heq1, List.append_assoc]
    · simp [heq2, List.append_assoc]

theorem carry_propagate_reaches_binary :
    ∀ (u : List MixedSRSSym) (t : MixedSRSSym),
      (∀ s, s ∈ u -> isBinaryInteriorSym s = true) ->
      (t = .T0 ∨ t = .T1 ∨ t = .T2) ->
      ∃ v : List MixedSRSSym,
        (∀ s, s ∈ v -> isBinaryInteriorSym s = true) ∧
        srsEvalInterior v = srsEvalInterior (t :: u) ∧
        MixedSRSReaches ([t] ++ u ++ [.R]) (v ++ [.R])
  | [], t, _, ht => by
    rcases ht with rfl | rfl | rfl
    · refine ⟨[.B1], ?_, rfl, ?_⟩
      · intro s hs; simp at hs; subst hs; rfl
      · exact MixedSRSReaches.step ⟨[], [.T0, .R], [.B1, .R], [], .r9_t0R, rfl, rfl⟩ (.refl _)
    · refine ⟨[.B0, .B0], ?_, rfl, ?_⟩
      · intro s hs; simp at hs; rcases hs with rfl | rfl <;> rfl
      · exact MixedSRSReaches.step ⟨[], [.T1, .R], [.B0, .B0, .R], [], .r10_t1R, rfl, rfl⟩ (.refl _)
    · refine ⟨[.B1, .B0], ?_, rfl, ?_⟩
      · intro s hs; simp at hs; rcases hs with rfl | rfl <;> rfl
      · exact MixedSRSReaches.step ⟨[], [.T2, .R], [.B1, .B0, .R], [], .r11_t2R, rfl, rfl⟩ (.refl _)
  | b :: u, t, hbin, ht => by
    have hb := hbin b List.mem_cons_self
    have hu : ∀ s, s ∈ u -> isBinaryInteriorSym s = true :=
      fun s hs => hbin s (List.mem_cons_of_mem b hs)
    have hstep_local : ∃ b' t' : MixedSRSSym,
        isBinaryInteriorSym b' = true ∧
        (t' = .T0 ∨ t' = .T1 ∨ t' = .T2) ∧
        MixedSRSBaseRule [t, b] [b', t'] ∧
        srsEvalInterior (t :: b :: u) = srsEvalInterior (b' :: t' :: u) := by
      cases b <;> simp [isBinaryInteriorSym] at hb
      · rcases ht with rfl | rfl | rfl
        · exact ⟨.B0, .T0, rfl, Or.inl rfl, .r3_t0b0, by simp [srsEvalInterior]; omega⟩
        · exact ⟨.B1, .T0, rfl, Or.inl rfl, .r5_t1b0, by simp [srsEvalInterior]; omega⟩
        · exact ⟨.B0, .T1, rfl, Or.inr (Or.inl rfl), .r7_t2b0, by simp [srsEvalInterior]; omega⟩
      · rcases ht with rfl | rfl | rfl
        · exact ⟨.B1, .T1, rfl, Or.inr (Or.inl rfl), .r4_t0b1, by simp [srsEvalInterior]; omega⟩
        · exact ⟨.B0, .T2, rfl, Or.inr (Or.inr rfl), .r6_t1b1, by simp [srsEvalInterior]; omega⟩
        · exact ⟨.B1, .T2, rfl, Or.inr (Or.inr rfl), .r8_t2b1, by simp [srsEvalInterior]; omega⟩
    rcases hstep_local with ⟨b', t', hb', ht', hrule, heval_eq⟩
    rcases carry_propagate_reaches_binary u t' hu ht' with ⟨v', hv'_bin, hv'_eval, hv'_reach⟩
    refine ⟨b' :: v', ?_, ?_, ?_⟩
    · intro s hs
      rcases List.mem_cons.mp hs with rfl | hmem
      · exact hb'
      · exact hv'_bin s hmem
    · rw [heval_eq]
      cases b' <;> simp [isBinaryInteriorSym] at hb' <;> simp [srsEvalInterior, hv'_eval]
    · have hs1 : MixedCollatzStep ([t] ++ (b :: u) ++ [.R]) ([b'] ++ ([t'] ++ u ++ [.R])) :=
        ⟨[], [t, b], [b', t'], u ++ [.R], hrule, rfl, rfl⟩
      have hs2 := mixedSRS_prepend_context [b'] hv'_reach
      exact MixedSRSReaches.step hs1 hs2

theorem encodePosBin_simulates_collatzStep (n : Nat) (hn : n ≥ 2) :
    MixedSRSReaches ([.L] ++ encodePosBin n ++ [.R])
      ([.L] ++ encodePosBin (collatzStep n) ++ [.R]) := by
  rcases encodePosBin_spec n (by omega) with ⟨heval_n, hbin_n⟩
  cases hu : encodePosBin n with
  | nil =>
    rw [hu] at heval_n
    simp [srsEvalInterior] at heval_n
    omega
  | cons b u =>
    rw [hu] at heval_n hbin_n
    have hb := hbin_n b List.mem_cons_self
    have hu_bin : ∀ s, s ∈ u -> isBinaryInteriorSym s = true :=
      fun s hs => hbin_n s (List.mem_cons_of_mem b hs)
    cases b <;> simp [isBinaryInteriorSym] at hb
    · simp only [srsEvalInterior] at heval_n
      have hev : (n % 2 == 0) = true := decide_eq_true (by omega)
      have hcstep : collatzStep n = srsEvalInterior u := by
        simp only [collatzStep, hev, ite_true]
        omega
      have hu_eq : u = encodePosBin (collatzStep n) := by
        rcases encodePosBin_spec (collatzStep n) (by rw [hcstep]; exact srsEvalInterior_pos u) with
          ⟨heval_c, hbin_c⟩
        exact binary_interior_unique u (encodePosBin (collatzStep n)) hu_bin hbin_c (by omega)
      rw [← hu_eq]
      exact MixedSRSReaches.step ⟨[], [.L, .B0], [.L], u ++ [.R], .r1_even, rfl, rfl⟩ (.refl _)
    · simp only [srsEvalInterior] at heval_n
      have hodd : (n % 2 == 0) = false := decide_eq_false (by omega)
      have hcstep : collatzStep n = 3 * srsEvalInterior u + 2 := by
        simp only [collatzStep, hodd, Bool.false_eq_true, ite_false]
        omega
      rcases carry_propagate_reaches_binary u .T2 hu_bin (Or.inr (Or.inr rfl)) with
        ⟨v, hv_bin, hv_eval, hv_reach⟩
      simp only [srsEvalInterior] at hv_eval
      have hv_eq : v = encodePosBin (collatzStep n) := by
        rcases encodePosBin_spec (collatzStep n) (by omega) with ⟨heval_c, hbin_c⟩
        exact binary_interior_unique v (encodePosBin (collatzStep n)) hv_bin hbin_c (by omega)
      have hs1 : MixedCollatzStep ([.L] ++ (.B1 :: u) ++ [.R]) ([.L] ++ ([.T2] ++ u ++ [.R])) :=
        ⟨[], [.L, .B1], [.L, .T2], u ++ [.R], .r2_odd, rfl, rfl⟩
      have hs2 := mixedSRS_prepend_context [.L] hv_reach
      rw [hv_eq] at hs2
      exact MixedSRSReaches.step hs1 hs2

theorem collatzIter_eq_one_implies_mixedSRS_halts :
    ∀ (k n : Nat), 1 ≤ n -> collatzIter k n = 1 ->
      MixedSRSReaches ([.L] ++ encodePosBin n ++ [.R]) [.L, .R]
  | 0, n, _, h1 => by
    simp [collatzIter] at h1
    subst h1
    exact MixedSRSReaches.refl [.L, .R]
  | k + 1, n, hn1, hk => by
    by_cases hn_eq1 : n = 1
    · subst hn_eq1
      exact MixedSRSReaches.refl [.L, .R]
    · have hn_ge2 : n ≥ 2 := by omega
      have hc_pos : 1 ≤ collatzStep n := by
        by_cases he : (n % 2 == 0) = true
        · have hm : n % 2 = 0 := of_decide_eq_true he
          simp only [collatzStep, he, ite_true]; omega
        · have hm : n % 2 = 1 := by
            have hne : ¬ (n % 2 = 0) := fun h => he (decide_eq_true h)
            omega
          have hef : (n % 2 == 0) = false := decide_eq_false (by omega)
          simp only [collatzStep, hef, Bool.false_eq_true, ite_false]; omega
      have hs1 := encodePosBin_simulates_collatzStep n hn_ge2
      have hs2 := collatzIter_eq_one_implies_mixedSRS_halts k (collatzStep n) hc_pos hk
      exact mixedSRSReaches_trans hs1 hs2

def ValidFramedMixedWord (w : List MixedSRSSym) : Prop :=
  ∃ u : List MixedSRSSym,
    w = [.L] ++ u ++ [.R] ∧ (∀ s, s ∈ u -> s ≠ .L ∧ s ≠ .R)

theorem interior_step_preserves_eval :
    ∀ (p l r q : List MixedSRSSym),
      MixedSRSBaseRule l r ->
      (∀ s, s ∈ p -> s ≠ .L ∧ s ≠ .R) ->
      (∀ s, s ∈ l -> s ≠ .L ∧ s ≠ .R) ->
      (∀ s, s ∈ q -> s ≠ .L ∧ s ≠ .R) ->
      (∀ s, s ∈ r -> s ≠ .L ∧ s ≠ .R) ∧
      srsEvalInterior (p ++ r ++ q) = srsEvalInterior (p ++ l ++ q) := by
  intro p l r q hrule hp hl _
  have hlr : (∀ s, s ∈ r -> s ≠ .L ∧ s ≠ .R) ∧
      srsEvalInterior (r ++ q) = srsEvalInterior (l ++ q) := by
    cases hrule with
    | r1_even => exfalso; exact (hl .L List.mem_cons_self).1 rfl
    | r2_odd  => exfalso; exact (hl .L List.mem_cons_self).1 rfl
    | r9_t0R  => exfalso; exact (hl .R (List.mem_cons_of_mem MixedSRSSym.T0 List.mem_cons_self)).2 rfl
    | r10_t1R => exfalso; exact (hl .R (List.mem_cons_of_mem MixedSRSSym.T1 List.mem_cons_self)).2 rfl
    | r11_t2R => exfalso; exact (hl .R (List.mem_cons_of_mem MixedSRSSym.T2 List.mem_cons_self)).2 rfl
    | r3_t0b0 =>
      refine ⟨?_, by simp [srsEvalInterior]; omega⟩
      intro s hs; simp at hs; rcases hs with rfl | rfl <;> decide
    | r4_t0b1 =>
      refine ⟨?_, by simp [srsEvalInterior]; omega⟩
      intro s hs; simp at hs; rcases hs with rfl | rfl <;> decide
    | r5_t1b0 =>
      refine ⟨?_, by simp [srsEvalInterior]; omega⟩
      intro s hs; simp at hs; rcases hs with rfl | rfl <;> decide
    | r6_t1b1 =>
      refine ⟨?_, by simp [srsEvalInterior]; omega⟩
      intro s hs; simp at hs; rcases hs with rfl | rfl <;> decide
    | r7_t2b0 =>
      refine ⟨?_, by simp [srsEvalInterior]; omega⟩
      intro s hs; simp at hs; rcases hs with rfl | rfl <;> decide
    | r8_t2b1 =>
      refine ⟨?_, by simp [srsEvalInterior]; omega⟩
      intro s hs; simp at hs; rcases hs with rfl | rfl <;> decide
  refine ⟨hlr.1, ?_⟩
  induction p with
  | nil => exact hlr.2
  | cons x xs ih =>
    have hx := hp x List.mem_cons_self
    have hxs : ∀ s, s ∈ xs -> s ≠ .L ∧ s ≠ .R :=
      fun s hs => hp s (List.mem_cons_of_mem x hs)
    have ih' := ih hxs
    cases x <;> simp at hx <;> simp only [List.cons_append, srsEvalInterior, ih']

theorem append_eq_single_R_iff {u1 u2 : List MixedSRSSym}
    (h : u1 ++ [.R] = u2 ++ [.R]) : u1 = u2 := by
  have hrev := congrArg List.reverse h
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
             List.cons_append, List.cons.injEq] at hrev
  have := congrArg List.reverse hrev.2
  simpa using this

theorem mem_prefix_of_snoc_eq {α : Type} :
    ∀ (u p tail : List α) (r : α),
      u ++ [r] = p ++ tail -> tail ≠ [] -> ∀ x, x ∈ p -> x ∈ u
  | [], [], _, _, _, _, _, hx => by simp at hx
  | [], y :: ps, tail, r, heq, hne, _, _ => by
    exfalso
    cases tail with
    | nil => exact hne rfl
    | cons t ts =>
      have hlen := congrArg List.length heq
      simp [List.length_append] at hlen
  | _ :: _, [], _, _, _, _, _, hx => by simp at hx
  | a :: us, y :: ps, tail, r, heq, hne, x, hx => by
    simp only [List.cons_append, List.cons.injEq] at heq
    rcases heq with ⟨hay, hrest⟩
    rcases List.mem_cons.mp hx with rfl | hps
    · rw [← hay]; exact List.mem_cons_self
    · exact List.mem_cons_of_mem a (mem_prefix_of_snoc_eq us ps tail r hrest hne x hps)

theorem split_framed_rule {r : List MixedSRSSym} (u p l q : List MixedSRSSym)
    (hu : ∀ s, s ∈ u -> s ≠ .L ∧ s ≠ .R)
    (hrule : MixedSRSBaseRule l r)
    (heq : [.L] ++ u ++ [.R] = p ++ l ++ q) :
    (p = [] ∧ (l = [.L, .B0] ∨ l = [.L, .B1])) ∨
    (∃ p' : List MixedSRSSym, p = .L :: p' ∧ q = [] ∧
      (l = [.T0, .R] ∨ l = [.T1, .R] ∨ l = [.T2, .R]) ∧ u = p' ++ [l.headD .T0]) ∨
    (∃ p' q' : List MixedSRSSym, p = .L :: p' ∧ q = q' ++ [.R] ∧
      u = p' ++ l ++ q' ∧ (∀ s, s ∈ l -> s ≠ .L ∧ s ≠ .R)) := by
  cases p with
  | nil =>
    simp only [List.nil_append] at heq
    cases hrule with
    | r1_even => exact Or.inl ⟨rfl, Or.inl rfl⟩
    | r2_odd  => exact Or.inl ⟨rfl, Or.inr rfl⟩
    | r3_t0b0 | r4_t0b1 | r5_t1b0 | r6_t1b1 | r7_t2b0 | r8_t2b1 | r9_t0R | r10_t1R | r11_t2R =>
      simp at heq
  | cons p0 p' =>
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at heq
    rcases heq with ⟨hp0, htail⟩
    have hp0_eq : p0 = .L := hp0.symm
    subst hp0_eq
    cases hrule with
    | r1_even | r2_odd =>
      exfalso
      have hmem : MixedSRSSym.L ∈ u ++ [.R] := by
        rw [htail]
        exact List.mem_append_left q (List.mem_append_right p' List.mem_cons_self)
      rcases List.mem_append.mp hmem with h_in_u | h_in_R
      · exact (hu .L h_in_u).1 rfl
      · simp at h_in_R
    | r9_t0R =>
      cases q with
      | nil =>
        simp only [List.append_nil] at htail
        have hu_eq : u = p' ++ [.T0] :=
          append_eq_single_R_iff (by simpa [List.append_assoc] using htail)
        exact Or.inr (Or.inl ⟨p', rfl, rfl, Or.inl rfl, hu_eq⟩)
      | cons q0 qs =>
        exfalso
        have hR_in_pref : MixedSRSSym.R ∈ p' ++ [.T0, .R] :=
          List.mem_append_right p' (List.mem_cons_of_mem MixedSRSSym.T0 List.mem_cons_self)
        have hR_in_u : MixedSRSSym.R ∈ u :=
          mem_prefix_of_snoc_eq u (p' ++ [.T0, .R]) (q0 :: qs) .R htail (by simp) .R hR_in_pref
        exact (hu .R hR_in_u).2 rfl
    | r10_t1R =>
      cases q with
      | nil =>
        simp only [List.append_nil] at htail
        have hu_eq : u = p' ++ [.T1] :=
          append_eq_single_R_iff (by simpa [List.append_assoc] using htail)
        exact Or.inr (Or.inl ⟨p', rfl, rfl, Or.inr (Or.inl rfl), hu_eq⟩)
      | cons q0 qs =>
        exfalso
        have hR_in_pref : MixedSRSSym.R ∈ p' ++ [.T1, .R] :=
          List.mem_append_right p' (List.mem_cons_of_mem MixedSRSSym.T1 List.mem_cons_self)
        have hR_in_u : MixedSRSSym.R ∈ u :=
          mem_prefix_of_snoc_eq u (p' ++ [.T1, .R]) (q0 :: qs) .R htail (by simp) .R hR_in_pref
        exact (hu .R hR_in_u).2 rfl
    | r11_t2R =>
      cases q with
      | nil =>
        simp only [List.append_nil] at htail
        have hu_eq : u = p' ++ [.T2] :=
          append_eq_single_R_iff (by simpa [List.append_assoc] using htail)
        exact Or.inr (Or.inl ⟨p', rfl, rfl, Or.inr (Or.inr rfl), hu_eq⟩)
      | cons q0 qs =>
        exfalso
        have hR_in_pref : MixedSRSSym.R ∈ p' ++ [.T2, .R] :=
          List.mem_append_right p' (List.mem_cons_of_mem MixedSRSSym.T2 List.mem_cons_self)
        have hR_in_u : MixedSRSSym.R ∈ u :=
          mem_prefix_of_snoc_eq u (p' ++ [.T2, .R]) (q0 :: qs) .R htail (by simp) .R hR_in_pref
        exact (hu .R hR_in_u).2 rfl
    | r3_t0b0 | r4_t0b1 | r5_t1b0 | r6_t1b1 | r7_t2b0 | r8_t2b1 =>
      have hrev := congrArg List.reverse htail
      cases hq_rev : q.reverse with
      | nil =>
        have hq_nil : q = [] := by
          have := congrArg List.reverse hq_rev; simpa using this
        subst hq_nil
        simp only [List.append_nil, List.reverse_append, List.reverse_cons, List.reverse_nil,
                   List.nil_append, List.cons_append] at hrev
        exfalso
        simp at hrev
      | cons qLast qRem =>
        let q' := qRem.reverse
        have hq_eq : q = q' ++ [qLast] := by
          have := congrArg List.reverse hq_rev
          simpa [q', List.reverse_append] using this
        rw [hq_eq] at htail
        have htail_rev := congrArg List.reverse htail
        simp only [List.reverse_append, List.reverse_cons, List.reverse_nil,
                   List.nil_append, List.cons_append, List.cons.injEq] at htail_rev
        have hqLast : qLast = .R := htail_rev.1.symm
        subst hqLast
        refine Or.inr (Or.inr ⟨p', q', rfl, hq_eq, ?_, ?_⟩)
        · have := congrArg List.reverse htail_rev.2
          simpa [List.reverse_append, List.append_assoc] using this
        · intro s hs; simp at hs; rcases hs with rfl | rfl <;> decide

theorem srsEvalInterior_msb_replace :
    ∀ (p' u1 u2 : List MixedSRSSym),
      (∀ s, s ∈ p' -> s ≠ .L ∧ s ≠ .R) ->
      srsEvalInterior u1 = srsEvalInterior u2 ->
      srsEvalInterior (p' ++ u1) = srsEvalInterior (p' ++ u2)
  | [], _, _, _, h => h
  | x :: xs, u1, u2, hp, h => by
    have hx := hp x List.mem_cons_self
    have hxs : ∀ s, s ∈ xs -> s ≠ .L ∧ s ≠ .R :=
      fun s hs => hp s (List.mem_cons_of_mem x hs)
    have ih := srsEvalInterior_msb_replace xs u1 u2 hxs h
    cases x <;> simp at hx <;> simp [srsEvalInterior, ih]

theorem mixedCollatzStep_sound {w1 w2 : List MixedSRSSym}
    (hv1 : ValidFramedMixedWord w1) (hs : MixedCollatzStep w1 w2) :
    ∃ u2 : List MixedSRSSym,
      w2 = [.L] ++ u2 ++ [.R] ∧
      (∀ s, s ∈ u2 -> s ≠ .L ∧ s ≠ .R) ∧
      (srsEvalInterior w2 = srsEvalInterior w1 ∨
       srsEvalInterior w2 = collatzStep (srsEvalInterior w1)) := by
  rcases hv1 with ⟨u1, hw1_eq, hu1_noLR⟩
  rcases hs with ⟨p, l, r, q, hrule, heq1, heq2⟩
  have heq_f : [.L] ++ u1 ++ [.R] = p ++ l ++ q := hw1_eq.symm.trans heq1
  rcases split_framed_rule u1 p l q hu1_noLR hrule heq_f with
    ⟨hp_nil, hl_left⟩ | ⟨p', hp_eq, hq_nil, hl_right, hu1_eq⟩ | ⟨p', q', hp_eq, hq_eq, hu1_eq, hl_noLR⟩
  · subst hp_nil
    simp only [List.nil_append] at heq_f heq2
    cases hrule with
    | r1_even =>
      cases u1 with
      | nil => simp at heq_f
      | cons s0 rest =>
        simp only [List.cons_append, List.nil_append, List.cons.injEq] at heq_f
        rcases heq_f with ⟨_, hs0, hrest_q⟩
        subst hs0
        subst hrest_q
        refine ⟨rest, ?_, fun s hs => hu1_noLR s (List.mem_cons_of_mem .B0 hs), Or.inr ?_⟩
        · simpa using heq2
        · rw [hw1_eq, heq2]
          simp only [List.cons_append, List.nil_append, srsEvalInterior]
          have heval_R : ∀ z : List MixedSRSSym,
              (∀ s, s ∈ z -> s ≠ .L ∧ s ≠ .R) -> srsEvalInterior (z ++ [.R]) = srsEvalInterior z := by
            intro z hz
            induction z with
            | nil => rfl
            | cons x xs ih =>
              have hx := hz x List.mem_cons_self
              have ih' := ih (fun s hs => hz s (List.mem_cons_of_mem x hs))
              cases x <;> simp at hx <;> simp only [List.cons_append, srsEvalInterior, ih']
          have h1 := heval_R rest (fun s hs => hu1_noLR s (List.mem_cons_of_mem .B0 hs))
          rw [h1]
          have hev : ((2 * srsEvalInterior rest) % 2 == 0) = true := decide_eq_true (by omega)
          simp only [collatzStep, hev, ite_true]
          omega
    | r2_odd =>
      cases u1 with
      | nil => simp at heq_f
      | cons s0 rest =>
        simp only [List.cons_append, List.nil_append, List.cons.injEq] at heq_f
        rcases heq_f with ⟨_, hs0, hrest_q⟩
        subst hs0
        subst hrest_q
        refine ⟨.T2 :: rest, ?_, ?_, Or.inr ?_⟩
        · simpa using heq2
        · intro s hs
          rcases List.mem_cons.mp hs with rfl | hmem
          · decide
          · exact hu1_noLR s (List.mem_cons_of_mem .B1 hmem)
        · rw [hw1_eq, heq2]
          simp only [List.cons_append, List.nil_append, srsEvalInterior]
          have heval_R : ∀ z : List MixedSRSSym,
              (∀ s, s ∈ z -> s ≠ .L ∧ s ≠ .R) -> srsEvalInterior (z ++ [.R]) = srsEvalInterior z := by
            intro z hz
            induction z with
            | nil => rfl
            | cons x xs ih =>
              have hx := hz x List.mem_cons_self
              have ih' := ih (fun s hs => hz s (List.mem_cons_of_mem x hs))
              cases x <;> simp at hx <;> simp only [List.cons_append, srsEvalInterior, ih']
          have h1 := heval_R rest (fun s hs => hu1_noLR s (List.mem_cons_of_mem .B1 hs))
          rw [h1]
          have hodd : ((2 * srsEvalInterior rest + 1) % 2 == 0) = false := decide_eq_false (by omega)
          simp only [collatzStep, hodd, Bool.false_eq_true, ite_false]
          omega
    | _ => rcases hl_left with h | h <;> simp at h
  · subst hp_eq; subst hq_nil
    have hp'_noLR : ∀ s, s ∈ p' -> s ≠ .L ∧ s ≠ .R := by
      intro s hs; rw [hu1_eq] at hu1_noLR; exact hu1_noLR s (List.mem_append_left _ hs)
    have heval_R : ∀ z : List MixedSRSSym,
        (∀ s, s ∈ z -> s ≠ .L ∧ s ≠ .R) -> srsEvalInterior (z ++ [.R]) = srsEvalInterior z := by
      intro z hz
      induction z with
      | nil => rfl
      | cons x xs ih =>
        have hx := hz x List.mem_cons_self
        have ih' := ih (fun s hs => hz s (List.mem_cons_of_mem x hs))
        cases x <;> simp at hx <;> simp only [List.cons_append, srsEvalInterior, ih']
    cases hrule with
    | r9_t0R =>
      simp only [List.headD] at hu1_eq
      refine ⟨p' ++ [.B1], by simpa [List.append_assoc] using heq2, ?_, Or.inl ?_⟩
      · intro s hs; rcases List.mem_append.mp hs with h1 | h2
        · exact hp'_noLR s h1
        · simp at h2; subst h2; decide
      · rw [hw1_eq, hu1_eq, heq2]
        simp only [List.cons_append, List.nil_append, List.append_nil, srsEvalInterior]
        have hA := heval_R (p' ++ [.B1]) (fun s hs => by
          rcases List.mem_append.mp hs with h1 | h2
          · exact hp'_noLR s h1
          · simp at h2; subst h2; decide)
        have hB := heval_R (p' ++ [.T0]) (fun s hs => by
          rcases List.mem_append.mp hs with h1 | h2
          · exact hp'_noLR s h1
          · simp at h2; subst h2; decide)
        have h1 : p' ++ [.B1, .R] = (p' ++ [.B1]) ++ [.R] := by simp [List.append_assoc]
        rw [h1, hA, hB]
        exact srsEvalInterior_msb_replace p' [.B1] [.T0] hp'_noLR rfl
    | r10_t1R =>
      simp only [List.headD] at hu1_eq
      refine ⟨p' ++ [.B0, .B0], by simpa [List.append_assoc] using heq2, ?_, Or.inl ?_⟩
      · intro s hs; rcases List.mem_append.mp hs with h1 | h2
        · exact hp'_noLR s h1
        · simp at h2; rcases h2 with rfl | rfl <;> decide
      · rw [hw1_eq, hu1_eq, heq2]
        simp only [List.cons_append, List.nil_append, List.append_nil, srsEvalInterior]
        have hA := heval_R (p' ++ [.B0, .B0]) (fun s hs => by
          rcases List.mem_append.mp hs with h1 | h2
          · exact hp'_noLR s h1
          · simp at h2; rcases h2 with rfl | rfl <;> decide)
        have hB := heval_R (p' ++ [.T1]) (fun s hs => by
          rcases List.mem_append.mp hs with h1 | h2
          · exact hp'_noLR s h1
          · simp at h2; subst h2; decide)
        have h1 : p' ++ [.B0, .B0, .R] = (p' ++ [.B0, .B0]) ++ [.R] := by simp [List.append_assoc]
        rw [h1, hA, hB]
        exact srsEvalInterior_msb_replace p' [.B0, .B0] [.T1] hp'_noLR rfl
    | r11_t2R =>
      simp only [List.headD] at hu1_eq
      refine ⟨p' ++ [.B1, .B0], by simpa [List.append_assoc] using heq2, ?_, Or.inl ?_⟩
      · intro s hs; rcases List.mem_append.mp hs with h1 | h2
        · exact hp'_noLR s h1
        · simp at h2; rcases h2 with rfl | rfl <;> decide
      · rw [hw1_eq, hu1_eq, heq2]
        simp only [List.cons_append, List.nil_append, List.append_nil, srsEvalInterior]
        have hA := heval_R (p' ++ [.B1, .B0]) (fun s hs => by
          rcases List.mem_append.mp hs with h1 | h2
          · exact hp'_noLR s h1
          · simp at h2; rcases h2 with rfl | rfl <;> decide)
        have hB := heval_R (p' ++ [.T2]) (fun s hs => by
          rcases List.mem_append.mp hs with h1 | h2
          · exact hp'_noLR s h1
          · simp at h2; subst h2; decide)
        have h1 : p' ++ [.B1, .B0, .R] = (p' ++ [.B1, .B0]) ++ [.R] := by simp [List.append_assoc]
        rw [h1, hA, hB]
        exact srsEvalInterior_msb_replace p' [.B1, .B0] [.T2] hp'_noLR rfl
    | _ => rcases hl_right with h | h | h <;> simp at h
  · subst hp_eq; subst hq_eq
    have hp'_noLR : ∀ s, s ∈ p' -> s ≠ .L ∧ s ≠ .R := by
      intro s hs; rw [hu1_eq] at hu1_noLR
      exact hu1_noLR s (List.mem_append_left q' (List.mem_append_left l hs))
    have hq'_noLR : ∀ s, s ∈ q' -> s ≠ .L ∧ s ≠ .R := by
      intro s hs; rw [hu1_eq] at hu1_noLR
      exact hu1_noLR s (List.mem_append_right _ hs)
    rcases interior_step_preserves_eval p' l r q' hrule hp'_noLR hl_noLR hq'_noLR with ⟨hr_noLR, heval_eq⟩
    have hu2_noLR : ∀ s, s ∈ p' ++ r ++ q' -> s ≠ .L ∧ s ≠ .R := by
      intro s hs
      rcases List.mem_append.mp hs with hpr | hq_m
      · rcases List.mem_append.mp hpr with hp_m | hr_m
        · exact hp'_noLR s hp_m
        · exact hr_noLR s hr_m
      · exact hq'_noLR s hq_m
    have heval_R : ∀ z : List MixedSRSSym,
        (∀ s, s ∈ z -> s ≠ .L ∧ s ≠ .R) -> srsEvalInterior (z ++ [.R]) = srsEvalInterior z := by
      intro z hz
      induction z with
      | nil => rfl
      | cons x xs ih =>
        have hx := hz x List.mem_cons_self
        have ih' := ih (fun s hs => hz s (List.mem_cons_of_mem x hs))
        cases x <;> simp at hx <;> simp only [List.cons_append, srsEvalInterior, ih']
    refine ⟨p' ++ r ++ q', by simpa [List.append_assoc] using heq2, hu2_noLR, Or.inl ?_⟩
    rw [hw1_eq, hu1_eq, heq2]
    have ha1 : (.L :: p') ++ r ++ (q' ++ [.R]) = .L :: ((p' ++ r ++ q') ++ [.R]) := by
      simp [List.append_assoc]
    rw [ha1]
    simp only [List.cons_append, List.nil_append, srsEvalInterior]
    rw [heval_R (p' ++ r ++ q') hu2_noLR, heval_R (p' ++ l ++ q') (by rw [← hu1_eq]; exact hu1_noLR)]
    exact heval_eq

theorem mixedSRSReaches_sound {w1 w2 : List MixedSRSSym}
    (hv1 : ValidFramedMixedWord w1) (hreach : MixedSRSReaches w1 w2) :
    ValidFramedMixedWord w2 ∧ ∃ k : Nat, collatzIter k (srsEvalInterior w1) = srsEvalInterior w2 := by
  induction hreach with
  | refl _ => exact ⟨hv1, 0, rfl⟩
  | step hs _ ih =>
    rcases mixedCollatzStep_sound hv1 hs with ⟨u2, hw2_eq, hu2_noLR, heval_step⟩
    have hv2 : ValidFramedMixedWord _ := ⟨u2, hw2_eq, hu2_noLR⟩
    rcases ih hv2 with ⟨hv3, k, hk⟩
    refine ⟨hv3, ?_⟩
    rcases heval_step with hsame | hcstep
    · exact ⟨k, by rw [← hsame]; exact hk⟩
    · refine ⟨k + 1, ?_⟩
      change collatzIter k (collatzStep (srsEvalInterior _)) = _
      rw [← hcstep]
      exact hk

/--
  Theorem T2.1a (Exact Halting Equivalence of the 11-Rule Mixed `(2, 3)` Collatz SRS):
  `CollatzConjectureStandard` holds IF AND ONLY IF every framed binary input
  `[L] ++ encodePosBin n ++ [R]` (`n ≥ 1`) rewrites to `[L, R]` under `MixedSRSReaches`!
-/
theorem collatz_standard_iff_mixed_srs_halting :
    CollatzConjectureStandard ↔
      ∀ n : Nat, n ≥ 1 ->
        MixedSRSReaches ([MixedSRSSym.L] ++ encodePosBin n ++ [MixedSRSSym.R])
          [MixedSRSSym.L, MixedSRSSym.R] := by
  rw [collatz_standard_iff_compressed]
  constructor
  · intro hcomp n hn
    rcases hcomp n (by omega) with ⟨k, hk⟩
    exact collatzIter_eq_one_implies_mixedSRS_halts k n hn hk
  · intro hsrs n hn
    have hreach := hsrs n (by omega)
    rcases encodePosBin_spec n (by omega) with ⟨heval_n, hbin_n⟩
    have hv1 : ValidFramedMixedWord ([.L] ++ encodePosBin n ++ [.R]) := by
      refine ⟨encodePosBin n, rfl, ?_⟩
      intro s hs
      have hb := hbin_n s hs
      cases s <;> simp [isBinaryInteriorSym] at hb <;> decide
    rcases mixedSRSReaches_sound hv1 hreach with ⟨_, k, hk⟩
    have heval_R : ∀ z : List MixedSRSSym,
        (∀ s, s ∈ z -> s ≠ .L ∧ s ≠ .R) -> srsEvalInterior (z ++ [.R]) = srsEvalInterior z := by
      intro z hz
      induction z with
      | nil => rfl
      | cons x xs ih =>
        have hx := hz x List.mem_cons_self
        have ih' := ih (fun s hs => hz s (List.mem_cons_of_mem x hs))
        cases x <;> simp at hx <;> simp only [List.cons_append, srsEvalInterior, ih']
    have hw1_eval : srsEvalInterior ([.L] ++ encodePosBin n ++ [.R]) = n := by
      simp only [List.cons_append, List.nil_append, srsEvalInterior]
      rw [heval_R (encodePosBin n) (by
        intro s hs; have hb := hbin_n s hs; cases s <;> simp [isBinaryInteriorSym] at hb <;> decide)]
      exact heval_n
    have hw2_eval : srsEvalInterior [.L, .R] = 1 := rfl
    rw [hw1_eval, hw2_eval] at hk
    exact ⟨k, hk⟩

/--
  Negative-MSB (`M2 = Z^-`) rewrite rules obtained by flipping ONLY the MSB unit
  `R = +1` to `R = -1` on `R9..R11` while keeping `R1..R8` 100% identical!
-/
inductive MixedSRSNegRule : List MixedSRSSym -> List MixedSRSSym -> Prop where
  | r1_even     : MixedSRSNegRule [.L, .B0] [.L]
  | r2_odd      : MixedSRSNegRule [.L, .B1] [.L, .T2]
  | r3_t0b0     : MixedSRSNegRule [.T0, .B0] [.B0, .T0]
  | r4_t0b1     : MixedSRSNegRule [.T0, .B1] [.B1, .T1]
  | r5_t1b0     : MixedSRSNegRule [.T1, .B0] [.B1, .T0]
  | r6_t1b1     : MixedSRSNegRule [.T1, .B1] [.B0, .T2]
  | r7_t2b0     : MixedSRSNegRule [.T2, .B0] [.B0, .T1]
  | r8_t2b1     : MixedSRSNegRule [.T2, .B1] [.B1, .T2]
  | r9_neg_t0R  : MixedSRSNegRule [.T0, .R] [.B1, .B0, .R]
  | r10_neg_t1R : MixedSRSNegRule [.T1, .R] [.B0, .R]
  | r11_neg_t2R : MixedSRSNegRule [.T2, .R] [.R]

def MixedNegStep (w1 w2 : List MixedSRSSym) : Prop :=
  ∃ p l r q : List MixedSRSSym,
    MixedSRSNegRule l r ∧ w1 = p ++ l ++ q ∧ w2 = p ++ r ++ q

def srsEvalNegInterior : List MixedSRSSym -> Int
  | [] => -1
  | .B0 :: u => 2 * srsEvalNegInterior u
  | .B1 :: u => 2 * srsEvalNegInterior u + 1
  | .T0 :: u => 3 * srsEvalNegInterior u
  | .T1 :: u => 3 * srsEvalNegInterior u + 1
  | .T2 :: u => 3 * srsEvalNegInterior u + 2
  | .L :: u => srsEvalNegInterior u
  | .R :: u => srsEvalNegInterior u

/--
  Theorem T2.1b (`Z^+` vs `M2 = Z^-` Boundary Flip Witness):
  Keeping all 8 left/interior rules `R1..R8` unchanged and flipping ONLY the MSB unit
  `R = +1` to `R = -1` produces an exact 9-step rewrite cycle on `-5 = [L, B1, B1, B0, R]`,
  proving that any termination proof of `MixedCollatzStep` MUST inspect the `R = +1` MSB rules!
-/
theorem mixed_srs_neg_unit_loop_witness :
    let w0 : List MixedSRSSym := [.L, .B1, .B1, .B0, .R]
    srsEvalNegInterior w0 = -5 ∧
    ∃ w1 w2 w3 w4 w5 w6 w7 w8 : List MixedSRSSym,
      MixedNegStep w0 w1 ∧ MixedNegStep w1 w2 ∧ MixedNegStep w2 w3 ∧
      MixedNegStep w3 w4 ∧ MixedNegStep w4 w5 ∧ MixedNegStep w5 w6 ∧
      MixedNegStep w6 w7 ∧ MixedNegStep w7 w8 ∧ MixedNegStep w8 w0 := by
  refine ⟨by decide,
    [.L, .T2, .B1, .B0, .R],
    [.L, .B1, .T2, .B0, .R],
    [.L, .B1, .B0, .T1, .R],
    [.L, .B1, .B0, .B0, .R],
    [.L, .T2, .B0, .B0, .R],
    [.L, .B0, .T1, .B0, .R],
    [.L, .B0, .B1, .T0, .R],
    [.L, .B0, .B1, .B1, .B0, .R], ?_⟩
  refine ⟨⟨[], [.L, .B1], [.L, .T2], [.B1, .B0, .R], .r2_odd, rfl, rfl⟩,
         ⟨[.L], [.T2, .B1], [.B1, .T2], [.B0, .R], .r8_t2b1, rfl, rfl⟩,
         ⟨[.L, .B1], [.T2, .B0], [.B0, .T1], [.R], .r7_t2b0, rfl, rfl⟩,
         ⟨[.L, .B1, .B0], [.T1, .R], [.B0, .R], [], .r10_neg_t1R, rfl, rfl⟩,
         ⟨[], [.L, .B1], [.L, .T2], [.B0, .B0, .R], .r2_odd, rfl, rfl⟩,
         ⟨[.L], [.T2, .B0], [.B0, .T1], [.B0, .R], .r7_t2b0, rfl, rfl⟩,
         ⟨[.L, .B0], [.T1, .B0], [.B1, .T0], [.R], .r5_t1b0, rfl, rfl⟩,
         ⟨[.L, .B0, .B1], [.T0, .R], [.B1, .B0, .R], [], .r9_neg_t0R, rfl, rfl⟩,
         ⟨[], [.L, .B0], [.L], [.B1, .B1, .B0, .R], .r1_even, rfl, rfl⟩⟩

/--
  Theorem T2.1c (Universal 1D Monotone Natural Affine Impossibility on `{R2, R8, R11}`):
  No 1-dimensional monotone natural affine interpretation `f_s(x) = m_s * x + c_s`
  (`m_L, m_B0, m_B1, m_T2 ≥ 1`) can orient `{R2_odd, R8_t2b1, R11_t2R}`!
-/
theorem no_1d_monotone_natural_affine_for_mixed_srs
    (mL _cL _mR cR mB0 cB0 mB1 cB1 mT2 cT2 : Nat)
    (hmL : mL ≥ 1) (hmB0 : mB0 ≥ 1) (hmB1 : mB1 ≥ 1) (hmT2 : mT2 ≥ 1)
    (hR2_slope : mL * mB1 ≥ mL * mT2)
    (hR8_const : cT2 + mT2 * cB1 > cB1 + mB1 * cT2)
    (hR11_const : cT2 + mT2 * cR > cB1 + mB1 * (cB0 + mB0 * cR)) :
    False := by
  have hm_ge : mB1 ≥ mT2 := by
    apply Classical.byContradiction
    intro hlt
    have hm := Nat.mul_lt_mul_of_pos_left (by omega : mB1 < mT2) (by omega : 0 < mL)
    omega
  by_cases hm_eq1 : mT2 = 1
  · subst hm_eq1
    have hm1 := Nat.mul_le_mul_right cT2 hmB1
    rw [Nat.one_mul] at hm1
    omega
  · have hmul_cR : mT2 * cR ≤ mB1 * (cB0 + mB0 * cR) := by
      have hm0 : cR ≤ mB0 * cR := by
        have h1 := Nat.mul_le_mul_right cR hmB0
        simpa using h1
      have h2 : cR ≤ cB0 + mB0 * cR := by omega
      calc
        mT2 * cR ≤ mB1 * cR := Nat.mul_le_mul_right cR hm_ge
        _ ≤ mB1 * (cB0 + mB0 * cR) := Nat.mul_le_mul_left mB1 h2
    have hcT2_gt_cB1 : cT2 > cB1 := by omega
    have hdiff : (mT2 - 1) * cB1 > (mB1 - 1) * cT2 := by
      have e1 : cT2 + (mT2 - 1) * cB1 + cB1 = cT2 + mT2 * cB1 := by
        have h := Nat.sub_mul mT2 1 cB1
        have h1 : 1 * cB1 ≤ mT2 * cB1 := Nat.mul_le_mul_right cB1 (by omega)
        omega
      have e2 : cB1 + (mB1 - 1) * cT2 + cT2 = cB1 + mB1 * cT2 := by
        have h := Nat.sub_mul mB1 1 cT2
        have h1 : 1 * cT2 ≤ mB1 * cT2 := Nat.mul_le_mul_right cT2 (by omega)
        omega
      omega
    have hmono : (mB1 - 1) * cT2 ≥ (mT2 - 1) * cB1 :=
      Nat.mul_le_mul (by omega) (by omega)
    omega

def arcticAdd (a b : Option Nat) : Option Nat :=
  match a, b with
  | some x, some y => some (x + y)
  | _, _ => none

def arcticMax : Option Nat -> Option Nat -> Option Nat
  | none, y => y
  | x, none => x
  | some x, some y => some (max x y)

def arcticDotRow (d : Nat) (row : Fin d -> Option Nat) (vec : Fin d -> Option Nat) :
    Nat -> Option Nat
  | 0 => none
  | k + 1 =>
    let rest := arcticDotRow d row vec k
    if hk : k < d then
      arcticMax rest (arcticAdd (row ⟨k, hk⟩) (vec ⟨k, hk⟩))
    else
      rest

def arcticMatVec (d : Nat) (M : Fin d -> Fin d -> Option Nat) (v : Fin d -> Option Nat) :
    Fin d -> Option Nat :=
  fun i => arcticDotRow d (M i) v d

def arcticEvalWord (d : Nat) (interp : MixedSRSSym -> Fin d -> Fin d -> Option Nat)
    (v0 : Fin d -> Option Nat) : List MixedSRSSym -> Fin d -> Option Nat
  | [] => v0
  | s :: w => arcticMatVec d (interp s) (arcticEvalWord d interp v0 w)

theorem arcticDotRow_bound (d K B : Nat) (row vec : Fin d -> Option Nat)
    (hrow : ∀ j, match row j with | none => True | some x => x ≤ K)
    (hvec : ∀ j, match vec j with | none => True | some y => y ≤ B) :
    ∀ n : Nat, match arcticDotRow d row vec n with | none => True | some z => z ≤ K + B
  | 0 => trivial
  | k + 1 => by
    have ih := arcticDotRow_bound d K B row vec hrow hvec k
    simp only [arcticDotRow]
    by_cases hk : k < d
    · simp only [hk, dite_true]
      have hr := hrow ⟨k, hk⟩
      have hv := hvec ⟨k, hk⟩
      cases h1 : arcticDotRow d row vec k <;>
      cases h2 : row ⟨k, hk⟩ <;>
      cases h3 : vec ⟨k, hk⟩ <;>
      simp [h1] at ih <;> simp [h2] at hr <;> simp [h3] at hv <;>
      simp [arcticAdd, arcticMax] <;> omega
    · simp only [hk, dite_false]
      exact ih

/--
  Universal Linear Height Bound for Any `d`-Dimensional Arctic Matrix Interpretation (`∀ d ≥ 1`):
  Every finite entry of `arcticEvalWord d interp v0 w` is bounded above by `K * (|w| + 1)`.
-/
theorem arcticEvalWord_linear_upper_bound (d K : Nat)
    (interp : MixedSRSSym -> Fin d -> Fin d -> Option Nat)
    (v0 : Fin d -> Option Nat)
    (hM : ∀ s i j, match interp s i j with | none => True | some x => x ≤ K)
    (hv0 : ∀ i, match v0 i with | none => True | some x => x ≤ K) :
    ∀ (w : List MixedSRSSym) (i : Fin d),
      match arcticEvalWord d interp v0 w i with
      | none => True
      | some z => z ≤ K * (w.length + 1)
  | [], i => by
    simp only [arcticEvalWord, List.length_nil, Nat.zero_add, Nat.mul_one]
    exact hv0 i
  | s :: w, i => by
    simp only [arcticEvalWord, arcticMatVec, List.length_cons]
    have hstep := arcticDotRow_bound d K (K * (w.length + 1)) (interp s i)
      (arcticEvalWord d interp v0 w) (hM s i)
      (fun j => arcticEvalWord_linear_upper_bound d K interp v0 hM hv0 w j) d
    cases h : arcticDotRow d (interp s i) (arcticEvalWord d interp v0 w) d with
    | none => trivial
    | some z =>
      rw [h] at hstep
      have hmul : K * (w.length + 1 + 1) = K + K * (w.length + 1) := by
        rw [Nat.mul_add K (w.length + 1) 1, Nat.mul_one]
        omega
      omega

inductive MixedSRSChain : Nat -> List MixedSRSSym -> List MixedSRSSym -> Prop where
  | zero (w : List MixedSRSSym) : MixedSRSChain 0 w w
  | succ {n : Nat} {w1 w2 w3 : List MixedSRSSym} :
      MixedCollatzStep w1 w2 -> MixedSRSChain n w2 w3 -> MixedSRSChain (n + 1) w1 w3

theorem mixedSRSChain_trans {m n : Nat} {w1 w2 w3 : List MixedSRSSym}
    (h1 : MixedSRSChain m w1 w2) (h2 : MixedSRSChain n w2 w3) :
    MixedSRSChain (m + n) w1 w3 := by
  induction h1 with
  | zero _ => simpa using h2
  | succ hs _ ih =>
    rw [Nat.succ_add]
    exact MixedSRSChain.succ hs (ih h2)

theorem replicate_snoc_sym (a : MixedSRSSym) :
    ∀ n : Nat, List.replicate n a ++ [a] = List.replicate (n + 1) a
  | 0 => rfl
  | n + 1 => by
    rw [List.replicate_succ, List.cons_append, replicate_snoc_sym a n]
    rfl

theorem t2_bubble_across_b1 :
    ∀ (k : Nat) (p q : List MixedSRSSym),
      MixedSRSChain k (p ++ [.T2] ++ List.replicate k .B1 ++ q)
        (p ++ List.replicate k .B1 ++ [.T2] ++ q)
  | 0, _, _ => by
    simp only [List.replicate, List.append_nil]
    exact MixedSRSChain.zero _
  | k + 1, p, q => by
    rw [List.replicate_succ]
    have hs1 : MixedCollatzStep (p ++ [.T2] ++ (.B1 :: List.replicate k .B1) ++ q)
        ((p ++ [.B1]) ++ [.T2] ++ List.replicate k .B1 ++ q) := by
      refine ⟨p, [.T2, .B1], [.B1, .T2], List.replicate k .B1 ++ q, .r8_t2b1, ?_, ?_⟩
      · simp [List.append_assoc]
      · simp [List.append_assoc]
    have ih := t2_bubble_across_b1 k (p ++ [.B1]) q
    have heq_end : (p ++ [.B1]) ++ List.replicate k .B1 ++ [.T2] ++ q =
        p ++ (.B1 :: List.replicate k .B1) ++ [.T2] ++ q := by
      simp [List.append_assoc]
    rw [heq_end] at ih
    exact MixedSRSChain.succ hs1 ih

theorem tri_step_identity : ∀ k : Nat, (k * (k + 1)) / 2 + (k + 1) = ((k + 1) * (k + 2)) / 2
  | 0 => rfl
  | k' + 1 => by
    have heven : (k' * (k' + 1)) % 2 = 0 := by
      by_cases h0 : k' % 2 = 0
      · rw [Nat.mul_mod, h0]; simp
      · have h1 : (k' + 1) % 2 = 0 := by omega
        rw [Nat.mul_mod, h1]; simp
    have hq : 2 * ((k' * (k' + 1)) / 2) = k' * (k' + 1) := by omega
    have h2 : ((k' + 1) * (k' + 2)) / 2 = (k' * (k' + 1)) / 2 + (k' + 1) := by
      rw [Nat.mul_add (k' + 1) k' 2, Nat.mul_comm (k' + 1) k', ← hq]
      omega
    have h3 : ((k' + 2) * (k' + 3)) / 2 = ((k' + 1) * (k' + 2)) / 2 + (k' + 2) := by
      have hev2 : ((k' + 1) * (k' + 2)) % 2 = 0 := by
        by_cases h0 : (k' + 1) % 2 = 0
        · rw [Nat.mul_mod, h0]; simp
        · have h1 : (k' + 2) % 2 = 0 := by omega
          rw [Nat.mul_mod, h1]; simp
      have hq2 : 2 * (((k' + 1) * (k' + 2)) / 2) = (k' + 1) * (k' + 2) := by omega
      rw [Nat.mul_add (k' + 2) (k' + 1) 2, Nat.mul_comm (k' + 2) (k' + 1), ← hq2]
      omega
    rw [h3]

/--
  Quadratic Derivation Pumping on `{R2_odd, R8_t2b1}`:
  For every `m : Nat`, `[L] ++ replicate m B1 ++ q` rewrites to `[L] ++ replicate m T2 ++ q`
  in EXACTLY `m * (m + 1) / 2` steps!
-/
theorem mixed_srs_quadratic_derivation_exists :
    ∀ (m : Nat) (q : List MixedSRSSym),
      MixedSRSChain ((m * (m + 1)) / 2)
        ([.L] ++ List.replicate m .B1 ++ q)
        ([.L] ++ List.replicate m .T2 ++ q)
  | 0, _ => by
    simp only [Nat.zero_mul, Nat.zero_div, List.replicate, List.append_nil]
    exact MixedSRSChain.zero _
  | m + 1, q => by
    rw [List.replicate_succ]
    have hs_r2 : MixedCollatzStep ([.L] ++ (.B1 :: List.replicate m .B1) ++ q)
        ([.L] ++ [.T2] ++ List.replicate m .B1 ++ q) :=
      ⟨[], [.L, .B1], [.L, .T2], List.replicate m .B1 ++ q, .r2_odd, rfl, rfl⟩
    have hbub := t2_bubble_across_b1 m [.L] q
    have hbub' : MixedSRSChain m ([.L] ++ [.T2] ++ List.replicate m .B1 ++ q)
        ([.L] ++ List.replicate m .B1 ++ ([.T2] ++ q)) := by
      simpa [List.append_assoc] using hbub
    have hchain1 : MixedSRSChain (m + 1) ([.L] ++ (.B1 :: List.replicate m .B1) ++ q)
        ([.L] ++ List.replicate m .B1 ++ ([.T2] ++ q)) :=
      MixedSRSChain.succ hs_r2 hbub'
    have ih := mixed_srs_quadratic_derivation_exists m ([.T2] ++ q)
    have htot := mixedSRSChain_trans hchain1 ih
    have hlen_eq : (m + 1) + (m * (m + 1)) / 2 = ((m + 1) * (m + 1 + 1)) / 2 := by
      rw [Nat.add_comm]; exact tri_step_identity m
    have hend_eq : [.L] ++ List.replicate m .T2 ++ ([.T2] ++ q) =
        [.L] ++ List.replicate (m + 1) .T2 ++ q := by
      rw [← replicate_snoc_sym .T2 m]
      simp [List.append_assoc]
    rw [hlen_eq, hend_eq] at htot
    exact htot

theorem arctic_chain_strict_decrease (d : Nat) (hd : 0 < d)
    (interp : MixedSRSSym -> Fin d -> Fin d -> Option Nat)
    (v0 : Fin d -> Option Nat)
    (hStepDec : ∀ u v : List MixedSRSSym, MixedCollatzStep u v ->
      ∃ zu zv : Nat,
        arcticEvalWord d interp v0 u ⟨0, hd⟩ = some zu ∧
        arcticEvalWord d interp v0 v ⟨0, hd⟩ = some zv ∧ zv < zu) :
    ∀ {n : Nat} {u v : List MixedSRSSym},
      n ≥ 1 -> MixedSRSChain n u v ->
      ∃ zu zv : Nat,
        arcticEvalWord d interp v0 u ⟨0, hd⟩ = some zu ∧
        arcticEvalWord d interp v0 v ⟨0, hd⟩ = some zv ∧ zv + n ≤ zu := by
  intro n u v hn hchain
  induction hchain with
  | zero _ => omega
  | @succ m w1 w2 _ hs hrest ih =>
    rcases hStepDec w1 w2 hs with ⟨z1, z2, hz1, hz2, hlt12⟩
    cases m with
    | zero =>
      cases hrest with
      | zero _ => exact ⟨z1, z2, hz1, hz2, by omega⟩
    | succ _ =>
      rcases ih (by omega) with ⟨z2', z3, hz2', hz3, hle23⟩
      rw [hz2] at hz2'
      injection hz2' with heq2
      subst heq2
      exact ⟨z1, z3, hz1, hz3, by omega⟩

/--
  Theorem T2.1d (Universal All-Dimension `∀ d ≥ 1` Arctic Matrix Impossibility):
  No nonnegative Arctic Matrix Interpretation of ANY dimension `d ≥ 1` and ANY max entry `K`
  can orient `MixedCollatzStep`, because `{R2_odd, R8_t2b1}` exhibits quadratic derivation
  height `m * (m + 1) / 2` on `[L] ++ replicate m B1 ++ [R]`!
-/
theorem no_arctic_matrix_interp_any_dim_for_mixed_srs (d K : Nat) (hd : 0 < d)
    (interp : MixedSRSSym -> Fin d -> Fin d -> Option Nat)
    (v0 : Fin d -> Option Nat)
    (hM : ∀ s i j, match interp s i j with | none => True | some x => x ≤ K)
    (hv0 : ∀ i, match v0 i with | none => True | some x => x ≤ K)
    (hStepDec : ∀ u v : List MixedSRSSym, MixedCollatzStep u v ->
      ∃ zu zv : Nat,
        arcticEvalWord d interp v0 u ⟨0, hd⟩ = some zu ∧
        arcticEvalWord d interp v0 v ⟨0, hd⟩ = some zv ∧ zv < zu) :
    False := by
  let m := 2 * K + 4
  let wStart := [MixedSRSSym.L] ++ List.replicate m .B1 ++ [.R]
  let wEnd := [MixedSRSSym.L] ++ List.replicate m .T2 ++ [.R]
  let N := (m * (m + 1)) / 2
  have hN_val : N = (K + 2) * (2 * K + 5) := by
    dsimp [N, m]
    have hmul : (2 * K + 4) * (2 * K + 4 + 1) = 2 * ((K + 2) * (2 * K + 5)) := by
      have : 2 * K + 4 = 2 * (K + 2) := by omega
      rw [this, show 2 * (K + 2) + 1 = 2 * K + 5 by omega, Nat.mul_assoc]
    rw [hmul, Nat.mul_div_right _ (by decide)]
  have hN_pos : N ≥ 1 := by
    rw [hN_val]
    have := Nat.mul_le_mul (by omega : 2 ≤ K + 2) (by omega : 5 ≤ 2 * K + 5)
    omega
  have hchain : MixedSRSChain N wStart wEnd := mixed_srs_quadratic_derivation_exists m [.R]
  rcases arctic_chain_strict_decrease d hd interp v0 hStepDec hN_pos hchain with
    ⟨zu, _, hzu, _, hdec⟩
  have hub := arcticEvalWord_linear_upper_bound d K interp v0 hM hv0 wStart ⟨0, hd⟩
  rw [hzu] at hub
  have hlen : wStart.length = 2 * K + 6 := by
    dsimp [wStart, m]; simp [List.length_replicate]
  rw [hlen] at hub
  have hquad : (K + 2) * (2 * K + 5) = 2 * (K * K) + 9 * K + 10 := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
    have hkk : K * (2 * K) = 2 * (K * K) := by
      rw [← Nat.mul_assoc, Nat.mul_comm K 2, Nat.mul_assoc]
    rw [hkk]
    omega
  have hlin : K * (2 * K + 6 + 1) = 2 * (K * K) + 7 * K := by
    rw [show 2 * K + 6 + 1 = 2 * K + 7 by omega, Nat.mul_add,
        ← Nat.mul_assoc K 2 K, Nat.mul_comm K 2, Nat.mul_assoc, Nat.mul_comm K 7]
  rw [hN_val, hquad] at hdec
  rw [hlin] at hub
  omega

/--
  2D Upper-Triangular Natural Matrix Interpretation `M = [[m, p], [0, n]], v = [c, d] ∈ Nat^2`.
-/
structure UpperTri2D where
  m : Nat
  p : Nat
  n : Nat
  c : Nat
  d : Nat
  deriving DecidableEq, Repr

def compUpperTri2D (A B : UpperTri2D) : UpperTri2D :=
  { m := A.m * B.m
    p := A.m * B.p + A.p * B.n
    n := A.n * B.n
    c := A.m * B.c + A.p * B.d + A.c
    d := A.n * B.d + A.d }

def evalWordUpperTri2D (interp : MixedSRSSym -> UpperTri2D) : List MixedSRSSym -> UpperTri2D
  | [] => { m := 1, p := 0, n := 1, c := 0, d := 0 }
  | s :: w => compUpperTri2D (interp s) (evalWordUpperTri2D interp w)

def orientsUpperTri2D (lhs rhs : UpperTri2D) : Prop :=
  lhs.m ≥ rhs.m ∧ lhs.p ≥ rhs.p ∧ lhs.n ≥ rhs.n ∧ lhs.c > rhs.c ∧ lhs.d ≥ rhs.d

def core3UpperTri2DCert : MixedSRSSym -> UpperTri2D
  | .L  => { m := 1, p := 0, n := 0, c := 0, d := 0 }
  | .R  => { m := 1, p := 0, n := 1, c := 0, d := 5 }
  | .B0 => { m := 1, p := 0, n := 0, c := 0, d := 0 }
  | .B1 => { m := 2, p := 1, n := 2, c := 2, d := 1 }
  | .T0 => { m := 2, p := 1, n := 1, c := 1, d := 0 }
  | .T1 => { m := 2, p := 1, n := 1, c := 1, d := 0 }
  | .T2 => { m := 2, p := 1, n := 1, c := 1, d := 0 }

/--
  Theorem T2.4a (Sharpness Certificate on `{R2_odd, R8_t2b1, R11_t2R}`):
  Although `{R2, R8, R11}` defeats ALL `d = 1` monotone natural affine interpretations (`T2.1c`),
  it IS oriented by an explicit `d = 2` upper-triangular Natural Matrix Interpretation
  (`m_B1 = m_T2 = 2 > 1`)!
-/
theorem core3_admits_2d_upper_triangular_natural_cert :
    (∀ s : MixedSRSSym, (core3UpperTri2DCert s).m ≥ 1) ∧
    (core3UpperTri2DCert .B1).m = 2 ∧
    orientsUpperTri2D (evalWordUpperTri2D core3UpperTri2DCert [.L, .B1])
      (evalWordUpperTri2D core3UpperTri2DCert [.L, .T2]) ∧
    orientsUpperTri2D (evalWordUpperTri2D core3UpperTri2DCert [.T2, .B1])
      (evalWordUpperTri2D core3UpperTri2DCert [.B1, .T2]) ∧
    orientsUpperTri2D (evalWordUpperTri2D core3UpperTri2DCert [.T2, .R])
      (evalWordUpperTri2D core3UpperTri2DCert [.B1, .B0, .R]) := by
  refine ⟨?_, rfl, ?_, ?_, ?_⟩
  · intro s; cases s <;> decide
  · unfold orientsUpperTri2D; decide
  · unfold orientsUpperTri2D; decide
  · unfold orientsUpperTri2D; decide

/--
  Theorem T2.4b (All-Dimension `∀ d ≥ 1` Upper-Triangular Top-Left Unit Collapse):
  In EVERY dimension `d ≥ 1`, because upper-triangular matrix multiplication multiplies `(0,0)`
  entries `(A * B)_{0,0} = A_{0,0} * B_{0,0}`, orienting `{R2, R5, R7, R9, R11}` with `m_s ≥ 1`
  collapses all 5 interior top-left entries to `m_B0 = m_B1 = m_T0 = m_T1 = m_T2 = 1`!
-/
theorem upper_triangular_top_left_unit_collapse_any_dim
    (mL mR mB0 mB1 mT0 mT1 mT2 : Nat)
    (hmL : mL ≥ 1) (hmR : mR ≥ 1)
    (_hmB0 : mB0 ≥ 1) (_hmB1 : mB1 ≥ 1)
    (_hmT0 : mT0 ≥ 1) (_hmT1 : mT1 ≥ 1) (_hmT2 : mT2 ≥ 1)
    (hR2 : mL * mB1 ≥ mL * mT2)
    (hR5 : mT1 * mB0 ≥ mB1 * mT0)
    (hR7 : mT2 * mB0 ≥ mB0 * mT1)
    (hR9 : mT0 * mR ≥ mB1 * mR)
    (hR11 : mT2 * mR ≥ mB1 * mB0 * mR) :
    mB0 = 1 ∧ mB1 = 1 ∧ mT0 = 1 ∧ mT1 = 1 ∧ mT2 = 1 := by
  have hB1_ge_T2 : mB1 ≥ mT2 := by
    apply Classical.byContradiction; intro h
    have := Nat.mul_lt_mul_of_pos_left (by omega : mB1 < mT2) (by omega : 0 < mL); omega
  have hT2_ge_B1B0 : mT2 ≥ mB1 * mB0 := by
    apply Classical.byContradiction; intro h
    have := Nat.mul_lt_mul_of_pos_right (by omega : mT2 < mB1 * mB0) (by omega : 0 < mR); omega
  have hB0_eq1 : mB0 = 1 := by
    by_cases h1 : mB0 = 1
    · exact h1
    · have hm2 : mB1 * mB0 ≥ mB1 * 2 := Nat.mul_le_mul_left mB1 (by omega)
      omega
  subst hB0_eq1
  rw [Nat.mul_one] at hT2_ge_B1B0 hR5 hR7
  rw [Nat.one_mul] at hR7
  have hT0_ge_B1 : mT0 ≥ mB1 := by
    apply Classical.byContradiction; intro h
    have := Nat.mul_lt_mul_of_pos_right (by omega : mT0 < mB1) (by omega : 0 < mR); omega
  have hB1_ge_sq : mB1 ≥ mB1 * mB1 := by
    have hsq : mB1 * mB1 ≤ mB1 * mT0 := Nat.mul_le_mul_left mB1 hT0_ge_B1
    omega
  have hB1_eq1 : mB1 = 1 := by
    by_cases h1 : mB1 = 1
    · exact h1
    · have hm2 : mB1 * mB1 ≥ mB1 * 2 := Nat.mul_le_mul_left mB1 (by omega)
      omega
  subst hB1_eq1
  omega

theorem upper_tri_comm_positivity (pX nX cX dX pY nY cY dY : Nat)
    (hp : pY + pX * nY ≥ pX + pY * nX)
    (hc : dY * pX + cY + cX > dX * pY + cX + cY)
    (hd : nX * dY + dX ≥ nY * dX + dY) :
    pX ≥ 1 ∧ dY ≥ 1 ∧ nX ≥ 1 ∧ nY ≥ 1 := by
  have hpX_dY : dY * pX > 0 := by omega
  have hpX_pos : pX ≥ 1 := by
    by_cases h0 : pX = 0
    · rw [h0, Nat.mul_zero] at hpX_dY; omega
    · omega
  have hdY_pos : dY ≥ 1 := by
    by_cases h0 : dY = 0
    · rw [h0, Nat.zero_mul] at hpX_dY; omega
    · omega
  have hnX_pos : nX ≥ 1 := by
    by_cases h0 : nX = 0
    · subst h0
      simp only [Nat.zero_mul, Nat.mul_zero, Nat.zero_add, Nat.add_zero] at hp hd
      have hnY_0 : nY = 0 := by
        by_cases hy0 : nY = 0
        · exact hy0
        · have hm : nY * dX ≥ 1 * dX := Nat.mul_le_mul_right dX (by omega)
          omega
      subst hnY_0
      simp only [Nat.zero_mul, Nat.mul_zero, Nat.zero_add, Nat.add_zero] at hp hd
      have hmul : dX * pY ≥ dY * pX := Nat.mul_le_mul hd hp
      omega
    · omega
  have hnY_pos : nY ≥ 1 := by
    by_cases h0 : nY = 0
    · subst h0
      simp only [Nat.mul_zero, Nat.add_zero] at hp
      have hm : pY * nX ≥ pY * 1 := Nat.mul_le_mul_left pY hnX_pos
      omega
    · omega
  exact ⟨hpX_pos, hdY_pos, hnX_pos, hnY_pos⟩

theorem upper_tri_2d_trichotomy_contradiction
    (mL pL dR pB1 dB0 dB1 pT2 dT2 nT nB : Nat)
    (hmL : mL ≥ 1) (_hpT2 : pT2 ≥ 1) (hdB0 : dB0 ≥ 1) (_hnT : nT ≥ 1) (hnB : nB ≥ 1)
    (hR2_p : mL * pB1 + pL * nB ≥ mL * pT2 + pL * nT)
    (hR8_p : pB1 + pT2 * nB ≥ pT2 + pB1 * nT)
    (hR8_c : pT2 * dB1 > pB1 * dT2)
    (hR8_d : nT * dB1 + dT2 ≥ nB * dT2 + dB1)
    (hR11_d : nT * dR + dT2 ≥ nB * (nB * dR + dB0) + dB1) :
    False := by
  have hdB1_pos : dB1 ≥ 1 := by
    by_cases h0 : dB1 = 0
    · rw [h0, Nat.mul_zero] at hR8_c; omega
    · omega
  by_cases hgt : nT > nB
  · have hpL_le : pL * nB ≤ pL * nT := Nat.mul_le_mul_left pL (by omega)
    have hmL_p : mL * pB1 ≥ mL * pT2 := by omega
    have hpB1_ge : pB1 ≥ pT2 := by
      apply Classical.byContradiction; intro h
      have := Nat.mul_lt_mul_of_pos_left (by omega : pB1 < pT2) (by omega : 0 < mL); omega
    have hm1 : pB1 * nT ≥ pB1 * (nB + 1) := Nat.mul_le_mul_left pB1 (by omega)
    rw [Nat.mul_add, Nat.mul_one] at hm1
    have hm2 : pB1 * nB ≥ pT2 * nB := Nat.mul_le_mul_right nB hpB1_ge
    omega
  · by_cases hlt : nT < nB
    · have hnB_sq_ge : nB * (nB * dR + dB0) ≥ nT * dR + nB * dB0 := by
        rw [Nat.mul_add, ← Nat.mul_assoc]
        have hsq : nB * nB ≥ nT := by
          have h1 : nB * nB ≥ nB * 1 := Nat.mul_le_mul_left nB (by omega)
          omega
        have hdR_le : nT * dR ≤ (nB * nB) * dR := Nat.mul_le_mul_right dR hsq
        omega
      have hnBdB0_pos : nB * dB0 ≥ 1 := Nat.mul_le_mul hnB hdB0
      have hm1 : nB * dT2 ≥ (nT + 1) * dT2 := Nat.mul_le_mul_right dT2 (by omega)
      rw [Nat.add_mul, Nat.one_mul] at hm1
      have hm2 : nT * dT2 ≥ nT * dB1 := Nat.mul_le_mul_left nT (by omega)
      omega
    · have heq_n : nT = nB := by omega
      rw [heq_n] at hR2_p hR8_p hR8_d hR11_d
      have hmL_p : mL * pB1 ≥ mL * pT2 := by omega
      have hpB1_ge : pB1 ≥ pT2 := by
        apply Classical.byContradiction; intro h
        have := Nat.mul_lt_mul_of_pos_left (by omega : pB1 < pT2) (by omega : 0 < mL); omega
      have hdB1_gt_dT2 : dB1 > dT2 := by
        apply Classical.byContradiction; intro hle
        have hm : pB1 * dT2 ≥ pT2 * dB1 := Nat.mul_le_mul hpB1_ge (by omega)
        omega
      have hnB_sq : nB * (nB * dR + dB0) ≥ nB * dR + nB * dB0 := by
        rw [Nat.mul_add, ← Nat.mul_assoc]
        have hsq : nB * nB ≥ nB := by
          have h1 : nB * nB ≥ nB * 1 := Nat.mul_le_mul_left nB (by omega)
          omega
        have hdR_le : nB * dR ≤ (nB * nB) * dR := Nat.mul_le_mul_right dR hsq
        omega
      have hnBdB0_pos : nB * dB0 ≥ 1 := Nat.mul_le_mul hnB hdB0
      omega

/--
  Theorem T2.4c (Complete Entry-Unbounded `d = 2` Upper-Triangular Natural Matrix Impossibility):
  Over ALL `Nat` entries `M_s = [[m_s, p_s], [0, n_s]]` (`m_s ≥ 1`, zero cap on any entry)
  and `v_s = [c_s, d_s] ∈ Nat^2`, NO `d = 2` upper-triangular Natural Matrix Interpretation
  can orient the 9-rule subsystem `{R2, R3, R4, R5, R6, R7, R8, R9, R11}` (hence none orients
  `R \ {R1_even}` or the full 11-rule Collatz SRS)!
-/
theorem no_2d_upper_triangular_natural_matrix_for_mixed_srs
    (interp : MixedSRSSym -> UpperTri2D)
    (hm_pos : ∀ s : MixedSRSSym, (interp s).m ≥ 1)
    (hR2  : orientsUpperTri2D (evalWordUpperTri2D interp [.L, .B1]) (evalWordUpperTri2D interp [.L, .T2]))
    (hR3  : orientsUpperTri2D (evalWordUpperTri2D interp [.T0, .B0]) (evalWordUpperTri2D interp [.B0, .T0]))
    (hR4  : orientsUpperTri2D (evalWordUpperTri2D interp [.T0, .B1]) (evalWordUpperTri2D interp [.B1, .T1]))
    (hR5  : orientsUpperTri2D (evalWordUpperTri2D interp [.T1, .B0]) (evalWordUpperTri2D interp [.B1, .T0]))
    (hR6  : orientsUpperTri2D (evalWordUpperTri2D interp [.T1, .B1]) (evalWordUpperTri2D interp [.B0, .T2]))
    (hR7  : orientsUpperTri2D (evalWordUpperTri2D interp [.T2, .B0]) (evalWordUpperTri2D interp [.B0, .T1]))
    (hR8  : orientsUpperTri2D (evalWordUpperTri2D interp [.T2, .B1]) (evalWordUpperTri2D interp [.B1, .T2]))
    (hR9  : orientsUpperTri2D (evalWordUpperTri2D interp [.T0, .R])  (evalWordUpperTri2D interp [.B1, .R]))
    (hR11 : orientsUpperTri2D (evalWordUpperTri2D interp [.T2, .R])  (evalWordUpperTri2D interp [.B1, .B0, .R])) :
    False := by
  simp only [orientsUpperTri2D, evalWordUpperTri2D, compUpperTri2D,
             Nat.mul_one, Nat.mul_zero, Nat.add_zero, Nat.zero_add]
    at hR2 hR3 hR4 hR5 hR6 hR7 hR8 hR9 hR11
  have hunit := upper_triangular_top_left_unit_collapse_any_dim
    (interp .L).m (interp .R).m (interp .B0).m (interp .B1).m
    (interp .T0).m (interp .T1).m (interp .T2).m
    (hm_pos .L) (hm_pos .R) (hm_pos .B0) (hm_pos .B1)
    (hm_pos .T0) (hm_pos .T1) (hm_pos .T2)
    hR2.1 hR5.1 hR7.1 hR9.1
    (by rw [Nat.mul_assoc]; exact hR11.1)
  rcases hunit with ⟨hmB0, hmB1, hmT0, hmT1, hmT2⟩
  simp only [hmB0, hmB1, hmT0, hmT1, hmT2, Nat.one_mul, Nat.mul_one]
    at hR2 hR3 hR4 hR5 hR6 hR7 hR8 hR9 hR11
  rcases upper_tri_comm_positivity
    (interp .T0).p (interp .T0).n (interp .T0).c (interp .T0).d
    (interp .B0).p (interp .B0).n (interp .B0).c (interp .B0).d
    (by omega) (by rw [Nat.mul_comm (interp .B0).d, Nat.mul_comm (interp .T0).d]; omega) (by omega)
    with ⟨_, hdB0_pos, hnT0_pos, hnB0_pos⟩
  rcases upper_tri_comm_positivity
    (interp .T2).p (interp .T2).n (interp .T2).c (interp .T2).d
    (interp .B1).p (interp .B1).n (interp .B1).c (interp .B1).d
    (by omega) (by rw [Nat.mul_comm (interp .B1).d, Nat.mul_comm (interp .T2).d]; omega) (by omega)
    with ⟨hpT2_pos, _, _, hnB1_pos⟩
  have hn_R4 : (interp .T0).n * (interp .B1).n ≥ (interp .B1).n * (interp .T1).n := hR4.2.2.1
  have hn_R5 : (interp .T1).n * (interp .B0).n ≥ (interp .B1).n * (interp .T0).n := hR5.2.2.1
  have hn_R6 : (interp .T1).n * (interp .B1).n ≥ (interp .B0).n * (interp .T2).n := hR6.2.2.1
  have hn_R7 : (interp .T2).n * (interp .B0).n ≥ (interp .B0).n * (interp .T1).n := hR7.2.2.1
  have hnT0_ge_T1 : (interp .T0).n ≥ (interp .T1).n := by
    apply Classical.byContradiction; intro h
    have hm := Nat.mul_lt_mul_of_pos_right (by omega : (interp .T0).n < (interp .T1).n) (by omega : 0 < (interp .B1).n)
    rw [Nat.mul_comm (interp .T1).n (interp .B1).n] at hm; omega
  have hnT2_ge_T1 : (interp .T2).n ≥ (interp .T1).n := by
    apply Classical.byContradiction; intro h
    have hm := Nat.mul_lt_mul_of_pos_left (by omega : (interp .T2).n < (interp .T1).n) (by omega : 0 < (interp .B0).n)
    rw [Nat.mul_comm (interp .B0).n (interp .T2).n] at hm; omega
  have hprod_R56 : ((interp .T1).n * (interp .T1).n) * ((interp .B0).n * (interp .B1).n) ≥
      ((interp .T0).n * (interp .T2).n) * ((interp .B0).n * (interp .B1).n) := by
    have hm := Nat.mul_le_mul hn_R5 hn_R6
    have hl : ((interp .T1).n * (interp .B0).n) * ((interp .T1).n * (interp .B1).n) =
        ((interp .T1).n * (interp .T1).n) * ((interp .B0).n * (interp .B1).n) := by
      rw [Nat.mul_assoc, ← Nat.mul_assoc (interp .B0).n, Nat.mul_comm (interp .B0).n (interp .T1).n,
          Nat.mul_assoc (interp .T1).n, ← Nat.mul_assoc]
    have hr : ((interp .B1).n * (interp .T0).n) * ((interp .B0).n * (interp .T2).n) =
        ((interp .T0).n * (interp .T2).n) * ((interp .B0).n * (interp .B1).n) := by
      rw [Nat.mul_comm (interp .B1).n (interp .T0).n, Nat.mul_assoc (interp .T0).n,
          ← Nat.mul_assoc (interp .B1).n, Nat.mul_comm (interp .B1).n (interp .B0).n,
          Nat.mul_comm ((interp .B0).n * (interp .B1).n) (interp .T2).n,
          ← Nat.mul_assoc]
    rw [hl, hr] at hm
    exact hm
  have hB0B1_pos : 0 < (interp .B0).n * (interp .B1).n := Nat.mul_pos hnB0_pos hnB1_pos
  have hT1sq_ge : (interp .T1).n * (interp .T1).n ≥ (interp .T0).n * (interp .T2).n := by
    apply Classical.byContradiction; intro h
    have := Nat.mul_lt_mul_of_pos_right (by omega : (interp .T1).n * (interp .T1).n < (interp .T0).n * (interp .T2).n) hB0B1_pos
    omega
  have hnT1_pos : (interp .T1).n ≥ 1 := by
    by_cases h0 : (interp .T1).n = 0
    · rw [h0, Nat.zero_mul] at hn_R5
      have := Nat.mul_pos hnB1_pos hnT0_pos; omega
    · omega
  have hnT_all_eq : (interp .T0).n = (interp .T1).n ∧ (interp .T2).n = (interp .T1).n := by
    refine ⟨?_, ?_⟩
    · apply Classical.byContradiction; intro hne
      have hm1 : (interp .T0).n * (interp .T2).n ≥ ((interp .T1).n + 1) * (interp .T1).n :=
        Nat.mul_le_mul (by omega) hnT2_ge_T1
      rw [Nat.add_mul, Nat.one_mul] at hm1; omega
    · apply Classical.byContradiction; intro hne
      have hm1 : (interp .T0).n * (interp .T2).n ≥ (interp .T1).n * ((interp .T1).n + 1) :=
        Nat.mul_le_mul hnT0_ge_T1 (by omega)
      rw [Nat.mul_add, Nat.mul_one] at hm1; omega
  rcases hnT_all_eq with ⟨hT0_eq, hT2_eq⟩
  rw [hT0_eq] at hn_R5
  rw [hT2_eq] at hn_R6
  have hnB_eq : (interp .B0).n = (interp .B1).n := by
    have h1 : (interp .B0).n ≥ (interp .B1).n := by
      apply Classical.byContradiction; intro h
      have hm := Nat.mul_lt_mul_of_pos_left (by omega : (interp .B0).n < (interp .B1).n) (by omega : 0 < (interp .T1).n)
      rw [Nat.mul_comm (interp .T1).n (interp .B1).n] at hm; omega
    have h2 : (interp .B1).n ≥ (interp .B0).n := by
      apply Classical.byContradiction; intro h
      have hm := Nat.mul_lt_mul_of_pos_left (by omega : (interp .B1).n < (interp .B0).n) (by omega : 0 < (interp .T1).n)
      rw [Nat.mul_comm (interp .T1).n (interp .B0).n] at hm; omega
    omega
  exact upper_tri_2d_trichotomy_contradiction
    (interp .L).m (interp .L).p (interp .R).d
    (interp .B1).p (interp .B0).d (interp .B1).d
    (interp .T2).p (interp .T2).d (interp .T1).n (interp .B1).n
    (hm_pos .L) hpT2_pos hdB0_pos hnT1_pos hnB1_pos
    (by rw [hT2_eq] at hR2; exact hR2.2.1)
    (by rw [hT2_eq] at hR8; exact hR8.2.1)
    (by have h8c := hR8.2.2.2.1; omega)
    (by rw [hT2_eq] at hR8; exact hR8.2.2.2.2)
    (by rw [hT2_eq, hnB_eq] at hR11; exact hR11.2.2.2.2)

-- ----------------------------------------------------------------------------
-- SECTION 5B: All-Weight 2^w1-Cancellation Sieve, Multi-Block Mod-373248 Sieve,
--             Cross-Track Quotient Equivalences, & Self-Congruent CRT Pumping
--             (Track 2 Theorems T2.2, T2.3, T2.5, & T2.6)
-- ----------------------------------------------------------------------------

theorem pow_pos_base (b : Nat) (hb : b > 0) : ∀ k : Nat, b ^ k ≥ 1
  | 0 => Nat.le_refl 1
  | k + 1 => by
    rw [Nat.pow_succ]
    have hm := Nat.mul_le_mul (pow_pos_base b hb k) hb
    omega

theorem pow3_odd_nat (k : Nat) : 3 ^ k % 2 = 1 := by
  induction k with
  | zero => rfl
  | succ m ih => rw [Nat.pow_succ]; omega

theorem collatzStep_of_even_nat (n : Nat) (h : n % 2 = 0) :
    collatzStep n = n / 2 := by
  unfold collatzStep; simp [h]

theorem collatzStep_of_odd_nat (n : Nat) (h : n % 2 = 1) :
    collatzStep n = (3 * n + 1) / 2 := by
  unfold collatzStep
  have hb : (n % 2 == 0) = false := decide_eq_false (by omega)
  rw [hb]; rfl

theorem collatzIter_one_in_one_two : ∀ d : Nat,
    0 < collatzIter d 1 ∧ collatzIter d 1 ≤ 2
  | 0 => by decide
  | 1 => by decide
  | d + 2 => by
    have h2 : collatzIter (d + 2) 1 = collatzIter d 1 := by
      have ha := collatzIter_add 2 d 1
      have h12 : collatzIter 2 1 = 1 := rfl
      rw [h12] at ha
      simpa [Nat.add_comm] using ha
    rw [h2]; exact collatzIter_one_in_one_two d

theorem minimal_counterexample_no_coalescence
    (nMin nPrime K1 K2 : Nat)
    (hnMin : nMin > 1)
    (hnoDesc : ∀ k : Nat, ¬ (0 < collatzIter k nMin ∧ collatzIter k nMin < nMin))
    (hminReach : ∀ m : Nat, 1 ≤ m -> m < nMin -> ∃ k1 : Nat, collatzIter k1 m = 1)
    (hp_lo : 1 ≤ nPrime) (hp_hi : nPrime < nMin)
    (hcoal : collatzIter K1 nPrime = collatzIter K2 nMin) :
    False := by
  have hn_ge3 : nMin ≥ 3 := by
    by_cases h2 : nMin = 2
    · subst h2; exact False.elim (hnoDesc 1 ⟨by decide, by decide⟩)
    · omega
  rcases hminReach nPrime hp_lo hp_hi with ⟨k1, hk1⟩
  by_cases hle : K1 ≤ k1
  · have hsplit : k1 = K1 + (k1 - K1) := by omega
    have h1 : collatzIter (K2 + (k1 - K1)) nMin = 1 := by
      rw [collatzIter_add, ← hcoal, ← collatzIter_add, ← hsplit, hk1]
    exact hnoDesc (K2 + (k1 - K1)) ⟨by omega, by omega⟩
  · have hsplit : K1 = k1 + (K1 - k1) := by omega
    have h1 : collatzIter K2 nMin = collatzIter (K1 - k1) 1 := by
      rw [← hcoal]; conv => lhs; rw [hsplit]
      rw [collatzIter_add, hk1]
    rcases collatzIter_one_in_one_two (K1 - k1) with ⟨_, _⟩
    exact hnoDesc K2 ⟨by omega, by omega⟩

theorem minimal_counterexample_k0_backward_exclusion
    (nMin nPrime : Nat) (u : List Bool)
    (hnMin : nMin > 1)
    (hnoDesc : ∀ k : Nat, ¬ (0 < collatzIter k nMin ∧ collatzIter k nMin < nMin))
    (hminReach : ∀ m : Nat, 1 ≤ m -> m < nMin -> ∃ k1 : Nat, collatzIter k1 m = 1)
    (hp_lo : 1 ≤ nPrime) (hp_hi : nPrime < nMin)
    (heq : 2 ^ u.length * nMin = 3 ^ parityWeight u * nPrime + affineCarry u) :
    False := by
  have hcast : (2 : Int) ^ u.length * (nMin : Int) =
      (3 : Int) ^ parityWeight u * (nPrime : Int) + affineCarryInt u := by
    have hc := congrArg (fun t : Nat => (t : Int)) heq
    rw [natCast_mul, natCast_pow2, natCast_add, natCast_mul, natCast_pow3,
        ← affineCarryInt_ofNat] at hc
    exact hc
  rcases general_affine_converse_universal u (nPrime : Int) (nMin : Int) hcast with ⟨_, hiter_int⟩
  have hiter_nat : collatzIter u.length nPrime = collatzIter 0 nMin := by
    rw [collatzIterInt_ofNat] at hiter_int
    simp only [collatzIter]; omega
  exact minimal_counterexample_no_coalescence nMin nPrime u.length 0
    hnMin hnoDesc hminReach hp_lo hp_hi hiter_nat

def affineStepSlope : Nat -> Nat -> Nat
  | 0, _ => 1
  | k + 1, r =>
    let s := affineStepSlope k r
    if (collatzIter k r) % 2 == 0 then s else 3 * s

theorem collatzIter_mod_pow2_universal :
    ∀ (k r q : Nat),
      collatzIter k (2 ^ k * q + r) = affineStepSlope k r * q + collatzIter k r
  | 0, r, q => by simp [collatzIter, affineStepSlope]
  | k + 1, r, q => by
    have hpow : 2 ^ (k + 1) * q = 2 ^ k * (2 * q) := by rw [Nat.pow_succ, Nat.mul_assoc]
    have hstep_lhs : collatzIter (k + 1) (2 ^ (k + 1) * q + r) =
        collatzStep (collatzIter k (2 ^ (k + 1) * q + r)) := by
      simpa [collatzIter] using collatzIter_add k 1 (2 ^ (k + 1) * q + r)
    have hstep_rhs : collatzIter (k + 1) r = collatzStep (collatzIter k r) := by
      simpa [collatzIter] using collatzIter_add k 1 r
    have ih := collatzIter_mod_pow2_universal k r (2 * q)
    rw [hstep_lhs, hpow, ih, hstep_rhs]
    let s := affineStepSlope k r
    have hs2 : s * (2 * q) = 2 * (s * q) := by rw [← Nat.mul_assoc, Nat.mul_comm s 2, Nat.mul_assoc]
    change collatzStep (s * (2 * q) + collatzIter k r) =
      (if (collatzIter k r) % 2 == 0 then s else 3 * s) * q + collatzStep (collatzIter k r)
    rw [hs2]
    by_cases hev : (collatzIter k r) % 2 = 0
    · have hb : ((collatzIter k r) % 2 == 0) = true := decide_eq_true hev
      have hev_lhs : (2 * (s * q) + collatzIter k r) % 2 = 0 := by omega
      simp only [hb, ite_true]
      rw [collatzStep_of_even_nat _ hev_lhs, collatzStep_of_even_nat _ hev]
      omega
    · have hodd : (collatzIter k r) % 2 = 1 := by omega
      have hb : ((collatzIter k r) % 2 == 0) = false := decide_eq_false hev
      have hodd_lhs : (2 * (s * q) + collatzIter k r) % 2 = 1 := by omega
      simp only [hb, Bool.false_eq_true, ite_false]
      rw [collatzStep_of_odd_nat _ hodd_lhs, collatzStep_of_odd_nat _ hodd, Nat.mul_assoc 3 s q]
      omega

theorem dyadic_descent_exclusion (nMin k r s c : Nat)
    (hnoDesc : ∀ m : Nat, ¬ (0 < collatzIter m nMin ∧ collatzIter m nMin < nMin))
    (hmod : nMin % 2 ^ k = r)
    (hs : affineStepSlope k r = s)
    (hc : collatzIter k r = c)
    (hs_lt : s ≤ 2 ^ k)
    (hc_pos : 0 < c)
    (hc_lt : c < r) :
    False := by
  let q := nMin / 2 ^ k
  have hn_eq : nMin = 2 ^ k * q + r := by
    have hdm := (Nat.div_add_mod nMin (2 ^ k)).symm
    rw [hmod] at hdm; exact hdm
  have hiter : collatzIter k nMin = s * q + c := by
    conv => lhs; rw [hn_eq]
    rw [collatzIter_mod_pow2_universal, hs, hc]
  have hsq : s * q ≤ 2 ^ k * q := Nat.mul_le_mul_right q hs_lt
  exact hnoDesc k ⟨by omega, by omega⟩

theorem dyadic_coalescence_exclusion (nMin k r s c k' r' m' : Nat)
    (hnMin : nMin > 1)
    (hnoDesc : ∀ m : Nat, ¬ (0 < collatzIter m nMin ∧ collatzIter m nMin < nMin))
    (hminReach : ∀ m : Nat, 1 ≤ m -> m < nMin -> ∃ k1 : Nat, collatzIter k1 m = 1)
    (hn_eq : nMin = 2 ^ k * (nMin / 2 ^ k) + r)
    (hs : affineStepSlope k r = s) (hc : collatzIter k r = c)
    (hp_lo : 1 ≤ 2 ^ k' * m' + r') (hp_hi : 2 ^ k' * m' + r' < nMin)
    (heq_iter : affineStepSlope k' r' * m' + collatzIter k' r' = s * (nMin / 2 ^ k) + c) :
    False := by
  let nPrime := 2 ^ k' * m' + r'
  have hi1 : collatzIter k nMin = s * (nMin / 2 ^ k) + c := by
    conv => lhs; rw [hn_eq]
    rw [collatzIter_mod_pow2_universal, hs, hc]
  have hi2 : collatzIter k' nPrime = s * (nMin / 2 ^ k) + c := by
    dsimp [nPrime]; rw [collatzIter_mod_pow2_universal, heq_iter]
  exact minimal_counterexample_no_coalescence nMin nPrime k' k hnMin hnoDesc hminReach
    hp_lo hp_hi (by rw [hi1, hi2])

theorem replicate_succ_append_local (b : Bool) :
    ∀ m : Nat, List.replicate (m + 1) b = List.replicate m b ++ [b]
  | 0 => rfl
  | m + 1 => by
    change b :: List.replicate (m + 1) b = b :: (List.replicate m b ++ [b])
    rw [replicate_succ_append_local b m]

theorem parityWeight_replicate_true_local : ∀ m : Nat, parityWeight (List.replicate m true) = m
  | 0 => rfl
  | m + 1 => by simp [List.replicate, parityWeight, parityWeight_replicate_true_local m]; omega

theorem affineCarry_replicate_true_local :
    ∀ m : Nat, affineCarry (List.replicate m true) + 2 ^ m = 3 ^ m
  | 0 => rfl
  | m + 1 => by
    rw [replicate_succ_append_local true m, affineCarry_append]
    have hc1 : affineCarry [true] = 1 := rfl
    have hw1 : parityWeight [true] = 1 := rfl
    rw [hc1, hw1, List.length_replicate, Nat.pow_succ 2 m, Nat.pow_succ 3 m]
    have ih := affineCarry_replicate_true_local m
    omega

/-- Parametric backward parity word `uHead ++ replicate (w1 + 1) true ++ [false, false]`
    that cancels `2^w1` identically across ALL initial `1`-run weights `w1 ≥ 2`. -/
def allWeightCancelWord (uHead : List Bool) (w1 : Nat) : List Bool :=
  (uHead ++ List.replicate (w1 + 1) true) ++ List.replicate 2 false

/--
  Theorem T2.3a (Universal All-Weight `2^w1`-Cancellation Master Theorem in `Nat`):
  For EVERY head word `uHead` and EVERY weight `w1 ≥ 2`, if `nMin = 2^w1 * u1 - 1`
  has first-block halving `a1 = 1` (`(3^w1 * u1 - 1) % 4 = 2`) and `nPrime` satisfies
  the `w1`-independent head equation `3^w(uHead) * nPrime + C(uHead) = 2^(|uHead|+1) * nMin + 2^|uHead|`,
  then `allWeightCancelWord uHead w1` merges `nPrime` into `collatzIter (w1 + 2) nMin`!
-/
theorem all_weight_head_cancellation_nat
    (uHead : List Bool) (w1 u1 nMin nPrime : Nat)
    (hw1 : w1 ≥ 2) (hu1 : u1 ≥ 1)
    (hn1 : nMin + 1 = 2 ^ w1 * u1)
    (ha1 : (3 ^ w1 * u1 - 1) % 4 = 2)
    (hHead : 3 ^ parityWeight uHead * nPrime + affineCarry uHead =
             2 ^ (uHead.length + 1) * nMin + 2 ^ uHead.length) :
    let u := allWeightCancelWord uHead w1
    2 ^ u.length * collatzIter (w1 + 2) nMin =
      3 ^ parityWeight u * nPrime + affineCarry u := by
  intro u
  let _ := hw1
  have hn_eq : nMin = 2 ^ w1 * u1 - 1 := by omega
  have hx_w1 : collatzIter w1 nMin = 3 ^ w1 * u1 - 1 := by
    rw [hn_eq]; exact odd_run_iter w1 u1 hu1
  have h3w1_pos : 3 ^ w1 ≥ 1 := pow3_pos_nat w1
  have hx_w1_even : (3 ^ w1 * u1 - 1) % 2 = 0 := by omega
  have hx_w1_1 : collatzIter (w1 + 1) nMin = (3 ^ w1 * u1 - 1) / 2 := by
    have hs : collatzIter (w1 + 1) nMin = collatzStep (collatzIter w1 nMin) := by
      simpa [collatzIter] using collatzIter_add w1 1 nMin
    rw [hs, hx_w1, collatzStep_of_even_nat _ hx_w1_even]
  have hx_w1_1_odd : ((3 ^ w1 * u1 - 1) / 2) % 2 = 1 := by omega
  have hx_w1_2 : collatzIter (w1 + 2) nMin = (3 * ((3 ^ w1 * u1 - 1) / 2) + 1) / 2 := by
    have hs : collatzIter (w1 + 2) nMin = collatzStep (collatzIter (w1 + 1) nMin) := by
      simpa [collatzIter] using collatzIter_add (w1 + 1) 1 nMin
    rw [hs, hx_w1_1, collatzStep_of_odd_nat _ hx_w1_1_odd]
  have h_iter_eq : 2 ^ (w1 + 2) * collatzIter (w1 + 2) nMin + 2 ^ w1 = 3 ^ (w1 + 1) * (nMin + 1) := by
    rw [hx_w1_2, hn1]
    have hpow2 : 2 ^ (w1 + 2) = 2 ^ w1 * 4 := by rw [Nat.pow_add]
    have hpow3 : 3 ^ (w1 + 1) = 3 * 3 ^ w1 := by rw [Nat.pow_succ, Nat.mul_comm]
    have h3u_pos : 3 ^ w1 * u1 ≥ 1 := by have := Nat.mul_le_mul h3w1_pos hu1; omega
    have h4 : 4 * ((3 * ((3 ^ w1 * u1 - 1) / 2) + 1) / 2) + 1 = 3 * (3 ^ w1 * u1) := by omega
    calc
      2 ^ (w1 + 2) * ((3 * ((3 ^ w1 * u1 - 1) / 2) + 1) / 2) + 2 ^ w1
          = 2 ^ w1 * (4 * ((3 * ((3 ^ w1 * u1 - 1) / 2) + 1) / 2) + 1) := by
            rw [hpow2, Nat.mul_assoc, Nat.mul_add, Nat.mul_one]
      _ = 2 ^ w1 * (3 * (3 ^ w1 * u1)) := by rw [h4]
      _ = 3 ^ (w1 + 1) * (2 ^ w1 * u1) := by
            rw [hpow3, ← Nat.mul_assoc (2 ^ w1), Nat.mul_comm (2 ^ w1) 3,
                Nat.mul_assoc 3 (2 ^ w1) (3 ^ w1 * u1),
                ← Nat.mul_assoc (2 ^ w1) (3 ^ w1) u1, Nat.mul_comm (2 ^ w1) (3 ^ w1),
                Nat.mul_assoc (3 ^ w1), ← Nat.mul_assoc 3 (3 ^ w1)]
  have hlen_u : u.length = (uHead.length + 1) + (w1 + 2) := by
    simp [u, allWeightCancelWord, List.length_append, List.length_replicate]; omega
  have hw_u : parityWeight u = (w1 + 1) + parityWeight uHead := by
    have h1 := (affineCarry_append_replicate_false (uHead ++ List.replicate (w1 + 1) true) 2).1
    change parityWeight ((uHead ++ List.replicate (w1 + 1) true) ++ List.replicate 2 false) =
      (w1 + 1) + parityWeight uHead
    rw [h1, parityWeight_append, parityWeight_replicate_true_local]
    omega
  have hc_u : affineCarry u + 2 ^ uHead.length * 2 ^ (w1 + 1) =
      3 ^ (w1 + 1) * affineCarry uHead + 2 ^ uHead.length * 3 ^ (w1 + 1) := by
    have h1 := (affineCarry_append_replicate_false (uHead ++ List.replicate (w1 + 1) true) 2).2
    have h2 := affineCarry_append uHead (List.replicate (w1 + 1) true)
    rw [parityWeight_replicate_true_local] at h2
    have hrep := affineCarry_replicate_true_local (w1 + 1)
    change affineCarry ((uHead ++ List.replicate (w1 + 1) true) ++ List.replicate 2 false) +
      2 ^ uHead.length * 2 ^ (w1 + 1) =
      3 ^ (w1 + 1) * affineCarry uHead + 2 ^ uHead.length * 3 ^ (w1 + 1)
    rw [h1, h2, Nat.add_assoc, ← Nat.mul_add (2 ^ uHead.length), hrep]
  apply Nat.add_right_cancel (m := 2 ^ uHead.length * 2 ^ (w1 + 1))
  have hlhs : 2 ^ u.length * collatzIter (w1 + 2) nMin + 2 ^ uHead.length * 2 ^ (w1 + 1) =
      2 ^ (uHead.length + 1) * (3 ^ (w1 + 1) * (nMin + 1)) := by
    rw [hlen_u, Nat.pow_add]
    have hp : 2 ^ uHead.length * 2 ^ (w1 + 1) = 2 ^ (uHead.length + 1) * 2 ^ w1 := by
      rw [Nat.pow_succ 2 uHead.length, Nat.pow_succ 2 w1,
          Nat.mul_assoc (2 ^ uHead.length) 2 (2 ^ w1),
          Nat.mul_comm 2 (2 ^ w1), ← Nat.mul_assoc]
    rw [hp, Nat.mul_assoc (2 ^ (uHead.length + 1)), ← Nat.mul_add, h_iter_eq]
  have hrhs : 3 ^ parityWeight u * nPrime + affineCarry u + 2 ^ uHead.length * 2 ^ (w1 + 1) =
      2 ^ (uHead.length + 1) * (3 ^ (w1 + 1) * (nMin + 1)) := by
    rw [Nat.add_assoc, hc_u, hw_u, Nat.pow_add, Nat.mul_assoc (3 ^ (w1 + 1)),
        ← Nat.add_assoc, ← Nat.mul_add (3 ^ (w1 + 1)), hHead]
    have hlin : 2 ^ (uHead.length + 1) * nMin + 2 ^ uHead.length + 2 ^ uHead.length =
        2 ^ (uHead.length + 1) * (nMin + 1) := by
      rw [Nat.mul_add, Nat.mul_one, Nat.pow_succ 2 uHead.length]
      omega
    calc
      3 ^ (w1 + 1) * (2 ^ (uHead.length + 1) * nMin + 2 ^ uHead.length) +
          2 ^ uHead.length * 3 ^ (w1 + 1)
          = 3 ^ (w1 + 1) * (2 ^ (uHead.length + 1) * nMin + 2 ^ uHead.length) +
            3 ^ (w1 + 1) * 2 ^ uHead.length := by rw [Nat.mul_comm (2 ^ uHead.length)]
      _ = 3 ^ (w1 + 1) * (2 ^ (uHead.length + 1) * nMin + 2 ^ uHead.length + 2 ^ uHead.length) := by
            rw [← Nat.mul_add]
      _ = 3 ^ (w1 + 1) * (2 ^ (uHead.length + 1) * (nMin + 1)) := by rw [hlin]
      _ = 2 ^ (uHead.length + 1) * (3 ^ (w1 + 1) * (nMin + 1)) := by
            rw [← Nat.mul_assoc, Nat.mul_comm (3 ^ (w1 + 1)), Nat.mul_assoc]
  rw [hlhs, hrhs]

theorem factor2AdicPos : ∀ (fuel m : Nat),
    1 ≤ m -> m ≤ fuel -> ∃ v u : Nat, u ≥ 1 ∧ u % 2 = 1 ∧ m = 2 ^ v * u
  | 0, _, hm1, hle => by omega
  | fuel + 1, m, hm1, hle => by
    by_cases hodd : m % 2 = 1
    · exact ⟨0, m, hm1, hodd, by simp⟩
    · have hev : m % 2 = 0 := by omega
      rcases factor2AdicPos fuel (m / 2) (by omega) (by omega) with ⟨v, u, hu1, hu_odd, hdiv⟩
      refine ⟨v + 1, u, hu1, hu_odd, ?_⟩
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ v) 2, Nat.mul_assoc, ← hdiv]
      omega

/--
  Theorem T2.3b (Minimal Counterexample All-Weight Head Exclusion):
  Any `uHead` satisfying `3^w(uHead) * nPrime + C(uHead) = 2^(|uHead|+1) * nMin + 2^|uHead|`
  with `1 ≤ nPrime < nMin` unconditionally refutes `nMin` across ALL weights `w1 ≥ 2`!
-/
theorem minimal_counterexample_all_weight_head_exclusion
    (nMin nPrime : Nat) (uHead : List Bool)
    (hnMin : nMin > 1)
    (hnoDesc : ∀ k : Nat, ¬ (0 < collatzIter k nMin ∧ collatzIter k nMin < nMin))
    (hminReach : ∀ m : Nat, 1 ≤ m -> m < nMin -> ∃ k1 : Nat, collatzIter k1 m = 1)
    (hp_lo : 1 ≤ nPrime) (hp_hi : nPrime < nMin)
    (hHead : 3 ^ parityWeight uHead * nPrime + affineCarry uHead =
             2 ^ (uHead.length + 1) * nMin + 2 ^ uHead.length) :
    False := by
  have hm1296 := minimal_counterexample_mod1296_in_131_classes nMin hnMin hnoDesc hminReach
  have hn_mod4 : nMin % 4 = 3 := by rcases hm1296 with ⟨h16, _, _, _, _⟩; omega
  rcases factor2AdicPos (nMin + 1) (nMin + 1) (by omega) (Nat.le_refl _) with
    ⟨w1, u1, hu1, hu1_odd, hn1⟩
  have hw1 : w1 ≥ 2 := by
    cases w1 with
    | zero => simp at hn1; omega
    | succ k =>
      cases k with
      | zero => simp at hn1; omega
      | succ _ => omega
  have h3_odd : 3 ^ w1 % 2 = 1 := pow3_odd_nat w1
  have hprod_odd : (3 ^ w1 * u1) % 2 = 1 := by rw [Nat.mul_mod, h3_odd, hu1_odd]
  have ha1 : (3 ^ w1 * u1 - 1) % 4 = 2 := by
    by_cases h0 : (3 ^ w1 * u1 - 1) % 4 = 0
    · rcases subdouble_entry_merger_step nMin 0 nMin w1 u1 hw1 hu1 rfl (by omega) hn1 h0 with
        ⟨hlo, hhi, hcoal⟩
      exact False.elim (minimal_counterexample_no_coalescence nMin ((nMin - 1) / 2) (w1 + 1)
        (0 + (w1 + 2)) hnMin hnoDesc hminReach hlo hhi hcoal)
    · omega
  let u := allWeightCancelWord uHead w1
  have hcancel : 2 ^ u.length * collatzIter (w1 + 2) nMin =
      3 ^ parityWeight u * nPrime + affineCarry u :=
    all_weight_head_cancellation_nat uHead w1 u1 nMin nPrime hw1 hu1 hn1 ha1 hHead
  have hcast : (2 : Int) ^ u.length * (collatzIter (w1 + 2) nMin : Int) =
      (3 : Int) ^ parityWeight u * (nPrime : Int) + affineCarryInt u := by
    have hc := congrArg (fun t : Nat => (t : Int)) hcancel
    rw [natCast_mul, natCast_pow2, natCast_add, natCast_mul, natCast_pow3,
        ← affineCarryInt_ofNat] at hc
    exact hc
  rcases general_affine_converse_universal u (nPrime : Int) (collatzIter (w1 + 2) nMin : Int) hcast with
    ⟨_, hiter_int⟩
  have hiter_nat : collatzIter u.length nPrime = collatzIter (w1 + 2) nMin := by
    rw [collatzIterInt_ofNat] at hiter_int; omega
  exact minimal_counterexample_no_coalescence nMin nPrime u.length (w1 + 2)
    hnMin hnoDesc hminReach hp_lo hp_hi hiter_nat

/--
  Theorem T2.3c (Multi-Block Sub-Quadruple Exit-Tail Forcing for `w1 ∈ {4, 5}`):
  Even when `x2 = collatzIter (w1 + 1) nMin > 2 * nMin`, if `(w1 = 4 ∧ w2 ∈ {1, 2})`
  or `(w1 = 5 ∧ w2 = 1)`, any `a2 ≥ 2` triggers `subquad_exit_tail_merger_step` (`xLast ≤ 4 * nMin`),
  forcing `(3^w2 * u2 - 1) % 4 = 2` (`a2 = 1`)!
-/
theorem block2_a2_eq_1_of_w1_4_or_5_exit_tail
    (nMin w1 u1 x2 w2 u2 : Nat)
    (hw_cases : (w1 = 4 ∧ (w2 = 1 ∨ w2 = 2)) ∨ (w1 = 5 ∧ w2 = 1))
    (hu1_odd : u1 % 2 = 1) (hu2_odd : u2 % 2 = 1)
    (hn1 : nMin + 1 = 2 ^ w1 * u1)
    (hx2_val : 2 * x2 = 3 ^ w1 * u1 - 1)
    (hx2_iter : collatzIter (w1 + 1) nMin = x2)
    (hx2_form : x2 + 1 = 2 ^ w2 * u2)
    (hnoMerger : ∀ nPrime K1 K2 : Nat,
      1 ≤ nPrime -> nPrime < nMin -> collatzIter K1 nPrime ≠ collatzIter K2 nMin) :
    (3 ^ w2 * u2 - 1) % 4 = 2 := by
  have h3w2_odd : 3 ^ w2 % 2 = 1 := pow3_odd_nat w2
  have hprod2_odd : (3 ^ w2 * u2) % 2 = 1 := by rw [Nat.mul_mod, h3w2_odd, hu2_odd]
  by_cases ha2_0 : (3 ^ w2 * u2 - 1) % 4 = 0
  · exfalso
    rcases hw_cases with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩
    · rcases subquad_exit_tail_merger_step nMin 5 x2 (by omega) (by omega) hx2_iter (by omega) with
        ⟨hlo, hhi, hcoal⟩
      exact hnoMerger ((x2 - 1) / 4) 1 8 hlo hhi hcoal
    · let xLast := 6 * u2 - 1
      have hx2_odd : x2 % 2 = 1 := by omega
      have hxL_iter : collatzIter 6 nMin = xLast := by
        have hs : collatzIter 6 nMin = collatzStep (collatzIter 5 nMin) :=
          collatzIter_add 5 1 nMin
        rw [hs, hx2_iter, collatzStep_of_odd_nat _ hx2_odd]
        dsimp [xLast]; omega
      rcases subquad_exit_tail_merger_step nMin 6 xLast
        (by dsimp [xLast]; omega) (by dsimp [xLast]; omega) hxL_iter (by dsimp [xLast]; omega) with
        ⟨hlo, hhi, hcoal⟩
      exact hnoMerger ((xLast - 1) / 4) 1 9 hlo hhi hcoal
    · rcases subquad_exit_tail_merger_step nMin 6 x2 (by omega) (by omega) hx2_iter (by omega) with
        ⟨hlo, hhi, hcoal⟩
      exact hnoMerger ((x2 - 1) / 4) 1 9 hlo hhi hcoal
  · omega

/-- Surviving 2-adic residue classes modulo `64` (`7 / 64`). -/
def IsSurvivingMod64Residue (r : Nat) : Prop :=
  r = 7 ∨ r = 27 ∨ r = 31 ∨ r = 39 ∨ r = 47 ∨ r = 59 ∨ r = 63

/-- Surviving 2-adic residue classes modulo `512` (`27 / 512`, minimum survivor `27`). -/
def IsSurvivingMod512Residue (r : Nat) : Prop :=
  r < 512 ∧ IsSurvivingMod64Residue (r % 64) ∧
  r % 128 ≠ 7 ∧ r % 128 ≠ 59 ∧ r % 128 ≠ 95 ∧
  r % 256 ≠ 39 ∧ r % 256 ≠ 63 ∧ r % 256 ≠ 123 ∧
  r % 256 ≠ 175 ∧ r % 256 ≠ 199 ∧ r % 256 ≠ 219 ∧
  r ≠ 287 ∧ r ≠ 367 ∧ r ≠ 383 ∧ r ≠ 411 ∧ r ≠ 487

/-- Surviving 3-adic residue classes modulo `81` (`43 / 81`). -/
def IsSurvivingMod81Residue (r : Nat) : Prop :=
  r < 81 ∧ r % 3 ≠ 2 ∧ r % 9 ≠ 4 ∧ r ≠ 10 ∧ r ≠ 60

/-- Surviving 3-adic residue classes modulo `729` (`382 / 729`). -/
def IsSurvivingMod729Residue (r : Nat) : Prop :=
  r < 729 ∧ r % 3 ≠ 2 ∧ r % 9 ≠ 4 ∧ r % 81 ≠ 10 ∧ r % 81 ≠ 60 ∧
  r ≠ 45 ∧ r ≠ 159 ∧ r ≠ 330 ∧ r ≠ 433 ∧ r ≠ 604

/-- Surviving minimal-counterexample residue classes modulo `5184 = 64 * 81` (`301 / 5184 ≈ 5.806%`). -/
def IsSurvivingMod5184Class (n : Nat) : Prop :=
  IsSurvivingMod64Residue (n % 64) ∧ IsSurvivingMod81Residue (n % 81)

/-- Surviving minimal-counterexample residue classes modulo `46656 = 64 * 729` (`2674 / 46656 ≈ 5.731%`). -/
def IsSurvivingMod46656Class (n : Nat) : Prop :=
  IsSurvivingMod64Residue (n % 64) ∧ IsSurvivingMod729Residue (n % 729)

/-- Surviving minimal-counterexample residue classes modulo `373248 = 512 * 729`
    (`10314 / 373248 = 191 / 6912 ≈ 2.7633%`). -/
def IsSurvivingMod373248Class (n : Nat) : Prop :=
  IsSurvivingMod512Residue (n % 512) ∧ IsSurvivingMod729Residue (n % 729)

def isSurvivingMod64Bool (r : Nat) : Bool :=
  r == 7 || r == 27 || r == 31 || r == 39 || r == 47 || r == 59 || r == 63

def isSurvivingMod512Bool (r : Nat) : Bool :=
  (r < 512) && isSurvivingMod64Bool (r % 64) &&
  !(r % 128 == 7) && !(r % 128 == 59) && !(r % 128 == 95) &&
  !(r % 256 == 39) && !(r % 256 == 63) && !(r % 256 == 123) &&
  !(r % 256 == 175) && !(r % 256 == 199) && !(r % 256 == 219) &&
  !(r == 287) && !(r == 367) && !(r == 383) && !(r == 411) && !(r == 487)

def isSurvivingMod81Bool (r : Nat) : Bool :=
  (r < 81) && !(r % 3 == 2) && !(r % 9 == 4) && !(r == 10) && !(r == 60)

def isSurvivingMod729Bool (r : Nat) : Bool :=
  (r < 729) && !(r % 3 == 2) && !(r % 9 == 4) && !(r % 81 == 10) && !(r % 81 == 60) &&
  !(r == 45) && !(r == 159) && !(r == 330) && !(r == 433) && !(r == 604)

def countGrid2DSieve (rows cols : Nat) (pred : Nat -> Bool) : Nat :=
  (List.range rows).foldl
    (fun acc i => acc + (List.range cols).countP (fun j => pred (cols * i + j)))
    0

theorem surviving_sieve_factored_counts :
    countGrid2DSieve 8 8 isSurvivingMod64Bool = 7 ∧
    countGrid2DSieve 16 32 isSurvivingMod512Bool = 27 ∧
    countGrid2DSieve 9 9 isSurvivingMod81Bool = 43 ∧
    countGrid2DSieve 27 27 isSurvivingMod729Bool = 382 ∧
    7 * 43 = 301 ∧ 7 * 382 = 2674 ∧ 27 * 382 = 10314 := by
  refine ⟨by decide, by decide, by decide, by decide, rfl, rfl, rfl⟩

theorem mod_mul_mod_eq (n M k : Nat) : (n % (M * k)) % M = n % M := by
  have hdm := (Nat.div_add_mod n (M * k)).symm
  conv => rhs; rw [hdm]
  rw [Nat.mul_assoc, Nat.add_mod, Nat.mul_mod M _ M, Nat.mod_self,
      Nat.zero_mul, Nat.zero_mod, Nat.zero_add, Nat.mod_mod]

theorem survivingMod373248_ge_27 (n : Nat) (h : IsSurvivingMod373248Class n) : n ≥ 27 := by
  rcases h with ⟨h512, _⟩
  rcases h512 with ⟨_, h64, h128_7, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  unfold IsSurvivingMod64Residue at h64
  omega

theorem survivingMod5184_imp_mod1296 (n : Nat) (h : IsSurvivingMod5184Class n) :
    IsSurvivingMod1296Class n ∧ n ≥ 7 := by
  rcases h with ⟨h64, h81⟩
  unfold IsSurvivingMod64Residue at h64
  rcases h81 with ⟨_, h3, h9, h10, h60⟩
  have hr3 : (n % 81) % 3 = n % 3 := mod_mul_mod_eq n 3 27
  have hr9 : (n % 81) % 9 = n % 9 := mod_mul_mod_eq n 9 9
  rw [hr3] at h3
  rw [hr9] at h9
  have h1275 : n % 1296 ≠ 1275 := by
    intro hc
    have h81_eq : (n % 1296) % 81 = n % 81 := mod_mul_mod_eq n 81 16
    rw [hc] at h81_eq
    exact h60 h81_eq.symm
  refine ⟨⟨by omega, h3, h9, h10, h1275⟩, by omega⟩

theorem survivingMod46656_imp_mod5184 (n : Nat) (h : IsSurvivingMod46656Class n) :
    IsSurvivingMod5184Class n := by
  rcases h with ⟨h64, h729⟩
  rcases h729 with ⟨_, h3, h9, h10, h60, _, _, _, _, _⟩
  have hr3 : (n % 81) % 3 = (n % 729) % 3 := by
    rw [mod_mul_mod_eq n 3 27, mod_mul_mod_eq n 3 243]
  have hr9 : (n % 81) % 9 = (n % 729) % 9 := by
    rw [mod_mul_mod_eq n 9 9, mod_mul_mod_eq n 9 81]
  have hr81 : (n % 729) % 81 = n % 81 := mod_mul_mod_eq n 81 9
  rw [hr81] at h10 h60
  exact ⟨h64, ⟨Nat.mod_lt n (by decide), by rw [hr3]; exact h3, by rw [hr9]; exact h9, h10, h60⟩⟩

theorem survivingMod46656_imp_mod1296 (n : Nat) (h : IsSurvivingMod46656Class n) :
    IsSurvivingMod1296Class n ∧ n ≥ 7 :=
  survivingMod5184_imp_mod1296 n (survivingMod46656_imp_mod5184 n h)

theorem survivingMod373248_imp_mod46656 (n : Nat) (h : IsSurvivingMod373248Class n) :
    IsSurvivingMod46656Class n := by
  rcases h with ⟨h512, h729⟩
  have hr64 : (n % 512) % 64 = n % 64 := mod_mul_mod_eq n 64 8
  rcases h512 with ⟨_, h64, _⟩
  rw [hr64] at h64
  exact ⟨h64, h729⟩

theorem surviving_mod373248_of_mod512_511_mod81_1 (x : Nat)
    (h512 : x % 512 = 511) (h81 : x % 81 = 1) :
    IsSurvivingMod5184Class x ∧ IsSurvivingMod46656Class x ∧ IsSurvivingMod373248Class x := by
  have hm64 : x % 64 = 63 := by
    have hr := mod_mul_mod_eq x 64 8
    rw [h512] at hr; exact hr.symm
  have hs64 : IsSurvivingMod64Residue (x % 64) := by
    rw [hm64]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  have hs512 : IsSurvivingMod512Residue (x % 512) := by
    rw [h512]
    refine ⟨by decide, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))),
      by decide, by decide, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
  have hs81 : IsSurvivingMod81Residue (x % 81) := by
    rw [h81]; refine ⟨by decide, by decide, by decide, by decide, by decide⟩
  have hs729 : IsSurvivingMod729Residue (x % 729) := by
    have hlt : x % 729 < 729 := Nat.mod_lt x (by decide)
    have hr81 : (x % 729) % 81 = 1 := by rw [mod_mul_mod_eq x 81 9, h81]
    refine ⟨hlt, by omega, by omega, by omega, by omega,
      by omega, by omega, by omega, by omega, by omega⟩
  exact ⟨⟨hs64, hs81⟩, ⟨hs64, hs729⟩, ⟨hs512, hs729⟩⟩

theorem minimal_counterexample_mod729_in_382_classes (nMin : Nat)
    (hnMin : nMin > 1)
    (hnoDesc : ∀ k : Nat, ¬ (0 < collatzIter k nMin ∧ collatzIter k nMin < nMin))
    (hminReach : ∀ m : Nat, 1 ≤ m -> m < nMin -> ∃ k1 : Nat, collatzIter k1 m = 1) :
    IsSurvivingMod729Residue (nMin % 729) := by
  have hm1296 := minimal_counterexample_mod1296_in_131_classes nMin hnMin hnoDesc hminReach
  rcases hm1296 with ⟨_, hn3, hn9, hn81_10, _⟩
  have hr3 : (nMin % 729) % 3 = nMin % 3 := mod_mul_mod_eq nMin 3 243
  have hr9 : (nMin % 729) % 9 = nMin % 9 := mod_mul_mod_eq nMin 9 81
  have hr81 : (nMin % 729) % 81 = nMin % 81 := mod_mul_mod_eq nMin 81 9
  have hn81_60 : nMin % 81 ≠ 60 := by
    intro h
    let q := nMin / 81
    have hn_eq : nMin = 81 * q + 60 := by dsimp [q]; omega
    exact minimal_counterexample_all_weight_head_exclusion nMin (64 * q + 47)
      [true, true, true, true, false] hnMin hnoDesc hminReach (by omega) (by omega)
      (by change 81 * (64 * q + 47) + 65 = 64 * nMin + 32; omega)
  refine ⟨Nat.mod_lt nMin (by decide), by rw [hr3]; exact hn3, by rw [hr9]; exact hn9,
    by rw [hr81]; exact hn81_10, by rw [hr81]; exact hn81_60, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    let q := nMin / 729
    have hn_eq : nMin = 729 * q + 45 := by dsimp [q]; omega
    exact minimal_counterexample_all_weight_head_exclusion nMin (512 * q + 31)
      [true, true, true, true, true, false, true, false] hnMin hnoDesc hminReach (by omega) (by omega)
      (by change 729 * (512 * q + 31) + 697 = 512 * nMin + 256; omega)
  · intro h
    let q := nMin / 729
    have hn_eq : nMin = 729 * q + 159 := by dsimp [q]; omega
    exact minimal_counterexample_all_weight_head_exclusion nMin (512 * q + 111)
      [true, true, true, true, false, true, true, false] hnMin hnoDesc hminReach (by omega) (by omega)
      (by change 729 * (512 * q + 111) + 745 = 512 * nMin + 256; omega)
  · intro h
    let q := nMin / 729
    have hn_eq : nMin = 729 * q + 330 := by dsimp [q]; omega
    exact minimal_counterexample_all_weight_head_exclusion nMin (512 * q + 231)
      [true, true, true, false, true, true, true, false] hnMin hnoDesc hminReach (by omega) (by omega)
      (by change 729 * (512 * q + 231) + 817 = 512 * nMin + 256; omega)
  · intro h
    let q := nMin / 729
    have hn_eq : nMin = 729 * q + 433 := by dsimp [q]; omega
    exact minimal_counterexample_k0_backward_exclusion nMin (512 * q + 303)
      [true, true, true, true, false, true, false, true, false] hnMin hnoDesc hminReach
      (by omega) (by omega) (by change 512 * nMin = 729 * (512 * q + 303) + 809; omega)
  · intro h
    let q := nMin / 729
    have hn_eq : nMin = 729 * q + 604 := by dsimp [q]; omega
    exact minimal_counterexample_k0_backward_exclusion nMin (512 * q + 423)
      [true, true, true, false, true, true, false, true, false] hnMin hnoDesc hminReach
      (by omega) (by omega) (by change 512 * nMin = 729 * (512 * q + 423) + 881; omega)

theorem minimal_counterexample_mod512_in_27_classes (nMin : Nat)
    (hnMin : nMin > 1)
    (hnoDesc : ∀ k : Nat, ¬ (0 < collatzIter k nMin ∧ collatzIter k nMin < nMin))
    (hminReach : ∀ m : Nat, 1 ≤ m -> m < nMin -> ∃ k1 : Nat, collatzIter k1 m = 1) :
    IsSurvivingMod512Residue (nMin % 512) := by
  have hm1296 := minimal_counterexample_mod1296_in_131_classes nMin hnMin hnoDesc hminReach
  have hm16 : nMin % 16 = 7 ∨ nMin % 16 = 11 ∨ nMin % 16 = 15 := hm1296.1
  have hn32_11 : nMin % 32 ≠ 11 := fun h =>
    dyadic_descent_exclusion nMin 5 11 27 10 hnoDesc h rfl rfl (by decide) (by decide) (by decide)
  have hn32_23 : nMin % 32 ≠ 23 := fun h =>
    dyadic_descent_exclusion nMin 5 23 27 20 hnoDesc h rfl rfl (by decide) (by decide) (by decide)
  have hn64_15 : nMin % 64 ≠ 15 := fun h =>
    dyadic_coalescence_exclusion nMin 6 15 81 20 5 7 (nMin / 64) hnMin hnoDesc hminReach
      (by omega) rfl rfl (by omega) (by omega)
      (by change 81 * (nMin / 64) + 20 = 81 * (nMin / 64) + 20; rfl)
  have hs64 : IsSurvivingMod64Residue (nMin % 64) := by
    unfold IsSurvivingMod64Residue; omega
  have hr64 : (nMin % 512) % 64 = nMin % 64 := mod_mul_mod_eq nMin 64 8
  have hr128 : (nMin % 512) % 128 = nMin % 128 := mod_mul_mod_eq nMin 128 4
  have hr256 : (nMin % 512) % 256 = nMin % 256 := mod_mul_mod_eq nMin 256 2
  refine ⟨Nat.mod_lt nMin (by decide), by rw [hr64]; exact hs64,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hr128]; exact fun h =>
      dyadic_descent_exclusion nMin 7 7 81 5 hnoDesc h rfl rfl (by decide) (by decide) (by decide)
  · rw [hr128]; exact fun h =>
      dyadic_descent_exclusion nMin 7 59 81 38 hnoDesc h rfl rfl (by decide) (by decide) (by decide)
  · rw [hr128]; exact fun h =>
      dyadic_coalescence_exclusion nMin 7 95 243 182 6 47 (nMin / 128) hnMin hnoDesc hminReach
        (by omega) rfl rfl (by omega) (by omega)
        (by change 243 * (nMin / 128) + 182 = 243 * (nMin / 128) + 182; rfl)
  · rw [hr256]; exact fun h =>
      dyadic_descent_exclusion nMin 8 39 243 38 hnoDesc h rfl rfl (by decide) (by decide) (by decide)
  · rw [hr256]; exact fun h =>
      dyadic_coalescence_exclusion nMin 8 63 729 182 7 31 (nMin / 256) hnMin hnoDesc hminReach
        (by omega) rfl rfl (by omega) (by omega)
        (by change 729 * (nMin / 256) + 182 = 729 * (nMin / 256) + 182; rfl)
  · rw [hr256]; exact fun h =>
      dyadic_descent_exclusion nMin 8 123 243 118 hnoDesc h rfl rfl (by decide) (by decide) (by decide)
  · rw [hr256]; exact fun h =>
      dyadic_descent_exclusion nMin 8 175 243 167 hnoDesc h rfl rfl (by decide) (by decide) (by decide)
  · rw [hr256]; exact fun h =>
      dyadic_descent_exclusion nMin 8 199 243 190 hnoDesc h rfl rfl (by decide) (by decide) (by decide)
  · rw [hr256]; exact fun h =>
      dyadic_descent_exclusion nMin 8 219 243 209 hnoDesc h rfl rfl (by decide) (by decide) (by decide)
  · intro h
    exact dyadic_coalescence_exclusion nMin 9 287 729 410 1 1 (243 * (nMin / 512) + 136)
      hnMin hnoDesc hminReach (by omega) rfl rfl (by omega) (by omega)
      (by change 3 * (243 * (nMin / 512) + 136) + 2 = 729 * (nMin / 512) + 410; omega)
  · intro h
    exact dyadic_coalescence_exclusion nMin 9 367 729 524 1 1 (243 * (nMin / 512) + 174)
      hnMin hnoDesc hminReach (by omega) rfl rfl (by omega) (by omega)
      (by change 3 * (243 * (nMin / 512) + 174) + 2 = 729 * (nMin / 512) + 524; omega)
  · intro h
    exact dyadic_coalescence_exclusion nMin 9 383 2187 1640 8 191 (nMin / 512)
      hnMin hnoDesc hminReach (by omega) rfl rfl (by omega) (by omega)
      (by change 2187 * (nMin / 512) + 1640 = 2187 * (nMin / 512) + 1640; rfl)
  · intro h
    exact dyadic_coalescence_exclusion nMin 9 411 729 587 5 7 (9 * (nMin / 512) + 7)
      hnMin hnoDesc hminReach (by omega) rfl rfl (by omega) (by omega)
      (by change 81 * (9 * (nMin / 512) + 7) + 20 = 729 * (nMin / 512) + 587; omega)
  · intro h
    exact dyadic_coalescence_exclusion nMin 9 487 729 695 4 11 (27 * (nMin / 512) + 25)
      hnMin hnoDesc hminReach (by omega) rfl rfl (by omega) (by omega)
      (by change 27 * (27 * (nMin / 512) + 25) + 20 = 729 * (nMin / 512) + 695; omega)

/--
  Theorem T2.5 (Complete Mod-373248 Multi-Block Minimal-Counterexample Sieve):
  Every minimal counterexample `nMin > 1` lies strictly inside `IsSurvivingMod373248Class nMin`
  (`10314 / 373248 = 191 / 6912 ≈ 2.7633%`, `nMin ≥ 27`)!
-/
theorem minimal_counterexample_mod373248_in_10314_classes (nMin : Nat)
    (hnMin : nMin > 1)
    (hnoDesc : ∀ k : Nat, ¬ (0 < collatzIter k nMin ∧ collatzIter k nMin < nMin))
    (hminReach : ∀ m : Nat, 1 ≤ m -> m < nMin -> ∃ k1 : Nat, collatzIter k1 m = 1) :
    IsSurvivingMod373248Class nMin :=
  ⟨minimal_counterexample_mod512_in_27_classes nMin hnMin hnoDesc hminReach,
   minimal_counterexample_mod729_in_382_classes nMin hnMin hnoDesc hminReach⟩

/--
  Theorem T2.3d (Complete Mod-46656 Minimal-Counterexample Sieve — `2674 / 46656 ≈ 5.731%`):
-/
theorem minimal_counterexample_mod46656_in_2674_classes (nMin : Nat)
    (hnMin : nMin > 1)
    (hnoDesc : ∀ k : Nat, ¬ (0 < collatzIter k nMin ∧ collatzIter k nMin < nMin))
    (hminReach : ∀ m : Nat, 1 ≤ m -> m < nMin -> ∃ k1 : Nat, collatzIter k1 m = 1) :
    IsSurvivingMod46656Class nMin :=
  survivingMod373248_imp_mod46656 nMin
    (minimal_counterexample_mod373248_in_10314_classes nMin hnMin hnoDesc hminReach)

theorem minimal_counterexample_mod5184_in_301_classes (nMin : Nat)
    (hnMin : nMin > 1)
    (hnoDesc : ∀ k : Nat, ¬ (0 < collatzIter k nMin ∧ collatzIter k nMin < nMin))
    (hminReach : ∀ m : Nat, 1 ≤ m -> m < nMin -> ∃ k1 : Nat, collatzIter k1 m = 1) :
    IsSurvivingMod5184Class nMin :=
  survivingMod46656_imp_mod5184 nMin
    (minimal_counterexample_mod46656_in_2674_classes nMin hnMin hnoDesc hminReach)

/-- Mod-46656 Sieved Forest Carry Collision Hypothesis (`2674 / 46656 ≈ 5.731%`). -/
def Mod46656SievedForestCarryCollisionProp : Prop :=
  ∀ n : Nat, n ≥ 7 -> IsSurvivingMod46656Class n ->
    ∃ (K r : Nat) (cs u : List Bool),
      IsSyracuseForestRoot r ∧ r < n ∧
      (2 : Int) ^ u.length * (collatzIter K n : Int) =
        (3 : Int) ^ parityWeight u * (syracuseForestVal r cs : Int) + affineCarryInt u

/-- Cross-Track Mod-373248 Core Quotient Contraction Hypothesis (`191 / 6912 ≈ 2.7633%`). -/
def Mod373248CoreQuotientContractionProp : Prop :=
  ∀ n : Nat, IsSurvivingMod373248Class n ->
    ∃ (K : Nat) (u : List Bool),
      K ≥ 1 ∧ IsCoreParityWord u ∧ exactBackwardQuotient (collatzIter K n) u 0 < n

/-- Cross-Track Mod-373248 Core Forest Quotient Collision Hypothesis (`191 / 6912 ≈ 2.7633%`). -/
def Mod373248CoreForestQuotientCollisionProp : Prop :=
  ∀ n : Nat, IsSurvivingMod373248Class n ->
    ∃ (K q r : Nat) (cs u : List Bool),
      K ≥ 1 ∧ IsCoreParityWord u ∧ IsSyracuseForestRoot r ∧ r < n ∧
      exactBackwardQuotient (collatzIter K n) u q = syracuseForestVal r cs

theorem mod373248_contraction_reaches_one_aux : ∀ (fuel n : Nat),
    Mod373248CoreQuotientContractionProp -> 1 ≤ n -> n ≤ fuel + 1 ->
    ∃ kn : Nat, collatzIter kn n = 1
  | 0, n, _, hn1, hle => by
    have hn_eq : n = 1 := by omega
    subst hn_eq; exact ⟨0, rfl⟩
  | fuel + 1, n, hprop, hn1, hle => by
    have hminReach : ∀ m : Nat, 1 ≤ m -> m < n -> ∃ k1 : Nat, collatzIter k1 m = 1 :=
      fun m hm1 hmlt => mod373248_contraction_reaches_one_aux fuel m hprop hm1 (by omega)
    by_cases hn_eq1 : n = 1
    · subst hn_eq1; exact ⟨0, rfl⟩
    · by_cases hdesc : ∃ k : Nat, 0 < collatzIter k n ∧ collatzIter k n < n
      · rcases hdesc with ⟨k, hk_pos, hk_lt⟩
        rcases hminReach (collatzIter k n) (by omega) hk_lt with ⟨km, hkm⟩
        exact ⟨k + km, by rw [collatzIter_add, hkm]⟩
      · have hnoDesc : ∀ k : Nat, ¬ (0 < collatzIter k n ∧ collatzIter k n < n) :=
          fun k hk => hdesc ⟨k, hk⟩
        have hm373 : IsSurvivingMod373248Class n :=
          minimal_counterexample_mod373248_in_10314_classes n (by omega) hnoDesc hminReach
        have hm1296 : IsSurvivingMod1296Class n :=
          (survivingMod46656_imp_mod1296 n (survivingMod373248_imp_mod46656 n hm373)).1
        rcases hprop n hm373 with ⟨K, u, hK_pos, hu_core, hy_lt⟩
        have hw_pos : parityWeight u ≥ 1 := by
          rcases hu_core with ⟨hhead, _⟩
          cases u with
          | nil => simp at hhead
          | cons b rest => simp at hhead; subst hhead; simp [parityWeight]
        have hxK_n3 : collatzIter K n % 3 ≠ 0 :=
          surviving_mod1296_iter_mod3_ne_zero K n hK_pos hm1296
        rcases exactBackwardQuotient_spec (collatzIter K n) u 0 hw_pos hxK_n3 with
          ⟨hy_ge1, _, hcoal, _⟩
        rcases hminReach (exactBackwardQuotient (collatzIter K n) u 0) hy_ge1 hy_lt with
          ⟨kz, hkz⟩
        exact coalescence_reaches_one n (exactBackwardQuotient (collatzIter K n) u 0)
          K (u.length + (canonicalSuffixShift u (collatzIter K n) + 0 * (2 * 3 ^ (parityWeight u - 1))))
          kz hcoal.symm hkz

theorem mod373248_forest_reaches_one_aux : ∀ (fuel n : Nat),
    Mod373248CoreForestQuotientCollisionProp -> 1 ≤ n -> n ≤ fuel + 1 ->
    ∃ kn : Nat, collatzIter kn n = 1
  | 0, n, _, hn1, hle => by
    have hn_eq : n = 1 := by omega
    subst hn_eq; exact ⟨0, rfl⟩
  | fuel + 1, n, hprop, hn1, hle => by
    have hminReach : ∀ m : Nat, 1 ≤ m -> m < n -> ∃ k1 : Nat, collatzIter k1 m = 1 :=
      fun m hm1 hmlt => mod373248_forest_reaches_one_aux fuel m hprop hm1 (by omega)
    by_cases hn_eq1 : n = 1
    · subst hn_eq1; exact ⟨0, rfl⟩
    · by_cases hdesc : ∃ k : Nat, 0 < collatzIter k n ∧ collatzIter k n < n
      · rcases hdesc with ⟨k, hk_pos, hk_lt⟩
        rcases hminReach (collatzIter k n) (by omega) hk_lt with ⟨km, hkm⟩
        exact ⟨k + km, by rw [collatzIter_add, hkm]⟩
      · have hnoDesc : ∀ k : Nat, ¬ (0 < collatzIter k n ∧ collatzIter k n < n) :=
          fun k hk => hdesc ⟨k, hk⟩
        have hm373 : IsSurvivingMod373248Class n :=
          minimal_counterexample_mod373248_in_10314_classes n (by omega) hnoDesc hminReach
        rcases survivingMod46656_imp_mod1296 n (survivingMod373248_imp_mod46656 n hm373) with
          ⟨hm1296, hn_ge7⟩
        rcases (mod1296_forest_collision_at_n_iff_core_quotient_at_n n hn_ge7 hm1296).mpr
          (hprop n hm373) with ⟨K, r, cs, u, hr_root, hr_lt, heq⟩
        let z := syracuseForestVal r cs
        rcases general_affine_converse_universal u (z : Int) (collatzIter K n : Int) heq with
          ⟨_, hiter_int⟩
        have hcoal_z : collatzIter u.length z = collatzIter K n := by
          rw [collatzIterInt_ofNat] at hiter_int; omega
        rcases syracuseForestVal_reaches_root r hr_root cs with ⟨kt, _, hkt⟩
        have hr_ge1 : 1 ≤ r := by rcases hr_root with ⟨hr5, _⟩; omega
        rcases hminReach r hr_ge1 hr_lt with ⟨kr, hkr⟩
        have hz_reach1 : collatzIter (kt + kr) z = 1 := by rw [collatzIter_add, hkt, hkr]
        exact coalescence_reaches_one n z K u.length (kt + kr) hcoal_z.symm hz_reach1

/--
  Theorem T2.6a (Cross-Track Global Equivalence: `CollatzConjectureStandard ↔ Mod373248CoreQuotientContractionProp`):
-/
theorem collatz_conjecture_iff_mod373248_core_quotient_contraction :
    CollatzConjectureStandard ↔ Mod373248CoreQuotientContractionProp := by
  constructor
  · intro hstd n hs
    have hn_ge27 : n ≥ 27 := survivingMod373248_ge_27 n hs
    rcases (collatz_standard_iff_compressed.mp hstd) n (by omega) with ⟨kn, hkn⟩
    have hkn_pos : kn ≥ 1 := by
      by_cases hk0 : kn = 0
      · subst hk0; simp [collatzIter] at hkn; omega
      · omega
    refine ⟨kn, [true], hkn_pos, ⟨rfl, rfl⟩, ?_⟩
    rw [hkn]
    have hq1 : exactBackwardQuotient 1 [true] 0 = 1 := by decide
    rw [hq1]; omega
  · intro hprop
    rw [collatz_standard_iff_compressed]
    intro n hn
    exact mod373248_contraction_reaches_one_aux n n hprop (by omega) (by omega)

/--
  Theorem T2.6b (Cross-Track Global Equivalence: `CollatzConjectureStandard ↔ Mod373248CoreForestQuotientCollisionProp`):
-/
theorem collatz_conjecture_iff_mod373248_core_forest_quotient_collision :
    CollatzConjectureStandard ↔ Mod373248CoreForestQuotientCollisionProp := by
  constructor
  · intro hstd n hs
    have hn_ge27 : n ≥ 27 := survivingMod373248_ge_27 n hs
    rcases (collatz_standard_iff_compressed.mp hstd) n (by omega) with ⟨kn, hkn⟩
    have hkn_pos : kn ≥ 1 := by
      by_cases hk0 : kn = 0
      · subst hk0; simp [collatzIter] at hkn; omega
      · omega
    refine ⟨kn, 1, 5, [], [true], hkn_pos, ⟨rfl, rfl⟩,
      ⟨by decide, by decide, by decide, Or.inl rfl⟩, by omega, ?_⟩
    rw [hkn]
    decide
  · intro hprop
    rw [collatz_standard_iff_compressed]
    intro n hn
    exact mod373248_forest_reaches_one_aux n n hprop (by omega) (by omega)

/--
  Theorem T2.3e (`CollatzConjectureStandard ↔ Mod46656SievedForestCarryCollisionProp`):
-/
theorem collatz_standard_iff_mod46656_sieved_forest_collision :
    CollatzConjectureStandard ↔ Mod46656SievedForestCarryCollisionProp := by
  constructor
  · intro hstd n hn hs
    exact (collatz_standard_iff_mod1296_sieved_forest_collision.mp hstd) n hn
      (survivingMod46656_imp_mod1296 n hs).1
  · intro hprop
    rw [collatz_conjecture_iff_mod373248_core_forest_quotient_collision]
    intro n hs373
    have hs46 := survivingMod373248_imp_mod46656 n hs373
    rcases survivingMod46656_imp_mod1296 n hs46 with ⟨hs1296, hn_ge7⟩
    exact (mod1296_forest_collision_at_n_iff_core_quotient_at_n n hn_ge7 hs1296).mp
      (hprop n hn_ge7 hs46)

-- ----------------------------------------------------------------------------
-- T2.2: Universal All-Horizon Mixed-Base Self-Congruent Syracuse Pumping Obstruction
-- ----------------------------------------------------------------------------

theorem mul2_mod81_inv (x : Nat) : (41 * ((2 * x) % 81)) % 81 = x % 81 := by
  have h1 : (41 * ((2 * x) % 81)) % 81 = (41 * (2 * x)) % 81 := by
    rw [Nat.mul_mod 41 ((2 * x) % 81) 81, Nat.mod_mod, ← Nat.mul_mod]
  rw [h1, ← Nat.mul_assoc]
  simpa using Nat.mul_mod 82 x 81

theorem coprime_pow2_cancel_mod81 :
    ∀ (k a b : Nat), (2 ^ k * a) % 81 = (2 ^ k * b) % 81 -> a % 81 = b % 81
  | 0, a, b, h => by simpa using h
  | k + 1, a, b, h => by
    have h1 : (2 ^ k * (2 * a)) % 81 = (2 ^ k * (2 * b)) % 81 := by
      rw [← Nat.mul_assoc, ← Nat.pow_succ, ← Nat.mul_assoc, ← Nat.pow_succ]; exact h
    have hc := congrArg (fun t => (41 * t) % 81) (coprime_pow2_cancel_mod81 k (2 * a) (2 * b) h1)
    simpa only [mul2_mod81_inv] using hc

def bezout3Base2 : Nat -> Nat × Nat
  | 0 => (1, 2)
  | p + 1 =>
    let (a, b) := bezout3Base2 p
    if b % 2 == 0 then (a, b / 2) else (a + 2 ^ p, (b + 3) / 2)

theorem bezout3Base2_spec : ∀ p : Nat,
    let (a, b) := bezout3Base2 p
    a ≥ 1 ∧ b ≥ 1 ∧ a % 2 = 1 ∧ 3 * a = 2 ^ p * b + 1
  | 0 => by decide
  | p + 1 => by
    have ih := bezout3Base2_spec p
    rcases hp : bezout3Base2 p with ⟨a, b⟩
    rw [hp] at ih
    rcases ih with ⟨ha1, hb1, ha_odd, heq⟩
    simp only [bezout3Base2, hp]
    by_cases hbev : b % 2 = 0
    · have hb_true : (b % 2 == 0) = true := decide_eq_true hbev
      simp only [hb_true, ite_true]
      obtain ⟨k, rfl⟩ : ∃ k : Nat, b = 2 * k := ⟨b / 2, by omega⟩
      have hk_div : (2 * k) / 2 = k := by omega
      rw [hk_div]
      have hmul : 2 ^ (p + 1) * k = 2 ^ p * (2 * k) := by
        rw [Nat.pow_succ, Nat.mul_assoc]
      exact ⟨ha1, by omega, ha_odd, by rw [hmul]; exact heq⟩
    · have hb_false : (b % 2 == 0) = false := decide_eq_false hbev
      simp only [hb_false, Bool.false_eq_true, ite_false]
      have hp_pos : p ≥ 1 := by
        cases p with
        | zero => simp [bezout3Base2] at hp; omega
        | succ _ => omega
      have hp_ev : 2 ^ p % 2 = 0 := by
        rw [show p = (p - 1) + 1 by omega, Nat.pow_succ]; omega
      have ha_next_odd : (a + 2 ^ p) % 2 = 1 := by rw [Nat.add_mod, ha_odd, hp_ev]
      obtain ⟨k, hk⟩ : ∃ k : Nat, b + 3 = 2 * k := ⟨(b + 3) / 2, by omega⟩
      have hk_div : (b + 3) / 2 = k := by omega
      rw [hk_div]
      have hmul : 2 ^ (p + 1) * k = 2 ^ p * b + 3 * 2 ^ p := by
        calc
          2 ^ (p + 1) * k = 2 ^ p * (2 * k) := by rw [Nat.pow_succ, Nat.mul_assoc]
          _ = 2 ^ p * (b + 3) := by rw [← hk]
          _ = 2 ^ p * b + 3 * 2 ^ p := by rw [Nat.mul_add, Nat.mul_comm (2 ^ p) 3]
      have h3a : 3 * (a + 2 ^ p) = 2 ^ (p + 1) * k + 1 := by
        calc
          3 * (a + 2 ^ p) = 3 * a + 3 * 2 ^ p := Nat.mul_add 3 a (2 ^ p)
          _ = (2 ^ p * b + 1) + 3 * 2 ^ p := by rw [heq]
          _ = (2 ^ p * b + 3 * 2 ^ p) + 1 := by
                rw [Nat.add_assoc, Nat.add_comm 1 (3 * 2 ^ p), ← Nat.add_assoc]
          _ = 2 ^ (p + 1) * k + 1 := by rw [hmul]
      exact ⟨Nat.le_add_right_of_le ha1, by omega, ha_next_odd, h3a⟩

theorem bezout_pow3_pow2_campaign : ∀ (P Q : Nat), Q ≥ 1 ->
    ∃ a b : Nat, a ≥ 1 ∧ b ≥ 1 ∧ a % 2 = 1 ∧ 3 ^ Q * a = 2 ^ P * b + 1 := by
  intro P Q hQ; obtain ⟨m, rfl⟩ : ∃ m, Q = m + 1 := ⟨Q - 1, by omega⟩; clear hQ
  induction m with
  | zero =>
    rcases hp : bezout3Base2 P with ⟨a, b⟩; have hs := bezout3Base2_spec P; rw [hp] at hs
    exact ⟨a, b, hs.1, hs.2.1, hs.2.2.1, by simpa using hs.2.2.2⟩
  | succ k ih =>
    rcases ih with ⟨a0, b0, ha0, hb0, ha0_odd, heq0⟩
    rcases hp : bezout3Base2 P with ⟨a1, b1⟩; have hs := bezout3Base2_spec P; rw [hp] at hs
    rcases hs with ⟨ha1, hb1, ha1_odd, heq1⟩
    refine ⟨a0 * a1, 2 ^ P * (b0 * b1) + b0 + b1, Nat.mul_le_mul ha0 ha1, by omega,
      by rw [Nat.mul_mod, ha0_odd, ha1_odd], ?_⟩
    calc
      3 ^ (k + 1 + 1) * (a0 * a1) = (3 ^ (k + 1) * a0) * (3 * a1) := by
        rw [Nat.pow_succ, Nat.mul_assoc (3 ^ (k + 1)) 3, ← Nat.mul_assoc 3 a0 a1,
            Nat.mul_comm 3 a0, Nat.mul_assoc a0 3 a1, ← Nat.mul_assoc (3 ^ (k + 1))]
      _ = (2 ^ P * b0 + 1) * (2 ^ P * b1 + 1) := by rw [heq0, heq1]
      _ = 2 ^ P * (2 ^ P * (b0 * b1) + b0 + b1) + 1 := by
        rw [Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.mul_one,
            Nat.mul_assoc (2 ^ P) b0 (2 ^ P * b1), ← Nat.mul_assoc b0 (2 ^ P) b1,
            Nat.mul_comm b0 (2 ^ P), Nat.mul_assoc (2 ^ P) b0 b1,
            Nat.mul_add (2 ^ P) (2 ^ P * (b0 * b1) + b0) b1,
            Nat.mul_add (2 ^ P) (2 ^ P * (b0 * b1)) b0]; omega

theorem pow2_pos_inverse_mod_pow3 (P Q : Nat) (hQ : Q ≥ 1) :
    ∃ inv q : Nat, inv ≥ 1 ∧ 2 ^ P * inv = 3 ^ Q * q + 1 := by
  rcases bezout_pow3_pow2_campaign P Q hQ with ⟨a, b, ha, hb, _, heq⟩
  have h3Q_ge3 : 3 ^ Q ≥ 3 := by
    obtain ⟨m, rfl⟩ : ∃ m, Q = m + 1 := ⟨Q - 1, by omega⟩
    rw [Nat.pow_succ]; have hp := pow_pos_base 3 (by decide) m; omega
  have h3Qa_ge3 : 3 ^ Q * a ≥ 3 := by have := Nat.mul_le_mul h3Q_ge3 ha; omega
  have hge_2a : a * (3 ^ Q * a) ≥ 2 * a := by rw [Nat.mul_comm 2 a]; exact Nat.mul_le_mul_left a (by omega)
  let q := a * (3 ^ Q * a) - 2 * a
  have hsq : (2 ^ P * b) * (2 ^ P * b) + (2 * (2 ^ P * b) + 1) = (3 ^ Q * a) * (3 ^ Q * a) := by
    calc (2 ^ P * b) * (2 ^ P * b) + (2 * (2 ^ P * b) + 1) = (2 ^ P * b + 1) * (2 ^ P * b + 1) := by
          rw [Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.mul_one]; omega
      _ = (3 ^ Q * a) * (3 ^ Q * a) := by rw [heq]
  have h2ab : 2 * (2 ^ P * b) + 2 = 3 ^ Q * (2 * a) := by
    have h1 := congrArg (fun t => 2 * t) heq; rw [Nat.mul_add] at h1
    calc 2 * (2 ^ P * b) + 2 = 2 * (3 ^ Q * a) := h1.symm
      _ = 3 ^ Q * (2 * a) := by rw [← Nat.mul_assoc, Nat.mul_comm 2 (3 ^ Q), Nat.mul_assoc]
  have hrhs : (3 ^ Q * a) * (3 ^ Q * a) = 3 ^ Q * q + 3 ^ Q * (2 * a) := by
    dsimp [q]; rw [← Nat.mul_add (3 ^ Q), Nat.sub_add_cancel hge_2a, Nat.mul_assoc (3 ^ Q) a (3 ^ Q * a)]
  refine ⟨2 ^ P * (b * b), q, ?_, ?_⟩
  · have hm := Nat.mul_le_mul (pow_pos_base 2 (by decide) P) (Nat.mul_le_mul hb hb); omega
  · have hassoc : 2 ^ P * (2 ^ P * (b * b)) = (2 ^ P * b) * (2 ^ P * b) := by
      rw [← Nat.mul_assoc (2 ^ P) b b, ← Nat.mul_assoc (2 ^ P) (2 ^ P * b) b,
          Nat.mul_comm (2 ^ P) (2 ^ P * b), Nat.mul_assoc]
    rw [hassoc]; omega

theorem coprime_pow2_cancel_pow3 (k Q x y : Nat) (hQ : Q ≥ 1)
    (hmod : (2 ^ k * x) % 3 ^ Q = (2 ^ k * y) % 3 ^ Q) :
    x % 3 ^ Q = y % 3 ^ Q := by
  rcases pow2_pos_inverse_mod_pow3 k Q hQ with ⟨inv, q, _, hinv⟩
  have hmul : ∀ z : Nat, (inv * ((2 ^ k * z) % 3 ^ Q)) % 3 ^ Q = z % 3 ^ Q := by
    intro z
    rw [Nat.mul_mod inv ((2 ^ k * z) % 3 ^ Q) (3 ^ Q), Nat.mod_mod, ← Nat.mul_mod,
        ← Nat.mul_assoc inv (2 ^ k) z, Nat.mul_comm inv (2 ^ k), hinv,
        Nat.add_mul, Nat.one_mul, Nat.add_mod,
        Nat.mul_assoc (3 ^ Q) q z, Nat.mul_mod (3 ^ Q) (q * z) (3 ^ Q),
        Nat.mod_self, Nat.zero_mul, Nat.zero_mod, Nat.zero_add, Nat.mod_mod]
  simpa only [hmul] using congrArg (fun t => (inv * t) % 3 ^ Q) hmod

theorem coprime_pow3_dvd_pow2_cancel (P Q z : Nat) (hQ : Q ≥ 1)
    (hmod : (3 ^ Q * z) % 2 ^ P = 0) : z % 2 ^ P = 0 := by
  rcases bezout_pow3_pow2_campaign P Q hQ with ⟨a, b, _, _, _, heq⟩
  have hmul : (a * ((3 ^ Q * z) % 2 ^ P)) % 2 ^ P = z % 2 ^ P := by
    rw [Nat.mul_mod a ((3 ^ Q * z) % 2 ^ P) (2 ^ P), Nat.mod_mod, ← Nat.mul_mod,
        ← Nat.mul_assoc a (3 ^ Q) z, Nat.mul_comm a (3 ^ Q), heq,
        Nat.add_mul, Nat.one_mul, Nat.add_mod,
        Nat.mul_assoc (2 ^ P) b z, Nat.mul_mod (2 ^ P) (b * z) (2 ^ P),
        Nat.mod_self, Nat.zero_mul, Nat.zero_mod, Nat.zero_add, Nat.mod_mod]
  rw [hmod, Nat.mul_zero, Nat.zero_mod] at hmul; exact hmul.symm

theorem add_mod_eq_imp_dvd (M x d : Nat) (hM : M > 0) (hmod : (x + d) % M = x % M) : d % M = 0 := by
  let rx := x % M; let rd := d % M
  have hrx : rx < M := Nat.mod_lt x hM; have hrd : rd < M := Nat.mod_lt d hM
  have hsum : (rx + rd) % M = rx := by dsimp [rx, rd]; rw [← Nat.add_mod, hmod]
  by_cases hlt : rx + rd < M
  · rw [Nat.mod_eq_of_lt hlt] at hsum; dsimp [rd] at hsum; omega
  · have hlt2 : rx + rd - M < M := by omega
    have heq2 : rx + rd = M * 1 + (rx + rd - M) := by omega
    have hm0 : (M * 1) % M = 0 := by rw [Nat.mul_one, Nat.mod_self]
    rw [heq2, Nat.add_mod, hm0, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hlt2] at hsum; omega

theorem crt_pow2_pow3_unique_le (A B x y : Nat) (hB : B ≥ 1) (hle : x ≤ y)
    (h2 : x % 2 ^ A = y % 2 ^ A) (h3 : x % 3 ^ B = y % 3 ^ B) :
    x % (2 ^ A * 3 ^ B) = y % (2 ^ A * 3 ^ B) := by
  let d := y - x; have hy : y = x + d := by omega
  rw [hy] at h2 h3 ⊢
  have hd2 : d % 2 ^ A = 0 := add_mod_eq_imp_dvd (2 ^ A) x d (pow_pos_base 2 (by decide) A) h2.symm
  have hd3 : d % 3 ^ B = 0 := add_mod_eq_imp_dvd (3 ^ B) x d (pow_pos_base 3 (by decide) B) h3.symm
  let k := d / 2 ^ A
  have hd_eq : d = 2 ^ A * k := by have hdm := (Nat.div_add_mod d (2 ^ A)).symm; rw [hd2, Nat.add_zero] at hdm; exact hdm
  have hk3 : (2 ^ A * k) % 3 ^ B = (2 ^ A * 0) % 3 ^ B := by rw [← hd_eq, hd3, Nat.mul_zero, Nat.zero_mod]
  have hk_div : k % 3 ^ B = 0 := by simpa using coprime_pow2_cancel_pow3 A B k 0 hB hk3
  let q := k / 3 ^ B
  have hk_eq : k = 3 ^ B * q := by have hdm := (Nat.div_add_mod k (3 ^ B)).symm; rw [hk_div, Nat.add_zero] at hdm; exact hdm
  have hd_prod : d = (2 ^ A * 3 ^ B) * q := by rw [hd_eq, hk_eq, Nat.mul_assoc]
  rw [hd_prod, Nat.add_mod, Nat.mul_mod (2 ^ A * 3 ^ B) q (2 ^ A * 3 ^ B),
      Nat.mod_self, Nat.zero_mul, Nat.zero_mod, Nat.add_zero, Nat.mod_mod]

theorem crt_pow2_pow3_unique (A B x y : Nat) (hB : B ≥ 1)
    (h2 : x % 2 ^ A = y % 2 ^ A) (h3 : x % 3 ^ B = y % 3 ^ B) :
    x % (2 ^ A * 3 ^ B) = y % (2 ^ A * 3 ^ B) := by
  by_cases hle : x ≤ y
  · exact crt_pow2_pow3_unique_le A B x y hB hle h2 h3
  · exact (crt_pow2_pow3_unique_le A B y x hB (by omega) h2.symm h3.symm).symm

theorem pair_11_chain_iter :
    ∀ (m t : Nat), t ≥ 1 -> collatzIter (2 * m) (4 ^ m * t + 1) = 3 ^ m * t + 1
  | 0, t, _ => by simp [collatzIter]
  | m + 1, t, ht => by
    have h4 : 4 ^ (m + 1) * t + 1 = 4 * (4 ^ m * t) + 1 := by rw [Nat.pow_succ, Nat.mul_comm (4 ^ m) 4, Nat.mul_assoc]
    have hpos : 4 ^ m * t ≥ 1 := Nat.mul_le_mul (pow_pos_base 4 (by decide) m) ht
    have hs1 : collatzStep (4 * (4 ^ m * t) + 1) = 6 * (4 ^ m * t) + 2 := by rw [collatzStep_of_odd_nat _ (by omega)]; omega
    have hs2 : collatzStep (6 * (4 ^ m * t) + 2) = 4 ^ m * (3 * t) + 1 := by
      rw [collatzStep_of_even_nat _ (by omega)]
      have h6 : (6 * (4 ^ m * t) + 2) / 2 = 3 * (4 ^ m * t) + 1 := by omega
      rw [h6, ← Nat.mul_assoc 3 (4 ^ m) t, Nat.mul_comm 3 (4 ^ m), Nat.mul_assoc]
    rw [show 2 * (m + 1) = 2 + 2 * m by omega, collatzIter_add 2 (2 * m), h4]
    have h2step : collatzIter 2 (4 * (4 ^ m * t) + 1) = 4 ^ m * (3 * t) + 1 := by
      change collatzStep (collatzStep (4 * (4 ^ m * t) + 1)) = 4 ^ m * (3 * t) + 1; rw [hs1, hs2]
    rw [h2step, pair_11_chain_iter m (3 * t) (by omega), Nat.pow_succ 3 m, Nat.mul_assoc]

theorem pow4_eq_pow2_even : ∀ m : Nat, 4 ^ m = 2 ^ (2 * m)
  | 0 => rfl
  | m + 1 => by rw [Nat.pow_succ 4 m, pow4_eq_pow2_even m, show 2 * (m + 1) = 2 * m + 2 by omega, Nat.pow_add 2 (2 * m) 2]

theorem pow3_succ_le_pow2_even : ∀ m : Nat, 3 ^ (m + 1) ≤ 2 ^ (2 * m + 2)
  | 0 => by decide
  | m + 1 => by
    have ih := pow3_succ_le_pow2_even m
    rw [Nat.pow_succ 3 (m + 1), show 2 * (m + 1) + 2 = (2 * m + 2) + 2 by omega,
        Nat.pow_add 2 (2 * m + 2) 2]
    omega

theorem pumping_growth_exists :
    ∀ (G m floor0 : Nat),
      ∃ w1 : Nat, w1 ≥ floor0 ∧ 3 ^ (w1 + m) ≥ (G + 1) * 2 ^ (w1 + 2 * m + 1) ∧ 2 ^ w1 > floor0 + 1 := by
  intro G m floor0
  have hexp_base : ∀ n : Nat, 2 ^ n > n := by intro n; induction n with | zero => decide | succ k ih => rw [Nat.pow_succ]; omega
  have h_ratio : ∀ d : Nat, 2 * 3 ^ d ≥ (d + 2) * 2 ^ d := by
    intro d; induction d with
    | zero => decide
    | succ k ih =>
      have hmul := Nat.mul_le_mul_left 3 ih
      have hlhs : 3 * (2 * 3 ^ k) = 2 * 3 ^ (k + 1) := by rw [Nat.pow_succ]; omega
      have hrhs : 3 * ((k + 2) * 2 ^ k) ≥ (k + 1 + 2) * 2 ^ (k + 1) := by
        rw [Nat.pow_succ, ← Nat.mul_assoc (k + 1 + 2) (2 ^ k) 2, Nat.mul_comm ((k + 1 + 2) * 2 ^ k) 2,
            ← Nat.mul_assoc 3 (k + 2) (2 ^ k), ← Nat.mul_assoc 2 (k + 1 + 2) (2 ^ k)]
        exact Nat.mul_le_mul_right (2 ^ k) (by omega)
      omega
  let M := (G + 1) * 2 ^ (2 * m + 2)
  let w1 := floor0 + 2 + M
  refine ⟨w1, by omega, ?_, ?_⟩
  · have hr := h_ratio w1
    have h3m : 3 ^ (w1 + m) ≥ 3 ^ w1 := by
      rw [Nat.pow_add]; have hm1 := Nat.mul_le_mul_left (3 ^ w1) (pow_pos_base 3 (by decide) m); omega
    have h2m : M * 2 ^ w1 = 2 * ((G + 1) * 2 ^ (w1 + 2 * m + 1)) := by
      dsimp [M]; rw [show w1 + 2 * m + 1 = w1 + (2 * m + 1) by omega, show 2 * m + 2 = (2 * m + 1) + 1 by omega,
          Nat.pow_add 2 w1 (2 * m + 1), Nat.pow_succ 2 (2 * m + 1)]
      calc (G + 1) * (2 ^ (2 * m + 1) * 2) * 2 ^ w1 = (G + 1) * 2 ^ (2 * m + 1) * (2 * 2 ^ w1) := by
            rw [← Nat.mul_assoc (G + 1) (2 ^ (2 * m + 1)) 2, Nat.mul_assoc]
        _ = 2 * ((G + 1) * (2 ^ w1 * 2 ^ (2 * m + 1))) := by
            rw [Nat.mul_comm 2 (2 ^ w1), ← Nat.mul_assoc ((G + 1) * 2 ^ (2 * m + 1)) (2 ^ w1) 2,
                Nat.mul_comm _ 2, Nat.mul_assoc (G + 1) (2 ^ (2 * m + 1)) (2 ^ w1), Nat.mul_comm (2 ^ (2 * m + 1)) (2 ^ w1)]
    have hw1_ge_M : w1 + 2 ≥ M := by dsimp [w1]; omega
    have hm1 := Nat.mul_le_mul_right (2 ^ w1) hw1_ge_M
    have hm2 := Nat.mul_le_mul_left 2 h3m
    omega
  · have hb := hexp_base w1; omega

theorem crt_combine_pos_identities
    (r2 r3 M2 M3 c3 c2 d2 qd2 : Nat)
    (hM2 : M2 ≥ 1) (hM3 : M3 ≥ 1)
    (hc32 : M3 * c3 = M2 * c2 + 1)
    (hd2 : M2 * d2 = M3 * qd2 + 1) :
    let u1 := r2 * (M3 * c3) + r3 * (M2 * d2) + M2 * M3
    u1 ≥ 1 ∧
    u1 = r2 + M2 * (r2 * c2 + r3 * d2 + M3) ∧
    u1 = r3 + M3 * (r2 * c3 + r3 * qd2 + M2) := by
  intro u1
  have hpos : M2 * M3 ≥ 1 := Nat.mul_le_mul hM2 hM3
  refine ⟨by dsimp [u1]; omega, ?_, ?_⟩
  · dsimp [u1]
    rw [hc32, Nat.mul_add r2 (M2 * c2) 1, Nat.mul_one,
        ← Nat.mul_assoc r2 M2 c2, Nat.mul_comm r2 M2, Nat.mul_assoc M2 r2 c2,
        ← Nat.mul_assoc r3 M2 d2, Nat.mul_comm r3 M2, Nat.mul_assoc M2 r3 d2,
        Nat.mul_add M2 (r2 * c2 + r3 * d2) M3, Nat.mul_add M2 (r2 * c2) (r3 * d2)]
    omega
  · dsimp [u1]
    rw [hd2, Nat.mul_add r3 (M3 * qd2) 1, Nat.mul_one,
        ← Nat.mul_assoc r2 M3 c3, Nat.mul_comm r2 M3, Nat.mul_assoc M3 r2 c3,
        ← Nat.mul_assoc r3 M3 qd2, Nat.mul_comm r3 M3, Nat.mul_assoc M3 r3 qd2,
        Nat.mul_add M3 (r2 * c3 + r3 * qd2) M2, Nat.mul_add M3 (r2 * c3) (r3 * qd2),
        Nat.mul_comm M2 M3]
    omega

theorem pumping_archimedean_step
    (G m w1 u1 xEnd : Nat)
    (hw1 : w1 ≥ 2) (hu1 : u1 ≥ 1)
    (hgrow : 3 ^ (w1 + m) ≥ (G + 1) * 2 ^ (w1 + 2 * m + 1))
    (hrel : 2 ^ (2 * m + 1) * xEnd + 3 ^ (m + 1) + 2 ^ (2 * m + 1) =
            3 ^ (w1 + m) * u1 + 2 ^ (2 * m + 2)) :
    xEnd > G * (2 ^ w1 * u1 - 1) := by
  have hp1 : 3 ^ (m + 1) ≤ 2 ^ (2 * m + 1) * 2 := by
    simpa [Nat.pow_succ] using pow3_succ_le_pow2_even m
  have hw4 : 2 ^ w1 ≥ 4 := by
    rw [show w1 = 2 + (w1 - 2) by omega, Nat.pow_add]
    have hp := pow_pos_base 2 (by decide) (w1 - 2); omega
  have hp2 : 2 ^ w1 * u1 ≥ 4 := Nat.mul_le_mul hw4 hu1
  have h3m1_lt : 3 ^ (m + 1) < 2 ^ (2 * m + 1) * (2 ^ w1 * u1) := by
    have hm := Nat.mul_le_mul_left (2 ^ (2 * m + 1)) hp2
    have hp_pos : 2 ^ (2 * m + 1) ≥ 1 := pow_pos_base 2 (by decide) (2 * m + 1)
    omega
  have h2m2 : 2 ^ (2 * m + 2) = 2 ^ (2 * m + 1) * 2 := by rw [Nat.pow_succ]
  have hgrow_u1 := Nat.mul_le_mul_right u1 hgrow
  rw [Nat.mul_assoc (G + 1), show w1 + 2 * m + 1 = (2 * m + 1) + w1 by omega,
      Nat.pow_add 2 (2 * m + 1) w1, Nat.mul_assoc (2 ^ (2 * m + 1)) (2 ^ w1) u1] at hgrow_u1
  have hsplit_G : (G + 1) * (2 ^ (2 * m + 1) * (2 ^ w1 * u1)) =
      2 ^ (2 * m + 1) * (G * (2 ^ w1 * u1)) + 2 ^ (2 * m + 1) * (2 ^ w1 * u1) := by
    rw [Nat.add_mul G 1, Nat.one_mul, ← Nat.mul_assoc G (2 ^ (2 * m + 1)),
        Nat.mul_comm G (2 ^ (2 * m + 1)), Nat.mul_assoc]
  have hx1_le : G * (2 ^ w1 * u1 - 1) ≤ G * (2 ^ w1 * u1) := Nat.mul_le_mul_left G (by omega)
  have hm_le := Nat.mul_le_mul_left (2 ^ (2 * m + 1)) hx1_le
  apply Classical.byContradiction
  intro hnot
  have hm_bad := Nat.mul_le_mul_left (2 ^ (2 * m + 1)) (by omega : xEnd ≤ G * (2 ^ w1 * u1 - 1))
  omega

theorem pumping_core_witness_exists
    (A B s G xFloor : Nat)
    (hA : A ≥ 1) (hB : B ≥ 1) (hs : s ≥ 4) (hG : G ≥ 1) :
    ∃ x1 K xEnd : Nat,
      x1 > xFloor ∧ K ≥ s ∧ collatzIter K x1 = xEnd ∧
      x1 % 512 = 511 ∧ xEnd % 512 = 511 ∧
      x1 % 81 = 1 ∧ xEnd % 81 = 1 ∧
      xEnd % (2 ^ A * 3 ^ B) = x1 % (2 ^ A * 3 ^ B) ∧
      xEnd > G * x1 := by
  let _ := hA; let _ := hG
  let m := s - 1
  have hm_ge3 : m ≥ 3 := by omega
  let aEff := A + 9
  let bEff := B + 4
  let P := (2 * m + 1) + aEff
  rcases pumping_growth_exists G m (aEff + bEff + xFloor + 2) with ⟨w1, hw1_fl, hgrow, hw1_pow⟩
  have hw1_ge_a : w1 ≥ aEff := by omega
  have hw1_ge_b1 : w1 ≥ bEff + 1 := by omega
  let M2 := 2 ^ P
  let M3 := 3 ^ bEff
  have hM2_pos : M2 ≥ 1 := pow_pos_base 2 (by decide) P
  have hM3_ge3 : M3 ≥ 3 := by
    dsimp [M3]; rw [show bEff = (bEff - 1) + 1 by omega, Nat.pow_succ]
    have hp := pow_pos_base 3 (by decide) (bEff - 1); omega
  have hP_gt : M2 ≥ 2 ^ (2 * m + 2) := by
    dsimp [M2]
    have he : P = (2 * m + 2) + (aEff - 1) := by dsimp [P, aEff]; omega
    rw [he, Nat.pow_add]
    exact Nat.le_mul_of_pos_right _ (pow_pos_base 2 (by decide) _)
  let T2 := (M2 - 2 ^ (2 * m + 2)) + 3 ^ (m + 1)
  have hT2_add : T2 + 2 ^ (2 * m + 2) = M2 + 3 ^ (m + 1) := by dsimp [T2]; omega
  rcases bezout_pow3_pow2_campaign P (w1 + m) (by omega) with ⟨inv3, q3, _, _, _, hinv3⟩
  let r2 := inv3 * T2
  have hM3_mul : M3 * 3 ^ (m + 1) ≥ 3 ^ (m + 1) := by
    have hm1 := Nat.mul_le_mul_right (3 ^ (m + 1)) hM3_ge3; omega
  let T3 := (M3 * 3 ^ (m + 1) - 3 ^ (m + 1)) + 2 ^ (2 * m + 2)
  have hT3_add : T3 + 3 ^ (m + 1) = M3 * 3 ^ (m + 1) + 2 ^ (2 * m + 2) := by dsimp [T3]; omega
  rcases pow2_pos_inverse_mod_pow3 ((2 * m + 1) + w1) bEff (by omega) with ⟨inv2, q2, _, hinv2⟩
  let r3 := inv2 * T3
  rcases bezout_pow3_pow2_campaign P bEff (by omega) with ⟨c3, c2, _, _, _, hc32⟩
  rcases pow2_pos_inverse_mod_pow3 P bEff (by omega) with ⟨d2, qd2, _, hd2⟩
  rcases crt_combine_pos_identities r2 r3 M2 M3 c3 c2 d2 qd2
    hM2_pos (by omega) hc32 hd2 with ⟨hu1_pos, hu1_eq2, hu1_eq3⟩
  let u1 := r2 * (M3 * c3) + r3 * (M2 * d2) + M2 * M3
  let k2 := r2 * c2 + r3 * d2 + M3
  let k3 := r2 * c3 + r3 * qd2 + M2
  change u1 ≥ 1 at hu1_pos
  change u1 = r2 + M2 * k2 at hu1_eq2
  change u1 = r3 + M3 * k3 at hu1_eq3
  let Q2 := q3 * T2 + 1 + 3 ^ (w1 + m) * k2
  have hQ2_pos : Q2 ≥ 1 := by dsimp [Q2]; omega
  have hmain_eq : 3 ^ (w1 + m) * u1 + 2 ^ (2 * m + 2) = M2 * Q2 + 3 ^ (m + 1) := by
    have hr2_step : 3 ^ (w1 + m) * r2 + 2 ^ (2 * m + 2) = M2 * (q3 * T2 + 1) + 3 ^ (m + 1) := by
      dsimp [r2]
      rw [← Nat.mul_assoc (3 ^ (w1 + m)) inv3 T2, hinv3, Nat.add_mul, Nat.one_mul,
          Nat.mul_assoc M2 q3 T2, Nat.add_assoc, hT2_add, Nat.mul_add M2 (q3 * T2) 1,
          Nat.mul_one, Nat.add_assoc]
    rw [hu1_eq2, Nat.mul_add (3 ^ (w1 + m)) r2 (M2 * k2)]
    calc
      3 ^ (w1 + m) * r2 + 3 ^ (w1 + m) * (M2 * k2) + 2 ^ (2 * m + 2)
          = (3 ^ (w1 + m) * r2 + 2 ^ (2 * m + 2)) + M2 * (3 ^ (w1 + m) * k2) := by
            rw [← Nat.mul_assoc (3 ^ (w1 + m)) M2 k2, Nat.mul_comm (3 ^ (w1 + m)) M2,
                Nat.mul_assoc M2 (3 ^ (w1 + m)) k2]
            omega
      _ = M2 * Q2 + 3 ^ (m + 1) := by
            rw [hr2_step]; dsimp [Q2]
            rw [Nat.mul_add M2 (q3 * T2 + 1) (3 ^ (w1 + m) * k2)]
            omega
  have haEff_pos : 2 ^ aEff ≥ 4 := by
    have he : aEff = 2 + (aEff - 2) := by dsimp [aEff]; omega
    rw [he, Nat.pow_add]; have hp := pow_pos_base 2 (by decide) (aEff - 2); omega
  have h2aQ_ge4 : 2 ^ aEff * Q2 ≥ 4 := by have hm := Nat.mul_le_mul haEff_pos hQ2_pos; omega
  have hM2_split : M2 * Q2 = 2 ^ (2 * m + 1) * (2 ^ aEff * Q2) := by
    dsimp [M2, P]; rw [Nat.pow_add, Nat.mul_assoc]
  have h2m2_split : 2 ^ (2 * m + 2) = 2 ^ (2 * m + 1) * 2 := by rw [Nat.pow_succ]
  have h3w1u1_ge3 : 3 ^ w1 * u1 ≥ 3 := by
    have h3w1 : 3 ^ w1 ≥ 3 := by
      rw [show w1 = (w1 - 1) + 1 by omega, Nat.pow_succ]
      have hp := pow_pos_base 3 (by decide) (w1 - 1); omega
    have hm := Nat.mul_le_mul h3w1 hu1_pos; omega
  have hfactor : 3 ^ m * (3 ^ w1 * u1 - 3) = 2 ^ (2 * m + 1) * (2 ^ aEff * Q2 - 2) := by
    have hlhs : 3 ^ m * (3 ^ w1 * u1 - 3) + 3 ^ (m + 1) = 3 ^ (w1 + m) * u1 := by
      have hsub : (3 ^ w1 * u1 - 3) + 3 = 3 ^ w1 * u1 := by omega
      have h1 := congrArg (fun z => 3 ^ m * z) hsub
      rw [Nat.mul_add] at h1
      have h3m1 : 3 ^ m * 3 = 3 ^ (m + 1) := by rw [Nat.pow_succ]
      have h3wm : 3 ^ m * (3 ^ w1 * u1) = 3 ^ (w1 + m) * u1 := by
        rw [← Nat.mul_assoc, ← Nat.pow_add, Nat.add_comm m w1]
      rw [h3m1, h3wm] at h1; exact h1
    have hrhs : 2 ^ (2 * m + 1) * (2 ^ aEff * Q2 - 2) + 2 ^ (2 * m + 2) = M2 * Q2 := by
      rw [h2m2_split, ← Nat.mul_add, Nat.sub_add_cancel (by omega), ← hM2_split]
    omega
  have hdvd_2m1 : (3 ^ w1 * u1 - 3) % 2 ^ (2 * m + 1) = 0 := by
    apply coprime_pow3_dvd_pow2_cancel (2 * m + 1) m (3 ^ w1 * u1 - 3) (by omega)
    rw [hfactor, Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod]
  obtain ⟨t, ht_eq⟩ : ∃ t : Nat, 3 ^ w1 * u1 - 3 = 2 ^ (2 * m + 1) * t := by
    refine ⟨(3 ^ w1 * u1 - 3) / 2 ^ (2 * m + 1), ?_⟩
    have hdm := (Nat.div_add_mod (3 ^ w1 * u1 - 3) (2 ^ (2 * m + 1))).symm
    rw [hdvd_2m1, Nat.add_zero] at hdm; exact hdm
  have h3mt : 3 ^ m * t = 2 ^ aEff * Q2 - 2 := by
    have hf := hfactor
    rw [ht_eq, ← Nat.mul_assoc (3 ^ m) (2 ^ (2 * m + 1)) t,
        Nat.mul_comm (3 ^ m) (2 ^ (2 * m + 1)), Nat.mul_assoc] at hf
    have hp_pos : 2 ^ (2 * m + 1) > 0 := pow_pos_base 2 (by decide) (2 * m + 1)
    have hdiv := congrArg (fun z => z / 2 ^ (2 * m + 1)) hf
    rw [Nat.mul_comm (2 ^ (2 * m + 1)) (3 ^ m * t), Nat.mul_div_cancel _ hp_pos,
        Nat.mul_comm (2 ^ (2 * m + 1)) (2 ^ aEff * Q2 - 2), Nat.mul_div_cancel _ hp_pos] at hdiv
    exact hdiv
  have ht_pos : t ≥ 1 := by
    by_cases ht0 : t = 0
    · rw [ht0, Nat.mul_zero] at h3mt; omega
    · omega
  let x1 := 2 ^ w1 * u1 - 1
  let xEnd := 2 ^ aEff * Q2 - 1
  let K := (w1 + 1) + 2 * m
  have hiter_K : collatzIter K x1 = xEnd := by
    have hx_w1 : collatzIter w1 x1 = 2 * (4 ^ m * t + 1) := by
      dsimp [x1]; rw [odd_run_iter w1 u1 hu1_pos]
      have h2m1 : 2 ^ (2 * m + 1) * t = 2 * (4 ^ m * t) := by
        rw [pow4_eq_pow2_even m, Nat.pow_succ 2 (2 * m),
            Nat.mul_comm (2 ^ (2 * m)) 2, Nat.mul_assoc]
      omega
    have hx_w1_1 : collatzIter (w1 + 1) x1 = 4 ^ m * t + 1 := by
      have hs : collatzIter (w1 + 1) x1 = collatzStep (collatzIter w1 x1) :=
        collatzIter_add w1 1 x1
      rw [hs, hx_w1, collatzStep_of_even_nat _ (by omega)]; omega
    dsimp [K]
    rw [collatzIter_add (w1 + 1) (2 * m) x1, hx_w1_1, pair_11_chain_iter m t ht_pos]
    dsimp [xEnd]; omega
  have hx1_512 : x1 % 512 = 511 := by
    have he : w1 = 9 + (w1 - 9) := by dsimp [aEff] at hw1_ge_a; omega
    have hx1_eq : x1 = 512 * (2 ^ (w1 - 9) * u1 - 1) + 511 := by
      dsimp [x1]
      have hp : 2 ^ (w1 - 9) * u1 ≥ 1 := Nat.mul_le_mul (pow_pos_base 2 (by decide) _) hu1_pos
      have hmul : 2 ^ w1 * u1 = 512 * (2 ^ (w1 - 9) * u1) := by
        conv => lhs; rw [he, Nat.pow_add]
        rw [show (2 : Nat) ^ 9 = 512 from rfl, Nat.mul_assoc]
      omega
    rw [hx1_eq]; omega
  have hxEnd_512 : xEnd % 512 = 511 := by
    have he : aEff = 9 + A := by dsimp [aEff]; omega
    have hxE_eq : xEnd = 512 * (2 ^ A * Q2 - 1) + 511 := by
      dsimp [xEnd]
      have hp : 2 ^ A * Q2 ≥ 1 := Nat.mul_le_mul (pow_pos_base 2 (by decide) A) hQ2_pos
      have hmul : 2 ^ aEff * Q2 = 512 * (2 ^ A * Q2) := by
        conv => lhs; rw [he, Nat.pow_add]
        rw [show (2 : Nat) ^ 9 = 512 from rfl, Nat.mul_assoc]
      omega
    rw [hxE_eq]; omega
  have hx1_mod2A : x1 % 2 ^ A = 2 ^ A - 1 := by
    have he : w1 = A + (w1 - A) := by dsimp [aEff] at hw1_ge_a; omega
    have hpA : 2 ^ A ≥ 1 := pow_pos_base 2 (by decide) A
    have hq_pos : 2 ^ (w1 - A) * u1 ≥ 1 := Nat.mul_le_mul (pow_pos_base 2 (by decide) _) hu1_pos
    have hx1_eq : x1 = 2 ^ A * (2 ^ (w1 - A) * u1 - 1) + (2 ^ A - 1) := by
      dsimp [x1]
      have hmul : 2 ^ w1 * u1 = 2 ^ A * (2 ^ (w1 - A) * u1) := by
        conv => lhs; rw [he, Nat.pow_add]
        rw [Nat.mul_assoc]
      have hadd : (2 ^ A * (2 ^ (w1 - A) * u1 - 1) + (2 ^ A - 1)) + 1 = 2 ^ w1 * u1 := by
        calc
          (2 ^ A * (2 ^ (w1 - A) * u1 - 1) + (2 ^ A - 1)) + 1
              = 2 ^ A * (2 ^ (w1 - A) * u1 - 1) + 2 ^ A * 1 := by
                rw [Nat.add_assoc, Nat.sub_add_cancel hpA, Nat.mul_one]
          _ = 2 ^ A * ((2 ^ (w1 - A) * u1 - 1) + 1) := (Nat.mul_add _ _ _).symm
          _ = 2 ^ A * (2 ^ (w1 - A) * u1) := by rw [Nat.sub_add_cancel hq_pos]
          _ = 2 ^ w1 * u1 := hmul.symm
      omega
    rw [hx1_eq, Nat.add_mod, Nat.mul_mod (2 ^ A) _ (2 ^ A), Nat.mod_self,
        Nat.zero_mul, Nat.zero_mod, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt (by omega)]
  have hxEnd_mod2A : xEnd % 2 ^ A = 2 ^ A - 1 := by
    have he : aEff = A + 9 := rfl
    have hpA : 2 ^ A ≥ 1 := pow_pos_base 2 (by decide) A
    have hq_pos : 2 ^ 9 * Q2 ≥ 1 := Nat.mul_le_mul (by decide : 1 ≤ 2 ^ 9) hQ2_pos
    have hxE_eq : xEnd = 2 ^ A * (2 ^ 9 * Q2 - 1) + (2 ^ A - 1) := by
      dsimp [xEnd]
      have hmul : 2 ^ aEff * Q2 = 2 ^ A * (2 ^ 9 * Q2) := by rw [he, Nat.pow_add, Nat.mul_assoc]
      have hadd : (2 ^ A * (2 ^ 9 * Q2 - 1) + (2 ^ A - 1)) + 1 = 2 ^ aEff * Q2 := by
        calc
          (2 ^ A * (2 ^ 9 * Q2 - 1) + (2 ^ A - 1)) + 1
              = 2 ^ A * (2 ^ 9 * Q2 - 1) + 2 ^ A * 1 := by
                rw [Nat.add_assoc, Nat.sub_add_cancel hpA, Nat.mul_one]
          _ = 2 ^ A * ((2 ^ 9 * Q2 - 1) + 1) := (Nat.mul_add _ _ _).symm
          _ = 2 ^ A * (2 ^ 9 * Q2) := by rw [Nat.sub_add_cancel hq_pos]
          _ = 2 ^ aEff * Q2 := hmul.symm
      rw [← hadd, Nat.add_sub_cancel]
    rw [hxE_eq, Nat.add_mod, Nat.mul_mod (2 ^ A) _ (2 ^ A), Nat.mod_self,
        Nat.zero_mul, Nat.zero_mod, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt (by omega)]
  have hx_rel_end : 2 ^ (2 * m + 1) * xEnd + 3 ^ (m + 1) + 2 ^ (2 * m + 1) =
      3 ^ (w1 + m) * u1 + 2 ^ (2 * m + 2) := by
    have h1 : 2 ^ (2 * m + 1) * xEnd + 2 ^ (2 * m + 1) = M2 * Q2 := by
      dsimp [xEnd]
      calc
        2 ^ (2 * m + 1) * (2 ^ aEff * Q2 - 1) + 2 ^ (2 * m + 1)
            = 2 ^ (2 * m + 1) * ((2 ^ aEff * Q2 - 1) + 1) :=
              (Nat.mul_succ (2 ^ (2 * m + 1)) (2 ^ aEff * Q2 - 1)).symm
        _ = 2 ^ (2 * m + 1) * (2 ^ aEff * Q2) := by rw [Nat.sub_add_cancel (by omega)]
        _ = M2 * Q2 := hM2_split.symm
    omega
  have h3wm_div_M3 : (3 ^ (w1 + m) * u1) % M3 = 0 := by
    dsimp [M3]
    have he : w1 + m = bEff + (w1 + m - bEff) := by omega
    rw [he, Nat.pow_add, Nat.mul_assoc, Nat.mul_mod (3 ^ bEff), Nat.mod_self, Nat.zero_mul, Nat.zero_mod]
  have hxEnd_M3_lhs : (2 ^ (2 * m + 1) * xEnd + 3 ^ (m + 1) + 2 ^ (2 * m + 1)) % M3 =
      2 ^ (2 * m + 2) % M3 := by
    rw [hx_rel_end, Nat.add_mod, h3wm_div_M3, Nat.zero_add, Nat.mod_mod]
  have hx1_M3_lhs : (2 ^ (2 * m + 1) * x1 + 3 ^ (m + 1) + 2 ^ (2 * m + 1)) % M3 =
      2 ^ (2 * m + 2) % M3 := by
    have hx1_mul : 2 ^ (2 * m + 1) * x1 + 2 ^ (2 * m + 1) = 2 ^ ((2 * m + 1) + w1) * u1 := by
      dsimp [x1]
      have hp : 2 ^ w1 * u1 ≥ 1 := Nat.mul_le_mul (pow_pos_base 2 (by decide) w1) hu1_pos
      calc
        2 ^ (2 * m + 1) * (2 ^ w1 * u1 - 1) + 2 ^ (2 * m + 1)
            = 2 ^ (2 * m + 1) * ((2 ^ w1 * u1 - 1) + 1) :=
              (Nat.mul_succ (2 ^ (2 * m + 1)) (2 ^ w1 * u1 - 1)).symm
        _ = 2 ^ (2 * m + 1) * (2 ^ w1 * u1) := by rw [Nat.sub_add_cancel hp]
        _ = 2 ^ ((2 * m + 1) + w1) * u1 := by
              rw [Nat.pow_add (2 : Nat) (2 * m + 1) w1, Nat.mul_assoc]
    have hsum1 : 2 ^ (2 * m + 1) * x1 + 3 ^ (m + 1) + 2 ^ (2 * m + 1) =
        2 ^ ((2 * m + 1) + w1) * u1 + 3 ^ (m + 1) := by omega
    rw [hsum1, hu1_eq3, Nat.mul_add]
    have hr3_mod : (2 ^ ((2 * m + 1) + w1) * r3 + 3 ^ (m + 1)) % M3 = 2 ^ (2 * m + 2) % M3 := by
      dsimp [r3]
      rw [← Nat.mul_assoc, hinv2, Nat.add_mul, Nat.one_mul, Nat.add_assoc, hT3_add]
      have hcomb : M3 * q2 * T3 + (M3 * 3 ^ (m + 1) + 2 ^ (2 * m + 2)) =
          M3 * (q2 * T3 + 3 ^ (m + 1)) + 2 ^ (2 * m + 2) := by
        rw [Nat.mul_assoc M3 q2 T3, ← Nat.add_assoc, ← Nat.mul_add M3]
      rw [hcomb, Nat.add_mod, Nat.mul_mod M3 _ M3, Nat.mod_self,
          Nat.zero_mul, Nat.zero_mod, Nat.zero_add, Nat.mod_mod]
    have hmul_M3 : 2 ^ ((2 * m + 1) + w1) * (M3 * k3) = M3 * (2 ^ ((2 * m + 1) + w1) * k3) := by
      rw [← Nat.mul_assoc, Nat.mul_comm _ M3, Nat.mul_assoc]
    have htot : 2 ^ ((2 * m + 1) + w1) * r3 + 2 ^ ((2 * m + 1) + w1) * (M3 * k3) + 3 ^ (m + 1) =
        (2 ^ ((2 * m + 1) + w1) * r3 + 3 ^ (m + 1)) + M3 * (2 ^ ((2 * m + 1) + w1) * k3) := by
      rw [hmul_M3]; omega
    rw [htot, Nat.add_mod, Nat.mul_mod M3 _ M3, Nat.mod_self,
        Nat.zero_mul, Nat.zero_mod, Nat.add_zero, Nat.mod_mod, hr3_mod]
  have h2m1_eq_M3 : (2 ^ (2 * m + 1) * xEnd) % M3 = (2 ^ (2 * m + 1) * x1) % M3 := by
    let C := 3 ^ (m + 1) + 2 ^ (2 * m + 1)
    let pad := M3 * C - C
    have hpad : C + pad = M3 * C := by dsimp [pad]; have hm := Nat.mul_le_mul_right C hM3_ge3; omega
    have hcancel : ∀ z : Nat, ((z + C) % M3 + pad) % M3 = z % M3 := by
      intro z
      rw [Nat.mod_add_mod, Nat.add_assoc, hpad, Nat.add_mod,
          Nat.mul_mod M3 C M3, Nat.mod_self, Nat.zero_mul, Nat.zero_mod, Nat.add_zero, Nat.mod_mod]
    have heq_sum : (2 ^ (2 * m + 1) * xEnd + C) % M3 = (2 ^ (2 * m + 1) * x1 + C) % M3 := by
      dsimp [C]; rw [← Nat.add_assoc, hxEnd_M3_lhs, ← Nat.add_assoc, hx1_M3_lhs]
    simpa only [hcancel] using congrArg (fun t => (t + pad) % M3) heq_sum
  have hx_eq_M3 : xEnd % M3 = x1 % M3 :=
    coprime_pow2_cancel_pow3 (2 * m + 1) bEff xEnd x1 (by omega) h2m1_eq_M3
  have hx_eq_3B : xEnd % 3 ^ B = x1 % 3 ^ B := by
    have hm_factor : M3 = 3 ^ B * 81 := by dsimp [M3, bEff]; rw [Nat.pow_add]
    rw [← mod_mul_mod_eq xEnd (3 ^ B) 81, ← mod_mul_mod_eq x1 (3 ^ B) 81, ← hm_factor, hx_eq_M3]
  have hxEnd_81 : xEnd % 81 = 1 := by
    have hm1_81 : 3 ^ (m + 1) % 81 = 0 := by
      have he : m + 1 = 4 + (m - 3) := by omega
      rw [he, Nat.pow_add, show (3 : Nat) ^ 4 = 81 from rfl,
          Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod]
    have h3wm_81 : (3 ^ (w1 + m) * u1) % 81 = 0 := by
      have he : w1 + m = 4 + (w1 + m - 4) := by omega
      rw [he, Nat.pow_add, show (3 : Nat) ^ 4 = 81 from rfl,
          Nat.mul_assoc, Nat.mul_mod, Nat.mod_self, Nat.zero_mul, Nat.zero_mod]
    have hlhs81 : (2 ^ (2 * m + 1) * xEnd + 3 ^ (m + 1) + 2 ^ (2 * m + 1)) % 81 =
        (2 ^ (2 * m + 1) * 1 + 2 ^ (2 * m + 1)) % 81 := by
      rw [hx_rel_end, Nat.add_mod, h3wm_81, Nat.zero_add, Nat.mod_mod,
          Nat.mul_one, Nat.pow_succ 2 (2 * m + 1)]
      omega
    have hlhs81_simp : (2 ^ (2 * m + 1) * xEnd + 2 ^ (2 * m + 1)) % 81 =
        (2 ^ (2 * m + 1) * xEnd + 3 ^ (m + 1) + 2 ^ (2 * m + 1)) % 81 := by
      have hcomm : 2 ^ (2 * m + 1) * xEnd + 3 ^ (m + 1) + 2 ^ (2 * m + 1) =
          (2 ^ (2 * m + 1) * xEnd + 2 ^ (2 * m + 1)) + 3 ^ (m + 1) := by omega
      rw [hcomm, Nat.add_mod (2 ^ (2 * m + 1) * xEnd + 2 ^ (2 * m + 1)) (3 ^ (m + 1)) 81, hm1_81]
      omega
    rw [← hlhs81_simp] at hlhs81
    let C81 := 2 ^ (2 * m + 1)
    let pad81 := 81 * C81 - C81
    have hp81 : C81 + pad81 = 81 * C81 := by dsimp [pad81]; omega
    have hcan81 : ∀ z : Nat, ((z + C81) % 81 + pad81) % 81 = z % 81 := by
      intro z
      rw [Nat.mod_add_mod, Nat.add_assoc, hp81, Nat.add_mod,
          Nat.mul_mod 81 C81 81, Nat.mod_self, Nat.zero_mul, Nat.zero_mod, Nat.add_zero, Nat.mod_mod]
    have hc := congrArg (fun t => (t + pad81) % 81) hlhs81
    rw [hcan81, hcan81] at hc
    exact coprime_pow2_cancel_mod81 (2 * m + 1) xEnd 1 hc
  have hx1_81 : x1 % 81 = 1 := by
    have hm_factor : M3 = 81 * 3 ^ B := by
      dsimp [M3, bEff]; rw [show B + 4 = 4 + B by omega, Nat.pow_add]
    rw [← mod_mul_mod_eq x1 81 (3 ^ B), ← hm_factor, ← hx_eq_M3, hm_factor,
        mod_mul_mod_eq xEnd 81 (3 ^ B), hxEnd_81]
  have hx_grow : xEnd > G * x1 :=
    pumping_archimedean_step G m w1 u1 xEnd (by dsimp [aEff] at hw1_ge_a; omega) hu1_pos hgrow hx_rel_end
  have hx1_floor : x1 > xFloor := by
    dsimp [x1]; have hm := Nat.mul_le_mul_left (2 ^ w1) hu1_pos; omega
  refine ⟨x1, K, xEnd, hx1_floor, by dsimp [K, m]; omega, hiter_K,
    hx1_512, hxEnd_512, hx1_81, hxEnd_81,
    crt_pow2_pow3_unique A B xEnd x1 hB (by rw [hxEnd_mod2A, hx1_mod2A]) hx_eq_3B,
    hx_grow⟩

/--
  Theorem T2.2a (Universal All-Horizon Mixed-Base Self-Congruent Syracuse Pumping Obstruction):
  For ALL `A ≥ 1, B ≥ 1, s ≥ 4, G ≥ 1, xFloor : Nat`, there exists a trajectory segment
  `collatzIter K x1 = xEnd` (`K ≥ s`, `x1 > xFloor`) whose start and end BOTH survive inside
  `IsSurvivingMod373248Class` (hence also `Mod46656`, `Mod5184`, `Mod1296`), achieve exact
  mixed-base modular self-return `xEnd % (2^A * 3^B) = x1 % (2^A * 3^B)`, and satisfy `xEnd > G * x1`!
-/
theorem self_congruent_syracuse_pumping_obstruction
    (A B s G xFloor : Nat)
    (hA : A ≥ 1) (hB : B ≥ 1) (hs : s ≥ 4) (hG : G ≥ 1) :
    ∃ x1 K xEnd : Nat,
      x1 > xFloor ∧
      K ≥ s ∧
      collatzIter K x1 = xEnd ∧
      IsSurvivingMod1296Class x1 ∧
      IsSurvivingMod5184Class x1 ∧
      IsSurvivingMod46656Class x1 ∧
      IsSurvivingMod373248Class x1 ∧
      IsSurvivingMod373248Class xEnd ∧
      xEnd % (2 ^ A * 3 ^ B) = x1 % (2 ^ A * 3 ^ B) ∧
      xEnd > G * x1 := by
  rcases pumping_core_witness_exists A B s G xFloor hA hB hs hG with
    ⟨x1, K, xEnd, hx_fl, hK, hiter, h512_1, h512_E, h81_1, h81_E, hcrt, hgrow⟩
  rcases surviving_mod373248_of_mod512_511_mod81_1 x1 h512_1 h81_1 with ⟨hs5184, hs46656, hs373_1⟩
  rcases surviving_mod373248_of_mod512_511_mod81_1 xEnd h512_E h81_E with ⟨_, _, hs373_E⟩
  exact ⟨x1, K, xEnd, hx_fl, hK, hiter,
    (survivingMod5184_imp_mod1296 x1 hs5184).1, hs5184, hs46656, hs373_1, hs373_E, hcrt, hgrow⟩

/--
  Theorem T2.2b (Universal Impossibility of Monotone Per-Residue `(2^A * 3^B)` Lyapunov Potentials):
  NO function `Φ : Nat -> Nat -> Int` that is residue-wise non-decreasing above `xFloor`
  (covering every modular-log and shifted-log `α_r log(x + c_r) + β_r` potential) can strictly
  decrease across `s ≥ 4` Syracuse blocks even when restricted to `IsSurvivingMod373248Class`!
-/
theorem no_monotone_per_residue_lyapunov_potential
    (A B s xFloor : Nat)
    (Phi : Nat -> Nat -> Int)
    (hA : A ≥ 1) (hB : B ≥ 1) (hs : s ≥ 4)
    (hMono : ∀ x y : Nat, x > xFloor -> x ≤ y ->
      Phi y (x % (2 ^ A * 3 ^ B)) ≥ Phi x (x % (2 ^ A * 3 ^ B)))
    (hDec : ∀ x K : Nat, x > xFloor -> IsSurvivingMod373248Class x -> K ≥ s ->
      collatzIter K x > x ->
      Phi (collatzIter K x) ((collatzIter K x) % (2 ^ A * 3 ^ B)) <
        Phi x (x % (2 ^ A * 3 ^ B))) :
    False := by
  rcases self_congruent_syracuse_pumping_obstruction A B s 1 xFloor hA hB hs (by decide) with
    ⟨x1, K, xEnd, hx_fl, hK, hiter, _, _, _, hs373, _, hcrt, hgrow⟩
  rw [Nat.one_mul] at hgrow
  have hlt := hDec x1 K hx_fl hs373 hK (by rw [hiter]; exact hgrow)
  rw [hiter, hcrt] at hlt
  have hge := hMono x1 xEnd hx_fl (by omega)
  omega

-- ============================================================================
-- SECTION 6: Track 1 Wave 2 — Mod-24 Determinant Gap, 2-Adic LTE Squeeze,
--            First-Block Discreteness Dichotomy, & Mod-96 Brox Equivalence
--            (`#14/#16`: `T5`–`T8`, Zero Custom Axioms `[]`)
-- ============================================================================

-- ----------------------------------------------------------------------------
-- T5: Levi ben Gerson Mod-24 Determinant Gap (`2^K - 3^W` for `K ≥ 3, W ≥ 1`)
-- ----------------------------------------------------------------------------

theorem pow2_ge3_mod24 : ∀ m : Nat, 2 ^ (m + 3) % 24 = 8 ∨ 2 ^ (m + 3) % 24 = 16
  | 0 => Or.inl rfl
  | m + 1 => by
    rw [show m + 1 + 3 = (m + 3) + 1 by omega, Nat.pow_succ, Nat.mul_mod]
    rcases pow2_ge3_mod24 m with h | h <;> rw [h] <;> decide

theorem pow3_ge1_mod24 : ∀ m : Nat, 3 ^ (m + 1) % 24 = 3 ∨ 3 ^ (m + 1) % 24 = 9
  | 0 => Or.inl rfl
  | m + 1 => by
    rw [Nat.pow_succ, Nat.mul_mod]
    rcases pow3_ge1_mod24 m with h | h <;> rw [h] <;> decide

theorem sub_mod24_four_classes (D A B : Nat)
    (hadd : D + B = A)
    (hA : A % 24 = 8 ∨ A % 24 = 16)
    (hB : B % 24 = 3 ∨ B % 24 = 9) :
    (D % 24 = 5 ∨ D % 24 = 7 ∨ D % 24 = 13 ∨ D % 24 = 23) ∧ D ≥ 5 := by
  let d := D % 24
  have hd_lt : d < 24 := Nat.mod_lt D (by decide)
  have hd_le : d ≤ D := Nat.mod_le D 24
  have hmod : (d + B % 24) % 24 = A % 24 := by
    dsimp [d]; rw [← Nat.add_mod, hadd]
  rcases hA with ha | ha <;> rcases hB with hb | hb <;> rw [ha, hb] at hmod
  · have hd5 : d = 5 := by omega
    exact ⟨Or.inl hd5, by omega⟩
  · have hd23 : d = 23 := by omega
    exact ⟨Or.inr (Or.inr (Or.inr hd23)), by omega⟩
  · have hd13 : d = 13 := by omega
    exact ⟨Or.inr (Or.inr (Or.inl hd13)), by omega⟩
  · have hd7 : d = 7 := by omega
    exact ⟨Or.inr (Or.inl hd7), by omega⟩

/--
  Theorem T5 (Levi ben Gerson Mod-24 Determinant Gap):
  For ALL `K ≥ 3` and `W ≥ 1` with `3^W < 2^K`, `D := 2^K - 3^W` satisfies
  `D % 24 ∈ {5, 7, 13, 23}` and `D ≥ 5` (eliminating `2^K - 3^W = 1` universally for `K ≥ 3`).
-/
theorem pow2_sub_pow3_mod24_in_4_classes (K W : Nat)
    (hK : K ≥ 3) (hW : W ≥ 1) (hgt : 3 ^ W < 2 ^ K) :
    let D := 2 ^ K - 3 ^ W
    (D % 24 = 5 ∨ D % 24 = 7 ∨ D % 24 = 13 ∨ D % 24 = 23) ∧ D ≥ 5 := by
  dsimp only
  have hA : 2 ^ K % 24 = 8 ∨ 2 ^ K % 24 = 16 := by
    rw [show K = (K - 3) + 3 by omega]; exact pow2_ge3_mod24 (K - 3)
  have hB : 3 ^ W % 24 = 3 ∨ 3 ^ W % 24 = 9 := by
    rw [show W = (W - 1) + 1 by omega]; exact pow3_ge1_mod24 (W - 1)
  exact sub_mod24_four_classes (2 ^ K - 3 ^ W) (2 ^ K) (3 ^ W) (by omega) hA hB

-- ----------------------------------------------------------------------------
-- T6: Universal 2-Adic LTE Bound & Elimination of All `q0 = 1` Mersenne 1-Cycles
-- ----------------------------------------------------------------------------

theorem pow3_odd_mod8 : ∀ k : Nat, 3 ^ (2 * k + 1) % 8 = 3
  | 0 => rfl
  | k + 1 => by
    rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 2 by omega, Nat.pow_add, Nat.mul_mod, pow3_odd_mod8 k]

theorem pow2_dvd_mul_odd_cancel : ∀ (a X Y : Nat),
    Y % 2 = 1 -> 2 ^ a ∣ X * Y -> 2 ^ a ∣ X
  | 0, X, _, _, _ => ⟨X, by simp⟩
  | a + 1, X, Y, hY, ⟨k, hk⟩ => by
    have hprod_ev : (X * Y) % 2 = 0 := by
      rw [hk, Nat.pow_succ, Nat.mul_comm (2 ^ a) 2, Nat.mul_assoc]; omega
    have hX_ev : X % 2 = 0 := by
      rw [Nat.mul_mod, hY] at hprod_ev; omega
    obtain ⟨xHalf, rfl⟩ : ∃ xHalf : Nat, X = 2 * xHalf := ⟨X / 2, by omega⟩
    have hk' : xHalf * Y = 2 ^ a * k := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ a) 2, Nat.mul_assoc] at hk
      rw [Nat.mul_assoc] at hk; omega
    rcases pow2_dvd_mul_odd_cancel a xHalf Y hY ⟨k, hk'⟩ with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rw [ht, Nat.pow_succ, Nat.mul_comm (2 ^ a) 2, Nat.mul_assoc]

theorem sq_sub_one_nat (X : Nat) (hX : X ≥ 1) :
    X * X - 1 = (X - 1) * (X + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m : Nat, X = m + 1 := ⟨X - 1, by omega⟩
  have h1 : (m + 1) * (m + 1) = m * (m + 2) + 1 := by
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.mul_one, Nat.mul_add]
    omega
  simp [h1]

theorem pow2_dvd_pow3_sub_one_aux : ∀ (fuel w a : Nat),
    w ≥ 1 -> w ≤ fuel -> 2 ^ a ∣ (3 ^ w - 1) -> 2 ^ a ≤ 4 * w
  | 0, w, _, hw, hle, _ => by omega
  | fuel + 1, w, a, hw, hle, hdvd => by
    by_cases hw_ev : w % 2 = 0
    · obtain ⟨m, rfl⟩ : ∃ m : Nat, w = 2 * m := ⟨w / 2, by omega⟩
      have hm_ge1 : m ≥ 1 := by omega
      have hsq : 3 ^ (2 * m) - 1 = (3 ^ m - 1) * (3 ^ m + 1) := by
        rw [show 2 * m = m + m by omega, Nat.pow_add]
        exact sq_sub_one_nat (3 ^ m) (pow3_pos_nat m)
      rw [hsq] at hdvd
      by_cases hm_ev : m % 2 = 0
      · have hm4 := pow3_mod4_nat m
        have hb : (m % 2 == 0) = true := decide_eq_true hm_ev
        rw [hb] at hm4
        simp only [ite_true] at hm4
        have hp1_mod4 : (3 ^ m + 1) % 4 = 2 := by omega
        obtain ⟨yOdd, hy_eq, hy_odd⟩ : ∃ yOdd : Nat, 3 ^ m + 1 = 2 * yOdd ∧ yOdd % 2 = 1 :=
          ⟨(3 ^ m + 1) / 2, by omega, by omega⟩
        have hrew : (3 ^ m - 1) * (3 ^ m + 1) = (2 * (3 ^ m - 1)) * yOdd := by
          rw [hy_eq, ← Nat.mul_assoc, Nat.mul_comm (3 ^ m - 1) 2, Nat.mul_assoc]
        rw [hrew] at hdvd
        have hdvd2 := pow2_dvd_mul_odd_cancel a (2 * (3 ^ m - 1)) yOdd hy_odd hdvd
        cases a with
        | zero => simp; omega
        | succ b =>
          rcases hdvd2 with ⟨t, ht⟩
          have hdvd_b : 2 ^ b ∣ (3 ^ m - 1) := by
            refine ⟨t, ?_⟩
            rw [Nat.pow_succ, Nat.mul_comm (2 ^ b) 2, Nat.mul_assoc] at ht
            omega
          have ih := pow2_dvd_pow3_sub_one_aux fuel m b hm_ge1 (by omega) hdvd_b
          rw [Nat.pow_succ]; omega
      · obtain ⟨j, rfl⟩ : ∃ j : Nat, m = 2 * j + 1 := ⟨m / 2, by omega⟩
        have hm8 := pow3_odd_mod8 j
        have hp3_ge3 : 3 ^ (2 * j + 1) ≥ 3 := by
          rw [Nat.pow_succ]; have hp := pow3_pos_nat (2 * j); omega
        obtain ⟨y1, hy1_eq, hy1_odd⟩ :
            ∃ y1 : Nat, 3 ^ (2 * j + 1) - 1 = 2 * y1 ∧ y1 % 2 = 1 :=
          ⟨(3 ^ (2 * j + 1) - 1) / 2, by omega, by omega⟩
        obtain ⟨y2, hy2_eq, hy2_odd⟩ :
            ∃ y2 : Nat, 3 ^ (2 * j + 1) + 1 = 4 * y2 ∧ y2 % 2 = 1 :=
          ⟨(3 ^ (2 * j + 1) + 1) / 4, by omega, by omega⟩
        have hrew : (3 ^ (2 * j + 1) - 1) * (3 ^ (2 * j + 1) + 1) = 8 * (y1 * y2) := by
          rw [hy1_eq, hy2_eq]
          calc
            (2 * y1) * (4 * y2) = 2 * (y1 * (4 * y2)) := Nat.mul_assoc 2 y1 (4 * y2)
            _ = 2 * (4 * (y1 * y2)) := by
              rw [← Nat.mul_assoc y1 4 y2, Nat.mul_comm y1 4, Nat.mul_assoc 4 y1 y2]
            _ = 8 * (y1 * y2) := (Nat.mul_assoc 2 4 (y1 * y2)).symm
        rw [hrew] at hdvd
        have hy12_odd : (y1 * y2) % 2 = 1 := by rw [Nat.mul_mod, hy1_odd, hy2_odd]
        have hdvd8 := pow2_dvd_mul_odd_cancel a 8 (y1 * y2) hy12_odd hdvd
        have hle8 : 2 ^ a ≤ 8 := Nat.le_of_dvd (by decide) hdvd8
        omega
    · have hm4 := pow3_mod4_nat w
      have hb : (w % 2 == 0) = false := decide_eq_false hw_ev
      rw [hb] at hm4
      simp only [Bool.false_eq_true, ite_false] at hm4
      have hp3_pos := pow3_pos_nat w
      obtain ⟨yOdd, hy_eq, hy_odd⟩ : ∃ yOdd : Nat, 3 ^ w - 1 = 2 * yOdd ∧ yOdd % 2 = 1 :=
        ⟨(3 ^ w - 1) / 2, by omega, by omega⟩
      rw [hy_eq] at hdvd
      have hdvd2 := pow2_dvd_mul_odd_cancel a 2 yOdd hy_odd hdvd
      have hle2 : 2 ^ a ≤ 2 := Nat.le_of_dvd (by decide) hdvd2
      omega

/--
  Theorem T6a (Universal 2-Adic Lifting-the-Exponent Upper Bound):
  For ALL `w ≥ 1` and `a : Nat`, `2^a ∣ (3^w - 1) -> 2^a ≤ 4 * w` (sharp at every `w = 2^k`, `k ≥ 1`).
-/
theorem pow2_dvd_pow3_sub_one_le_four_mul :
    ∀ (w a : Nat), w ≥ 1 -> 2 ^ a ∣ (3 ^ w - 1) -> 2 ^ a ≤ 4 * w :=
  fun w a hw hdvd => pow2_dvd_pow3_sub_one_aux w w a hw (Nat.le_refl w) hdvd

theorem broxOddCarry_replicate_false : ∀ c : Nat,
    broxOddCarry (List.replicate c false) = 2 ^ (c + 1) - 1
  | 0 => rfl
  | c + 1 => by
    simp only [List.replicate_succ, broxOddCarry, parityWeight_replicate_false, Nat.pow_zero]
    rw [broxOddCarry_replicate_false c]
    have hp : 2 ^ (c + 1) ≥ 1 := pow2_pos_nat (c + 1)
    have h2 : 2 ^ (c + 1 + 1) = 2 * 2 ^ (c + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
    omega

theorem pow2_even_mod3_local : ∀ j : Nat, 2 ^ (2 * j) % 3 = 1
  | 0 => rfl
  | j + 1 => by
    rw [show 2 * (j + 1) = 2 * j + 2 by omega, Nat.pow_add, Nat.mul_mod, pow2_even_mod3_local j]

/--
  Theorem T6b (1-Block Cycle Binary-Prefix Squeeze & Unconditional Elimination of `q0 = 1`):
  In any hypothetical positive 1-block cycle `(2^(w1 + a1) - 3^w1) * q0 = 2^a1 - 1` (`w1 ≥ 2`),
  `3^w1 / 2^a1 = 2^w1 - 1` (`3^w1` begins with `w1` leading `1` bits in binary) and `q0 ≥ 3`
  (eliminating all Mersenne `x0 = 2^w1 - 1` 1-cycles with zero transcendental bounds).
-/
theorem one_block_cycle_binary_squeeze_and_q0_ge_three (w1 c q0 : Nat)
    (hw1 : w1 ≥ 2) (hq0 : q0 ≥ 1) (hq0_odd : q0 % 2 = 1)
    (hgt : 3 ^ w1 < 2 ^ (w1 + 1 + c))
    (hbrox : (2 ^ (w1 + 1 + c) - 3 ^ w1) * q0 = broxOddCarry (List.replicate c false)) :
    let a1 := c + 1
    broxOddCarry (List.replicate c false) = 2 ^ a1 - 1 ∧
    (3 ^ w1) / (2 ^ a1) = 2 ^ w1 - 1 ∧
    q0 ≠ 1 ∧ q0 ≥ 3 ∧
    3 * (2 ^ (w1 + a1) - 3 ^ w1) ≤ 2 ^ a1 - 1 := by
  dsimp only
  let a1 := c + 1
  have hexp : w1 + 1 + c = w1 + a1 := by dsimp [a1]; omega
  have hrep := broxOddCarry_replicate_false c
  change broxOddCarry (List.replicate c false) = 2 ^ a1 - 1 at hrep
  rw [hexp, hrep] at hbrox
  rw [hexp] at hgt
  let D := 2 ^ (w1 + a1) - 3 ^ w1
  have hD_pos : D ≥ 1 := by dsimp [D]; omega
  have hD_le : D ≤ 2 ^ a1 - 1 := by
    have hm : D * 1 ≤ D * q0 := Nat.mul_le_mul_left D hq0
    dsimp [D] at hm; omega
  have hp_a1 : 2 ^ a1 ≥ 2 := by
    dsimp [a1]; rw [Nat.pow_succ]; have hp := pow2_pos_nat c; omega
  have hp_w1 : 2 ^ w1 ≥ 4 := by
    have hm := pow2_mono_nat hw1; simpa using hm
  have h2wa_split : 2 ^ (w1 + a1) = 2 ^ a1 * (2 ^ w1 - 1) + 2 ^ a1 := by
    calc
      2 ^ (w1 + a1) = 2 ^ a1 * 2 ^ w1 := by rw [Nat.pow_add, Nat.mul_comm]
      _ = 2 ^ a1 * ((2 ^ w1 - 1) + 1) := by rw [Nat.sub_add_cancel (by omega)]
      _ = 2 ^ a1 * (2 ^ w1 - 1) + 2 ^ a1 := by rw [Nat.mul_add, Nat.mul_one]
  have h3w_decomp : 3 ^ w1 = 2 ^ a1 * (2 ^ w1 - 1) + (2 ^ a1 - D) := by
    have hadd : D + 3 ^ w1 = 2 ^ (w1 + a1) := by dsimp [D]; omega
    omega
  have hdiv_eq : (3 ^ w1) / (2 ^ a1) = 2 ^ w1 - 1 := by
    have hdm := div_mod_of_mul_add_lt (2 ^ a1) (2 ^ w1 - 1) (2 ^ a1 - D) (by omega)
    rw [← h3w_decomp] at hdm
    exact hdm.2
  have hq0_ne1 : q0 ≠ 1 := by
    intro hq1
    subst hq1
    rw [Nat.mul_one] at hbrox
    have hfactor : 3 ^ w1 - 1 = 2 ^ a1 * (2 ^ w1 - 1) := by omega
    by_cases hw_ev : w1 % 2 = 0
    · obtain ⟨k, rfl⟩ : ∃ k : Nat, w1 = 2 * k := ⟨w1 / 2, by omega⟩
      have hk_ge1 : k ≥ 1 := by omega
      have h2_mod3 : 2 ^ (2 * k) % 3 = 1 := pow2_even_mod3_local k
      have hrhs_mod3 : (2 ^ a1 * (2 ^ (2 * k) - 1)) % 3 = 0 := by
        have hm0 : (2 ^ (2 * k) - 1) % 3 = 0 := by omega
        rw [Nat.mul_mod, hm0, Nat.mul_zero, Nat.zero_mod]
      have h3_mod3 : 3 ^ (2 * k) % 3 = 0 := by
        rw [show 2 * k = (2 * k - 1) + 1 by omega, Nat.pow_succ, Nat.mul_mod]; simp
      have hp3_ge3 : 3 ^ (2 * k) ≥ 3 := by
        rw [show 2 * k = (2 * k - 1) + 1 by omega, Nat.pow_succ]
        have hp := pow3_pos_nat (2 * k - 1); omega
      have hlhs_mod3 : (3 ^ (2 * k) - 1) % 3 = 2 := by omega
      rw [hfactor] at hlhs_mod3
      omega
    · have hm4 := pow3_mod4_nat w1
      have hb : (w1 % 2 == 0) = false := decide_eq_false hw_ev
      rw [hb] at hm4
      simp only [Bool.false_eq_true, ite_false] at hm4
      have hp3_pos := pow3_pos_nat w1
      have hlhs_mod4 : (3 ^ w1 - 1) % 4 = 2 := by omega
      by_cases ha_ge2 : a1 ≥ 2
      · have h2a_mod4 : 2 ^ a1 % 4 = 0 := by
          rw [show a1 = (a1 - 2) + 2 by omega, Nat.pow_add, Nat.mul_mod]; simp
        have hrhs_mod4 : (2 ^ a1 * (2 ^ w1 - 1)) % 4 = 0 := by
          rw [Nat.mul_mod, h2a_mod4, Nat.zero_mul, Nat.zero_mod]
        rw [hfactor] at hlhs_mod4
        omega
      · have ha1_eq1 : a1 = 1 := by dsimp [a1] at ha_ge2 ⊢; omega
        rw [ha1_eq1] at hgt
        have hlt := pow2_succ_lt_pow3 w1 hw1
        omega
  have hq0_ge3 : q0 ≥ 3 := by omega
  have h3D : 3 * (2 ^ (w1 + a1) - 3 ^ w1) ≤ 2 ^ a1 - 1 := by
    have hm : 3 * (2 ^ (w1 + a1) - 3 ^ w1) ≤ q0 * (2 ^ (w1 + a1) - 3 ^ w1) :=
      Nat.mul_le_mul_right _ hq0_ge3
    rw [Nat.mul_comm q0] at hm
    omega
  exact ⟨hrep, hdiv_eq, hq0_ne1, hq0_ge3, h3D⟩

-- ----------------------------------------------------------------------------
-- T7: Trailing-`false` Brox Split & Integer-Discreteness First-Block Dichotomy
-- ----------------------------------------------------------------------------

theorem parityWeight_append_false (u : List Bool) :
    parityWeight (u ++ [false]) = parityWeight u := by
  rw [parityWeight_append]; simp [parityWeight]

/--
  Theorem T7a (Exact Trailing-`false` Decomposition of `broxOddCarry`):
-/
theorem broxOddCarry_append_false :
    ∀ (init : List Bool),
      broxOddCarry (init ++ [false]) = broxOddCarry init + 2 ^ (init.length + 1)
  | [] => rfl
  | b :: u => by
    simp only [List.cons_append, broxOddCarry, parityWeight_append_false, List.length_cons]
    rw [broxOddCarry_append_false u]
    have hp : 2 ^ (u.length + 1 + 1) = 2 * 2 ^ (u.length + 1) := by
      rw [Nat.pow_succ, Nat.mul_comm]
    omega

theorem matchesParity_append_split : ∀ (u1 u2 : List Bool) (x : Int),
    matchesParity (u1 ++ u2) x ->
    matchesParity u1 x ∧ matchesParity u2 (collatzIterInt u1.length x)
  | [], _, _, h => ⟨trivial, h⟩
  | false :: rest, u2, x, ⟨he, hr⟩ => by
    rcases matchesParity_append_split rest u2 (collatzStepInt x) hr with ⟨h1, h2⟩
    exact ⟨⟨he, h1⟩, h2⟩
  | true :: rest, u2, x, ⟨ho, hr⟩ => by
    rcases matchesParity_append_split rest u2 (collatzStepInt x) hr with ⟨h1, h2⟩
    exact ⟨⟨ho, h1⟩, h2⟩

/--
  Theorem T7b (Integer-Discreteness First-Block Dichotomy at a Global Cycle Minimum):
  Separates `Z^+` from multi-block contracting `Q_(2)^+` cycles (`v = 1^3 0^2 1^5 0^3` at
  `x0 = 10561/1631 < x1 = 11369/1631`, where `0 < x1 - x0 < 1` allows `2^(w_i + a_i) > 3^w_i`
  on EVERY block over `Q_(2)^+`!). Over `Nat`, either `T^(w1 + a1)(x0) = x0` (1-block period)
  or `x1 ≥ x0 + 1` forces strict first-block expansion `2^(w1 + a1) < 3^w1`.
-/
theorem cycle_min_first_block_dichotomy (x0 p w1 a1 : Nat) (tail : List Bool)
    (hp : p > 0)
    (hcyc : collatzIter p x0 = x0)
    (hmin : ∀ k : Nat, x0 ≤ collatzIter k x0)
    (hv : parityOfIter p x0 = List.replicate w1 true ++ List.replicate a1 false ++ tail) :
    collatzIter (w1 + a1) x0 = x0 ∨ 2 ^ (w1 + a1) < 3 ^ w1 := by
  let _ := hp
  let _ := hcyc
  let u1 := List.replicate w1 true ++ List.replicate a1 false
  have hu1_len : u1.length = w1 + a1 := by
    dsimp [u1]; rw [List.length_append, List.length_replicate, List.length_replicate]
  have hu1_wt : parityWeight u1 = w1 := by
    dsimp [u1]
    rw [parityWeight_append, parityWeight_replicate_true_local, parityWeight_replicate_false, Nat.add_zero]
  have hu1_car : affineCarryInt u1 = (3 : Int) ^ w1 - (2 : Int) ^ w1 :=
    one_cycle_carry_closed_form_universal w1 a1
  have hpar_full : matchesParity (u1 ++ tail) (x0 : Int) := by
    have hm := parityOfIter_matches p x0
    rwa [hv] at hm
  have hpar_u1 : matchesParity u1 (x0 : Int) :=
    (matchesParity_append_split u1 tail (x0 : Int) hpar_full).1
  have hdec := affine_decomposition_universal u1 (x0 : Int) hpar_u1
  rw [hu1_len, hu1_wt, hu1_car, collatzIterInt_ofNat] at hdec
  let x1 := collatzIter (w1 + a1) x0
  have heq_nat : 2 ^ (w1 + a1) * x1 + 2 ^ w1 = 3 ^ w1 * (x0 + 1) := by
    have h1 : ((2 ^ (w1 + a1) * x1 + 2 ^ w1 : Nat) : Int) =
        ((3 ^ w1 * (x0 + 1) : Nat) : Int) := by
      rw [natCast_add, natCast_mul, natCast_pow2, natCast_pow2,
          natCast_mul, natCast_pow3, natCast_add]
      dsimp [x1]
      rw [Int.mul_add, Int.mul_one]
      omega
    omega
  have hge := hmin (w1 + a1)
  change x0 ≤ x1 at hge
  by_cases hx_eq : x1 = x0
  · exact Or.inl hx_eq
  · right
    have hx1_ge : x0 + 1 ≤ x1 := by omega
    have hm : 2 ^ (w1 + a1) * (x0 + 1) ≤ 2 ^ (w1 + a1) * x1 :=
      Nat.mul_le_mul_left (2 ^ (w1 + a1)) hx1_ge
    have hp2w : 2 ^ w1 ≥ 1 := pow2_pos_nat w1
    have hstrict : 2 ^ (w1 + a1) * (x0 + 1) < 3 ^ w1 * (x0 + 1) := by omega
    by_cases hlt : 2 ^ (w1 + a1) < 3 ^ w1
    · exact hlt
    · have hle : 3 ^ w1 * (x0 + 1) ≤ 2 ^ (w1 + a1) * (x0 + 1) :=
        Nat.mul_le_mul_right (x0 + 1) (by omega)
      omega

-- ----------------------------------------------------------------------------
-- T8: Mod-96 `1/12` Sieve + Sharpened Brox Dichotomy Equivalence
-- ----------------------------------------------------------------------------

def leadingFalseCount : List Bool -> Nat
  | false :: u => 1 + leadingFalseCount u
  | _ => 0

def IsSharpenedBroxCycleWitness (w1 : Nat) (init : List Bool) (q0 : Nat) : Prop :=
  let K := w1 + 2 + init.length
  let W := w1 + parityWeight init
  let D := 2 ^ K - 3 ^ W
  let x0 := 2 ^ w1 * q0 - 1
  let a1 := leadingFalseCount (false :: (init ++ [false]))
  w1 ≥ 2 ∧ q0 ≥ 1 ∧ q0 % 2 = 1 ∧
  (x0 % 96 = 7 ∨ x0 % 96 = 31 ∨ x0 % 96 = 47 ∨ x0 % 96 = 59 ∨
   x0 % 96 = 71 ∨ x0 % 96 = 79 ∨ x0 % 96 = 91 ∨ x0 % 96 = 95) ∧
  W ≥ 5 ∧ K ≥ 8 ∧
  21 ^ W < 7 ^ W * 2 ^ K ∧ 7 ^ W * 2 ^ K ≤ 22 ^ W ∧
  2 ^ K * x0 ^ W ≤ (3 * x0 + 1) ^ W ∧
  (D % 24 = 5 ∨ D % 24 = 7 ∨ D % 24 = 13 ∨ D % 24 = 23) ∧ D ≥ 5 ∧
  D * q0 = broxOddCarry init + 2 ^ (init.length + 1) ∧
  ((parityWeight init = 0 ∧ q0 ≥ 3 ∧ (3 ^ w1) / (2 ^ (init.length + 2)) = 2 ^ w1 - 1) ∨
   (parityWeight init ≥ 1 ∧ 2 ^ (w1 + a1) < 3 ^ w1))

theorem split_leading_false : ∀ u : List Bool,
    ∃ tail : List Bool,
      u = List.replicate (leadingFalseCount u) false ++ tail ∧
      (tail = [] ∨ tail.head? = some true)
  | [] => ⟨[], rfl, Or.inl rfl⟩
  | true :: rest => ⟨true :: rest, rfl, Or.inr rfl⟩
  | false :: rest => by
    rcases split_leading_false rest with ⟨tail, heq, htail⟩
    refine ⟨tail, ?_, htail⟩
    simp only [leadingFalseCount]
    rw [Nat.add_comm 1, List.replicate_succ, List.cons_append, ← heq]

theorem parityOfIter_append_split : ∀ (k1 k2 n : Nat),
    parityOfIter (k1 + k2) n = parityOfIter k1 n ++ parityOfIter k2 (collatzIter k1 n)
  | 0, _, _ => by simp [parityOfIter, collatzIter]
  | k1 + 1, k2, n => by
    rw [Nat.succ_add]
    simp only [parityOfIter, collatzIter, List.cons_append]
    rw [parityOfIter_append_split k1 k2 (collatzStep n)]

theorem mod96_8classes_imp_mod16_and_mod3 (x0 : Nat)
    (h96 : x0 % 96 = 7 ∨ x0 % 96 = 31 ∨ x0 % 96 = 47 ∨ x0 % 96 = 59 ∨
           x0 % 96 = 71 ∨ x0 % 96 = 79 ∨ x0 % 96 = 91 ∨ x0 % 96 = 95) :
    (x0 % 16 = 7 ∨ x0 % 16 = 11 ∨ x0 % 16 = 15) ∧ x0 % 3 ≠ 0 := by
  have h16 : x0 % 16 = (x0 % 96) % 16 := (mod_mul_mod_eq x0 16 6).symm
  have h3 : x0 % 3 = (x0 % 96) % 3 := (mod_mul_mod_eq x0 3 32).symm
  rw [h16, h3]
  rcases h96 with h | h | h | h | h | h | h | h <;> rw [h] <;> decide

theorem mod32_mod3_to_mod96_8classes (x0 : Nat)
    (hm16 : x0 % 16 = 7 ∨ x0 % 16 = 11 ∨ x0 % 16 = 15)
    (hne11 : x0 % 32 ≠ 11) (hne23 : x0 % 32 ≠ 23)
    (hn3 : x0 % 3 ≠ 0) :
    x0 % 96 = 7 ∨ x0 % 96 = 31 ∨ x0 % 96 = 47 ∨ x0 % 96 = 59 ∨
    x0 % 96 = 71 ∨ x0 % 96 = 79 ∨ x0 % 96 = 91 ∨ x0 % 96 = 95 := by
  let r := x0 % 96
  have hr_lt : r < 96 := Nat.mod_lt x0 (by decide)
  have hr16 : r % 16 = x0 % 16 := mod_mul_mod_eq x0 16 6
  have hr32 : r % 32 = x0 % 32 := mod_mul_mod_eq x0 32 3
  have hr3 : r % 3 = x0 % 3 := mod_mul_mod_eq x0 3 32
  rw [← hr16] at hm16
  rw [← hr32] at hne11 hne23
  rw [← hr3] at hn3
  change r = 7 ∨ r = 31 ∨ r = 47 ∨ r = 59 ∨ r = 71 ∨ r = 79 ∨ r = 91 ∨ r = 95
  omega

theorem list_append_inj_left_eq_len {α : Type} : ∀ (l1 l2 r1 r2 : List α),
    l1.length = r1.length -> l1 ++ l2 = r1 ++ r2 -> l1 = r1 ∧ l2 = r2
  | [], l2, [], r2, _, h => ⟨rfl, h⟩
  | _ :: _, _, [], _, hlen, _ => by simp at hlen
  | [], _, _ :: _, _, hlen, _ => by simp at hlen
  | a :: l1, l2, b :: r1, r2, hlen, h => by
    simp only [List.cons_append, List.cons.injEq] at h
    simp only [List.length_cons] at hlen
    rcases list_append_inj_left_eq_len l1 l2 r1 r2 (by omega) h.2 with ⟨h1, h2⟩
    exact ⟨by rw [h.1, h1], h2⟩

theorem extract_brox_q0_from_min_cycle (x0 P w1 : Nat) (rest : List Bool)
    (hw1_ge2 : w1 ≥ 2) (h3W_lt_2P : 3 ^ (w1 + parityWeight rest) < 2 ^ P)
    (hx0_cyc : collatzIter P x0 = x0)
    (hv_eq : parityOfIter P x0 = List.replicate w1 true ++ (false :: rest)) :
    ∃ q0 : Nat,
      q0 ≥ 1 ∧ q0 % 2 = 1 ∧ x0 = 2 ^ w1 * q0 - 1 ∧
      (2 ^ P - 3 ^ (w1 + parityWeight rest)) * q0 = broxOddCarry rest := by
  let v := parityOfIter P x0
  let W := w1 + parityWeight rest
  have hv_len : v.length = P := parityOfIter_length P x0
  have hv_wt : parityWeight v = W := by
    dsimp [v, W]
    rw [hv_eq, parityWeight_append, parityWeight_replicate_true_local]
    rfl
  have hp_pos : P ≥ 3 := by
    rw [← hv_len]; dsimp [v]
    rw [hv_eq, List.length_append, List.length_replicate, List.length_cons]
    omega
  have hv_par : matchesParity v (x0 : Int) := parityOfIter_matches P x0
  have hcyc_int : collatzIterInt v.length (x0 : Int) = (x0 : Int) := by
    rw [hv_len, collatzIterInt_ofNat, hx0_cyc]
  have hbs := bohm_sontacchi_cycle_equation_universal v (x0 : Int) hv_par hcyc_int
  rw [hv_len, hv_wt] at hbs
  have hshift := brox_shift_carry_identity w1 rest
  dsimp only at hshift
  rw [← hv_eq, hv_len, hv_wt] at hshift
  have hmul_eq : ((2 : Int) ^ P - (3 : Int) ^ W) * ((x0 : Int) + 1) =
      (2 : Int) ^ w1 * (broxOddCarry rest : Int) := by
    rw [Int.mul_add, Int.mul_one, hbs]; exact hshift
  have hD_odd : ((2 : Int) ^ P - (3 : Int) ^ W) % 2 = 1 := by
    have hp2_ev : ((2 : Int) ^ P) % 2 = 0 := by
      rw [show P = (P - 1) + 1 by omega, Int.pow_succ]; omega
    have hp3_odd : ((3 : Int) ^ W) % 2 = 1 := pow3_mod2 W
    omega
  have hbrox_odd_int : (broxOddCarry rest : Int) % 2 = 1 := by
    have ho := (broxOddCarry_odd_and_ge_pow3 rest).1; omega
  rcases odd_mul_pow2_exact_factor w1 ((2 : Int) ^ P - (3 : Int) ^ W)
      ((x0 : Int) + 1) (broxOddCarry rest : Int) hD_odd hbrox_odd_int hmul_eq with
    ⟨qInt, hqInt_eq, hqInt_odd⟩
  have hqInt_pos : qInt ≥ 1 := by
    have hp2w1_pos : (2 : Int) ^ w1 ≥ 1 := pow_pos_int 2 w1 (by omega)
    by_cases hge : qInt ≥ 1
    · exact hge
    · have hm_np : (2 : Int) ^ w1 * (-qInt) ≥ 0 := Int.mul_nonneg (by omega) (by omega)
      rw [Int.mul_neg] at hm_np; omega
  let q0 : Nat := qInt.toNat
  have hq0_cast : (q0 : Int) = qInt := Int.toNat_of_nonneg (by omega)
  have hq0_ge1 : q0 ≥ 1 := by omega
  have hq0_odd : q0 % 2 = 1 := by omega
  have hx0_eq_q0 : x0 = 2 ^ w1 * q0 - 1 := by
    rw [← hq0_cast] at hqInt_eq
    have h1 : ((x0 + 1 : Nat) : Int) = ((2 ^ w1 * q0 : Nat) : Int) := by
      rw [natCast_add, natCast_mul, natCast_pow2]; exact hqInt_eq
    omega
  have hbrox_q0_int : ((2 : Int) ^ P - (3 : Int) ^ W) * (q0 : Int) = (broxOddCarry rest : Int) := by
    apply mul_left_cancel_pow2_int w1
    calc
      (2 : Int) ^ w1 * (((2 : Int) ^ P - (3 : Int) ^ W) * (q0 : Int))
          = ((2 : Int) ^ P - (3 : Int) ^ W) * ((2 : Int) ^ w1 * (q0 : Int)) := by
            rw [← Int.mul_assoc, Int.mul_comm ((2 : Int) ^ w1), Int.mul_assoc]
      _ = ((2 : Int) ^ P - (3 : Int) ^ W) * ((x0 : Int) + 1) := by rw [← hq0_cast] at hqInt_eq; rw [hqInt_eq]
      _ = (2 : Int) ^ w1 * (broxOddCarry rest : Int) := hmul_eq
  have hbrox_q0_nat : (2 ^ P - 3 ^ W) * q0 = broxOddCarry rest := by
    have hsub : ((2 ^ P - 3 ^ W : Nat) : Int) = (2 : Int) ^ P - (3 : Int) ^ W := by
      have hadd : (2 ^ P - 3 ^ W) + 3 ^ W = 2 ^ P := Nat.sub_add_cancel (Nat.le_of_lt h3W_lt_2P)
      have hc2 : (((2 ^ P - 3 ^ W) + 3 ^ W : Nat) : Int) = ((2 ^ P : Nat) : Int) :=
        congrArg (fun t : Nat => (t : Int)) hadd
      rw [natCast_add, natCast_pow3, natCast_pow2] at hc2
      omega
    have h1 : (((2 ^ P - 3 ^ W) * q0 : Nat) : Int) = (broxOddCarry rest : Int) := by
      rw [natCast_mul, hsub]; exact hbrox_q0_int
    omega
  exact ⟨q0, hq0_ge1, hq0_odd, hx0_eq_q0, hbrox_q0_nat⟩

/--
  Theorem T8 (Mod-96 `1/12` Sieve + Sharpened Brox Dichotomy Equivalence):
  `NoNontrivialPositiveCycles` holds IF AND ONLY IF no `(w1, init, q0)` satisfies
  `IsSharpenedBroxCycleWitness w1 init q0`!
-/
theorem no_nontrivial_cycles_iff_sharpened_brox_obstruction :
    NoNontrivialPositiveCycles ↔
      ∀ (w1 : Nat) (init : List Bool) (q0 : Nat), ¬ IsSharpenedBroxCycleWitness w1 init q0 := by
  constructor
  · intro hnocyc w1 init q0 hwit
    rcases hwit with
      ⟨hw1, hq0, hq0_odd, hm96, hW5, hK8, hband_lo, hband_hi, hup_x0, _, _, hbrox_init, _⟩
    let rest := init ++ [false]
    have hlen_r : w1 + 1 + rest.length = w1 + 2 + init.length := by
      dsimp [rest]; rw [List.length_append]; simp; omega
    have hwt_r : w1 + parityWeight rest = w1 + parityWeight init := by
      dsimp [rest]; rw [parityWeight_append_false]
    rcases mod96_8classes_imp_mod16_and_mod3 (2 ^ w1 * q0 - 1) hm96 with ⟨hm16, hn3⟩
    have hbrox_rest : (2 ^ (w1 + 2 + init.length) - 3 ^ (w1 + parityWeight init)) * q0 =
        broxOddCarry rest := by
      dsimp [rest]
      rw [broxOddCarry_append_false init]
      exact hbrox_init
    have hwit_base : IsBroxNatCycleMinWitness w1 rest q0 := by
      unfold IsBroxNatCycleMinWitness
      dsimp only
      rw [hlen_r, hwt_r]
      exact ⟨hw1, hq0, hq0_odd, hm16, hn3, hW5, hK8, hband_lo, hband_hi, hup_x0, hbrox_rest⟩
    exact (no_nontrivial_cycles_iff_brox_nat_obstruction.mp hnocyc) w1 rest q0 hwit_base
  · intro hnowit x p hx hp hcyc
    by_cases htriv : x = 1 ∨ x = 2
    · exact htriv
    · exfalso
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
      have hm96 : x0 % 96 = 7 ∨ x0 % 96 = 31 ∨ x0 % 96 = 47 ∨ x0 % 96 = 59 ∨
          x0 % 96 = 71 ∨ x0 % 96 = 79 ∨ x0 % 96 = 91 ∨ x0 % 96 = 95 :=
        mod32_mod3_to_mod96_8classes x0 hm16 hne11 hne23 hx0_n3
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
          ⟨x0', ⟨i', hi'_lt, hi'_eq⟩, _, hmin', _, _, _, hW1_5, hp1_8, hband1_lo, hband1_hi, hup1⟩
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
        have h3w1_lt_2p1 : 3 ^ w1 < 2 ^ p1 := by
          rw [show (21 : Nat) ^ w1 = 7 ^ w1 * 3 ^ w1 from mul_pow_nat 7 3 w1] at hband1_lo
          by_cases hlt : 3 ^ w1 < 2 ^ p1
          · exact hlt
          · have hm := Nat.mul_le_mul_left (7 ^ w1) (by omega : 2 ^ p1 ≤ 3 ^ w1); omega
        have ha1_ge2 : a1 ≥ 2 := by
          have hp23 := pow2_succ_lt_pow3 w1 hw1_ge2
          by_cases hge2 : a1 ≥ 2
          · exact hge2
          · have ha1_1 : a1 = 1 := by omega
            dsimp [p1] at h3w1_lt_2p1
            rw [ha1_1] at h3w1_lt_2p1
            omega
        let init := List.replicate (a1 - 2) false
        let rest1 := init ++ [false]
        have hrest1_rep : rest1 = List.replicate (a1 - 1) false := by
          dsimp [rest1, init]
          rw [← replicate_succ_append_local false (a1 - 2), show a1 - 2 + 1 = a1 - 1 by omega]
        have hv1_brox : parityOfIter p1 x0 = List.replicate w1 true ++ (false :: rest1) := by
          rw [hv1_eq, hrest1_rep, ← List.replicate_succ, show a1 - 1 + 1 = a1 by omega]
        have hwt_rest1 : parityWeight rest1 = 0 := by rw [hrest1_rep, parityWeight_replicate_false]
        rcases extract_brox_q0_from_min_cycle x0 p1 w1 rest1 hw1_ge2
            (by rw [hwt_rest1, Nat.add_zero]; exact h3w1_lt_2p1) hcyc1 hv1_brox with
          ⟨q0, hq0_ge1, hq0_odd, hx0_q0, hbrox1⟩
        rw [hwt_rest1, Nat.add_zero] at hbrox1
        have hp1_K : p1 = w1 + 2 + init.length := by
          dsimp [p1, init]; rw [List.length_replicate]; omega
        have hwt_init : parityWeight init = 0 := parityWeight_replicate_false _
        rcases pow2_sub_pow3_mod24_in_4_classes p1 w1 (by omega) (by omega) h3w1_lt_2p1 with
          ⟨hD24, hD5⟩
        have hc_eq : p1 = w1 + 1 + (a1 - 1) := by dsimp [p1]; omega
        have hbrox_c : (2 ^ (w1 + 1 + (a1 - 1)) - 3 ^ w1) * q0 =
            broxOddCarry (List.replicate (a1 - 1) false) := by
          rw [← hc_eq, ← hrest1_rep]; exact hbrox1
        rcases one_block_cycle_binary_squeeze_and_q0_ge_three w1 (a1 - 1) q0
            hw1_ge2 hq0_ge1 hq0_odd (by rw [← hc_eq]; exact h3w1_lt_2p1) hbrox_c with
          ⟨_, hdiv_sq, _, hq0_ge3, _⟩
        have ha1_init : a1 - 1 + 1 = init.length + 2 := by
          dsimp [init]; rw [List.length_replicate]; omega
        rw [ha1_init] at hdiv_sq
        have hbrox_split : (2 ^ p1 - 3 ^ w1) * q0 = broxOddCarry init + 2 ^ (init.length + 1) := by
          rw [← broxOddCarry_append_false init]; exact hbrox1
        have hwit : IsSharpenedBroxCycleWitness w1 init q0 := by
          unfold IsSharpenedBroxCycleWitness
          dsimp only
          rw [← hp1_K, hwt_init, Nat.add_zero, ← hx0_q0]
          exact ⟨hw1_ge2, hq0_ge1, hq0_odd, hm96, hW1_5, hp1_8, hband1_lo, hband1_hi, hup1,
            hD24, hD5, hbrox_split, Or.inl ⟨rfl, hq0_ge3, hdiv_sq⟩⟩
        exact hnowit w1 init q0 hwit
      · -- Case B: Multi-block cycle (`collatzIter (w1 + a1) x0 ≠ x0` and `2 ^ (w1 + a1) < 3 ^ w1`):
        have htail_true : tail.head? = some true := by
          rcases htail_cases with hnil | htr
          · subst hnil
            rw [List.append_nil] at hv_block
            have hp_eq : p = w1 + a1 := by
              rw [← hv_len, hv_block, List.length_append,
                  List.length_replicate, List.length_replicate]
            have hlt_w : 2 ^ p < 3 ^ W := by
              have hW_w1 : W = w1 := by
                dsimp [W]
                rw [hv_block, parityWeight_append, parityWeight_replicate_true_local,
                    parityWeight_replicate_false, Nat.add_zero]
              rw [hp_eq, hW_w1]; exact hlt_block
            omega
          · exact htr
        -- Predecessor `y := collatzIter (p - 1) x0` must be even (`y ≥ x0 ≥ 7` and `collatzStep y = x0`):
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
          · have hodd : y % 2 = 1 := by omega
            rw [collatzStep_of_odd_nat y hodd] at hy_step
            omega
        have hv_last_false : v = parityOfIter (p - 1) x0 ++ [false] := by
          dsimp [v]
          conv => lhs; rw [show p = (p - 1) + 1 by omega]
          rw [parityOfIter_append_split (p - 1) 1 x0]
          dsimp [y] at hy_ev
          have hb : (collatzIter (p - 1) x0 % 2 == 0) = true := decide_eq_true hy_ev
          simp [parityOfIter, hb]
        have hrest_nonempty : rest ≠ [] := by
          intro hnil
          subst hnil
          simp [leadingFalseCount] at hlead_eq
          subst hlead_eq
          simp at htail_true
        have hv_rev_f : v.reverse.head? = some false := by
          rw [hv_last_false, List.reverse_append]; rfl
        have hrest_rev_f : rest.reverse.head? = some false := by
          rw [hv_eq, List.reverse_append, List.reverse_cons] at hv_rev_f
          cases hr : rest.reverse with
          | nil =>
            have h0 := congrArg List.reverse hr
            simp at h0; exact False.elim (hrest_nonempty h0)
          | cons lastBit revInit =>
            rw [hr] at hv_rev_f
            simp at hv_rev_f
            exact congrArg some hv_rev_f
        obtain ⟨init, hrest_init⟩ : ∃ init : List Bool, rest = init ++ [false] := by
          cases hr : rest.reverse with
          | nil => simp [hr] at hrest_rev_f
          | cons lastBit revInit =>
            rw [hr] at hrest_rev_f
            simp at hrest_rev_f
            subst hrest_rev_f
            refine ⟨revInit.reverse, ?_⟩
            have h0 := congrArg List.reverse hr
            simpa using h0
        have hp_K : p = w1 + 2 + init.length := by
          rw [← hv_len, hv_eq, hrest_init, List.length_append, List.length_replicate,
              List.length_cons, List.length_append]
          simp; omega
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
            simp at htail_true; subst htail_true
            simp [parityWeight] at hw_f; omega
        rcases extract_brox_q0_from_min_cycle x0 p w1 rest hw1_ge2
            (by rw [hrest_init, parityWeight_append_false, ← hW_init]; exact h3W_lt_2p)
            hx0_cyc hv_eq with
          ⟨q0, hq0_ge1, hq0_odd, hx0_q0, hbrox_r⟩
        rw [hrest_init, parityWeight_append_false, ← hW_init, broxOddCarry_append_false] at hbrox_r
        rcases pow2_sub_pow3_mod24_in_4_classes p W (by omega) (by omega) h3W_lt_2p with
          ⟨hD24, hD5⟩
        have ha1_init_eq : leadingFalseCount (false :: (init ++ [false])) = a1 := by
          dsimp [a1]; rw [hrest_init]
        have hwit : IsSharpenedBroxCycleWitness w1 init q0 := by
          unfold IsSharpenedBroxCycleWitness
          dsimp only
          rw [← hp_K, ← hW_init, ← hx0_q0, ha1_init_eq]
          exact ⟨hw1_ge2, hq0_ge1, hq0_odd, hm96, hW5, hp8, hband_lo, hband_hi, hup_x0,
            hD24, hD5, hbrox_r, Or.inr ⟨hwt_init_pos, hlt_block⟩⟩
        exact hnowit w1 init q0 hwit

-- ============================================================================
-- SECTION 7: Track 3 Wave 2 & Cross-Track Fusions — Arbitrary-Depth Forest
--            Collapse, Horizon-Supercritical Core Reduction, Mod-373248 Fusion,
--            & Koopman Fiber Annihilation (`#15/#16` + `#20`, `T3.8`–`T3.12`)
-- ============================================================================

-- ----------------------------------------------------------------------------
-- T3.8: Pointwise Arbitrary-Depth Inverse Syracuse Forest Collapse (`∀ n, ∀ cs`)
-- ----------------------------------------------------------------------------

theorem exactBackwardQuotient_zero_le_q (x : Nat) (u : List Bool)
    (hw : parityWeight u ≥ 1) (hx : x % 3 ≠ 0) :
    ∀ q : Nat, exactBackwardQuotient x u 0 ≤ exactBackwardQuotient x u q
  | 0 => Nat.le_refl _
  | q + 1 => by
    have ih := exactBackwardQuotient_zero_le_q x u hw hx q
    have hrec := (exactBackwardQuotient_period_recurrence_and_mod3 x u q hw hx).1
    omega

theorem exactBackwardQuotient_of_trail_eq (x z trail : Nat) (u : List Bool)
    (hw : parityWeight u ≥ 1) (hx : x % 3 ≠ 0)
    (heq : 2 ^ (u.length + trail) * x = 3 ^ parityWeight u * z + affineCarry u) :
    ∃ q : Nat, exactBackwardQuotient x u q = z := by
  let w := parityWeight u
  let P := 2 * 3 ^ (w - 1)
  let M := 3 ^ w
  have hP_pos : P > 0 := by dsimp [P]; have hp := pow3_pos_nat (w - 1); omega
  have hM_pos : M > 0 := pow3_pos_nat w
  let q := trail / P
  let a' := trail % P
  have ha'_lt : a' < P := Nat.mod_lt trail hP_pos
  have htrail_eq : trail = a' + q * P := by
    have hdm := (Nat.div_add_mod trail P).symm
    dsimp [q, a']; rw [Nat.mul_comm P (trail / P)] at hdm; omega
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
  refine ⟨q, ?_⟩
  unfold exactBackwardQuotient
  change (2 ^ (u.length + (canonicalSuffixShift u x + q * P)) * x - affineCarry u) / M = z
  rw [← ha'_eq, ← htrail_eq, heq]
  change (M * z + affineCarry u - affineCarry u) / M = z
  have hsub : M * z + affineCarry u - affineCarry u = M * z := by omega
  rw [hsub, Nat.mul_comm M z, Nat.mul_div_cancel z hM_pos]

/--
  Theorem T3.8 (Pointwise Arbitrary-Depth Inverse Syracuse Forest Collapse):
  For EVERY odd `n ≥ 7`, EVERY disjoint forest root `r < n`, and EVERY choice sequence `cs`
  (even when `syracuseForestVal r cs ≫ n`), any carry collision at step `K` collapses within
  `1 ≤ K' ≤ K + 6 * cs.length + 1` steps to a depth-`0` core quotient contraction `≤ r < n`!
-/
theorem odd_forest_collision_collapses_to_core_contraction (n K r : Nat) (cs u : List Bool)
    (hn : n ≥ 7) (hodd_n : n % 2 = 1)
    (hr : IsSyracuseForestRoot r) (hr_lt : r < n)
    (heq : (2 : Int) ^ u.length * (collatzIter K n : Int) =
      (3 : Int) ^ parityWeight u * (syracuseForestVal r cs : Int) + affineCarryInt u) :
    ∃ (K' : Nat) (uCore : List Bool),
      1 ≤ K' ∧ K' ≤ K + 6 * cs.length + 1 ∧
      IsCoreParityWord uCore ∧
      exactBackwardQuotient (collatzIter K' n) uCore 0 ≤ r := by
  let _ := hn
  let _ := hr_lt
  let z := syracuseForestVal r cs
  rcases general_affine_converse_universal u (z : Int) (collatzIter K n : Int) heq with ⟨_, hiter_int⟩
  rw [collatzIterInt_ofNat] at hiter_int
  have hcoal_z : collatzIter u.length z = collatzIter K n := by omega
  rcases syracuseForestVal_reaches_root r hr cs with ⟨kTree, hk_le, hk_root⟩
  change collatzIter kTree z = r at hk_root
  have hr_odd : r % 2 = 1 := hr.2.1
  by_cases hle : u.length ≤ kTree
  · let d := kTree - u.length
    have hr_reach : collatzIter (K + d) n = r := by
      rw [collatzIter_add K d n, ← hcoal_z, ← collatzIter_add u.length d z,
          show u.length + d = kTree by dsimp [d]; omega, hk_root]
    let K' := K + d + 1
    have hK'_eq : collatzIter K' n = collatzStep r := by
      dsimp [K']; rw [collatzIter_add (K + d) 1 n, hr_reach]; rfl
    have hr_step2 : 2 * collatzStep r = 3 * r + 1 := by
      rw [collatzStep_of_odd_nat r hr_odd]; omega
    have hr_step_n3 : collatzStep r % 3 ≠ 0 := by
      have hm2 := collatzStep_odd_mod3_eq_two r hr_odd; omega
    rcases canonicalSuffixShift_spec_unique [true] (collatzStep r) (by decide) hr_step_n3 with
      ⟨_, _, huniq⟩
    have hshift0 : canonicalSuffixShift [true] (collatzStep r) = 0 := by
      symm
      apply huniq 0 (by decide)
      change (2 ^ 1 * collatzStep r) % 3 = 1 % 3
      omega
    have hquot_r : exactBackwardQuotient (collatzStep r) [true] 0 = r := by
      unfold exactBackwardQuotient
      rw [show parityWeight [true] = 1 from rfl, show affineCarry [true] = 1 from rfl, hshift0]
      change (2 ^ 1 * collatzStep r - 1) / 3 = r
      omega
    refine ⟨K', [true], by dsimp [K']; omega, by dsimp [K', d]; omega, ⟨rfl, rfl⟩, ?_⟩
    rw [hK'_eq, hquot_r]; exact Nat.le_refl r
  · let d := u.length - kTree
    have hd_pos : d ≥ 1 := by dsimp [d]; omega
    have hr_to_xK : collatzIter d r = collatzIter K n := by
      rw [← hk_root, ← collatzIter_add kTree d z,
          show kTree + d = u.length by dsimp [d]; omega, hcoal_z]
    let v := parityOfIter d r
    have hv_len : v.length = d := parityOfIter_length d r
    have hv_head : v.head? = some true := by
      dsimp [v]
      rw [show d = (d - 1) + 1 by omega]
      simp only [parityOfIter]
      have hb : (r % 2 == 0) = false := decide_eq_false (by omega)
      simp [hb]
    have hv_wt : parityWeight v ≥ 1 := by
      cases hv_c : v with
      | nil => rw [hv_c] at hv_head; simp at hv_head
      | cons b rest =>
        rw [hv_c] at hv_head; simp at hv_head; subst hv_head; simp [parityWeight]
    have hdec_v := affine_decomposition_universal v (r : Int) (parityOfIter_matches d r)
    rw [hv_len, collatzIterInt_ofNat, hr_to_xK] at hdec_v
    have heq_v_nat : 2 ^ v.length * collatzIter K n = 3 ^ parityWeight v * r + affineCarry v := by
      rw [hv_len]
      have h1 : ((2 ^ d * collatzIter K n : Nat) : Int) =
          ((3 ^ parityWeight v * r + affineCarry v : Nat) : Int) := by
        rw [natCast_mul, natCast_pow2, natCast_add, natCast_mul, natCast_pow3, ← affineCarryInt_ofNat]
        exact hdec_v
      omega
    have hex_K1 : ∃ (K1 : Nat) (u1 : List Bool),
        1 ≤ K1 ∧ K1 ≤ K + 1 ∧ u1.head? = some true ∧ parityWeight u1 ≥ 1 ∧
        2 ^ u1.length * collatzIter K1 n = 3 ^ parityWeight u1 * r + affineCarry u1 := by
      by_cases hK0 : K = 0
      · subst hK0
        simp only [collatzIter] at heq_v_nat
        have hstep_n : 2 * collatzIter 1 n = 3 * n + 1 := by
          change 2 * collatzStep n = 3 * n + 1
          rw [collatzStep_of_odd_nat n hodd_n]; omega
        let u1 := v ++ [true]
        have hu1_len : u1.length = v.length + 1 := by simp [u1]
        have hu1_wt : parityWeight u1 = parityWeight v + 1 := by
          simp [u1, parityWeight_append, parityWeight]
        have hu1_car : affineCarry u1 = 3 * affineCarry v + 2 ^ v.length := by
          dsimp [u1]; rw [affineCarry_append]
          change 3 ^ 1 * affineCarry v + 2 ^ v.length * 1 = 3 * affineCarry v + 2 ^ v.length
          omega
        refine ⟨1, u1, by omega, by omega, head_append_of_some v [true] true hv_head, by omega, ?_⟩
        rw [hu1_len, hu1_wt, hu1_car]
        calc
          2 ^ (v.length + 1) * collatzIter 1 n
              = 2 ^ v.length * (2 * collatzIter 1 n) := by rw [Nat.pow_succ, Nat.mul_assoc]
          _ = 2 ^ v.length * (3 * n + 1) := by rw [hstep_n]
          _ = 3 * (2 ^ v.length * n) + 2 ^ v.length := by
                rw [Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc,
                    Nat.mul_comm (2 ^ v.length) 3, Nat.mul_assoc]
          _ = 3 * (3 ^ parityWeight v * r + affineCarry v) + 2 ^ v.length := by rw [heq_v_nat]
          _ = 3 ^ (parityWeight v + 1) * r + (3 * affineCarry v + 2 ^ v.length) := by
                rw [Nat.mul_add, ← Nat.mul_assoc 3 (3 ^ parityWeight v),
                    Nat.mul_comm 3 (3 ^ parityWeight v), ← Nat.pow_succ, Nat.add_assoc]
      · exact ⟨K, v, by omega, by omega, hv_head, hv_wt, heq_v_nat⟩
    rcases hex_K1 with ⟨K1, u1, hK1_pos, hK1_le, hu1_head, hu1_wt, heq_u1⟩
    rcases stripTrailingFalse_spec u1 with ⟨hrep, hcases, hhead_imp⟩
    let uCore := (stripTrailingFalse u1).1
    let trail := (stripTrailingFalse u1).2
    change uCore ++ List.replicate trail false = u1 at hrep
    have huCore_last : uCore.reverse.head? = some true := by
      rcases hcases with ⟨_, hwt0⟩ | ⟨_, hlast⟩
      · omega
      · exact hlast
    have huCore_core : IsCoreParityWord uCore := ⟨hhead_imp hu1_head, huCore_last⟩
    rcases affineCarry_append_replicate_false uCore trail with ⟨hwt_c, hcar_c⟩
    rw [hrep] at hwt_c hcar_c
    have hw_c : parityWeight uCore ≥ 1 := by omega
    have hu1_len : u1.length = uCore.length + trail := by
      rw [← hrep, List.length_append, List.length_replicate]
    have hxK_n3 : collatzIter K1 n % 3 ≠ 0 :=
      collatzIter_pos_step_mod3_ne_zero K1 n hK1_pos hodd_n
    have heq_trail : 2 ^ (uCore.length + trail) * collatzIter K1 n =
        3 ^ parityWeight uCore * r + affineCarry uCore := by
      rw [← hu1_len, heq_u1, hwt_c, hcar_c]
    rcases exactBackwardQuotient_of_trail_eq (collatzIter K1 n) r trail uCore hw_c hxK_n3 heq_trail with
      ⟨q, hq_eq⟩
    have h0_le : exactBackwardQuotient (collatzIter K1 n) uCore 0 ≤ r := by
      rw [← hq_eq]
      exact exactBackwardQuotient_zero_le_q (collatzIter K1 n) uCore hw_c hxK_n3 q
    exact ⟨K1, uCore, hK1_pos, by omega, huCore_core, h0_le⟩

-- ----------------------------------------------------------------------------
-- T3.9: Universal Prefix-Factorization Law & Subcritical Prefix Elimination
-- ----------------------------------------------------------------------------

/--
  Theorem T3.9a (Universal Prefix-Factorization Law for `exactBackwardQuotient`):
-/
theorem exactBackwardQuotient_prefix_step_law (x : Nat) (u1 u2 : List Bool)
    (hw2 : parityWeight u2 ≥ 1) (hx : x % 3 ≠ 0) :
    let y0 := exactBackwardQuotient x (u1 ++ u2) 0
    let y1 := collatzIter u1.length y0
    2 ^ u1.length * y1 = 3 ^ parityWeight u1 * y0 + affineCarry u1 ∧
    exactBackwardQuotient x u2 0 ≤ y1 := by
  dsimp only
  have hw12 : parityWeight (u1 ++ u2) ≥ 1 := by rw [parityWeight_append]; omega
  rcases exactBackwardQuotient_spec x (u1 ++ u2) 0 hw12 hx with ⟨_, heq_nat, _, _⟩
  let y0 := exactBackwardQuotient x (u1 ++ u2) 0
  let y1 := collatzIter u1.length y0
  let a := canonicalSuffixShift (u1 ++ u2) x
  simp only [Nat.zero_mul, Nat.add_zero] at heq_nat
  change 2 ^ ((u1 ++ u2).length + a) * x =
    3 ^ parityWeight (u1 ++ u2) * y0 + affineCarry (u1 ++ u2) at heq_nat
  let u2a := u2 ++ List.replicate a false
  let uFull := u1 ++ u2a
  have huFull_assoc : uFull = (u1 ++ u2) ++ List.replicate a false :=
    (List.append_assoc u1 u2 (List.replicate a false)).symm
  rcases affineCarry_append_replicate_false (u1 ++ u2) a with ⟨hwt_full, hcar_full⟩
  rw [← huFull_assoc] at hwt_full hcar_full
  have hlen_full : uFull.length = (u1 ++ u2).length + a := by
    rw [huFull_assoc, List.length_append, List.length_replicate]
  have heq_full_int : (2 : Int) ^ uFull.length * (x : Int) =
      (3 : Int) ^ parityWeight uFull * (y0 : Int) + affineCarryInt uFull := by
    rw [hlen_full, hwt_full, affineCarryInt_ofNat, hcar_full]
    have hc := congrArg (fun t : Nat => (t : Int)) heq_nat
    rw [natCast_mul, natCast_pow2, natCast_add, natCast_mul, natCast_pow3] at hc
    exact hc
  rcases general_affine_converse_universal uFull (y0 : Int) (x : Int) heq_full_int with
    ⟨hpar_full, hiter_full⟩
  rcases matchesParity_append_split u1 u2a (y0 : Int) hpar_full with ⟨hpar1, hpar2⟩
  have hdec1 := affine_decomposition_universal u1 (y0 : Int) hpar1
  rw [collatzIterInt_ofNat] at hdec1 hpar2
  change matchesParity u2a (y1 : Int) at hpar2
  have heq1_nat : 2 ^ u1.length * y1 = 3 ^ parityWeight u1 * y0 + affineCarry u1 := by
    have h1 : ((2 ^ u1.length * y1 : Nat) : Int) =
        ((3 ^ parityWeight u1 * y0 + affineCarry u1 : Nat) : Int) := by
      rw [natCast_mul, natCast_pow2, natCast_add, natCast_mul, natCast_pow3, ← affineCarryInt_ofNat]
      exact hdec1
    omega
  have hiter_u2a : collatzIterInt u2a.length (y1 : Int) = (x : Int) := by
    have hlen_split : uFull.length = u1.length + u2a.length := List.length_append
    rw [collatzIterInt_ofNat] at hiter_full
    have hx_eq : collatzIter (u1.length + u2a.length) y0 = x := by
      rw [← hlen_split]; omega
    rw [collatzIter_add] at hx_eq
    change collatzIter u2a.length y1 = x at hx_eq
    rw [collatzIterInt_ofNat, hx_eq]
  have hdec2 := affine_decomposition_universal u2a (y1 : Int) hpar2
  rw [hiter_u2a] at hdec2
  rcases affineCarry_append_replicate_false u2 a with ⟨hwt2a, hcar2a⟩
  change parityWeight u2a = parityWeight u2 at hwt2a
  change affineCarry u2a = affineCarry u2 at hcar2a
  have hlen2a : u2a.length = u2.length + a := by
    dsimp [u2a]; rw [List.length_append, List.length_replicate]
  have heq2_nat : 2 ^ (u2.length + a) * x = 3 ^ parityWeight u2 * y1 + affineCarry u2 := by
    have h1 : ((2 ^ (u2.length + a) * x : Nat) : Int) =
        ((3 ^ parityWeight u2 * y1 + affineCarry u2 : Nat) : Int) := by
      rw [natCast_mul, natCast_pow2, natCast_add, natCast_mul, natCast_pow3,
          ← hlen2a, ← hwt2a, ← hcar2a, ← affineCarryInt_ofNat]
      exact hdec2
    omega
  rcases exactBackwardQuotient_of_trail_eq x y1 a u2 hw2 hx heq2_nat with ⟨q2, hq2_eq⟩
  have hle_y1 : exactBackwardQuotient x u2 0 ≤ y1 := by
    rw [← hq2_eq]
    exact exactBackwardQuotient_zero_le_q x u2 hw2 hx q2
  exact ⟨heq1_nat, hle_y1⟩

/--
  Theorem T3.9b (Universal `x`-Independent Subcritical Prefix Elimination):
-/
theorem exactBackwardQuotient_subcritical_prefix_le (x : Nat) (u1 u2 : List Bool)
    (hw2 : parityWeight u2 ≥ 1) (hx : x % 3 ≠ 0)
    (hsub : 3 ^ parityWeight u1 + affineCarry u1 ≤ 2 ^ u1.length) :
    exactBackwardQuotient x u2 0 ≤ exactBackwardQuotient x (u1 ++ u2) 0 := by
  have hw12 : parityWeight (u1 ++ u2) ≥ 1 := by rw [parityWeight_append]; omega
  have hy0_ge1 := (exactBackwardQuotient_spec x (u1 ++ u2) 0 hw12 hx).1
  rcases exactBackwardQuotient_prefix_step_law x u1 u2 hw2 hx with ⟨heq1, hle2⟩
  let y0 := exactBackwardQuotient x (u1 ++ u2) 0
  let y1 := collatzIter u1.length y0
  change y0 ≥ 1 at hy0_ge1
  change 2 ^ u1.length * y1 = 3 ^ parityWeight u1 * y0 + affineCarry u1 at heq1
  have hc_le : affineCarry u1 ≤ affineCarry u1 * y0 := by
    have hm := Nat.mul_le_mul_left (affineCarry u1) hy0_ge1; omega
  have hmul_le : 2 ^ u1.length * y1 ≤ 2 ^ u1.length * y0 := by
    have hm := Nat.mul_le_mul_right y0 hsub
    rw [Nat.add_mul] at hm
    omega
  have hp_pos : 2 ^ u1.length > 0 := pow2_pos_nat u1.length
  have hy1_le_y0 : y1 ≤ y0 := by
    by_cases hle : y1 ≤ y0
    · exact hle
    · have hm := Nat.mul_le_mul_left (2 ^ u1.length) (by omega : y0 + 1 ≤ y1)
      rw [Nat.mul_add, Nat.mul_one] at hm
      omega
  exact Nat.le_trans hle2 hy1_le_y0

-- ----------------------------------------------------------------------------
-- T3.10 & T3.11: Supercritical & Horizon-Supercritical Core Reductions + Fusions
-- ----------------------------------------------------------------------------

def IsSupercriticalCoreWord (u : List Bool) : Prop :=
  IsCoreParityWord u ∧
  ∀ u1 u2 : List Bool, u = u1 ++ u2 -> u1 ≠ [] -> u2 ≠ [] ->
    2 ^ u1.length < 3 ^ parityWeight u1 + affineCarry u1

def IsHorizonSupercriticalFor (n : Nat) (u : List Bool) : Prop :=
  IsCoreParityWord u ∧
  ∀ u1 u2 : List Bool, u = u1 ++ u2 -> u1 ≠ [] -> u2 ≠ [] ->
    2 ^ u1.length * n ≤ 3 ^ parityWeight u1 * (n - 1) + affineCarry u1

def findProperSplitAux (bad : List Bool -> Bool) (pref : List Bool) :
    List Bool -> Option (List Bool × List Bool)
  | [] => none
  | b :: rest =>
    let pref' := pref ++ [b]
    match rest with
    | [] => none
    | _ :: _ =>
      if bad pref' then some (pref', rest)
      else findProperSplitAux bad pref' rest

theorem findProperSplitAux_spec (bad : List Bool -> Bool) :
    ∀ (suff pref : List Bool),
      (∀ u1 u2 : List Bool,
        findProperSplitAux bad pref suff = some (u1, u2) ->
        pref ++ suff = u1 ++ u2 ∧ u1.length > pref.length ∧ u2 ≠ [] ∧ bad u1 = true) ∧
      (findProperSplitAux bad pref suff = none ->
        ∀ p2 u2 : List Bool, suff = p2 ++ u2 -> p2 ≠ [] -> u2 ≠ [] ->
          bad (pref ++ p2) = false)
  | [], _ => ⟨fun _ _ h => by simp [findProperSplitAux] at h,
              fun _ p2 _ hs hp2 _ => by cases p2 with | nil => exact False.elim (hp2 rfl) | cons _ _ => simp at hs⟩
  | b :: rest, pref => by
    cases rest with
    | nil =>
      refine ⟨fun _ _ h => by simp [findProperSplitAux] at h, ?_⟩
      intro _ p2 u2 hs hp2 hu2
      cases p2 with
      | nil => exact False.elim (hp2 rfl)
      | cons x pTail =>
        simp only [List.cons_append, List.cons.injEq] at hs
        have hlen := congrArg List.length hs.2
        cases u2 with
        | nil => exact False.elim (hu2 rfl)
        | cons _ _ => simp at hlen
    | cons r0 rTail =>
      simp only [findProperSplitAux]
      by_cases hb : bad (pref ++ [b]) = true
      · rw [hb]
        simp only [ite_true]
        refine ⟨?_, fun h => by simp at h⟩
        intro u1 u2 hsome
        simp only [Option.some.injEq, Prod.mk.injEq] at hsome
        rcases hsome with ⟨rfl, rfl⟩
        refine ⟨by rw [List.append_assoc]; rfl, by simp, by simp, hb⟩
      · have hbf : bad (pref ++ [b]) = false := by
          cases hval : bad (pref ++ [b]) with
          | false => rfl
          | true => exact False.elim (hb hval)
        rw [hbf]
        simp only [Bool.false_eq_true, ite_false]
        rcases findProperSplitAux_spec bad (r0 :: rTail) (pref ++ [b]) with ⟨ih_some, ih_none⟩
        refine ⟨?_, ?_⟩
        · intro u1 u2 hsome
          rcases ih_some u1 u2 hsome with ⟨happ, hlen, hu2, hbad⟩
          rw [List.append_assoc] at happ
          simp only [List.singleton_append] at happ
          rw [List.length_append] at hlen
          exact ⟨happ, by simp at hlen; omega, hu2, hbad⟩
        · intro hnone p2 u2 hs hp2 hu2
          cases p2 with
          | nil => exact False.elim (hp2 rfl)
          | cons x pTail =>
            simp only [List.cons_append, List.cons.injEq] at hs
            rcases hs with ⟨rfl, hrest_eq⟩
            cases pTail with
            | nil => simpa using hbf
            | cons y pTail' =>
              have hres := ih_none hnone (y :: pTail') u2 hrest_eq (by simp) hu2
              rw [List.append_assoc] at hres
              simpa using hres

theorem exactBackwardQuotient_append_replicate_false_ge (x : Nat) (u : List Bool)
    (hw : parityWeight u ≥ 1) (hx : x % 3 ≠ 0) :
    ∀ k : Nat, exactBackwardQuotient x u 0 ≤ exactBackwardQuotient x (u ++ List.replicate k false) 0
  | 0 => by simp
  | k + 1 => by
    rw [replicate_succ_append_local false k, ← List.append_assoc]
    have hwt : parityWeight (u ++ List.replicate k false) ≥ 1 := by
      rw [(affineCarry_append_replicate_false u k).1]; exact hw
    have hstep := (exactBackwardQuotient_false_cons_and_snoc x (u ++ List.replicate k false) hwt hx).2.2
    exact Nat.le_trans (exactBackwardQuotient_append_replicate_false_ge x u hw hx k) hstep

theorem reverse_head_true_imp_weight_pos (c : List Bool) (h : c.reverse.head? = some true) :
    parityWeight c ≥ 1 := by
  have hmem : ∀ l : List Bool, true ∈ l -> parityWeight l ≥ 1 := by
    intro l hm
    induction l with
    | nil => cases hm
    | cons b rest ih =>
      cases b with
      | true => simp [parityWeight]
      | false =>
        simp at hm
        simpa [parityWeight] using ih hm
  apply hmem c
  rw [← List.mem_reverse]
  cases hr : c.reverse with
  | nil => rw [hr] at h; simp at h
  | cons x xs =>
    rw [hr] at h; simp at h; subst h; simp

theorem append_last_true_imp_right_last_true (u1 u2 : List Bool)
    (hlast : (u1 ++ u2).reverse.head? = some true) (hu2 : u2 ≠ []) :
    u2.reverse.head? = some true := by
  rw [List.reverse_append] at hlast
  cases hr : u2.reverse with
  | nil =>
    have h0 := congrArg List.reverse hr
    simp at h0; exact False.elim (hu2 h0)
  | cons b rest =>
    rw [hr] at hlast; simp at hlast; subst hlast; rfl

theorem supercritical_core_word_dominance_aux : ∀ (fuel : Nat) (v : List Bool),
    v.length ≤ fuel -> parityWeight v ≥ 1 ->
    ∃ u : List Bool,
      u.length ≤ v.length ∧ IsSupercriticalCoreWord u ∧
      ∀ x : Nat, x % 3 ≠ 0 -> exactBackwardQuotient x u 0 ≤ exactBackwardQuotient x v 0
  | 0, v, hlen, hw => by
    cases v with
    | nil => simp [parityWeight] at hw
    | cons _ _ => simp at hlen
  | fuel + 1, v, hlen, hw => by
    rcases stripTrailingFalse_spec v with ⟨hrep, hcases, _⟩
    let c := (stripTrailingFalse v).1
    let trail := (stripTrailingFalse v).2
    change c ++ List.replicate trail false = v at hrep
    have hc_last : c.reverse.head? = some true := by
      rcases hcases with ⟨_, hwt0⟩ | ⟨_, hlast⟩
      · omega
      · exact hlast
    have hc_wt : parityWeight c ≥ 1 := reverse_head_true_imp_weight_pos c hc_last
    have hc_len : c.length ≤ v.length := by
      rw [← hrep, List.length_append]; omega
    have hc_le_v : ∀ x : Nat, x % 3 ≠ 0 ->
        exactBackwardQuotient x c 0 ≤ exactBackwardQuotient x v 0 := by
      intro x hx
      rw [← hrep]
      exact exactBackwardQuotient_append_replicate_false_ge x c hc_wt hx trail
    let bad : List Bool -> Bool := fun p => decide (3 ^ parityWeight p + affineCarry p ≤ 2 ^ p.length)
    rcases findProperSplitAux_spec bad c [] with ⟨hsome_sp, hnone_sp⟩
    cases hfind : findProperSplitAux bad [] c with
    | some pair =>
      rcases pair with ⟨u1, u2⟩
      rcases hsome_sp u1 u2 hfind with ⟨hc_split, hu1_len, hu2_ne, hbad_u1⟩
      simp only [List.nil_append, List.length_nil] at hc_split hu1_len
      have hsub_u1 : 3 ^ parityWeight u1 + affineCarry u1 ≤ 2 ^ u1.length :=
        of_decide_eq_true hbad_u1
      have hu2_last : u2.reverse.head? = some true :=
        append_last_true_imp_right_last_true u1 u2 (by rw [← hc_split]; exact hc_last) hu2_ne
      have hu2_wt : parityWeight u2 ≥ 1 := reverse_head_true_imp_weight_pos u2 hu2_last
      have hu2_len_lt : u2.length < v.length := by
        have hsum : c.length = u1.length + u2.length := by rw [hc_split, List.length_append]
        omega
      rcases supercritical_core_word_dominance_aux fuel u2 (by omega) hu2_wt with
        ⟨u, hu_len, hu_sup, hu_dom⟩
      refine ⟨u, by omega, hu_sup, ?_⟩
      intro x hx
      have h1 := hu_dom x hx
      have h2 : exactBackwardQuotient x u2 0 ≤ exactBackwardQuotient x c 0 := by
        rw [hc_split]
        exact exactBackwardQuotient_subcritical_prefix_le x u1 u2 hu2_wt hx hsub_u1
      exact Nat.le_trans h1 (Nat.le_trans h2 (hc_le_v x hx))
    | none =>
      have hno_bad := hnone_sp hfind
      have hc_head : c.head? = some true := by
        cases hc_def : c with
        | nil => rw [hc_def] at hc_last; simp at hc_last
        | cons b rest =>
          cases b with
          | true => rfl
          | false =>
            cases rest with
            | nil => rw [hc_def] at hc_last; simp at hc_last
            | cons r0 rTail =>
              have hbf := hno_bad [false] (r0 :: rTail) (by rw [hc_def]; rfl) (by simp) (by simp)
              simp only [List.nil_append] at hbf
              have hbt : bad [false] = true := by decide
              rw [hbt] at hbf; simp at hbf
      have hsup : IsSupercriticalCoreWord c := by
        refine ⟨⟨hc_head, hc_last⟩, ?_⟩
        intro u1 u2 hc_eq hu1 hu2
        have hbf := hno_bad u1 u2 hc_eq hu1 hu2
        simp only [List.nil_append] at hbf
        have hnle : ¬ (3 ^ parityWeight u1 + affineCarry u1 ≤ 2 ^ u1.length) :=
          of_decide_eq_false hbf
        omega
      exact ⟨c, hc_len, hsup, hc_le_v⟩

/--
  Theorem T3.10a (Universal `x`-Independent Supercritical Core-Word Dominance):
  Every parity word `v` of weight `≥ 1` admits a supercritical core word `u` (`u.length ≤ v.length`)
  such that `exactBackwardQuotient x u 0 ≤ exactBackwardQuotient x v 0` simultaneously for ALL `x % 3 ≠ 0`!
-/
theorem supercritical_core_word_dominance (v : List Bool) (hv : parityWeight v ≥ 1) :
    ∃ u : List Bool,
      u.length ≤ v.length ∧ IsSupercriticalCoreWord u ∧
      ∀ x : Nat, x % 3 ≠ 0 -> exactBackwardQuotient x u 0 ≤ exactBackwardQuotient x v 0 :=
  supercritical_core_word_dominance_aux v.length v (Nat.le_refl _) hv

theorem horizon_supercritical_core_reduction_aux (n x : Nat) (hn : n ≥ 2) (hx : x % 3 ≠ 0) :
    ∀ (fuel : Nat) (v : List Bool),
      v.length ≤ fuel -> parityWeight v ≥ 1 -> exactBackwardQuotient x v 0 < n ->
      ∃ u : List Bool,
        u.length ≤ v.length ∧ IsHorizonSupercriticalFor n u ∧
        exactBackwardQuotient x u 0 < n
  | 0, v, hlen, hw, _ => by
    cases v with
    | nil => simp [parityWeight] at hw
    | cons _ _ => simp at hlen
  | fuel + 1, v, hlen, hw, hlt => by
    rcases stripTrailingFalse_spec v with ⟨hrep, hcases, _⟩
    let c := (stripTrailingFalse v).1
    let trail := (stripTrailingFalse v).2
    change c ++ List.replicate trail false = v at hrep
    have hc_last : c.reverse.head? = some true := by
      rcases hcases with ⟨_, hwt0⟩ | ⟨_, hlast⟩
      · omega
      · exact hlast
    have hc_wt : parityWeight c ≥ 1 := reverse_head_true_imp_weight_pos c hc_last
    have hc_len : c.length ≤ v.length := by rw [← hrep, List.length_append]; omega
    have hc_lt : exactBackwardQuotient x c 0 < n := by
      have hle : exactBackwardQuotient x c 0 ≤ exactBackwardQuotient x v 0 := by
        rw [← hrep]
        exact exactBackwardQuotient_append_replicate_false_ge x c hc_wt hx trail
      omega
    let badN : List Bool -> Bool :=
      fun p => decide (3 ^ parityWeight p * (n - 1) + affineCarry p < 2 ^ p.length * n)
    rcases findProperSplitAux_spec badN c [] with ⟨hsome_sp, hnone_sp⟩
    cases hfind : findProperSplitAux badN [] c with
    | some pair =>
      rcases pair with ⟨u1, u2⟩
      rcases hsome_sp u1 u2 hfind with ⟨hc_split, hu1_len, hu2_ne, hbad_u1⟩
      simp only [List.nil_append, List.length_nil] at hc_split hu1_len
      have hsub_n : 3 ^ parityWeight u1 * (n - 1) + affineCarry u1 < 2 ^ u1.length * n :=
        of_decide_eq_true hbad_u1
      have hu2_last : u2.reverse.head? = some true :=
        append_last_true_imp_right_last_true u1 u2 (by rw [← hc_split]; exact hc_last) hu2_ne
      have hu2_wt : parityWeight u2 ≥ 1 := reverse_head_true_imp_weight_pos u2 hu2_last
      have hu2_len_lt : u2.length < v.length := by
        have hsum : c.length = u1.length + u2.length := by rw [hc_split, List.length_append]
        omega
      have hc_lt' : exactBackwardQuotient x (u1 ++ u2) 0 < n := by rw [← hc_split]; exact hc_lt
      rcases exactBackwardQuotient_prefix_step_law x u1 u2 hu2_wt hx with ⟨heq1, hle2⟩
      let y0 := exactBackwardQuotient x (u1 ++ u2) 0
      let y1 := collatzIter u1.length y0
      change 2 ^ u1.length * y1 = 3 ^ parityWeight u1 * y0 + affineCarry u1 at heq1
      have hy0_le : y0 ≤ n - 1 := by dsimp [y0]; omega
      have hm_y0 : 3 ^ parityWeight u1 * y0 ≤ 3 ^ parityWeight u1 * (n - 1) :=
        Nat.mul_le_mul_left _ hy0_le
      have hy1_mul_lt : 2 ^ u1.length * y1 < 2 ^ u1.length * n := by omega
      have hy1_lt : y1 < n := by
        by_cases hy_lt : y1 < n
        · exact hy_lt
        · have hm := Nat.mul_le_mul_left (2 ^ u1.length) (by omega : n ≤ y1); omega
      have hu2_lt : exactBackwardQuotient x u2 0 < n := Nat.lt_of_le_of_lt hle2 hy1_lt
      rcases horizon_supercritical_core_reduction_aux n x hn hx fuel u2 (by omega) hu2_wt hu2_lt with
        ⟨u, hu_len, hu_hor, hu_lt⟩
      exact ⟨u, by omega, hu_hor, hu_lt⟩
    | none =>
      have hno_bad := hnone_sp hfind
      have hc_head : c.head? = some true := by
        cases hc_def : c with
        | nil => rw [hc_def] at hc_last; simp at hc_last
        | cons b rest =>
          cases b with
          | true => rfl
          | false =>
            cases rest with
            | nil => rw [hc_def] at hc_last; simp at hc_last
            | cons r0 rTail =>
              have hbf := hno_bad [false] (r0 :: rTail) (by rw [hc_def]; rfl) (by simp) (by simp)
              simp only [List.nil_append] at hbf
              have hnlt : ¬ (3 ^ parityWeight [false] * (n - 1) + affineCarry [false] <
                  2 ^ ([false] : List Bool).length * n) := of_decide_eq_false hbf
              have h0_car : affineCarry [false] = 0 := rfl
              have h0_wt : parityWeight [false] = 0 := rfl
              have h0_len : ([false] : List Bool).length = 1 := rfl
              rw [h0_car, h0_wt, h0_len] at hnlt
              simp at hnlt
              omega
      have hhor : IsHorizonSupercriticalFor n c := by
        refine ⟨⟨hc_head, hc_last⟩, ?_⟩
        intro u1 u2 hc_eq hu1 hu2
        have hbf := hno_bad u1 u2 hc_eq hu1 hu2
        simp only [List.nil_append] at hbf
        have hnlt : ¬ (3 ^ parityWeight u1 * (n - 1) + affineCarry u1 < 2 ^ u1.length * n) :=
          of_decide_eq_false hbf
        omega
      exact ⟨c, hc_len, hhor, hc_lt⟩

/--
  Theorem T3.10b (Pointwise `n`-Horizon Supercritical Core-Word Reduction):
  Eliminates `19/5`, `29/5`, AND `319/13 = 24.54` proper prefixes at `n ≥ 7` via `y0 ≤ n - 1`!
-/
theorem horizon_supercritical_core_reduction_at_n (n x : Nat) (v : List Bool)
    (hn : n ≥ 2) (hx : x % 3 ≠ 0) (hv : parityWeight v ≥ 1)
    (hlt : exactBackwardQuotient x v 0 < n) :
    ∃ u : List Bool,
      u.length ≤ v.length ∧ IsHorizonSupercriticalFor n u ∧
      exactBackwardQuotient x u 0 < n :=
  horizon_supercritical_core_reduction_aux n x hn hx v.length v (Nat.le_refl _) hv hlt

def Mod1296HorizonSupercriticalContractionProp : Prop :=
  ∀ n : Nat, n ≥ 7 -> IsSurvivingMod1296Class n ->
    ∃ (K : Nat) (u : List Bool),
      K ≥ 1 ∧ IsHorizonSupercriticalFor n u ∧
      exactBackwardQuotient (collatzIter K n) u 0 < n

/--
  Theorem T3.11a (`CollatzConjectureStandard ↔ Mod1296HorizonSupercriticalContractionProp`):
-/
theorem collatz_standard_iff_mod1296_horizon_supercritical_contraction :
    CollatzConjectureStandard ↔ Mod1296HorizonSupercriticalContractionProp := by
  rw [collatz_standard_iff_mod1296_core_quotient_contraction]
  constructor
  · intro hcore n hn hs
    rcases hcore n hn hs with ⟨K, v, hK, hv_core, hlt⟩
    have hv_wt : parityWeight v ≥ 1 := reverse_head_true_imp_weight_pos v hv_core.2
    have hx_n3 : collatzIter K n % 3 ≠ 0 := surviving_mod1296_iter_mod3_ne_zero K n hK hs
    rcases horizon_supercritical_core_reduction_at_n n (collatzIter K n) v (by omega) hx_n3 hv_wt hlt with
      ⟨u, _, hhor, hu_lt⟩
    exact ⟨K, u, hK, hhor, hu_lt⟩
  · intro hhor n hn hs
    rcases hhor n hn hs with ⟨K, u, hK, hu_hor, hlt⟩
    exact ⟨K, u, hK, hu_hor.1, hlt⟩

def Mod46656HorizonSupercriticalContractionProp : Prop :=
  ∀ n : Nat, n ≥ 7 -> IsSurvivingMod46656Class n ->
    ∃ (K : Nat) (u : List Bool),
      K ≥ 1 ∧ IsHorizonSupercriticalFor n u ∧
      exactBackwardQuotient (collatzIter K n) u 0 < n

def Mod373248HorizonSupercriticalContractionProp : Prop :=
  ∀ n : Nat, IsSurvivingMod373248Class n ->
    ∃ (K : Nat) (u : List Bool),
      K ≥ 1 ∧ IsHorizonSupercriticalFor n u ∧
      exactBackwardQuotient (collatzIter K n) u 0 < n

/--
  Theorem T3.11b (Cross-Track Master Fusion: `CollatzConjectureStandard ↔ Mod373248HorizonSupercriticalContractionProp`):
  Couples Track 2's `10314 / 373248 ≈ 2.7633%` (`n ≥ 27`) sieve with Track 3's `IsHorizonSupercriticalFor n u`!
-/
theorem collatz_standard_iff_mod373248_horizon_supercritical_contraction :
    CollatzConjectureStandard ↔ Mod373248HorizonSupercriticalContractionProp := by
  rw [collatz_conjecture_iff_mod373248_core_quotient_contraction]
  constructor
  · intro hcore n hs373
    rcases hcore n hs373 with ⟨K, v, hK, hv_core, hlt⟩
    have hn_ge27 : n ≥ 27 := survivingMod373248_ge_27 n hs373
    have hs1296 : IsSurvivingMod1296Class n :=
      (survivingMod46656_imp_mod1296 n (survivingMod373248_imp_mod46656 n hs373)).1
    have hv_wt : parityWeight v ≥ 1 := reverse_head_true_imp_weight_pos v hv_core.2
    have hx_n3 : collatzIter K n % 3 ≠ 0 := surviving_mod1296_iter_mod3_ne_zero K n hK hs1296
    rcases horizon_supercritical_core_reduction_at_n n (collatzIter K n) v (by omega) hx_n3 hv_wt hlt with
      ⟨u, _, hhor, hu_lt⟩
    exact ⟨K, u, hK, hhor, hu_lt⟩
  · intro hhor n hs373
    rcases hhor n hs373 with ⟨K, u, hK, hu_hor, hlt⟩
    exact ⟨K, u, hK, hu_hor.1, hlt⟩

/--
  Theorem T3.11c (Cross-Track Fusion: `CollatzConjectureStandard ↔ Mod46656HorizonSupercriticalContractionProp`):
-/
theorem collatz_standard_iff_mod46656_horizon_supercritical_contraction :
    CollatzConjectureStandard ↔ Mod46656HorizonSupercriticalContractionProp := by
  constructor
  · intro hstd n hn hs46
    exact (collatz_standard_iff_mod1296_horizon_supercritical_contraction.mp hstd) n hn
      (survivingMod46656_imp_mod1296 n hs46).1
  · intro hprop
    rw [collatz_standard_iff_mod373248_horizon_supercritical_contraction]
    intro n hs373
    have hn_ge27 : n ≥ 27 := survivingMod373248_ge_27 n hs373
    exact hprop n (by omega) (survivingMod373248_imp_mod46656 n hs373)

-- ----------------------------------------------------------------------------
-- T3.12: Koopman `3^(w-1)`-Fiber Annihilation & Log Suffix-Shift Bottleneck
-- ----------------------------------------------------------------------------

def koopmanBranch0 (w b : Nat) : Nat := (((3 ^ w + 1) / 2) * b) % 3 ^ w
def koopmanBranch1 (w b : Nat) : Nat := (((3 ^ w + 1) / 2) * (3 * b + 1)) % 3 ^ w
def scaledKoopman (w : Nat) (f : Nat -> Int) (b : Nat) : Int :=
  f (koopmanBranch0 w b) + f (koopmanBranch1 w b)

/--
  Theorem T3.12a (Koopman `3^(w-1)`-Fiber Annihilation of the `3x + 1` Branch for ALL `w ≥ 1`):
-/
theorem koopman_primitive_fiber_annihilation (w b t1 t2 : Nat) (f : Nat -> Int) (hw : w ≥ 1) :
    (2 * koopmanBranch0 w b) % 3 ^ w = b % 3 ^ w ∧
    (2 * koopmanBranch1 w b) % 3 ^ w = (3 * b + 1) % 3 ^ w ∧
    koopmanBranch1 w b % 3 = 2 ∧
    koopmanBranch1 w (b + t1 * 3 ^ (w - 1)) = koopmanBranch1 w b ∧
    scaledKoopman w f (b + t1 * 3 ^ (w - 1)) - scaledKoopman w f (b + t2 * 3 ^ (w - 1)) =
      f (koopmanBranch0 w (b + t1 * 3 ^ (w - 1))) - f (koopmanBranch0 w (b + t2 * 3 ^ (w - 1))) := by
  let M := 3 ^ w
  have hp3_odd : M % 2 = 1 := pow3_mod2_nat w
  obtain ⟨inv2, hinv2_eq⟩ : ∃ inv2 : Nat, M + 1 = 2 * inv2 := ⟨(M + 1) / 2, by omega⟩
  have hdiv_inv2 : (M + 1) / 2 = inv2 := by omega
  have hmul2_cancel : ∀ z : Nat, (2 * ((inv2 * z) % M)) % M = z % M := by
    intro z
    rw [Nat.mul_mod 2 ((inv2 * z) % M) M, Nat.mod_mod, ← Nat.mul_mod,
        ← Nat.mul_assoc 2 inv2 z, ← hinv2_eq, Nat.add_mul, Nat.one_mul,
        Nat.add_mod, Nat.mul_mod M z M, Nat.mod_self, Nat.zero_mul, Nat.zero_mod,
        Nat.zero_add, Nat.mod_mod]
  have hc0 : (2 * koopmanBranch0 w b) % M = b % M := by
    unfold koopmanBranch0; change (2 * (((M + 1) / 2 * b) % M)) % M = b % M
    rw [hdiv_inv2]; exact hmul2_cancel b
  have hc1 : (2 * koopmanBranch1 w b) % M = (3 * b + 1) % M := by
    unfold koopmanBranch1; change (2 * (((M + 1) / 2 * (3 * b + 1)) % M)) % M = (3 * b + 1) % M
    rw [hdiv_inv2]; exact hmul2_cancel (3 * b + 1)
  have hM_factor : M = 3 * 3 ^ (w - 1) := by
    dsimp [M]
    conv => lhs; rw [show w = (w - 1) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
  have hc2 : koopmanBranch1 w b % 3 = 2 := by
    have h2mod3 : (2 * koopmanBranch1 w b) % 3 = 1 := by
      have hm1 := congrArg (fun z => z % 3) hc1
      rw [hM_factor, mod_mul_mod_eq _ 3 (3 ^ (w - 1)), mod_mul_mod_eq _ 3 (3 ^ (w - 1))] at hm1
      have hr : (3 * b + 1) % 3 = 1 := by omega
      rw [hr] at hm1; exact hm1
    omega
  have hfiber : ∀ t : Nat, koopmanBranch1 w (b + t * 3 ^ (w - 1)) = koopmanBranch1 w b := by
    intro t
    unfold koopmanBranch1
    change (((M + 1) / 2) * (3 * (b + t * 3 ^ (w - 1)) + 1)) % M =
      (((M + 1) / 2) * (3 * b + 1)) % M
    rw [hdiv_inv2]
    have harg : 3 * (b + t * 3 ^ (w - 1)) + 1 = (3 * b + 1) + M * t := by
      calc
        3 * (b + t * 3 ^ (w - 1)) + 1
            = 3 * b + 3 * (t * 3 ^ (w - 1)) + 1 := by rw [Nat.mul_add]
        _ = (3 * b + 1) + (3 * 3 ^ (w - 1)) * t := by
              rw [← Nat.mul_assoc 3 t, Nat.mul_comm 3 t, Nat.mul_assoc t 3, Nat.mul_comm t]
              omega
        _ = (3 * b + 1) + M * t := by rw [← hM_factor]
    rw [harg, Nat.mul_add, ← Nat.mul_assoc inv2 M t, Nat.mul_comm inv2 M, Nat.mul_assoc M inv2 t,
        Nat.add_mod, Nat.mul_mod M (inv2 * t) M, Nat.mod_self, Nat.zero_mul, Nat.zero_mod,
        Nat.add_zero, Nat.mod_mod]
  refine ⟨hc0, hc1, hc2, hfiber t1, ?_⟩
  unfold scaledKoopman
  rw [hfiber t1, hfiber t2]
  omega

theorem affineCarry_true_cons (r : List Bool) :
    affineCarry (true :: r) = 3 ^ parityWeight r + 2 * affineCarry r := by
  have h : (affineCarry (true :: r) : Int) =
      ((3 ^ parityWeight r + 2 * affineCarry r : Nat) : Int) := by
    rw [natCast_add, natCast_pow3, natCast_mul, ← affineCarryInt_ofNat, ← affineCarryInt_ofNat]
    unfold affineCarryInt
    simp only [affineCarryAuxInt]
    have h10 : 3 * (0 : Int) + (2 : Int) ^ 0 = 1 := rfl
    have h01 : 0 + 1 = 1 := rfl
    rw [h01, h10, affineCarryAuxInt_shift r 1 1]
    omega
  omega

/--
  Theorem T3.12b (Sharp Universal Carry Upper Bound — Equality on `0^(L - w) 1^w`):
-/
theorem affineCarry_universal_upper_bound : ∀ (u : List Bool),
    affineCarry u ≤ 2 ^ (u.length - parityWeight u) * (3 ^ parityWeight u - 2 ^ parityWeight u)
  | [] => by simp [affineCarry, affineCarryAux, parityWeight]
  | false :: r => by
    have ih := affineCarry_universal_upper_bound r
    have hle_len := parityWeight_le_length r
    have hsub : (false :: r).length - parityWeight (false :: r) = (r.length - parityWeight r) + 1 := by
      simp [parityWeight]; omega
    rw [affineCarry_false_cons, hsub, Nat.pow_succ, Nat.mul_comm (2 ^ (r.length - parityWeight r)) 2,
        Nat.mul_assoc]
    simp only [parityWeight]
    exact Nat.mul_le_mul_left 2 ih
  | true :: r => by
    have ih := affineCarry_universal_upper_bound r
    let w := parityWeight r
    let z := r.length - w
    have hsub : (true :: r).length - parityWeight (true :: r) = z := by
      dsimp [z, w]; simp [parityWeight]; omega
    have hwt : parityWeight (true :: r) = w + 1 := by dsimp [w]; simp [parityWeight]; omega
    rw [affineCarry_true_cons, hsub, hwt]
    change 3 ^ w + 2 * affineCarry r ≤ 2 ^ z * (3 ^ (w + 1) - 2 ^ (w + 1))
    have hpz : 1 ≤ 2 ^ z := pow2_pos_nat z
    have h23 : 2 ^ w ≤ 3 ^ w := pow2_le_pow3 w
    have h1_le : 3 ^ w ≤ 2 ^ z * 3 ^ w := by
      have hm := Nat.mul_le_mul_right (3 ^ w) hpz; simpa using hm
    have h2_le : 2 * affineCarry r ≤ 2 ^ z * (2 * (3 ^ w - 2 ^ w)) := by
      have hm := Nat.mul_le_mul_left 2 ih
      change 2 * affineCarry r ≤ 2 * (2 ^ z * (3 ^ w - 2 ^ w)) at hm
      rwa [← Nat.mul_assoc 2 (2 ^ z), Nat.mul_comm 2 (2 ^ z), Nat.mul_assoc] at hm
    have hrhs_eq : 2 ^ z * 3 ^ w + 2 ^ z * (2 * (3 ^ w - 2 ^ w)) =
        2 ^ z * (3 ^ (w + 1) - 2 ^ (w + 1)) := by
      rw [← Nat.mul_add (2 ^ z)]
      congr 1
      rw [Nat.pow_succ 3 w, Nat.pow_succ 2 w]
      omega
    omega

/--
  Theorem T3.12c (Non-Descending Archimedean Suffix-Shift Bottleneck):
  Whenever a non-descending iterate `x ≥ n ≥ 1` (`x % 3 ≠ 0`) achieves contractive quotient
  `exactBackwardQuotient x u 0 < n`, `canonicalSuffixShift u x` MUST fall inside the
  logarithmic arc `2^a < 3^w` (`a < ⌈w log_2 3⌉` inside `[0, 2 * 3^(w - 1))`)!
-/
theorem non_descending_contraction_forces_log_shift_arc (n x : Nat) (u : List Bool)
    (hn : n ≥ 1) (hx_ge : x ≥ n) (hx : x % 3 ≠ 0) (hw : parityWeight u ≥ 1)
    (hlt : exactBackwardQuotient x u 0 < n) :
    2 ^ (canonicalSuffixShift u x) < 3 ^ parityWeight u := by
  let w := parityWeight u
  let a := canonicalSuffixShift u x
  let y := exactBackwardQuotient x u 0
  let z := u.length - w
  rcases exactBackwardQuotient_spec x u 0 hw hx with ⟨_, heq, _, _⟩
  simp only [Nat.zero_mul, Nat.add_zero] at heq
  change 2 ^ (u.length + a) * x = 3 ^ w * y + affineCarry u at heq
  have hle_len : w ≤ u.length := parityWeight_le_length u
  have hlen_split : u.length = z + w := by dsimp [z]; omega
  have hpz_ge1 : 2 ^ z ≥ 1 := pow2_pos_nat z
  have hpw_ge2 : 2 ^ w ≥ 2 := by
    rw [show w = (w - 1) + 1 by omega, Nat.pow_succ]
    have hp := pow2_pos_nat (w - 1); omega
  have h2u_ge : 1 + 2 ^ z ≤ 2 ^ u.length := by
    rw [hlen_split, Nat.pow_add]
    have hm := Nat.mul_le_mul_left (2 ^ z) hpw_ge2
    omega
  have hc_ub := affineCarry_universal_upper_bound u
  change affineCarry u ≤ 2 ^ z * (3 ^ w - 2 ^ w) at hc_ub
  have h23 : 2 ^ w ≤ 3 ^ w := pow2_le_pow3 w
  have hc_lt : affineCarry u < 2 ^ z * 3 ^ w := by
    have hsub_lt : 3 ^ w - 2 ^ w < 3 ^ w := by omega
    have hm : 2 ^ z * (3 ^ w - 2 ^ w) < 2 ^ z * 3 ^ w :=
      Nat.mul_lt_mul_of_pos_left hsub_lt hpz_ge1
    omega
  have hy_le : 3 ^ w * y ≤ 3 ^ w * (n - 1) := Nat.mul_le_mul_left (3 ^ w) (by dsimp [y]; omega)
  have hzn_le : 2 ^ z * 3 ^ w ≤ 2 ^ z * (3 ^ w * n) := by
    have hm : 3 ^ w * 1 ≤ 3 ^ w * n := Nat.mul_le_mul_left (3 ^ w) hn
    rw [Nat.mul_one] at hm
    exact Nat.mul_le_mul_left (2 ^ z) hm
  have hsum_lt : 2 ^ (u.length + a) * x < 2 ^ u.length * (3 ^ w * n) := by
    have hprod_le : (1 + 2 ^ z) * (3 ^ w * n) ≤ 2 ^ u.length * (3 ^ w * n) :=
      Nat.mul_le_mul_right (3 ^ w * n) h2u_ge
    rw [Nat.add_mul, Nat.one_mul] at hprod_le
    have hn_le : 3 ^ w * (n - 1) ≤ 3 ^ w * n := Nat.mul_le_mul_left (3 ^ w) (by omega)
    omega
  by_cases harc : 2 ^ a < 3 ^ w
  · exact harc
  · have hge_arc : 3 ^ w ≤ 2 ^ a := by omega
    have hm_ax : 3 ^ w * n ≤ 2 ^ a * x := Nat.mul_le_mul hge_arc hx_ge
    have hm_full : 2 ^ u.length * (3 ^ w * n) ≤ 2 ^ (u.length + a) * x := by
      rw [Nat.pow_add, Nat.mul_assoc]
      exact Nat.mul_le_mul_left (2 ^ u.length) hm_ax
    omega

end CollatzFormal
