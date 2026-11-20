/-
  CollatzFormal/Wave13WholeSpace.lean
  Wave 13 Whole-Space Mathematical & CS Proof Loop (Synthesis — Fronts C & D):
  1. Front C (Branches P1.2 & P5.12):
     - Weighted Residue-Potential Mod-`9` Branch Lookahead (`optShiftMod9`, `cMod9 y * y ≤ 8 * cMod9 x * x`)
       & Eventual (`∀ M_0 ≥ 3`) Unrestricted-Numerator Cube-Root-of-2 Critical-Base Impossibility
       (`p_B ^ 3 < 2 * q_B ^ 3`, refuting `(5, 4), (6, 5), (7, 6), (8, 7), (9, 8)` + Base-`5/4` Certificate),
     - Universal `3`-Coprime-Preserving Backward Shift Even-Spine Minimax Floor (`evenSpineIter r_pol (2*k) x_0
       ≥ 64^k * x_0` across ALL Mod-`27`, Mod-`81`, Mod-`3^K`, and Arbitrary `x`-Oracle Policies, Proving
       `2^(1/3)` Is the Exact Sharp Minimax Ceiling of `3`-Coprime-Preserving Branch Trees),
     - Eventual (`∀ M_0 ≥ 3`) Impossibility of ALL Single-Exponential-Numerator / Quadratic-Exponential-
       Denominator (`(p_D / q_D)^(binBitLength(n)^2)`, `p_D > q_D ≥ 1`) Preimage Weights Along Reverse
       Syracuse Chains (`L_0^2 - L_{4s}^2 ≥ 20 * s^2 + 16 * s + 3`),
     - End-to-End Global Convergence, 8-Tier `ω^8` Cascade (`Cone 11 -> Cone 10 -> ... -> Cone 5 -> Φ_2`),
       Choice-Free `Q_(6)^+` Cone-11 Avoidance, 6-Step Newton–Hensel `mod 2^31` Odd-Inverse, & `[]`-Axiom
       `M1/M2/M3` Counter-Model Separation for the 10th Solvable `(3x + 1)`-Cousin `T_diamond10`
       (`25769147597 -> 9663430349` in `20` steps to `1`).
  2. Front D (Branches P2.2 & P5.3):
     - Complete Mod-`1458` (`2 * 3^6`) Markov Shift Bijection (`Fin 486` ↔ `486` surviving classes, matching
       the automatic `w(u) ≥ 7` weight across 100% of length `≥ 10` surviving `mod 512` core extensions!),
       Universal `7`-Ones `729 mod 1458` Lock, & `3^(w - 7)` (`j = 6`) Multi-Step Fiber Equidistribution,
     - Choice-Free Dyadic Window `M = 5` (`[32, 64)`) Empty-Window Impossibility (`∀ L_max,
       dyadicWindowSurvivingQ0Leaves L_max 5 = []`) vs `M = 4` (`[27]`) and `M = 6` (`111, 127`),
     - Constructive Two-Zero-Run Family `uWin M j` (`a = 3, w = 11, y % 512 = 511, y % 81 = 1`) Proving
       Unconditional Strictly Growing Lower-Bound Dyadic-Window Occupancy
       `(dyadicWindowSurvivingQ0Leaves (M + 15) M).length ≥ R` (`∀ R ≥ 1, ∀ M ≥ R * 3188646`).

  Zero `sorry`, zero `native_decide`, zero custom axioms.
-/

import CollatzFormal.Wave13WholeSpaceCore

namespace CollatzFormal

-- ============================================================================
-- SECTION 1: Front C Part 1 (Branch P1.2) — Cube-Root-of-2 (`p_B^3 < 2 * q_B^3`)
--            Critical-Base Impossibility, Universal Mod-`3^K` Even-Spine `64^k`
--            Minimax Floor, & Quadratic-Exponential Denominator Impossibility (`W13_H3`)
-- ============================================================================

private theorem mul_pow_w13s (a b : Nat) : ∀ n : Nat, (a * b) ^ n = a ^ n * b ^ n
  | 0 => rfl
  | n + 1 => by
    rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, mul_pow_w13s a b n]
    ac_rfl

private theorem pow_mono_base_w13s (a b : Nat) (hle : a ≤ b) : ∀ n : Nat, a ^ n ≤ b ^ n
  | 0 => Nat.le_refl 1
  | n + 1 => Nat.mul_le_mul (pow_mono_base_w13s a b hle n) hle

private theorem id_lt_pow2_w13s : ∀ n : Nat, n < 2 ^ n
  | 0 => by decide
  | n + 1 => by
    have ih := id_lt_pow2_w13s n
    have hp := pow2_pos_nat n
    rw [Nat.pow_succ]
    omega

private theorem ite_true_dec {p : Prop} [inst : Decidable p] {α : Type} {a b : α} (hp : p) :
    (if p then a else b) = a := by
  cases inst with
  | isTrue _ => rfl
  | isFalse hnp => exact False.elim (hnp hp)

private theorem ite_false_dec {p : Prop} [inst : Decidable p] {α : Type} {a b : α} (hnp : ¬ p) :
    (if p then a else b) = b := by
  cases inst with
  | isTrue hp => exact False.elim (hnp hp)
  | isFalse _ => rfl

private theorem bernoulli_nat_mul_w13s (A : Nat) :
    ∀ n : Nat, A ^ (n + 1) + n * A ^ n ≤ A * (A + 1) ^ n
  | 0 => by simp
  | n + 1 => by
    have ih := bernoulli_nat_mul_w13s A n
    have hm := Nat.mul_le_mul_right (A + 1) ih
    have hr : (A * (A + 1) ^ n) * (A + 1) = A * (A + 1) ^ (n + 1) := by
      rw [Nat.mul_assoc, ← Nat.pow_succ]
    rw [hr] at hm
    have hl : A ^ (n + 2) + (n + 1) * A ^ (n + 1) ≤ (A ^ (n + 1) + n * A ^ n) * (A + 1) := by
      have heq : (A ^ (n + 1) + n * A ^ n) * (A + 1) =
          (A ^ (n + 2) + (n + 1) * A ^ (n + 1)) + n * A ^ n := by
        rw [show n + 2 = (n + 1) + 1 from rfl, Nat.pow_succ A (n + 1),
            Nat.add_mul n 1 (A ^ (n + 1)), Nat.one_mul,
            Nat.pow_succ A n,
            Nat.add_mul (A ^ n * A) (n * A ^ n) (A + 1),
            Nat.mul_add (A ^ n * A) A 1, Nat.mul_one,
            Nat.mul_add (n * A ^ n) A 1, Nat.mul_one]
        ac_rfl
      rw [heq]
      exact Nat.le_add_right _ _
    exact Nat.le_trans hl hm

private theorem pow_gt_const_mul_pow_of_lt_w13s (A B K_0 : Nat) (hA : A ≥ 1) (hAB : A < B) :
    let k := K_0 * A
    K_0 * A ^ k < B ^ k := by
  dsimp only
  let k := K_0 * A
  have hbern := bernoulli_nat_mul_w13s A k
  have hb_mono : A * (A + 1) ^ k ≤ A * B ^ k :=
    Nat.mul_le_mul_left A (pow_mono_base_w13s (A + 1) B (by omega) k)
  have hle_AB : A ^ (k + 1) + k * A ^ k ≤ A * B ^ k := Nat.le_trans hbern hb_mono
  have hfac : A ^ (k + 1) + k * A ^ k = A * ((K_0 + 1) * A ^ k) := by
    dsimp only [k]
    rw [Nat.pow_succ A (K_0 * A), Nat.mul_comm (A ^ (K_0 * A)) A,
        Nat.add_mul K_0 1 (A ^ (K_0 * A)), Nat.one_mul, Nat.mul_add A]
    ac_rfl
  rw [hfac] at hle_AB
  have hle_B : (K_0 + 1) * A ^ k ≤ B ^ k :=
    nat_mul_le_cancel_left_w5 A _ _ (by omega) hle_AB
  have hAk_pos : A ^ k ≥ 1 := nat_pow_pos_of_pos A (by omega) k
  rw [Nat.add_mul K_0 1 (A ^ k), Nat.one_mul] at hle_B
  dsimp only [k] at hle_B hAk_pos ⊢
  omega

private theorem two_mul_pow_self_le_succ_pow_w13s (q : Nat) (hq : q ≥ 1) :
    2 * q ^ q ≤ (q + 1) ^ q := by
  have hb := bernoulli_nat_mul_w13s q q
  have hfac : q ^ (q + 1) + q * q ^ q = q * (2 * q ^ q) := by
    rw [Nat.pow_succ q q, show (2 : Nat) = 1 + 1 from rfl, Nat.add_mul 1 1 (q ^ q),
        Nat.one_mul, Nat.mul_add q]
    ac_rfl
  rw [hfac] at hb
  exact nat_mul_le_cancel_left_w5 q _ _ (by omega) hb

-- ----------------------------------------------------------------------------
-- Section 1A: Weighted Residue-Potential Mod-`9` Branch Lookahead (`optShiftMod9`)
--             & Cube-Root-of-2 (`p_B^3 < 2 * q_B^3`) Critical-Base Impossibility
-- ----------------------------------------------------------------------------

/-- Minimax Mod-`9` backward halving-shift policy `r(x mod 9) ∈ {1, 2, 3, 4}` sending `2^r * x`
    to `{2, 8} mod 9` while strictly bounding weighted residue potential growth by `8x` per step! -/
def optShiftMod9 (x : Nat) : Nat :=
  match x % 9 with
  | 1 => 1
  | 2 => 2
  | 4 => 1
  | 5 => 2
  | 7 => 3
  | _ => 4

/-- Residue potential multiplier `cMod9(x) ∈ {1, 2, 4}` solving the minimax eigenvector inequality
    `cMod9(y_i) * y_i ≤ 8 * cMod9(x) * x` across BOTH backward Collatz children `y_0, y_1`! -/
def cMod9 (x : Nat) : Nat :=
  match x % 9 with
  | 1 => 1
  | 2 => 2
  | 4 => 1
  | 5 => 1
  | 7 => 2
  | _ => 4

/-- Greedy backward Collatz branch selector under `optShiftMod9`. -/
def cubeRootTwoBranchNext (wNum wDen : Nat -> Nat) (x : Nat) : Nat :=
  let m := 2 ^ optShiftMod9 x * x
  let y0 := 2 * m
  let y1 := (2 * m - 1) / 3
  if 2 * wNum y0 * wDen m ≤ wNum m * wDen y0 then y0 else y1

/-- `k`-step iteration of `cubeRootTwoBranchNext`. -/
def cubeRootTwoBranchIter (wNum wDen : Nat -> Nat) : Nat -> Nat -> Nat
  | 0, x => x
  | k + 1, x => cubeRootTwoBranchIter wNum wDen k (cubeRootTwoBranchNext wNum wDen x)

private theorem cMod9_bounds (z : Nat) : 1 ≤ cMod9 z ∧ cMod9 z ≤ 4 := by
  unfold cMod9
  have hr : z % 9 < 9 := Nat.mod_lt z (by decide)
  rcases (by omega :
    z % 9 = 0 ∨ z % 9 = 1 ∨ z % 9 = 2 ∨ z % 9 = 3 ∨ z % 9 = 4 ∨
    z % 9 = 5 ∨ z % 9 = 6 ∨ z % 9 = 7 ∨ z % 9 = 8) with
    h | h | h | h | h | h | h | h | h <;> simp [h]

private theorem cMod9_le_two_of_mod3_eq_one (z : Nat) (hz : z % 3 = 1) : cMod9 z ≤ 2 := by
  unfold cMod9
  have hr : z % 9 < 9 := Nat.mod_lt z (by decide)
  rcases (by omega : z % 9 = 1 ∨ z % 9 = 4 ∨ z % 9 = 7) with h | h | h <;> simp [h]

private theorem optShiftMod9_step_potential (x : Nat) (hx_ge2 : x ≥ 2) (hx3 : x % 3 ≠ 0) :
    let r := optShiftMod9 x
    let m := 2 ^ r * x
    let y0 := 2 * m
    let y1 := (2 * m - 1) / 3
    1 ≤ r ∧ r ≤ 4 ∧
    m % 3 = 2 ∧
    x < y0 ∧ x < y1 ∧
    y0 % 3 ≠ 0 ∧ y1 % 3 ≠ 0 ∧
    cMod9 y0 * y0 ≤ 8 * (cMod9 x * x) ∧
    cMod9 y1 * y1 ≤ 8 * (cMod9 x * x) := by
  dsimp only
  have hr9 : x % 9 < 9 := Nat.mod_lt x (by decide)
  have hcases : x % 9 = 1 ∨ x % 9 = 2 ∨ x % 9 = 4 ∨ x % 9 = 5 ∨ x % 9 = 7 ∨ x % 9 = 8 := by omega
  rcases hcases with h9 | h9 | h9 | h9 | h9 | h9
  · -- `x % 9 = 1`: `r = 1`, `m = 2 * x`, `y0 = 4 * x` (`% 9 = 4`, `c = 1`), `y1 = (4 * x - 1) / 3` (`c ≤ 4`):
    have hr : optShiftMod9 x = 1 := by unfold optShiftMod9; simp [h9]
    have hcx : cMod9 x = 1 := by unfold cMod9; simp [h9]
    have hy0_9 : (2 * (2 ^ 1 * x)) % 9 = 4 := by
      have hm : (4 * x) % 9 = 4 := by rw [Nat.mul_mod, h9]
      simpa [show 2 * (2 ^ 1 * x) = 4 * x by omega] using hm
    have hcy0 : cMod9 (2 * (2 ^ 1 * x)) = 1 := by unfold cMod9; simp [hy0_9]
    have hcy1 : cMod9 ((2 * (2 ^ 1 * x) - 1) / 3) ≤ 4 := (cMod9_bounds _).2
    have hy1_3 : ((2 * (2 ^ 1 * x) - 1) / 3) % 3 = 1 := by omega
    rw [hr, hcx, hcy0]
    refine ⟨by decide, by decide, by omega, by omega, by omega, by omega, by omega, by omega, ?_⟩
    have hm_y1 : cMod9 ((2 * (2 ^ 1 * x) - 1) / 3) * ((2 * (2 ^ 1 * x) - 1) / 3) ≤
        4 * ((4 * x - 1) / 3) := by
      rw [show 2 * (2 ^ 1 * x) = 4 * x by omega] at hcy1 ⊢
      exact Nat.mul_le_mul_right _ hcy1
    omega
  · -- `x % 9 = 2`: `r = 2`, `m = 4 * x` (`% 9 = 8`), `y0 = 8 * x` (`% 9 = 7`, `c = 2`), `y1` (`c ≤ 4`):
    have hr : optShiftMod9 x = 2 := by unfold optShiftMod9; simp [h9]
    have hcx : cMod9 x = 2 := by unfold cMod9; simp [h9]
    have hy0_9 : (2 * (2 ^ 2 * x)) % 9 = 7 := by
      have hm : (8 * x) % 9 = 7 := by rw [Nat.mul_mod, h9]
      simpa [show 2 * (2 ^ 2 * x) = 8 * x by omega] using hm
    have hcy0 : cMod9 (2 * (2 ^ 2 * x)) = 2 := by unfold cMod9; simp [hy0_9]
    have hcy1 : cMod9 ((2 * (2 ^ 2 * x) - 1) / 3) ≤ 4 := (cMod9_bounds _).2
    rw [hr, hcx, hcy0]
    refine ⟨by decide, by decide, by omega, by omega, by omega, by omega, by omega, by omega, ?_⟩
    have hm_y1 : cMod9 ((2 * (2 ^ 2 * x) - 1) / 3) * ((2 * (2 ^ 2 * x) - 1) / 3) ≤
        4 * ((8 * x - 1) / 3) := by
      rw [show 2 * (2 ^ 2 * x) = 8 * x by omega] at hcy1 ⊢
      exact Nat.mul_le_mul_right _ hcy1
    omega
  · -- `x % 9 = 4`: `r = 1`, `m = 2 * x` (`% 9 = 8`), `y0 = 4 * x` (`% 9 = 7`, `c = 2`), `y1` (`c ≤ 4`):
    have hr : optShiftMod9 x = 1 := by unfold optShiftMod9; simp [h9]
    have hcx : cMod9 x = 1 := by unfold cMod9; simp [h9]
    have hy0_9 : (2 * (2 ^ 1 * x)) % 9 = 7 := by
      have hm : (4 * x) % 9 = 7 := by rw [Nat.mul_mod, h9]
      simpa [show 2 * (2 ^ 1 * x) = 4 * x by omega] using hm
    have hcy0 : cMod9 (2 * (2 ^ 1 * x)) = 2 := by unfold cMod9; simp [hy0_9]
    have hcy1 : cMod9 ((2 * (2 ^ 1 * x) - 1) / 3) ≤ 4 := (cMod9_bounds _).2
    rw [hr, hcx, hcy0]
    refine ⟨by decide, by decide, by omega, by omega, by omega, by omega, by omega, by omega, ?_⟩
    have hm_y1 : cMod9 ((2 * (2 ^ 1 * x) - 1) / 3) * ((2 * (2 ^ 1 * x) - 1) / 3) ≤
        4 * ((4 * x - 1) / 3) := by
      rw [show 2 * (2 ^ 1 * x) = 4 * x by omega] at hcy1 ⊢
      exact Nat.mul_le_mul_right _ hcy1
    omega
  · -- `x % 9 = 5`: `r = 2`, `m = 4 * x` (`% 9 = 2`), `y0 = 8 * x` (`% 9 = 4`, `c = 1`), `y1 % 3 = 1` (`c ≤ 2`):
    have hr : optShiftMod9 x = 2 := by unfold optShiftMod9; simp [h9]
    have hcx : cMod9 x = 1 := by unfold cMod9; simp [h9]
    have hy0_9 : (2 * (2 ^ 2 * x)) % 9 = 4 := by
      have hm : (8 * x) % 9 = 4 := by rw [Nat.mul_mod, h9]
      simpa [show 2 * (2 ^ 2 * x) = 8 * x by omega] using hm
    have hcy0 : cMod9 (2 * (2 ^ 2 * x)) = 1 := by unfold cMod9; simp [hy0_9]
    have hy1_3 : ((2 * (2 ^ 2 * x) - 1) / 3) % 3 = 1 := by
      rw [show 2 * (2 ^ 2 * x) = 8 * x by omega]
      have h8x9 : (8 * x) % 9 = 4 := by rw [Nat.mul_mod, h9]
      omega
    have hcy1 : cMod9 ((2 * (2 ^ 2 * x) - 1) / 3) ≤ 2 := cMod9_le_two_of_mod3_eq_one _ hy1_3
    rw [hr, hcx, hcy0]
    refine ⟨by decide, by decide, by omega, by omega, by omega, by omega, by omega, by omega, ?_⟩
    have hm_y1 : cMod9 ((2 * (2 ^ 2 * x) - 1) / 3) * ((2 * (2 ^ 2 * x) - 1) / 3) ≤
        2 * ((8 * x - 1) / 3) := by
      rw [show 2 * (2 ^ 2 * x) = 8 * x by omega] at hcy1 ⊢
      exact Nat.mul_le_mul_right _ hcy1
    omega
  · -- `x % 9 = 7`: `r = 3`, `m = 8 * x` (`% 9 = 2`), `y0 = 16 * x` (`% 9 = 4`, `c = 1`), `y1 % 3 = 1` (`c ≤ 2`):
    have hr : optShiftMod9 x = 3 := by unfold optShiftMod9; simp [h9]
    have hcx : cMod9 x = 2 := by unfold cMod9; simp [h9]
    have hy0_9 : (2 * (2 ^ 3 * x)) % 9 = 4 := by
      have hm : (16 * x) % 9 = 4 := by rw [Nat.mul_mod, h9]
      simpa [show 2 * (2 ^ 3 * x) = 16 * x by omega] using hm
    have hcy0 : cMod9 (2 * (2 ^ 3 * x)) = 1 := by unfold cMod9; simp [hy0_9]
    have hy1_3 : ((2 * (2 ^ 3 * x) - 1) / 3) % 3 = 1 := by
      rw [show 2 * (2 ^ 3 * x) = 16 * x by omega]
      have h16x9 : (16 * x) % 9 = 4 := by rw [Nat.mul_mod, h9]
      omega
    have hcy1 : cMod9 ((2 * (2 ^ 3 * x) - 1) / 3) ≤ 2 := cMod9_le_two_of_mod3_eq_one _ hy1_3
    rw [hr, hcx, hcy0]
    refine ⟨by decide, by decide, by omega, by omega, by omega, by omega, by omega, by omega, ?_⟩
    have hm_y1 : cMod9 ((2 * (2 ^ 3 * x) - 1) / 3) * ((2 * (2 ^ 3 * x) - 1) / 3) ≤
        2 * ((16 * x - 1) / 3) := by
      rw [show 2 * (2 ^ 3 * x) = 16 * x by omega] at hcy1 ⊢
      exact Nat.mul_le_mul_right _ hcy1
    omega
  · -- `x % 9 = 8`: `r = 4`, `m = 16 * x` (`% 9 = 2`), `y0 = 32 * x` (`% 9 = 4`, `c = 1`), `y1 % 3 = 1` (`c ≤ 2`):
    have hr : optShiftMod9 x = 4 := by unfold optShiftMod9; simp [h9]
    have hcx : cMod9 x = 4 := by unfold cMod9; simp [h9]
    have hy0_9 : (2 * (2 ^ 4 * x)) % 9 = 4 := by
      have hm : (32 * x) % 9 = 4 := by rw [Nat.mul_mod, h9]
      simpa [show 2 * (2 ^ 4 * x) = 32 * x by omega] using hm
    have hcy0 : cMod9 (2 * (2 ^ 4 * x)) = 1 := by unfold cMod9; simp [hy0_9]
    have hy1_3 : ((2 * (2 ^ 4 * x) - 1) / 3) % 3 = 1 := by
      rw [show 2 * (2 ^ 4 * x) = 32 * x by omega]
      have h32x9 : (32 * x) % 9 = 4 := by rw [Nat.mul_mod, h9]
      omega
    have hcy1 : cMod9 ((2 * (2 ^ 4 * x) - 1) / 3) ≤ 2 := cMod9_le_two_of_mod3_eq_one _ hy1_3
    rw [hr, hcx, hcy0]
    refine ⟨by decide, by decide, by omega, by omega, by omega, by omega, by omega, by omega, ?_⟩
    have hm_y1 : cMod9 ((2 * (2 ^ 4 * x) - 1) / 3) * ((2 * (2 ^ 4 * x) - 1) / 3) ≤
        2 * ((32 * x - 1) / 3) := by
      rw [show 2 * (2 ^ 4 * x) = 32 * x by omega] at hcy1 ⊢
      exact Nat.mul_le_mul_right _ hcy1
    omega

private theorem cubeRootTwoBranchNext_eventual_step
    (M_0 : Nat) (hM0 : M_0 ≥ 3)
    (wNum wDen : Nat -> Nat) (pTheta qTheta x : Nat)
    (hw : IsEventualPositiveRationalPreimageWeight M_0 wNum wDen pTheta qTheta)
    (hx_2M0 : x ≥ 2 * M_0) (hx3 : x % 3 ≠ 0) :
    let x' := cubeRootTwoBranchNext wNum wDen x
    x < x' ∧ x' % 3 ≠ 0 ∧ cMod9 x' * x' ≤ 8 * (cMod9 x * x) ∧
    2 * wNum x' * wDen x ≤ wNum x * wDen x' := by
  dsimp only
  have hq_pos : qTheta > 0 := Nat.lt_of_lt_of_le hw.1 hw.2.1
  rcases optShiftMod9_step_potential x (by omega) hx3 with
    ⟨hr1, _, hm_m3, hlt0, hlt1, hy0_3, hy1_3, hpot0, hpot1⟩
  let r := optShiftMod9 x
  let m := 2 ^ r * x
  let y0 := 2 * m
  let y1 := (2 * m - 1) / 3
  have hp_lo : 2 ≤ 2 ^ r := by simpa using pow2_mono_nat hr1
  have hm_ge2x : m ≥ 2 * x := Nat.mul_le_mul_right x hp_lo
  have heven_step : ∀ z : Nat, z ≥ 2 * M_0 -> wNum (2 * z) * wDen z ≤ wNum z * wDen (2 * z) := by
    intro z hz
    by_cases hz2 : z % 3 = 2
    · let nOdd := (2 * z - 1) / 3
      have hdn_pos : wDen nOdd > 0 := (hw.2.2.1 nOdd (by dsimp only [nOdd]; omega)).2
      have hpre_z := hw.2.2.2.2 z (by omega) hz2
      dsimp only at hpre_z
      have hbr_z : (wNum (2 * z) * wDen nOdd + wNum nOdd * wDen (2 * z)) * wDen z ≤
          wNum z * (wDen (2 * z) * wDen nOdd) :=
        nat_mul_le_cancel_left_w5 qTheta _ _ hq_pos
          (Nat.le_trans hpre_z (Nat.mul_le_mul_right _ hw.2.1))
      have hdrop : (wNum (2 * z) * wDen z) * wDen nOdd ≤ (wNum z * wDen (2 * z)) * wDen nOdd := by
        have hl : (wNum (2 * z) * wDen z) * wDen nOdd = (wNum (2 * z) * wDen nOdd) * wDen z := by ac_rfl
        have hr : (wNum z * wDen (2 * z)) * wDen nOdd = wNum z * (wDen (2 * z) * wDen nOdd) := by ac_rfl
        rw [hl, hr]; rw [Nat.add_mul] at hbr_z; omega
      exact nat_mul_le_cancel_right_w5 (wDen nOdd) _ _ hdn_pos hdrop
    · exact nat_mul_le_cancel_left_w5 qTheta _ _ hq_pos
        (Nat.le_trans (hw.2.2.2.1 z (by omega) hz2) (Nat.mul_le_mul_right _ hw.2.1))
  have hpow2_le : ∀ d : Nat, wNum (2 ^ d * x) * wDen x ≤ wNum x * wDen (2 ^ d * x) := by
    intro d; induction d with
    | zero => simp
    | succ d' ih =>
      have hzd : 2 ^ d' * x ≥ 2 * M_0 := by
        have hm1 := Nat.mul_le_mul (pow2_pos_nat d') hx_2M0; omega
      have hmul : 2 ^ (d' + 1) * x = 2 * (2 ^ d' * x) := by
        rw [Nat.pow_succ, Nat.mul_comm (2 ^ d') 2, Nat.mul_assoc]
      rw [hmul]
      exact rat_le_trans_pos_w5 _ _ (wNum (2 ^ d' * x)) (wDen (2 ^ d' * x)) _ _
        (hw.2.2.1 (2 ^ d' * x) (by omega)).2 (heven_step (2 ^ d' * x) hzd) ih
  have hm_le_x : wNum m * wDen x ≤ wNum x * wDen m := hpow2_le r
  have hpre := hw.2.2.2.2 m (by omega) hm_m3
  dsimp only at hpre
  have hbr : (wNum y0 * wDen y1 + wNum y1 * wDen y0) * wDen m ≤
      wNum m * (wDen y0 * wDen y1) :=
    nat_mul_le_cancel_left_w5 qTheta _ _ hq_pos
      (Nat.le_trans hpre (Nat.mul_le_mul_right _ hw.2.1))
  have hbm_pos : wDen m > 0 := (hw.2.2.1 m (by omega)).2
  have hb0_pos : wDen y0 > 0 := (hw.2.2.1 y0 (by omega)).2
  have hb1_pos : wDen y1 > 0 := (hw.2.2.1 y1 (by omega)).2
  unfold cubeRootTwoBranchNext; dsimp only
  change x < (if 2 * wNum y0 * wDen m ≤ wNum m * wDen y0 then y0 else y1) ∧ _
  if hcond : 2 * wNum y0 * wDen m ≤ wNum m * wDen y0 then
    rw [ite_true_dec hcond]
    exact ⟨hlt0, hy0_3, hpot0, rat_le_trans_pos_w5 _ _ (wNum m) (wDen m) _ _ hbm_pos hcond hm_le_x⟩
  else
    rw [ite_false_dec hcond]
    have hc1 : 2 * wNum y1 * wDen m ≤ wNum m * wDen y1 := by
      if hc : 2 * wNum y1 * wDen m ≤ wNum m * wDen y1 then
        exact hc
      else
        exfalso
        have hm0 := Nat.mul_lt_mul_of_pos_right (by omega : wNum m * wDen y0 < 2 * wNum y0 * wDen m) hb1_pos
        have hm1 := Nat.mul_lt_mul_of_pos_right (by omega : wNum m * wDen y1 < 2 * wNum y1 * wDen m) hb0_pos
        have hl0 : (wNum m * wDen y0) * wDen y1 = wNum m * (wDen y0 * wDen y1) := by ac_rfl
        have hl1 : (wNum m * wDen y1) * wDen y0 = wNum m * (wDen y0 * wDen y1) := by ac_rfl
        have hr0 : (2 * wNum y0 * wDen m) * wDen y1 = 2 * ((wNum y0 * wDen y1) * wDen m) := by ac_rfl
        have hr1 : (2 * wNum y1 * wDen m) * wDen y0 = 2 * ((wNum y1 * wDen y0) * wDen m) := by ac_rfl
        rw [hl0, hr0] at hm0; rw [hl1, hr1] at hm1; rw [Nat.add_mul] at hbr
        omega
    exact ⟨hlt1, hy1_3, hpot1, rat_le_trans_pos_w5 _ _ (wNum m) (wDen m) _ _ hbm_pos hc1 hm_le_x⟩

/--
  Theorem W13.3a (`eventual_exp_bitlength_cube_root_two_impossibility`,
  choice-free `zero custom axioms`):
  Weighted Residue-Potential Mod-`9` Branch Lookahead & Eventual (`∀ M_0 ≥ 3`) Cube-Root-of-2
  (`p_B ^ 3 < 2 * q_B ^ 3`) Critical-Base Impossibility (`Branch P1.2`,
  witness `ZPOS_MOD3K_EVEN_SPINE_4_AND_BASE_5_4_COLLAPSE`, `W13_H3`):
  1. **Universal Potential-Bounded Branch Growth (`∀ x ≥ 2, x % 3 ≠ 0`) & Base-`5/4` Collapse**:
     `cMod9 (cubeRootTwoBranchNext wNum wDen x) * cubeRootTwoBranchNext wNum wDen x ≤ 8 * (cMod9 x * x)`,
     so `cubeRootTwoBranchIter wNum wDen k x < 2 ^ (3 * k + 2 + x)` for ALL `k : Nat`, AND bases
     `(5, 4), (6, 5), (7, 6), (8, 7), (9, 8)` ALL satisfy `p_B ^ 3 < 2 * q_B ^ 3` (with explicit
     `k = 2` collapse `5 -> 13 -> 17` on `(5 / 4)^binBitLength(n)`!).
  2. **Eventual Unrestricted-Numerator Cube-Root-of-2 Impossibility (`∀ M_0 ≥ 3`, `p_B ^ 3 < 2 * q_B ^ 3`)**:
     For ANY threshold `M_0 ≥ 3`, ANY `wNum, wDen` (with ZERO upper bound on `wNum`!), and ANY
     `p_B, q_B ≥ 1` with `p_B ^ 3 < 2 * q_B ^ 3`: if
       `∀ n ≥ M_0, q_B ^ binBitLength n * wDen n ≤ C_den * p_B ^ binBitLength n`,
     then `¬ IsEventualPositiveRationalPreimageWeight M_0 wNum wDen pTheta qTheta`!
-/
theorem eventual_exp_bitlength_cube_root_two_impossibility :
    ((∀ (wNum wDen : Nat -> Nat) (x : Nat),
        x ≥ 2 -> x % 3 ≠ 0 ->
        cMod9 (cubeRootTwoBranchNext wNum wDen x) * cubeRootTwoBranchNext wNum wDen x ≤
          8 * (cMod9 x * x)) ∧
     5 ^ 3 < 2 * 4 ^ 3 ∧
     6 ^ 3 < 2 * 5 ^ 3 ∧
     7 ^ 3 < 2 * 6 ^ 3 ∧
     8 ^ 3 < 2 * 7 ^ 3 ∧
     9 ^ 3 < 2 * 8 ^ 3 ∧
     (let w54Den : Nat -> Nat := fun n => Nat.max 1 (5 ^ binBitLength n / 4 ^ binBitLength n)
      let x2 := cubeRootTwoBranchIter (fun _ => 1) w54Den 2 5
      x2 = 17 ∧ 4 * 1 * w54Den 5 > 1 * w54Den x2)) ∧
    (∀ (M_0 : Nat), M_0 ≥ 3 ->
      ∀ (wNum wDen : Nat -> Nat) (C_den p_B q_B pTheta qTheta : Nat),
        p_B ≥ 1 -> q_B ≥ 1 ->
        p_B ^ 3 < 2 * q_B ^ 3 ->
        (∀ n : Nat, n ≥ M_0 ->
          q_B ^ binBitLength n * wDen n ≤ C_den * p_B ^ binBitLength n) ->
        ¬ IsEventualPositiveRationalPreimageWeight M_0 wNum wDen pTheta qTheta) := by
  have hpot_one : ∀ (wNum wDen : Nat -> Nat) (x : Nat),
      x ≥ 2 -> x % 3 ≠ 0 ->
      cMod9 (cubeRootTwoBranchNext wNum wDen x) * cubeRootTwoBranchNext wNum wDen x ≤
        8 * (cMod9 x * x) := by
    intro wNum wDen x hx2 hx3
    rcases optShiftMod9_step_potential x hx2 hx3 with ⟨_, _, _, _, _, _, _, hp0, hp1⟩
    unfold cubeRootTwoBranchNext; dsimp only
    if hc : 2 * wNum (2 * (2 ^ optShiftMod9 x * x)) * wDen (2 ^ optShiftMod9 x * x) ≤
        wNum (2 ^ optShiftMod9 x * x) * wDen (2 * (2 ^ optShiftMod9 x * x)) then
      rw [ite_true_dec hc]; exact hp0
    else
      rw [ite_false_dec hc]; exact hp1
  refine ⟨⟨hpot_one, by decide, by decide, by decide, by decide, by decide, by decide⟩, ?_⟩
  intro M_0 hM0 wNum wDen C_den p_B q_B pTheta qTheta hpB hqB hcrit hden hw
  if hle_pq : p_B ≤ q_B then
    -- Subcase 1 (`p_B ≤ q_B`): `p_B ^ 13 ≤ q_B ^ 13 < 4 * q_B ^ 13`, apply `W12.3b`:
    have hcrit13 : p_B ^ 13 < 4 * q_B ^ 13 := by
      have h1 := pow_mono_base_w13s p_B q_B hle_pq 13
      have h2 := nat_pow_pos_of_pos q_B (by omega) 13
      omega
    exact eventual_exp_bitlength_critical_base_impossibility.2 M_0 hM0
      wNum wDen C_den p_B q_B pTheta qTheta hpB hqB hcrit13 hden hw
  else
    -- Subcase 2 (`q_B < p_B`):
    have hqp : q_B ≤ p_B := by omega
    let x0 := 6 * M_0 + 5
    have hx0_2M0 : x0 ≥ 2 * M_0 := by dsimp only [x0]; omega
    have hx0_3 : x0 % 3 ≠ 0 := by dsimp only [x0]; omega
    -- Inductive telescope along `cubeRootTwoBranchIter`:
    have hiter : ∀ (k z : Nat), z ≥ 2 * M_0 -> z % 3 ≠ 0 ->
        let zk := cubeRootTwoBranchIter wNum wDen k z
        zk ≥ z ∧ zk % 3 ≠ 0 ∧
        cMod9 zk * zk ≤ 8 ^ k * (cMod9 z * z) ∧
        2 ^ k * wNum zk * wDen z ≤ wNum z * wDen zk := by
      intro k; induction k with
      | zero =>
        intro z _ hz3; simp [cubeRootTwoBranchIter, hz3]
      | succ k' ih =>
        intro z hz_2M0 hz3
        dsimp only [cubeRootTwoBranchIter]
        rcases cubeRootTwoBranchNext_eventual_step M_0 hM0 wNum wDen pTheta qTheta z hw hz_2M0 hz3 with
          ⟨hz_lt, hz1_3, hpot1, hrat1⟩
        let z1 := cubeRootTwoBranchNext wNum wDen z
        change z < z1 at hz_lt
        rcases ih z1 (by omega) hz1_3 with ⟨hzk_ge, hzk_3, hpot_k, hrat_k⟩
        let zk := cubeRootTwoBranchIter wNum wDen k' z1
        have hpot_tot : cMod9 zk * zk ≤ 8 ^ (k' + 1) * (cMod9 z * z) := by
          calc
            cMod9 zk * zk ≤ 8 ^ k' * (cMod9 z1 * z1) := hpot_k
            _ ≤ 8 ^ k' * (8 * (cMod9 z * z)) := Nat.mul_le_mul_left (8 ^ k') hpot1
            _ = (8 ^ k' * 8) * (cMod9 z * z) := by ac_rfl
            _ = 8 ^ (k' + 1) * (cMod9 z * z) := by rw [← Nat.pow_succ 8 k']
        have hbd1_pos : wDen z1 > 0 := (hw.2.2.1 z1 (by omega)).2
        have hrat_tot : 2 ^ (k' + 1) * wNum zk * wDen z ≤ wNum z * wDen zk := by
          have hstep_a : (2 ^ (k' + 1) * wNum zk) * wDen z1 ≤ (2 * wNum z1) * wDen zk := by
            rw [Nat.pow_succ 2 k']
            calc
              (2 ^ k' * 2 * wNum zk) * wDen z1 = 2 * (2 ^ k' * wNum zk * wDen z1) := by ac_rfl
              _ ≤ 2 * (wNum z1 * wDen zk) := Nat.mul_le_mul_left 2 hrat_k
              _ = (2 * wNum z1) * wDen zk := by ac_rfl
          exact rat_le_trans_pos_w5 (2 ^ (k' + 1) * wNum zk) (wDen zk) (2 * wNum z1) (wDen z1)
            (wNum z) (wDen z) hbd1_pos hstep_a hrat1
        exact ⟨Nat.le_trans (Nat.le_of_lt hz_lt) hzk_ge, hzk_3, hpot_tot, hrat_tot⟩
    let A := p_B ^ 3
    let B := 2 * q_B ^ 3
    have hA_pos : A ≥ 1 := nat_pow_pos_of_pos p_B (by omega) 3
    let K_0 := wNum x0 * C_den * p_B ^ (2 + x0)
    let k := K_0 * A
    have hlt_AB : K_0 * A ^ k < B ^ k := pow_gt_const_mul_pow_of_lt_w13s A B K_0 hA_pos hcrit
    rcases hiter k x0 hx0_2M0 hx0_3 with ⟨hxk_ge, _, hpot_k, hrat_k⟩
    let xk := cubeRootTwoBranchIter wNum wDen k x0
    change xk ≥ x0 at hxk_ge
    change cMod9 xk * xk ≤ 8 ^ k * (cMod9 x0 * x0) at hpot_k
    change 2 ^ k * wNum xk * wDen x0 ≤ wNum x0 * wDen xk at hrat_k
    -- Extract `2 ^ k ≤ wNum x0 * wDen xk` from `2 ^ k * wNum xk * wDen x0 ≤ wNum x0 * wDen xk`:
    have h2k_le : 2 ^ k ≤ wNum x0 * wDen xk := by
      have hwn_pos : wNum xk ≥ 1 := (hw.2.2.1 xk (by dsimp only [x0] at hxk_ge; omega)).1
      have hwd0_pos : wDen x0 ≥ 1 := (hw.2.2.1 x0 (by dsimp only [x0]; omega)).2
      have h1 : 1 ≤ wNum xk * wDen x0 := Nat.mul_le_mul hwn_pos hwd0_pos
      have hm := Nat.mul_le_mul_left (2 ^ k) h1
      rw [Nat.mul_one, ← Nat.mul_assoc] at hm
      exact Nat.le_trans hm hrat_k
    -- Bound `xk ≤ 2 ^ (3 * k + 2 + x0) - 1`, so `binBitLength xk ≤ 3 * k + 2 + x0`:
    have hxk_lt : xk ≤ 2 ^ (3 * k + 2 + x0) - 1 := by
      have hc_lo : 1 ≤ cMod9 xk := (cMod9_bounds xk).1
      have hc_hi : cMod9 x0 ≤ 4 := (cMod9_bounds x0).2
      have h1 : xk ≤ cMod9 xk * xk := by simpa using Nat.mul_le_mul_right xk hc_lo
      have h8_pow : 8 ^ k = 2 ^ (3 * k) := by
        rw [show (8 : Nat) = 2 ^ 3 from rfl, pow_pow_eq_mul_w5 2 3 k]
      have hx0_pow : x0 < 2 ^ x0 := id_lt_pow2_w13s x0
      have h2 : 8 ^ k * (cMod9 x0 * x0) < 2 ^ (3 * k + 2 + x0) := by
        have hc4 : cMod9 x0 * x0 ≤ 4 * x0 := Nat.mul_le_mul_right x0 hc_hi
        have h4x0 : 4 * x0 < 2 ^ (2 + x0) := by
          rw [Nat.pow_add 2 2 x0]
          change 4 * x0 < 4 * 2 ^ x0
          exact Nat.mul_lt_mul_of_pos_left hx0_pow (by decide)
        have hm := Nat.mul_lt_mul_of_pos_left (Nat.lt_of_le_of_lt hc4 h4x0) (pow2_pos_nat (3 * k))
        rw [← Nat.pow_add 2 (3 * k) (2 + x0), ← h8_pow, ← Nat.add_assoc (3 * k) 2 x0] at hm
        exact hm
      exact Nat.le_pred_of_lt (Nat.lt_of_le_of_lt (Nat.le_trans h1 hpot_k) h2)
    let L := binBitLength xk
    let N := 3 * k + 2 + x0
    have hL_le_N : L ≤ N := by
      have hp := (binBitLength_pow2_and_pred (3 * k + 1 + x0)).2
      have hm := binBitLength_mono xk (2 ^ (3 * k + 2 + x0) - 1)
        (by simpa [show 3 * k + 1 + x0 + 1 = 3 * k + 2 + x0 by omega] using hxk_lt)
      dsimp only [L, N]
      rw [show 3 * k + 1 + x0 + 1 = 3 * k + 2 + x0 by omega] at hp
      omega
    let E := N - L
    have hLN : L + E = N := by omega
    have hden_N : q_B ^ N * wDen xk ≤ C_den * p_B ^ N := by
      have hdL := hden xk (by dsimp only [x0] at hxk_ge; omega)
      change q_B ^ L * wDen xk ≤ C_den * p_B ^ L at hdL
      have hqE_pE : q_B ^ E ≤ p_B ^ E := pow_mono_base_w13s q_B p_B hqp E
      calc
        q_B ^ N * wDen xk = q_B ^ E * (q_B ^ L * wDen xk) := by
          rw [← hLN, Nat.pow_add q_B L E]; ac_rfl
        _ ≤ p_B ^ E * (C_den * p_B ^ L) := Nat.mul_le_mul hqE_pE hdL
        _ = C_den * p_B ^ N := by
          rw [← hLN, Nat.pow_add p_B L E]; ac_rfl
    have hBk_le : B ^ k * q_B ^ (2 + x0) ≤ K_0 * A ^ k := by
      have hN_sp : N = 3 * k + (2 + x0) := by dsimp only [N]; omega
      have hBk_eq : B ^ k * q_B ^ (2 + x0) = q_B ^ N * 2 ^ k := by
        dsimp only [B]
        rw [hN_sp, mul_pow_w13s 2 (q_B ^ 3) k, pow_pow_eq_mul_w5 q_B 3 k,
            Nat.pow_add q_B (3 * k) (2 + x0)]
        ac_rfl
      have hAk_eq : wNum x0 * (C_den * p_B ^ N) = K_0 * A ^ k := by
        dsimp only [K_0, A]
        rw [hN_sp, Nat.pow_add p_B (3 * k) (2 + x0), ← pow_pow_eq_mul_w5 p_B 3 k]
        ac_rfl
      calc
        B ^ k * q_B ^ (2 + x0) = q_B ^ N * 2 ^ k := hBk_eq
        _ ≤ q_B ^ N * (wNum x0 * wDen xk) := Nat.mul_le_mul_left (q_B ^ N) h2k_le
        _ = wNum x0 * (q_B ^ N * wDen xk) := by ac_rfl
        _ ≤ wNum x0 * (C_den * p_B ^ N) := Nat.mul_le_mul_left (wNum x0) hden_N
        _ = K_0 * A ^ k := hAk_eq
    have hq_pos_tail : q_B ^ (2 + x0) ≥ 1 := nat_pow_pos_of_pos q_B (by omega) (2 + x0)
    have hBk_self : B ^ k ≤ B ^ k * q_B ^ (2 + x0) := by
      simpa using Nat.mul_le_mul_left (B ^ k) hq_pos_tail
    exact Nat.lt_irrefl (B ^ k) (Nat.lt_of_le_of_lt (Nat.le_trans hBk_self hBk_le) hlt_AB)

-- ----------------------------------------------------------------------------
-- Section 1B: Universal Mod-`27` / Mod-`81` / Mod-`3^K` `3`-Coprime-Preserving
--             Even-Spine `64^k` Minimax Floor (Choice-Free)
-- ----------------------------------------------------------------------------

/-- Pure even-preimage backward step `y_0(z) = 2 * (2 ^ r_pol(z) * z)` induced by any backward
    shift policy `r_pol : Nat -> Nat`. -/
def evenSpineStep (r_pol : Nat -> Nat) (z : Nat) : Nat :=
  2 * (2 ^ r_pol z * z)

/-- `t`-step iteration of `evenSpineStep r_pol`. -/
def evenSpineIter (r_pol : Nat -> Nat) : Nat -> Nat -> Nat
  | 0, z => z
  | t + 1, z => evenSpineIter r_pol t (evenSpineStep r_pol z)

private theorem pow2_mod9_ge_two (e : Nat) (he : e ≥ 2) :
    (e < 6 -> (e = 2 ∧ 2 ^ e % 9 = 4) ∨ (e = 3 ∧ 2 ^ e % 9 = 8) ∨
              (e = 4 ∧ 2 ^ e % 9 = 7) ∨ (e = 5 ∧ 2 ^ e % 9 = 5)) ∧
    (2 ^ e % 9 = 1 -> e ≥ 6) ∧
    (2 ^ e % 9 = 7 -> e ≥ 4) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hlt
    rcases (by omega : e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 5) with rfl | rfl | rfl | rfl <;> decide
  · intro hm1
    by_cases hlt : e < 6
    · rcases (by omega : e = 2 ∨ e = 3 ∨ e = 4 ∨ e = 5) with rfl | rfl | rfl | rfl <;> simp at hm1
    · omega
  · intro hm7
    by_cases hlt : e < 4
    · rcases (by omega : e = 2 ∨ e = 3) with rfl | rfl <;> simp at hm7
    · omega

/--
  Theorem W13.3b (`mod3k_even_spine_64k_minimax_floor`,
  choice-free `zero custom axioms`):
  Universal `3`-Coprime-Preserving Backward Shift Even-Spine `64^k` Minimax Floor (`Branch P1.2`,
  witness `ZPOS_MOD3K_EVEN_SPINE_4_AND_BASE_5_4_COLLAPSE`, `W13_H3`):
  For ANY backward halving-shift policy `r_pol : Nat -> Nat` (simultaneously subsuming ALL Mod-`9`,
  Mod-`27`, Mod-`81`, Mod-`3^K`, and arbitrary infinite-lookahead oracle policies!) satisfying
    `∀ z : Nat, z % 3 ≠ 0 -> r_pol z ≥ 1 ∧ (2 ^ r_pol z * z) % 3 = 2 ∧ ((2 * (2 ^ r_pol z * z) - 1) / 3) % 3 ≠ 0`:
  1. **Universal `{4, 7} mod 9` Even-Child Trapping (`∀ z, z % 3 ≠ 0`)**:
     `(2 ^ r_pol z * z) % 9 = 2 ∨ (2 ^ r_pol z * z) % 9 = 8`, hence
     `evenSpineStep r_pol z % 9 = 4 ∨ evenSpineStep r_pol z % 9 = 7`!
  2. **Universal `64 ^ k * x_0` 2-Step Minimax Growth Floor (`∀ x_0`, `x_0 % 9 ∈ {4, 7}`, `∀ k : Nat`)**:
     `(evenSpineIter r_pol (2 * k) x_0 % 9 = 4 ∨ evenSpineIter r_pol (2 * k) x_0 % 9 = 7)` AND
     `evenSpineIter r_pol (2 * k) x_0 ≥ 64 ^ k * x_0`!
     (In particular at `x_0 = 4`, `evenSpineIter r_pol (2 * k) 4 ≥ 4 * 64 ^ k`, proving `2 ^ (1 / 3)`
     is the **exact sharp minimax ceiling** of all `3`-coprime-preserving backward branch trees!)
-/
theorem mod3k_even_spine_64k_minimax_floor
    (r_pol : Nat -> Nat)
    (hvalid : ∀ z : Nat, z % 3 ≠ 0 ->
      r_pol z ≥ 1 ∧
      (2 ^ r_pol z * z) % 3 = 2 ∧
      ((2 * (2 ^ r_pol z * z) - 1) / 3) % 3 ≠ 0) :
    (∀ z : Nat, z % 3 ≠ 0 ->
      ((2 ^ r_pol z * z) % 9 = 2 ∨ (2 ^ r_pol z * z) % 9 = 8) ∧
      (evenSpineStep r_pol z % 9 = 4 ∨ evenSpineStep r_pol z % 9 = 7)) ∧
    (∀ (x_0 k : Nat), (x_0 % 9 = 4 ∨ x_0 % 9 = 7) ->
      (evenSpineIter r_pol (2 * k) x_0 % 9 = 4 ∨ evenSpineIter r_pol (2 * k) x_0 % 9 = 7) ∧
      evenSpineIter r_pol (2 * k) x_0 ≥ 64 ^ k * x_0) := by
  have htrap : ∀ z : Nat, z % 3 ≠ 0 ->
      ((2 ^ r_pol z * z) % 9 = 2 ∨ (2 ^ r_pol z * z) % 9 = 8) ∧
      (evenSpineStep r_pol z % 9 = 4 ∨ evenSpineStep r_pol z % 9 = 7) := by
    intro z hz3
    rcases hvalid z hz3 with ⟨_, hm3, hy1_3⟩
    let m := 2 ^ r_pol z * z
    change m % 3 = 2 at hm3
    change ((2 * m - 1) / 3) % 3 ≠ 0 at hy1_3
    have hm9_ne5 : m % 9 ≠ 5 := by
      intro hm5
      apply hy1_3
      omega
    have hm9 : m % 9 = 2 ∨ m % 9 = 8 := by omega
    refine ⟨hm9, ?_⟩
    unfold evenSpineStep
    change (2 * m) % 9 = 4 ∨ (2 * m) % 9 = 7
    rcases hm9 with h2 | h8
    · left; rw [Nat.mul_mod, h2]
    · right; rw [Nat.mul_mod, h8]
  -- Single-step growth bounds from `z % 9 = 4` and `z % 9 = 7`:
  have hfrom4 : ∀ z : Nat, z % 9 = 4 ->
      (evenSpineStep r_pol z % 9 = 7 ∧ evenSpineStep r_pol z ≥ 4 * z) ∨
      (evenSpineStep r_pol z % 9 = 4 ∧ evenSpineStep r_pol z ≥ 64 * z) := by
    intro z hz4
    have hz3 : z % 3 ≠ 0 := by omega
    have hr1 : r_pol z ≥ 1 := (hvalid z hz3).1
    rcases (htrap z hz3).2 with hy4 | hy7
    · right
      refine ⟨hy4, ?_⟩
      -- `2 ^ (r_pol z + 1) * z ≡ 4 (mod 9)` with `z ≡ 4 (mod 9)` -> `2 ^ (r_pol z + 1) ≡ 1 (mod 9)`:
      have hev_eq : evenSpineStep r_pol z = 2 ^ (r_pol z + 1) * z := by
        unfold evenSpineStep
        rw [Nat.pow_succ 2 (r_pol z), Nat.mul_comm (2 ^ r_pol z) 2, Nat.mul_assoc]
      have hp_mod1 : 2 ^ (r_pol z + 1) % 9 = 1 := by
        have hm : (2 ^ (r_pol z + 1) * z) % 9 = 4 := by rwa [← hev_eq]
        rw [Nat.mul_mod, hz4] at hm
        have hlt9 : 2 ^ (r_pol z + 1) % 9 < 9 := Nat.mod_lt _ (by decide)
        omega
      have he_ge6 : r_pol z + 1 ≥ 6 := (pow2_mod9_ge_two (r_pol z + 1) (by omega)).2.1 hp_mod1
      have hp64 : 2 ^ (r_pol z + 1) ≥ 64 := by
        have hc : (2 : Nat) ^ 6 = 64 := by decide
        rw [← hc]; exact pow2_mono_nat he_ge6
      rw [hev_eq]
      exact Nat.mul_le_mul_right z hp64
    · left
      refine ⟨hy7, ?_⟩
      unfold evenSpineStep
      have hp2 : 2 ^ r_pol z ≥ 2 := by simpa using pow2_mono_nat hr1
      have hm := Nat.mul_le_mul_right z hp2
      omega
  have hfrom7 : ∀ z : Nat, z % 9 = 7 ->
      (evenSpineStep r_pol z % 9 = 4 ∨ evenSpineStep r_pol z % 9 = 7) ∧
      evenSpineStep r_pol z ≥ 16 * z := by
    intro z hz7
    have hz3 : z % 3 ≠ 0 := by omega
    have hr1 : r_pol z ≥ 1 := (hvalid z hz3).1
    have htr := (htrap z hz3).2
    refine ⟨htr, ?_⟩
    have hev_eq : evenSpineStep r_pol z = 2 ^ (r_pol z + 1) * z := by
      unfold evenSpineStep
      rw [Nat.pow_succ 2 (r_pol z), Nat.mul_comm (2 ^ r_pol z) 2, Nat.mul_assoc]
    rcases htr with hy4 | hy7
    · -- `(2 ^ (r_pol z + 1) * 7) % 9 = 4 -> 2 ^ (r_pol z + 1) % 9 = 7 -> r_pol z + 1 ≥ 4`:
      have hp_mod7 : 2 ^ (r_pol z + 1) % 9 = 7 := by
        have hm : (2 ^ (r_pol z + 1) * z) % 9 = 4 := by rwa [← hev_eq]
        rw [Nat.mul_mod, hz7] at hm
        have hlt9 : 2 ^ (r_pol z + 1) % 9 < 9 := Nat.mod_lt _ (by decide)
        omega
      have he_ge4 : r_pol z + 1 ≥ 4 := (pow2_mod9_ge_two (r_pol z + 1) (by omega)).2.2 hp_mod7
      have hp16 : 2 ^ (r_pol z + 1) ≥ 16 := by
        have hc : (2 : Nat) ^ 4 = 16 := by decide
        rw [← hc]; exact pow2_mono_nat he_ge4
      rw [hev_eq]
      exact Nat.mul_le_mul_right z hp16
    · -- `(2 ^ (r_pol z + 1) * 7) % 9 = 7 -> 2 ^ (r_pol z + 1) % 9 = 1 -> r_pol z + 1 ≥ 6`:
      have hp_mod1 : 2 ^ (r_pol z + 1) % 9 = 1 := by
        have hm : (2 ^ (r_pol z + 1) * z) % 9 = 7 := by rwa [← hev_eq]
        rw [Nat.mul_mod, hz7] at hm
        have hlt9 : 2 ^ (r_pol z + 1) % 9 < 9 := Nat.mod_lt _ (by decide)
        omega
      have he_ge6 : r_pol z + 1 ≥ 6 := (pow2_mod9_ge_two (r_pol z + 1) (by omega)).2.1 hp_mod1
      have hp64 : 2 ^ (r_pol z + 1) ≥ 64 := by
        have hc : (2 : Nat) ^ 6 = 64 := by decide
        rw [← hc]; exact pow2_mono_nat he_ge6
      rw [hev_eq]
      exact Nat.le_trans (Nat.mul_le_mul_right z (by decide : 16 ≤ 64)) (Nat.mul_le_mul_right z hp64)
  -- 2-step block lemma: from any `z` with `z % 9 ∈ {4, 7}`, `evenSpineIter r_pol 2 z % 9 ∈ {4, 7}` and `≥ 64 * z`:
  have htwo_step : ∀ z : Nat, (z % 9 = 4 ∨ z % 9 = 7) ->
      let z2 := evenSpineStep r_pol (evenSpineStep r_pol z)
      (z2 % 9 = 4 ∨ z2 % 9 = 7) ∧ z2 ≥ 64 * z := by
    intro z hz47; dsimp only
    let z1 := evenSpineStep r_pol z
    rcases hz47 with hz4 | hz7
    · rcases hfrom4 z hz4 with ⟨hz1_7, hge4⟩ | ⟨hz1_4, hge64⟩
      · rcases hfrom7 z1 hz1_7 with ⟨hz2_47, hge16⟩
        exact ⟨hz2_47, by dsimp only [z1] at hge4 hge16 ⊢; omega⟩
      · rcases hfrom4 z1 hz1_4 with ⟨hz2_7, h2_4⟩ | ⟨hz2_4, h2_64⟩
        · exact ⟨Or.inr hz2_7, by dsimp only [z1] at hge64 h2_4 ⊢; omega⟩
        · exact ⟨Or.inl hz2_4, by dsimp only [z1] at hge64 h2_64 ⊢; omega⟩
    · rcases hfrom7 z hz7 with ⟨hz1_47, hge16⟩
      rcases hz1_47 with hz1_4 | hz1_7
      · rcases hfrom4 z1 hz1_4 with ⟨hz2_7, h2_4⟩ | ⟨hz2_4, h2_64⟩
        · exact ⟨Or.inr hz2_7, by dsimp only [z1] at hge16 h2_4 ⊢; omega⟩
        · exact ⟨Or.inl hz2_4, by dsimp only [z1] at hge16 h2_64 ⊢; omega⟩
      · rcases hfrom7 z1 hz1_7 with ⟨hz2_47, h2_16⟩
        exact ⟨hz2_47, by dsimp only [z1] at hge16 h2_16 ⊢; omega⟩
  refine ⟨htrap, ?_⟩
  intro x_0 k hx0
  have hiter_k : ∀ (t z : Nat), (z % 9 = 4 ∨ z % 9 = 7) ->
      (evenSpineIter r_pol (2 * t) z % 9 = 4 ∨ evenSpineIter r_pol (2 * t) z % 9 = 7) ∧
      evenSpineIter r_pol (2 * t) z ≥ 64 ^ t * z := by
    intro t; induction t with
    | zero =>
      intro z hz; simp only [evenSpineIter, Nat.pow_zero, Nat.one_mul]
      exact ⟨hz, Nat.le_refl z⟩
    | succ t' ih =>
      intro z hz
      rcases htwo_step z hz with ⟨hz2_47, hz2_ge⟩
      let z2 := evenSpineStep r_pol (evenSpineStep r_pol z)
      rcases ih z2 hz2_47 with ⟨hend_47, hend_ge⟩
      have hrew : evenSpineIter r_pol (2 * (t' + 1)) z = evenSpineIter r_pol (2 * t') z2 := by
        rw [Nat.mul_succ 2 t']
        rfl
      rw [hrew]
      refine ⟨hend_47, ?_⟩
      calc
        64 ^ (t' + 1) * z = (64 ^ t' * 64) * z := by rw [Nat.pow_succ 64 t']
        _ = 64 ^ t' * (64 * z) := by ac_rfl
        _ ≤ 64 ^ t' * z2 := Nat.mul_le_mul_left (64 ^ t') hz2_ge
        _ ≤ evenSpineIter r_pol (2 * t') z2 := hend_ge
  exact hiter_k k x_0 hx0

-- ----------------------------------------------------------------------------
-- Section 1C: Quadratic-Exponential Denominator vs Single-Exponential Numerator
--             Impossibility Along Reverse Syracuse Odd-Branch Chains
-- ----------------------------------------------------------------------------

/--
  Theorem W13.3c (`eventual_exp_num_quad_exp_den_bitlength_impossibility`,
  `zero custom axioms`):
  Quadratic Bit-Length Drop (`L_0^2 - L_{4s}^2 ≥ 20 * s^2 + 16 * s + 3`) & Eventual (`∀ M_0 ≥ 3`)
  Impossibility of Single-Exponential-Numerator / Quadratic-Exponential-Denominator Preimage Weights
  (`Branch P1.2`, `W13_H3`):
  1. **Quadratic Bit-Length Drop Along `revSyracuseNode (2 * s)` (`∀ s ≥ 1`)**:
     `(binBitLength (revSyracuseNode (2 * s) 0)) ^ 2 ≥
        (binBitLength (revSyracuseNode (2 * s) (4 * s))) ^ 2 + 20 * s ^ 2 + 16 * s + 3`!
  2. **Eventual Single-Exponential Numerator vs Quadratic-Exponential Denominator Impossibility (`∀ M_0 ≥ 3`)**:
     For ANY `M_0 ≥ 3`, ANY `c_1 ≥ 1`, ANY `p_N ≥ 1`, ANY `p_D > q_D ≥ 1`, and ANY `C_den, C_num, pTheta, qTheta`:
     if `∀ n ≥ M_0`:
       `wNum n ≤ C_num * p_N ^ binBitLength n` AND
       `c_1 * p_D ^ ((binBitLength n) ^ 2) ≤ q_D ^ ((binBitLength n) ^ 2) * wDen n` AND
       `q_D ^ ((binBitLength n) ^ 2) * wDen n ≤ C_den * p_D ^ ((binBitLength n) ^ 2)`,
     then `¬ IsEventualPositiveRationalPreimageWeight M_0 wNum wDen pTheta qTheta`!
-/
theorem eventual_exp_num_quad_exp_den_bitlength_impossibility :
    (∀ s : Nat, s ≥ 1 ->
      (binBitLength (revSyracuseNode (2 * s) 0)) ^ 2 ≥
        (binBitLength (revSyracuseNode (2 * s) (4 * s))) ^ 2 + 20 * s ^ 2 + 16 * s + 3) ∧
    (∀ (M_0 : Nat), M_0 ≥ 3 ->
      ∀ (wNum wDen : Nat -> Nat) (c_1 C_den C_num p_N p_D q_D pTheta qTheta : Nat),
        c_1 ≥ 1 -> p_N ≥ 1 -> q_D ≥ 1 -> q_D < p_D ->
        (∀ n : Nat, n ≥ M_0 -> wNum n ≤ C_num * p_N ^ binBitLength n) ->
        (∀ n : Nat, n ≥ M_0 ->
          c_1 * p_D ^ ((binBitLength n) ^ 2) ≤ q_D ^ ((binBitLength n) ^ 2) * wDen n ∧
          q_D ^ ((binBitLength n) ^ 2) * wDen n ≤ C_den * p_D ^ ((binBitLength n) ^ 2)) ->
        ¬ IsEventualPositiveRationalPreimageWeight M_0 wNum wDen pTheta qTheta) := by
  rcases eventual_poly_num_any_exp_base_bitlength_impossibility.1 with ⟨hchain, hbits⟩
  have hquad_gap : ∀ s : Nat, s ≥ 1 ->
      (binBitLength (revSyracuseNode (2 * s) 0)) ^ 2 ≥
        (binBitLength (revSyracuseNode (2 * s) (4 * s))) ^ 2 + 20 * s ^ 2 + 16 * s + 3 := by
    intro s hs1
    rcases hbits s hs1 with ⟨hbl_end, hbl_lo0, _⟩
    have hsq_lo : (6 * s + 2) ^ 2 ≤ (binBitLength (revSyracuseNode (2 * s) 0)) ^ 2 := by
      rw [Nat.pow_two, Nat.pow_two]; exact Nat.mul_le_mul hbl_lo0 hbl_lo0
    have h6s2 : (6 * s + 2) ^ 2 = (4 * s + 1) ^ 2 + 20 * s ^ 2 + 16 * s + 3 := by
      rw [Nat.pow_two (6 * s + 2), Nat.pow_two (4 * s + 1), Nat.pow_two s]
      have h66 : (6 * s + 2) * (6 * s + 2) = 36 * (s * s) + 24 * s + 4 := by
        rw [Nat.mul_add, Nat.add_mul, Nat.add_mul]
        have h1 : 6 * s * (6 * s) = (6 * 6) * (s * s) := by ac_rfl
        have h2 : 6 * s * 2 = 12 * s := by omega
        have h3 : 2 * (6 * s) = 12 * s := by omega
        rw [h1, h2, h3]; omega
      have h44 : (4 * s + 1) * (4 * s + 1) = 16 * (s * s) + 8 * s + 1 := by
        rw [Nat.mul_add, Nat.add_mul, Nat.add_mul]
        have h1 : 4 * s * (4 * s) = (4 * 4) * (s * s) := by ac_rfl
        rw [h1]; omega
      rw [h66, h44]; omega
    rw [hbl_end]
    omega
  refine ⟨hquad_gap, ?_⟩
  intro M_0 hM0 wNum wDen c_1 C_den C_num p_N p_D q_D pTheta qTheta hc1 hpN hqD hqp hnum hden hw
  have hq_pos : qTheta > 0 := Nat.lt_of_lt_of_le hw.1 hw.2.1
  let E_C := C_den * C_num + 1
  let R := M_0 + E_C + p_N * (7 * q_D + 1) + 1
  let s := q_D * R
  have hR_ge2 : R ≥ 2 := by dsimp only [R]; omega
  have hs_ge1 : s ≥ 1 := by
    dsimp only [s]; simpa using Nat.mul_le_mul hqD (by omega : 1 ≤ R)
  let m := 2 * s
  -- Every node along `revSyracuseNode m t` (`t ≤ 2 * m`) is `≥ M_0`:
  have hnode_ge : ∀ t : Nat, t ≤ 2 * m -> revSyracuseNode m t ≥ M_0 := by
    intro t ht
    unfold revSyracuseNode
    have h1 : 2 ^ (t + 1) * 3 ^ (2 * m - t) ≥ 2 ^ (t + 1) * 2 ^ (2 * m - t) :=
      Nat.mul_le_mul_left _ (pow2_le_pow3 _)
    rw [← Nat.pow_add, show (t + 1) + (2 * m - t) = 2 * m + 1 by omega] at h1
    have h2 : 2 * m + 1 < 2 ^ (2 * m + 1) := id_lt_pow2_w13s (2 * m + 1)
    have hs_M0 : s ≥ M_0 := by
      have hm1 : 1 * R ≤ q_D * R := Nat.mul_le_mul_right R hqD
      dsimp only [s, R] at hm1 ⊢; omega
    dsimp only [m] at h1 h2 ⊢; omega
  have hstep_rs : ∀ t : Nat, t < 2 * m ->
      wNum (revSyracuseNode m (t + 1)) * wDen (revSyracuseNode m t) ≤
        wNum (revSyracuseNode m t) * wDen (revSyracuseNode m (t + 1)) := by
    intro t ht
    let xt := revSyracuseNode m t
    let xn := revSyracuseNode m (t + 1)
    rcases (hchain m).2.2 t ht with ⟨hxt_m3, hnOdd_eq⟩
    have hxt_M0 : xt ≥ M_0 := hnode_ge t (Nat.le_of_lt ht)
    have hpre := hw.2.2.2.2 xt hxt_M0 hxt_m3
    dsimp only at hpre
    rw [hnOdd_eq] at hpre
    have hbr : (wNum (2 * xt) * wDen xn + wNum xn * wDen (2 * xt)) * wDen xt ≤
        wNum xt * (wDen (2 * xt) * wDen xn) :=
      nat_mul_le_cancel_left_w5 qTheta _ _ hq_pos
        (Nat.le_trans hpre (Nat.mul_le_mul_right _ hw.2.1))
    have hd2_pos : wDen (2 * xt) > 0 := (hw.2.2.1 (2 * xt) (by omega)).2
    have hdrop : (wNum xn * wDen xt) * wDen (2 * xt) ≤ (wNum xt * wDen xn) * wDen (2 * xt) := by
      have hl : (wNum xn * wDen xt) * wDen (2 * xt) = (wNum xn * wDen (2 * xt)) * wDen xt := by ac_rfl
      have hr : (wNum xt * wDen xn) * wDen (2 * xt) = wNum xt * (wDen (2 * xt) * wDen xn) := by ac_rfl
      rw [hl, hr]; rw [Nat.add_mul] at hbr; omega
    exact nat_mul_le_cancel_right_w5 (wDen (2 * xt)) _ _ hd2_pos hdrop
  have htele : ∀ r : Nat, r ≤ 2 * m ->
      wNum (revSyracuseNode m r) * wDen (revSyracuseNode m 0) ≤
        wNum (revSyracuseNode m 0) * wDen (revSyracuseNode m r) := by
    intro r hr; induction r with
    | zero => exact Nat.le_refl _
    | succ r' ih =>
      have hs_r := hstep_rs r' hr
      have hdr_pos : wDen (revSyracuseNode m r') > 0 :=
        (hw.2.2.1 (revSyracuseNode m r') (hnode_ge r' (Nat.le_of_lt hr))).2
      exact rat_le_trans_pos_w5 _ _ (wNum (revSyracuseNode m r')) (wDen (revSyracuseNode m r')) _ _
        hdr_pos hs_r (ih (Nat.le_of_lt hr))
  let x0 := revSyracuseNode m 0
  let xend := revSyracuseNode m (2 * m)
  have hrat_end : wDen x0 ≤ wNum x0 * wDen xend := by
    have ht := htele (2 * m) (Nat.le_refl _)
    have hwn_end : wNum xend ≥ 1 := (hw.2.2.1 xend (hnode_ge (2 * m) (Nat.le_refl _))).1
    have hm1 : 1 * wDen x0 ≤ wNum xend * wDen x0 := Nat.mul_le_mul_right _ hwn_end
    rw [Nat.one_mul] at hm1
    exact Nat.le_trans hm1 ht
  rcases hbits s hs_ge1 with ⟨_, _, hbl_hi0⟩
  have hqgap := hquad_gap s hs_ge1
  have hxend_rew : revSyracuseNode (2 * s) (4 * s) = xend := by
    dsimp only [xend, m]; rw [show 2 * (2 * s) = 4 * s by omega]
  rw [hxend_rew] at hqgap
  let L0 := binBitLength x0
  let Q0 := L0 ^ 2
  let Qend := (binBitLength xend) ^ 2
  let D_q := Q0 - Qend
  have hDq_ge : 20 * s ^ 2 ≤ D_q := by dsimp only [D_q, Q0, Qend, L0, x0, m]; omega
  have hQ0_sp : Qend + D_q = Q0 := by dsimp only [D_q, Q0, Qend, L0, x0, m]; omega
  have hlo_den0 := (hden x0 (hnode_ge 0 (Nat.zero_le _))).1
  have hhi_denE := (hden xend (hnode_ge (2 * m) (Nat.le_refl _))).2
  change c_1 * p_D ^ Q0 ≤ q_D ^ Q0 * wDen x0 at hlo_den0
  change q_D ^ Qend * wDen xend ≤ C_den * p_D ^ Qend at hhi_denE
  have hcomb_Q : (p_D ^ Qend * q_D ^ Qend) * (c_1 * p_D ^ D_q) ≤
      (p_D ^ Qend * q_D ^ Qend) * (C_den * wNum x0 * q_D ^ D_q) := by
    have hl : (p_D ^ Qend * q_D ^ Qend) * (c_1 * p_D ^ D_q) =
        (c_1 * p_D ^ Q0) * q_D ^ Qend := by
      rw [← hQ0_sp, Nat.pow_add p_D Qend D_q]; ac_rfl
    have hr : (p_D ^ Qend * q_D ^ Qend) * (C_den * wNum x0 * q_D ^ D_q) =
        q_D ^ Q0 * (wNum x0 * (C_den * p_D ^ Qend)) := by
      rw [← hQ0_sp, Nat.pow_add q_D Qend D_q]; ac_rfl
    rw [hl, hr]
    calc
      (c_1 * p_D ^ Q0) * q_D ^ Qend ≤ (q_D ^ Q0 * wDen x0) * q_D ^ Qend :=
        Nat.mul_le_mul_right _ hlo_den0
      _ ≤ (q_D ^ Q0 * (wNum x0 * wDen xend)) * q_D ^ Qend :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hrat_end)
      _ = q_D ^ Q0 * (wNum x0 * (q_D ^ Qend * wDen xend)) := by ac_rfl
      _ ≤ q_D ^ Q0 * (wNum x0 * (C_den * p_D ^ Qend)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hhi_denE)
  have hPQ_pos : p_D ^ Qend * q_D ^ Qend > 0 := by
    have h1 := nat_pow_pos_of_pos p_D (by omega) Qend
    have h2 := nat_pow_pos_of_pos q_D (by omega) Qend
    have hm1 := Nat.mul_le_mul h1 h2; omega
  have hdrop_ineq : p_D ^ D_q ≤ C_den * wNum x0 * q_D ^ D_q := by
    have hc := nat_mul_le_cancel_left_w5 _ _ _ hPQ_pos hcomb_Q
    have h1 : 1 * p_D ^ D_q ≤ c_1 * p_D ^ D_q := Nat.mul_le_mul_right _ hc1
    omega
  -- Step down from `D_q ≥ 20 * s ^ 2` to `20 * s ^ 2`:
  let S20 := 20 * s ^ 2
  let E_ex := D_q - S20
  have hsE : S20 + E_ex = D_q := by dsimp only [S20, E_ex]; omega
  have hs_ineq : p_D ^ S20 ≤ C_den * wNum x0 * q_D ^ S20 := by
    have hqE_pE : q_D ^ E_ex ≤ p_D ^ E_ex := pow_mono_base_w13s q_D p_D (by omega) E_ex
    have hm1 : q_D ^ E_ex * p_D ^ S20 ≤ q_D ^ E_ex * (C_den * wNum x0 * q_D ^ S20) := by
      calc
        q_D ^ E_ex * p_D ^ S20 ≤ p_D ^ E_ex * p_D ^ S20 := Nat.mul_le_mul_right _ hqE_pE
        _ = p_D ^ D_q := by rw [← hsE, Nat.pow_add p_D S20 E_ex, Nat.mul_comm]
        _ ≤ C_den * wNum x0 * q_D ^ D_q := hdrop_ineq
        _ = C_den * wNum x0 * (q_D ^ E_ex * q_D ^ S20) := by
          rw [← hsE, Nat.pow_add q_D S20 E_ex, Nat.mul_comm (q_D ^ S20) (q_D ^ E_ex)]
        _ = q_D ^ E_ex * (C_den * wNum x0 * q_D ^ S20) := by ac_rfl
    exact nat_mul_le_cancel_left_w5 (q_D ^ E_ex) _ _
      (nat_pow_pos_of_pos q_D (by omega) E_ex) hm1
  -- Lower bound `p_D ^ S20 ≥ 2 ^ (20 * q_D * R ^ 2) * q_D ^ S20`:
  let K_exp := 20 * q_D * R ^ 2
  have hS20_eq : S20 = q_D * K_exp := by
    dsimp only [S20, K_exp, s]
    rw [Nat.pow_two (q_D * R), Nat.pow_two R]
    ac_rfl
  have hp_lo : 2 ^ K_exp * q_D ^ S20 ≤ p_D ^ S20 := by
    have hbase := Nat.le_trans (two_mul_pow_self_le_succ_pow_w13s q_D hqD)
      (pow_mono_base_w13s (q_D + 1) p_D (by omega) q_D)
    have hpowK := pow_mono_base_w13s (2 * q_D ^ q_D) (p_D ^ q_D) hbase K_exp
    rw [hS20_eq]
    rwa [mul_pow_w13s 2 (q_D ^ q_D) K_exp,
         pow_pow_eq_mul_w5 q_D q_D K_exp,
         pow_pow_eq_mul_w5 p_D q_D K_exp] at hpowK
  -- Upper bound `C_den * wNum x0 < 2 ^ K_exp`:
  have hnum_lt : C_den * wNum x0 < 2 ^ K_exp := by
    have hn0 := hnum x0 (hnode_ge 0 (Nat.zero_le _))
    change wNum x0 ≤ C_num * p_N ^ L0 at hn0
    have hL0_le : L0 ≤ 7 * s + 1 := hbl_hi0
    have hpN_pow2 : p_N ≤ 2 ^ p_N := Nat.le_of_lt (id_lt_pow2_w13s p_N)
    have hpN_L0 : p_N ^ L0 ≤ 2 ^ (p_N * (7 * s + 1)) := by
      calc
        p_N ^ L0 ≤ (2 ^ p_N) ^ L0 := pow_mono_base_w13s p_N (2 ^ p_N) hpN_pow2 L0
        _ = 2 ^ (p_N * L0) := pow_pow_eq_mul_w5 2 p_N L0
        _ ≤ 2 ^ (p_N * (7 * s + 1)) := pow2_mono_nat (Nat.mul_le_mul_left p_N hL0_le)
    have hEC_lt : C_den * C_num < 2 ^ E_C := by
      have hlt := id_lt_pow2_w13s E_C
      dsimp only [E_C] at hlt ⊢; omega
    have hprod_lt : C_den * wNum x0 < 2 ^ (E_C + p_N * (7 * s + 1)) := by
      have h1 : C_den * wNum x0 ≤ (C_den * C_num) * 2 ^ (p_N * (7 * s + 1)) := by
        calc
          C_den * wNum x0 ≤ C_den * (C_num * p_N ^ L0) := Nat.mul_le_mul_left C_den hn0
          _ = (C_den * C_num) * p_N ^ L0 := by ac_rfl
          _ ≤ (C_den * C_num) * 2 ^ (p_N * (7 * s + 1)) := Nat.mul_le_mul_left _ hpN_L0
      have h2 := Nat.mul_lt_mul_of_pos_right hEC_lt (pow2_pos_nat (p_N * (7 * s + 1)))
      rw [← Nat.pow_add 2 E_C (p_N * (7 * s + 1))] at h2
      exact Nat.lt_of_le_of_lt h1 h2
    have hexp_le : E_C + p_N * (7 * s + 1) ≤ K_exp := by
      have hlin_R : E_C + p_N * (7 * s + 1) ≤ R * R := by
        have h7s1 : 7 * s + 1 ≤ (7 * q_D + 1) * R := by
          dsimp only [s]
          rw [Nat.add_mul (7 * q_D) 1 R, Nat.one_mul]
          have h7 : 7 * (q_D * R) = 7 * q_D * R := by ac_rfl
          rw [h7]; omega
        have hm_pN := Nat.mul_le_mul_left p_N h7s1
        rw [← Nat.mul_assoc p_N (7 * q_D + 1) R] at hm_pN
        have hEC_R : E_C ≤ 1 * R := by
          rw [Nat.one_mul]; dsimp only [R]; omega
        have hsum_R : E_C + p_N * (7 * s + 1) ≤ (1 + p_N * (7 * q_D + 1)) * R := by
          rw [Nat.add_mul]; omega
        have hcoeff_R : 1 + p_N * (7 * q_D + 1) ≤ R := by dsimp only [R]; omega
        exact Nat.le_trans hsum_R (Nat.mul_le_mul_right R hcoeff_R)
      have hRR_K : R * R ≤ K_exp := by
        dsimp only [K_exp]
        rw [← Nat.pow_two R]
        have h20q : 1 ≤ 20 * q_D := by omega
        simpa using Nat.mul_le_mul_right (R ^ 2) h20q
      exact Nat.le_trans hlin_R hRR_K
    exact Nat.lt_of_lt_of_le hprod_lt (pow2_mono_nat hexp_le)
  have hq_S20_pos : q_D ^ S20 > 0 := nat_pow_pos_of_pos q_D (by omega) S20
  have hlt_tot : (C_den * wNum x0) * q_D ^ S20 < 2 ^ K_exp * q_D ^ S20 :=
    Nat.mul_lt_mul_of_pos_right hnum_lt hq_S20_pos
  omega

-- ============================================================================
-- SECTION 2: Front C Part 2 (Branch P5.12) — 10th Solvable Cousin `T_diamond10`
--            with Genuine 8-Tier `ω^8` Cascade (`Cone 11 -> Cone 10 -> ... -> Cone 5`)
-- ============================================================================

/-- Cone 11 of `T_diamond10`: `656179 + x = 2 ^ a * 3 ^ b` with `a ≥ 31, b ≥ 1`
    (starting at `x = 2 ^ 31 * 3 - 656179 = 6441794765`). -/
def isDiamond10Cone11 (x : Nat) : Prop :=
  x ≥ 6441794765 ∧ x % 2147483648 = 2146827469 ∧ x % 3 = 2 ∧ coprime23Core (656179 + x) = 1

instance (x : Nat) : Decidable (isDiamond10Cone11 x) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/--
  10th solvable mixed-(2, 3) Collatz cousin `T_diamond10` on `Nat`:
  Extends `T_diamond9` by adding Cone 11 (`isDiamond10Cone11 x -> (3 * x + 1) / 8`, a genuine
  `v_2(3x + 1) = 3` Syracuse jump that steps `2 ^ a * 3 ^ b - 656179 -> 2 ^ (a - 3) * 3 ^ (b + 1) - 246067`
  directly into Cone 10 -> Cone 9 -> Cone 8 -> Cone 7 -> Cone 6 -> Cone 5's `r`-block spiral climb, e.g.
  `25769147597 -> 9663430349 -> 3623786381 -> 1358919893 -> 31849685 -> 746477 -> 279929 -> ... -> 1`
  in `20` steps, jumping `cousinDiamond2Phi` upward `+38.44x` and defeating 7-tier `ω^7` rankings)!
-/
def cousinDiamond10Step (x : Nat) : Nat :=
  if isDiamond10Cone11 x then (3 * x + 1) / 8 else cousinDiamond9Step x

def cousinDiamond10Iter : Nat -> Nat -> Nat
  | 0, x => x
  | k + 1, x => cousinDiamond10Iter k (cousinDiamond10Step x)

theorem cousinDiamond10Iter_add : ∀ (a b x : Nat),
    cousinDiamond10Iter (a + b) x = cousinDiamond10Iter b (cousinDiamond10Iter a x)
  | 0, _, _ => by simp [cousinDiamond10Iter]
  | a + 1, b, x => by
    rw [Nat.succ_add]
    exact cousinDiamond10Iter_add a b (cousinDiamond10Step x)

/-- Signed extension of `T_diamond10` (`q = 3`) to `Int` for `M2 = Z^-` separation. -/
def cousinDiamond10StepInt (x : Int) : Int :=
  if x ≥ 6441794765 ∧ x % 2147483648 = 2146827469 ∧ x % 3 = 2 ∧ coprime23Core (656179 + x.toNat) = 1
  then (3 * x + 1) / 8
  else cousinDiamond9StepInt x

def cousinDiamond10IterInt : Nat -> Int -> Int
  | 0, x => x
  | k + 1, x => cousinDiamond10IterInt k (cousinDiamond10StepInt x)

/-- Hensel lift of `invMod268435456Odd` (`2^28`) to `mod 2147483648` (`2^31`, since `28 * 2 = 56 ≥ 31`). -/
def invMod2147483648Odd (d : Nat) : Nat :=
  let i268m := invMod268435456Odd d
  (i268m * (4294967298 - ((d % 2147483648) * i268m) % 2147483648)) % 2147483648

/-- Canonical reduced-pair extension of `T_diamond10` (`q = 3`) to positive `Q_(6)^+`. -/
def cousinDiamond10StepQ6 (p : Nat × Nat) : Nat × Nat :=
  let num := p.1
  let den := p.2
  let r2b := (num * invMod2147483648Odd den) % 2147483648
  let r3 := (num * (den % 3)) % 3
  if num ≥ 6441794765 * den ∧ r2b = 2146827469 ∧ r3 = 2 ∧ core3 (core2 (656179 * den + num)) = den
  then reduceRatPair (3 * num + den) (8 * den)
  else cousinDiamond9StepQ6 p

def cousinDiamond10IterQ6 : Nat -> (Nat × Nat) -> (Nat × Nat)
  | 0, p => p
  | k + 1, p => cousinDiamond10IterQ6 k (cousinDiamond10StepQ6 p)

/-- Generalized odd-multiplier `q` step of `T_diamond10` on `Nat` for `M3` (`q = 7`) separation. -/
def cousinDiamond10StepParam (q x : Nat) : Nat :=
  if isDiamond10Cone11 x then (q * x + 1) / 8 else cousinDiamond9StepParam q x

def cousinDiamond10IterParam (q : Nat) : Nat -> Nat -> Nat
  | 0, x => x
  | k + 1, x => cousinDiamond10IterParam q k (cousinDiamond10StepParam q x)

/--
  Theorem W13.3d (`cousinDiamond10StepInt_ofNat_eq`, `zero custom axioms`):
  Exact `Nat`/`Int` step agreement for `T_diamond10` (`∀ x : Nat`).
-/
theorem cousinDiamond10StepInt_ofNat_eq (x : Nat) :
    cousinDiamond10StepInt (x : Int) = (cousinDiamond10Step x : Int) := by
  have h1 : ((x : Int) ≥ 6441794765) ↔ (x ≥ 6441794765) := by omega
  have h2 : ((x : Int) % 2147483648 = 2146827469) ↔ (x % 2147483648 = 2146827469) :=
    ⟨Int.ofNat.inj, congrArg Int.ofNat⟩
  have h3 : ((x : Int) % 3 = 2) ↔ (x % 3 = 2) :=
    ⟨Int.ofNat.inj, congrArg Int.ofNat⟩
  have hdiv : ((3 * (x : Int) + 1) / 8) = (((3 * x + 1) / 8 : Nat) : Int) := by omega
  have htoNat : (x : Int).toNat = x := rfl
  unfold cousinDiamond10StepInt cousinDiamond10Step isDiamond10Cone11
  rw [htoNat]
  simp only [h1, h2, h3]
  by_cases hc11 : x ≥ 6441794765 ∧ x % 2147483648 = 2146827469 ∧ x % 3 = 2 ∧ coprime23Core (656179 + x) = 1
  · simp only [hc11, and_self, ite_true, hdiv]
  · simp only [hc11, ite_false]
    exact cousinDiamond9StepInt_ofNat_eq x

theorem cousinDiamond10Step_pos (x : Nat) (hx : x > 0) : cousinDiamond10Step x > 0 := by
  unfold cousinDiamond10Step
  by_cases hc11 : isDiamond10Cone11 x
  · simp only [hc11, ite_true]
    have hge : x ≥ 6441794765 := hc11.1
    clear hc11
    have hle : (3 * 6441794765 + 1) / 8 ≤ (3 * x + 1) / 8 :=
      Nat.div_le_div_right (by omega)
    exact Nat.lt_of_lt_of_le (by decide : 0 < (3 * 6441794765 + 1) / 8) hle
  · simp only [hc11, ite_false]; exact cousinDiamond9Step_pos x hx

theorem cousinDiamond10Step_eq_d9_of_not_cone11 (x : Nat) (hnc11 : ¬ isDiamond10Cone11 x) :
    cousinDiamond10Step x = cousinDiamond9Step x := by
  unfold cousinDiamond10Step; simp [hnc11]

/--
  Theorem W13.3e (`cousin_diamond10_outside_cones4to11_strict_descent`, `zero custom axioms`):
  Outside Cones 4, 5, 6, 7, 8, 9, 10, and 11, EVERY `x > 2` strictly decreases `cousinDiamond2Phi` in 1 step!
-/
theorem cousin_diamond10_outside_cones4to11_strict_descent
    (x : Nat) (hx : x > 2)
    (hnc4 : ¬ isDiamond3Cone4 x) (hnc5 : ¬ isDiamond4Cone5 x)
    (hnc6 : ¬ isDiamond5Cone6 x) (hnc7 : ¬ isDiamond6Cone7 x)
    (hnc8 : ¬ isDiamond7Cone8 x) (hnc9 : ¬ isDiamond8Cone9 x)
    (hnc10 : ¬ isDiamond9Cone10 x) (hnc11 : ¬ isDiamond10Cone11 x) :
    cousinDiamond2Phi (cousinDiamond10Step x) < cousinDiamond2Phi x := by
  rw [cousinDiamond10Step_eq_d9_of_not_cone11 x hnc11]
  exact cousin_diamond9_outside_cones4to10_strict_descent x hx hnc4 hnc5 hnc6 hnc7 hnc8 hnc9 hnc10

-- Modular Cone-11 avoidance helpers (`2146827469 % 268435456 = 267779277, % 256 = 205, % 32 = 13`):

theorem mod268m_of_cone11 (z : Nat) (hc11 : isDiamond10Cone11 z) : z % 268435456 = 267779277 := by
  have h := congrArg (· % 268435456) hc11.2.1
  rwa [Nat.mod_mod_of_dvd z (by decide : 268435456 ∣ 2147483648)] at h

theorem mod256_of_cone11 (z : Nat) (hc11 : isDiamond10Cone11 z) : z % 256 = 205 := by
  have h := congrArg (· % 256) (mod268m_of_cone11 z hc11)
  rwa [Nat.mod_mod_of_dvd z (by decide : 256 ∣ 268435456)] at h

theorem mod32_of_cone11 (z : Nat) (hc11 : isDiamond10Cone11 z) : z % 32 = 13 := by
  have h := congrArg (· % 32) (mod256_of_cone11 z hc11)
  rwa [Nat.mod_mod_of_dvd z (by decide : 32 ∣ 256)] at h

theorem not_cone11_of_even (z : Nat) (hev : z % 2 = 0) : ¬ isDiamond10Cone11 z := by
  intro hc11
  have h := congrArg (· % 2) (mod32_of_cone11 z hc11)
  rw [Nat.mod_mod_of_dvd z (by decide : 2 ∣ 32), hev] at h
  cases h

theorem not_cone11_of_mod4_eq_3 (z : Nat) (hm4 : z % 4 = 3) : ¬ isDiamond10Cone11 z := by
  intro hc11
  have h := congrArg (· % 4) (mod32_of_cone11 z hc11)
  rw [Nat.mod_mod_of_dvd z (by decide : 4 ∣ 32), hm4] at h
  cases h

theorem not_cone11_of_mod8_ne_5 (z : Nat) (hm8 : z % 8 ≠ 5) : ¬ isDiamond10Cone11 z := by
  intro hc11
  have h := congrArg (· % 8) (mod32_of_cone11 z hc11)
  rw [Nat.mod_mod_of_dvd z (by decide : 8 ∣ 32)] at h
  exact hm8 h

theorem not_cone11_of_mod16_ne_13 (z : Nat) (hm16 : z % 16 ≠ 13) : ¬ isDiamond10Cone11 z := by
  intro hc11
  have h := congrArg (· % 16) (mod32_of_cone11 z hc11)
  rw [Nat.mod_mod_of_dvd z (by decide : 16 ∣ 32)] at h
  exact hm16 h

theorem not_cone11_of_mod32_ne_13 (z : Nat) (hm32 : z % 32 ≠ 13) : ¬ isDiamond10Cone11 z :=
  fun hc11 => hm32 (mod32_of_cone11 z hc11)

theorem not_cone11_of_mod256_ne_205 (z : Nat) (hm256 : z % 256 ≠ 205) : ¬ isDiamond10Cone11 z :=
  fun hc11 => hm256 (mod256_of_cone11 z hc11)

theorem not_cone11_of_mod268m_ne (z : Nat) (hm : z % 268435456 ≠ 267779277) : ¬ isDiamond10Cone11 z :=
  fun hc11 => hm (mod268m_of_cone11 z hc11)

theorem not_cone11_of_mod3_ne_2 (z : Nat) (hm3 : z % 3 ≠ 2) : ¬ isDiamond10Cone11 z := by
  rintro ⟨_, _, h3, _⟩; exact hm3 h3

/--
  Theorem W13.3f (`not_cone11_six_mul_pow9_sub1`, choice-free `zero custom axioms`):
  Universal Post-Climb Drain Non-Reentry into Cone 11 (`∀ m : Nat`, `(6 * 9^m - 1) % 16 = 5 ≠ 13`).
-/
theorem not_cone11_six_mul_pow9_sub1 (m : Nat) :
    ¬ isDiamond10Cone11 (6 * 9 ^ m - 1) := by
  apply not_cone11_of_mod16_ne_13
  have hp9 := nat_pow_pos_of_pos 9 (by decide) m
  have hm8 := pow9_mod8_eq_one_w5 m
  have hdm := (Nat.div_add_mod (9 ^ m) 8).symm
  omega

theorem isDiamond9Cone10_of_pow2_pow3 (p q : Nat) (hp : p ≥ 28) (hq : q ≥ 1) :
    isDiamond9Cone10 (2 ^ p * 3 ^ q - 246067) := by
  have hc : (2 : Nat) ^ 28 = 268435456 := by decide
  have hp2_ge : 2 ^ p ≥ 268435456 := by
    rw [← hc]; exact pow2_mono_nat hp
  have hp3_ge : 3 ^ q ≥ 3 := by
    simpa using nat_pow_mono_exp_pos 3 1 q (by decide) hq
  have hprod_ge : 2 ^ p * 3 ^ q ≥ 805306368 := by
    simpa using Nat.mul_le_mul hp2_ge hp3_ge
  have hp268m : 268435456 ∣ 2 ^ p * 3 ^ q := by
    have hsp : p = 28 + (p - 28) := by omega
    rw [hsp, Nat.pow_add 2 28 (p - 28), hc, Nat.mul_assoc]
    exact ⟨2 ^ (p - 28) * 3 ^ q, rfl⟩
  have hp3_div : 3 ∣ 2 ^ p * 3 ^ q := by
    have hsp : q = 1 + (q - 1) := by omega
    rw [hsp, Nat.pow_add 3 1 (q - 1), Nat.pow_one,
        ← Nat.mul_assoc (2 ^ p) 3, Nat.mul_comm (2 ^ p) 3, Nat.mul_assoc]
    exact ⟨2 ^ p * 3 ^ (q - 1), rfl⟩
  refine ⟨by clear hc hp2_ge hp3_ge hp268m hp3_div; generalize 2 ^ p * 3 ^ q = P at hprod_ge ⊢; omega,
          ?_, ?_, ?_⟩
  · rcases hp268m with ⟨k, hk⟩
    clear hc hp2_ge hp3_ge hp3_div
    generalize 2 ^ p * 3 ^ q = P at hprod_ge hk ⊢
    have hk_ge : k ≥ 3 := by omega
    rw [hk, show k = (k - 1) + 1 by omega, Nat.mul_add 268435456 (k - 1) 1, Nat.mul_one]
    generalize k - 1 = k'
    have hsub : 268435456 * k' + 268435456 - 246067 = 268189389 + 268435456 * k' := by omega
    rw [hsub, Nat.add_mul_mod_self_left]
  · rcases hp3_div with ⟨k3, hk3⟩
    clear hc hp2_ge hp3_ge hp268m
    generalize 2 ^ p * 3 ^ q = P at hprod_ge hk3 ⊢
    omega
  · have hadd : 246067 + (2 ^ p * 3 ^ q - 246067) = 2 ^ p * 3 ^ q := by
      clear hc hp2_ge hp3_ge hp268m hp3_div
      generalize 2 ^ p * 3 ^ q = P at hprod_ge ⊢
      omega
    rw [hadd]
    exact coprime23Core_pow2_pow3 p q

theorem cousin_diamond10_mersenne_scaled :
    ∀ (k a q : Nat), k + 1 ≤ a -> q ≥ 1 ->
      cousinDiamond10Iter k (2 ^ a * q - 1) = 3 ^ k * 2 ^ (a - k) * q - 1
  | 0, _, _, _, _ => by simp [cousinDiamond10Iter]
  | k + 1, a, q, hka, hq => by
    have hp4 : 2 ^ a * q = 4 * (2 ^ (a - 2) * q) := by
      conv => lhs; rw [show a = (a - 2) + 2 by omega]
      rw [Nat.pow_add 2 (a - 2) 2, show (2 : Nat) ^ 2 = 4 from rfl,
          Nat.mul_comm (2 ^ (a - 2)) 4, Nat.mul_assoc]
    have hm_pos : 2 ^ (a - 2) * q ≥ 1 := Nat.mul_le_mul (pow2_pos_nat (a - 2)) hq
    have hz4 : (2 ^ a * q - 1) % 4 = 3 := by omega
    simp only [cousinDiamond10Iter]
    rw [cousinDiamond10Step_eq_d9_of_not_cone11 _ (not_cone11_of_mod4_eq_3 _ hz4)]
    have hd9 := cousin_diamond9_mersenne_scaled 1 a q (by omega) hq
    simp only [cousinDiamond9Iter, Nat.pow_one] at hd9
    have hstep_eq : cousinDiamond9Step (2 ^ a * q - 1) = 2 ^ (a - 1) * (3 * q) - 1 := by
      rw [hd9]; apply congrArg (· - 1); ac_rfl
    rw [hstep_eq, cousin_diamond10_mersenne_scaled k (a - 1) (3 * q) (by omega) (by omega),
        show a - 1 - k = a - (k + 1) by omega, Nat.pow_succ 3 k]
    apply congrArg (· - 1); ac_rfl

theorem cousin_diamond10_even9_spine_drain :
    ∀ k : Nat, cousinDiamond10Iter k ((9 ^ (k + 1) - 1) / 4) = 2
  | 0 => rfl
  | k + 1 => by
    let j := k + 1
    have hp9j_ge9 : 9 ^ j ≥ 9 := by
      dsimp only [j]; rw [Nat.pow_succ]; have hp := nat_pow_pos_of_pos 9 (by decide) k; omega
    have hp9j_m8 : 9 ^ j % 8 = 1 := pow9_mod8_eq_one_w5 j
    let q := (9 ^ j - 1) / 8
    have hp9j_eq : 9 ^ j = 8 * q + 1 := by dsimp only [q]; omega
    have he_j1 : (9 ^ (j + 1) - 1) / 4 = 18 * q + 2 := by rw [Nat.pow_succ 9 j, hp9j_eq]; omega
    simp only [cousinDiamond10Iter]
    change cousinDiamond10Iter k (cousinDiamond10Step ((9 ^ (j + 1) - 1) / 4)) = 2
    have hnc11 : ¬ isDiamond10Cone11 ((9 ^ (j + 1) - 1) / 4) := by
      rw [he_j1]; exact not_cone11_of_even _ (by omega)
    rw [cousinDiamond10Step_eq_d9_of_not_cone11 _ hnc11]
    have hd9 : cousinDiamond9Step ((9 ^ (j + 1) - 1) / 4) = (9 ^ j - 1) / 4 := by
      have he_j : (9 ^ j - 1) / 4 = 2 * q := by rw [hp9j_eq]; omega
      rw [he_j1, he_j,
          cousinDiamond9Step_eq_d8_of_not_cone10 _ (not_cone10_of_even _ (by omega)),
          cousinDiamond8Step_eq_d7_of_not_cone9 _ (not_cone9_of_even _ (by omega)),
          cousinDiamond7Step_eq_d6_of_not_cone8 _ (not_cone8_of_even _ (by omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 _ (not_cone7_of_even _ (by omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _ (not_cone6_of_even _ (by omega))]
      have hnc5 : ¬ isDiamond4Cone5 (18 * q + 2) := by rintro ⟨_, h32, _, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5]; unfold cousinDiamond3Step
      have hq_pos : q ≥ 1 := by dsimp only [q]; omega
      have hodd_f : ¬ ((18 * q + 2) % 2 = 1) := by omega
      have h18_t : 18 * q + 2 ≥ 20 ∧ (18 * q + 2) % 18 = 2 := ⟨by omega, by omega⟩
      simp only [hodd_f, h18_t, and_self, ite_true, ite_false]; omega
    rw [hd9]
    exact cousin_diamond10_even9_spine_drain k

theorem cousin_diamond10_pow3_sub1_drain :
    ∀ k : Nat, cousinDiamond10Iter k (3 ^ (k + 1) - 1) = 2
  | 0 => rfl
  | k + 1 => by
    let j := k + 1
    have hp3_ge3 : 3 ^ j ≥ 3 := by dsimp only [j]; rw [Nat.pow_succ]; have hp := pow3_pos_nat k; omega
    have ho_j1 := pow3_odd_nat_sec8 (j + 1)
    have hp_j1 := pow3_pos_nat (j + 1)
    simp only [cousinDiamond10Iter]
    change cousinDiamond10Iter k (cousinDiamond10Step (3 ^ (j + 1) - 1)) = 2
    rw [cousinDiamond10Step_eq_d9_of_not_cone11 _ (not_cone11_of_even _ (by omega)),
        cousinDiamond9Step_eq_d8_of_not_cone10 _ (not_cone10_of_even _ (by omega)),
        cousinDiamond8Step_eq_d7_of_not_cone9 _ (not_cone9_of_even _ (by omega)),
        cousinDiamond7Step_eq_d6_of_not_cone8 _ (not_cone8_of_even _ (by omega)),
        cousinDiamond6Step_eq_d5_of_not_cone7 _ (not_cone7_of_even _ (by omega)),
        cousinDiamond5Step_eq_d4_of_not_cone6 _ (not_cone6_of_even _ (by omega))]
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
            dsimp only [j]; rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ]; omega
          have ho' := pow3_odd_nat_sec8 k'; omega
      have hm6 : 3 ^ (j + 1) - 1 > 2 ∧ (3 ^ (j + 1) - 1) % 6 = 2 := by rw [h3j1]; omega
      unfold cousinDiamond3Step
      simp only [hev, hn18, hm6, and_self, ite_true, ite_false]
      rw [h3j1]; omega
    rw [hd4]
    exact cousin_diamond10_pow3_sub1_drain k

theorem cousin_diamond10_cone5_two_step_climb :
    ∀ (q_c a b : Nat), 3 * q_c + 2 ≤ a -> b ≥ 1 ->
      cousinDiamond10Iter (2 * q_c) (2 ^ a * 3 ^ b - 7) =
        2 ^ (a - 3 * q_c) * 3 ^ (b + 2 * q_c) - 7
  | 0, _, _, _, _ => by simp [cousinDiamond10Iter]
  | q_c + 1, a, b, ha, hb => by
    have ha5 : a ≥ 5 := by omega
    have hc5 := isDiamond4Cone5_of_pow2_pow3 a b ha5 hb
    have hnc11_0 : ¬ isDiamond10Cone11 (2 ^ a * 3 ^ b - 7) :=
      not_cone11_of_mod32_ne_13 _ (by have h := hc5.2.1; omega)
    let mid := 2 ^ (a - 2) * 3 ^ (b + 1) - 5
    have hmid_4 : mid % 4 = 3 := by
      dsimp only [mid]
      have hp8 : 2 ^ (a - 2) = 8 * 2 ^ (a - 5) := by
        conv => lhs; rw [show a - 2 = 3 + (a - 5) by omega]; rw [Nat.pow_add]
      rw [hp8, Nat.mul_assoc 8]
      have hp_pos : 2 ^ (a - 5) * 3 ^ (b + 1) ≥ 1 :=
        Nat.mul_le_mul (pow2_pos_nat _) (pow3_pos_nat _)
      omega
    have hnc11_1 : ¬ isDiamond10Cone11 mid := not_cone11_of_mod4_eq_3 mid hmid_4
    have hd9_2 := cousin_diamond9_cone5_two_step_climb 1 a b (by omega) hb
    simp only [Nat.mul_one, cousinDiamond9Iter] at hd9_2
    have hd9_s1 : cousinDiamond9Step (2 ^ a * 3 ^ b - 7) = mid := by
      rw [cousinDiamond9Step_eq_d8_of_not_cone10 _
            (not_cone10_of_mod32_ne_13 _ (by have h := hc5.2.1; omega)),
          cousinDiamond8Step_eq_d7_of_not_cone9 _
            (not_cone9_of_mod32_ne_13 _ (by have h := hc5.2.1; omega)),
          cousinDiamond7Step_eq_d6_of_not_cone8 _
            (not_cone8_of_mod32_ne_21 _ (by have h := hc5.2.1; omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 _
            (not_cone7_of_mod32_ne_21 _ (by have h := hc5.2.1; omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _
            (not_cone6_of_mod32_ne_13 _ (by have h := hc5.2.1; omega))]
      unfold cousinDiamond4Step; simp only [hc5, ite_true]
      dsimp only [mid]
      have hp4 : 2 ^ a = 4 * 2 ^ (a - 2) := by
        conv => lhs; rw [show a = 2 + (a - 2) by omega]; rw [Nat.pow_add]
      have hp_pos : 2 ^ (a - 2) * 3 ^ b ≥ 8 * 3 := by
        have h1 : 8 ≤ 2 ^ (a - 2) := by
          have hc : (2 : Nat) ^ 3 = 8 := by decide
          rw [← hc]; exact pow2_mono_nat (by omega)
        have h2 : 3 ≤ 3 ^ b := by simpa using nat_pow_mono_exp_pos 3 1 b (by decide) hb
        simpa using Nat.mul_le_mul h1 h2
      have h3_eq : 2 ^ (a - 2) * 3 ^ (b + 1) = 3 * (2 ^ (a - 2) * 3 ^ b) := by
        rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm _ 3]
      rw [hp4, Nat.mul_assoc 4, h3_eq]
      generalize 2 ^ (a - 2) * 3 ^ b = A at hp_pos ⊢
      omega
    rw [hd9_s1] at hd9_2
    have hs1 : cousinDiamond10Step (2 ^ a * 3 ^ b - 7) = mid := by
      rw [cousinDiamond10Step_eq_d9_of_not_cone11 _ hnc11_0]; exact hd9_s1
    have hs2 : cousinDiamond10Step mid = 2 ^ (a - 3) * 3 ^ (b + 2) - 7 := by
      rw [cousinDiamond10Step_eq_d9_of_not_cone11 _ hnc11_1]; exact hd9_2
    rw [Nat.mul_succ 2 q_c, Nat.add_comm (2 * q_c) 2,
        cousinDiamond10Iter_add 2 (2 * q_c)]
    have hi2 : cousinDiamond10Iter 2 (2 ^ a * 3 ^ b - 7) = 2 ^ (a - 3) * 3 ^ (b + 2) - 7 := by
      simp only [cousinDiamond10Iter, hs1, hs2]
    rw [hi2, cousin_diamond10_cone5_two_step_climb q_c (a - 3) (b + 2) (by omega) (by omega)]
    apply congrArg (· - 7)
    congr 1
    · apply congrArg (2 ^ ·); omega
    · apply congrArg (3 ^ ·); omega

theorem cousin_diamond10_a0_3_drain (b0 : Nat) (hb0 : b0 ≥ 3) :
    cousinDiamond10Step (8 * 3 ^ b0 - 7) = 12 * 3 ^ b0 - 10 ∧
    cousinDiamond10Step (12 * 3 ^ b0 - 10) = 4 * 3 ^ b0 - 4 ∧
    cousinDiamond10Step (4 * 3 ^ b0 - 4) = 4 * 3 ^ (b0 - 1) - 2 ∧
    cousinDiamond10Iter ((b0 - 1) / 2 + 7) (8 * 3 ^ b0 - 7) = 1 := by
  rcases cousin_diamond9_a0_3_drain b0 hb0 with ⟨hd9_1, hd9_2, hd9_3, _⟩
  have hp3_ge27 : 3 ^ b0 ≥ 27 := by simpa using nat_pow_mono_exp_pos 3 3 b0 (by decide) hb0
  have hp3_b1_ge9 : 3 ^ (b0 - 1) ≥ 9 := by
    simpa using nat_pow_mono_exp_pos 3 2 (b0 - 1) (by decide) (by omega)
  have hnc11_1 : ¬ isDiamond10Cone11 (8 * 3 ^ b0 - 7) := by
    apply not_cone11_of_mod32_ne_13; have ho := pow3_odd_nat_sec8 b0; omega
  have hs1 : cousinDiamond10Step (8 * 3 ^ b0 - 7) = 12 * 3 ^ b0 - 10 := by
    rw [cousinDiamond10Step_eq_d9_of_not_cone11 _ hnc11_1]; exact hd9_1
  have hs2 : cousinDiamond10Step (12 * 3 ^ b0 - 10) = 4 * 3 ^ b0 - 4 := by
    rw [cousinDiamond10Step_eq_d9_of_not_cone11 _ (not_cone11_of_even _ (by omega))]; exact hd9_2
  have hs3 : cousinDiamond10Step (4 * 3 ^ b0 - 4) = 4 * 3 ^ (b0 - 1) - 2 := by
    rw [cousinDiamond10Step_eq_d9_of_not_cone11 _ (not_cone11_of_even _ (by omega))]; exact hd9_3
  refine ⟨hs1, hs2, hs3, ?_⟩
  by_cases hev_b1 : (b0 - 1) % 2 = 0
  · let m := (b0 - 1) / 2
    have hm1 : m ≥ 1 := by dsimp only [m]; omega
    have hb1_eq : b0 - 1 = 2 * m := by dsimp only [m]; omega
    have hp9_ge9 : 9 ^ m ≥ 9 := by rw [pow9_eq_pow3_double m, ← hb1_eq]; exact hp3_b1_ge9
    have hp9_m8 : 9 ^ m % 8 = 1 := pow9_mod8_eq_one_w5 m
    have h4_eq : 4 * 3 ^ (b0 - 1) - 2 = 4 * 9 ^ m - 2 := by
      rw [hb1_eq, ← pow9_eq_pow3_double m]
    let zr := 2 * 9 ^ m - 1
    let yr := (3 * 9 ^ m - 1) / 2
    have hs4 : cousinDiamond10Step (4 * 9 ^ m - 2) = zr := by
      rw [cousinDiamond10Step_eq_d9_of_not_cone11 _ (not_cone11_of_even _ (by omega)),
          cousinDiamond9Step_eq_d8_of_not_cone10 _ (not_cone10_of_even _ (by omega)),
          cousinDiamond8Step_eq_d7_of_not_cone9 _ (not_cone9_of_even _ (by omega)),
          cousinDiamond7Step_eq_d6_of_not_cone8 _ (not_cone8_of_even _ (by omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 _ (not_cone7_of_even _ (by omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _ (not_cone6_of_even _ (by omega))]
      have hnc5 : ¬ isDiamond4Cone5 (4 * 9 ^ m - 2) := by rintro ⟨_, h32, _, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5]
      have h9m9 : 9 ^ m % 9 = 0 := by rw [show m = (m - 1) + 1 by omega, Nat.pow_succ]; omega
      rw [cousinDiamond3Step_even_plain_half_w8 _ (by omega) (by omega) (by omega) (by omega)]
      dsimp only [zr]; omega
    have hsz : cousinDiamond10Step zr = yr := by
      rw [cousinDiamond10Step_eq_d9_of_not_cone11 zr (not_cone11_of_mod8_ne_5 zr (by dsimp only [zr]; omega)),
          cousinDiamond9Step_eq_d8_of_not_cone10 zr (not_cone10_of_mod8_ne_5 zr (by dsimp only [zr]; omega)),
          cousinDiamond8Step_eq_d7_of_not_cone9 zr (not_cone9_of_mod8_ne_5 zr (by dsimp only [zr]; omega)),
          cousinDiamond7Step_eq_d6_of_not_cone8 zr (not_cone8_of_mod8_ne_5 zr (by dsimp only [zr]; omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 zr (not_cone7_of_mod8_ne_5 zr (by dsimp only [zr]; omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 zr (not_cone6_of_mod16_ne_13 zr (by dsimp only [zr]; omega))]
      have hnc5 : ¬ isDiamond4Cone5 zr := by rintro ⟨_, h32, _, _⟩; dsimp only [zr] at h32; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 zr hnc5]
      have hc3 : core3 (zr + 1) = 2 := by
        rw [show zr + 1 = 2 * 9 ^ m by dsimp only [zr]; omega,
            core3_mul2 (9 ^ m) (by omega), (pow9_eq_v3Pow_w5 m).2]
      rw [cousinDiamond3Step_of_core3_succ_two_w8 zr (by dsimp only [zr]; omega) (by dsimp only [zr]; omega) hc3]
      dsimp only [zr, yr]; omega
    have hsy : cousinDiamond10Step yr = (9 ^ (m + 1) - 1) / 4 := by
      have hyr_m3 : yr % 3 = 1 := by
        have hm3 : 9 ^ m % 3 = 0 := by rw [show m = (m - 1) + 1 by omega, Nat.pow_succ]; omega
        dsimp only [yr]; omega
      rw [cousinDiamond10Step_eq_d9_of_not_cone11 yr (not_cone11_of_mod3_ne_2 yr (by omega)),
          cousinDiamond9Step_eq_d8_of_not_cone10 yr (not_cone10_of_mod3_ne_2 yr (by omega)),
          cousinDiamond8Step_eq_d7_of_not_cone9 yr (not_cone9_of_mod3_ne_2 yr (by omega)),
          cousinDiamond7Step_eq_d6_of_not_cone8 yr (not_cone8_of_mod3_ne_2 yr (by omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 yr (not_cone7_of_mod9_ne_8 yr (by omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 yr (not_cone6_of_mod9_ne_8 yr (by omega))]
      have hnc5 : ¬ isDiamond4Cone5 yr := by rintro ⟨_, _, hm3, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 yr hnc5]
      have hc3_2 : core3 (2 * yr + 1) = 1 := by
        rw [show 2 * yr + 1 = 3 * 9 ^ m by dsimp only [yr]; omega,
            core3_mul3 (9 ^ m) (by omega), (pow9_eq_v3Pow_w5 m).2]
      have hc3_1 : core3 (yr + 1) ≠ 2 := by
        have hnd3 : (yr + 1) % 3 ≠ 0 := by
          clear hd9_1 hd9_2 hd9_3 hs1 hs2 hs3 h4_eq hs4 hsz hnc5 hc3_2; omega
        rw [core3_not_div3 (yr + 1) hnd3]
        clear hd9_1 hd9_2 hd9_3 hs1 hs2 hs3 h4_eq hs4 hsz hnc5 hc3_2
        dsimp only [yr]; omega
      have hnc4 : ¬ isDiamond3Cone4 yr := by
        rintro ⟨hge169, _, hc2⟩
        by_cases hm_eq1 : m = 1
        · clear hd9_1 hd9_2 hd9_3 hs1 hs2 hs3 h4_eq hs4 hsz hnc5 hc3_2 hc3_1 hc2
          dsimp only [yr] at hge169; rw [hm_eq1] at hge169; omega
        · have hm2 : m ≥ 2 := by
            clear hd9_1 hd9_2 hd9_3 hs1 hs2 hs3 h4_eq hs4 hsz hnc5 hc3_2 hc3_1 hge169 hc2; omega
          rcases eq_pow2_of_core2_eq_one (3 * yr + 5)
            (by clear hd9_1 hd9_2 hd9_3 hs1 hs2 hs3 h4_eq hs4 hsz hnc5 hc3_2 hc3_1; dsimp only [yr]; omega) hc2 with
            ⟨M0, hM0⟩
          have h9_eq : 9 ^ (m + 1) + 7 = 2 ^ (M0 + 1) := by
            have h2mul : 2 * (3 * yr + 5) = 9 ^ (m + 1) + 7 := by
              clear hd9_1 hd9_2 hd9_3 hs1 hs2 hs3 h4_eq hs4 hsz hnc5 hc3_2 hc3_1 hc2 hM0
              rw [Nat.pow_succ 9 m, Nat.mul_comm (9 ^ m) 9]; dsimp only [yr]; omega
            rw [← h2mul, hM0, Nat.pow_succ 2 M0, Nat.mul_comm]
          exact pow9_succ_add_seven_ne_pow2 m (M0 + 1) hm2 h9_eq
      rw [cousinDiamond3Step_odd_half_w8 yr (by dsimp only [yr]; omega) hnc4 hc3_2 hc3_1]
      dsimp only [yr]; rw [Nat.pow_succ 9 m]; omega
    change cousinDiamond10Iter (m + 7) (8 * 3 ^ b0 - 7) = 1
    rw [show m + 7 = 4 + 1 + 1 + m + 1 by omega,
        cousinDiamond10Iter_add (4 + 1 + 1 + m) 1,
        cousinDiamond10Iter_add (4 + 1 + 1) m,
        cousinDiamond10Iter_add (4 + 1) 1,
        cousinDiamond10Iter_add 4 1]
    have hi4 : cousinDiamond10Iter 4 (8 * 3 ^ b0 - 7) = zr := by
      simp only [cousinDiamond10Iter, hs1, hs2, hs3, h4_eq, hs4]
    rw [hi4]
    have hiz : cousinDiamond10Iter 1 zr = yr := hsz
    rw [hiz]
    have hiy : cousinDiamond10Iter 1 yr = (9 ^ (m + 1) - 1) / 4 := hsy
    rw [hiy, cousin_diamond10_even9_spine_drain m]
    decide
  · let m := (b0 - 1) / 2
    have hm1 : m ≥ 1 := by dsimp only [m]; omega
    have hb1_eq : b0 - 1 = 2 * m + 1 := by dsimp only [m]; omega
    have hp9_ge9 : 9 ^ m ≥ 9 := by
      rw [show m = (m - 1) + 1 by omega, Nat.pow_succ]
      have hp := nat_pow_pos_of_pos 9 (by decide) (m - 1); omega
    have hp9_m8 : 9 ^ m % 8 = 1 := pow9_mod8_eq_one_w5 m
    let ur := 6 * 9 ^ m - 1
    let wr := (9 ^ (m + 1) - 1) / 2
    have hu_eq : 4 * 3 ^ (b0 - 1) - 2 = 12 * 9 ^ m - 2 := by
      rw [hb1_eq, Nat.pow_succ 3 (2 * m), ← pow9_eq_pow3_double m]; omega
    have hs4 : cousinDiamond10Step (12 * 9 ^ m - 2) = ur := by
      rw [cousinDiamond10Step_eq_d9_of_not_cone11 _ (not_cone11_of_even _ (by omega)),
          cousinDiamond9Step_eq_d8_of_not_cone10 _ (not_cone10_of_even _ (by omega)),
          cousinDiamond8Step_eq_d7_of_not_cone9 _ (not_cone9_of_even _ (by omega)),
          cousinDiamond7Step_eq_d6_of_not_cone8 _ (not_cone8_of_even _ (by omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 _ (not_cone7_of_even _ (by omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _ (not_cone6_of_even _ (by omega))]
      have hnc5 : ¬ isDiamond4Cone5 (12 * 9 ^ m - 2) := by rintro ⟨_, h32, _, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5]
      have h9m9 : 9 ^ m % 9 = 0 := by rw [show m = (m - 1) + 1 by omega, Nat.pow_succ]; omega
      rw [cousinDiamond3Step_even_plain_half_w8 _ (by omega) (by omega) (by omega) (by omega)]
      dsimp only [ur]; omega
    have hsu : cousinDiamond10Step ur = wr := by
      rw [cousinDiamond10Step_eq_d9_of_not_cone11 ur (not_cone11_six_mul_pow9_sub1 m),
          cousinDiamond9Step_eq_d8_of_not_cone10 ur (not_cone10_six_mul_pow9_sub1 m),
          cousinDiamond8Step_eq_d7_of_not_cone9 ur (not_cone9_six_mul_pow9_sub1 m),
          cousinDiamond7Step_eq_d6_of_not_cone8 ur (not_cone8_six_mul_pow9_sub1 m),
          cousinDiamond6Step_eq_d5_of_not_cone7 ur (not_cone7_six_mul_pow9_sub1 m),
          cousinDiamond5Step_eq_d4_of_not_cone6 ur (not_cone6_of_mod16_ne_13 ur (by dsimp only [ur]; omega))]
      have hnc5 : ¬ isDiamond4Cone5 ur := by rintro ⟨_, h32, _, _⟩; dsimp only [ur] at h32; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 ur hnc5]
      have hc3 : core3 (ur + 1) = 2 := by
        rw [show ur + 1 = 2 * (3 * 9 ^ m) by dsimp only [ur]; omega,
            core3_mul2 (3 * 9 ^ m) (by omega),
            core3_mul3 (9 ^ m) (by omega), (pow9_eq_v3Pow_w5 m).2]
      rw [cousinDiamond3Step_of_core3_succ_two_w8 ur (by dsimp only [ur]; omega) (by dsimp only [ur]; omega) hc3]
      dsimp only [ur, wr]; rw [Nat.pow_succ 9 m]; omega
    have hsw : cousinDiamond10Step wr = (9 ^ (m + 1) - 1) / 4 := by
      let q := (9 ^ m - 1) / 8
      have hq_pos : q ≥ 1 := by dsimp only [q]; omega
      have hp9_eq : 9 ^ m = 8 * q + 1 := by dsimp only [q]; omega
      have hwr_eq : wr = 36 * q + 4 := by dsimp only [wr]; rw [Nat.pow_succ 9 m, hp9_eq]; omega
      have hnext_eq : (9 ^ (m + 1) - 1) / 4 = 18 * q + 2 := by rw [Nat.pow_succ 9 m, hp9_eq]; omega
      rw [hwr_eq, hnext_eq,
          cousinDiamond10Step_eq_d9_of_not_cone11 _ (not_cone11_of_even _ (by omega)),
          cousinDiamond9Step_eq_d8_of_not_cone10 _ (not_cone10_of_even _ (by omega)),
          cousinDiamond8Step_eq_d7_of_not_cone9 _ (not_cone9_of_even _ (by omega)),
          cousinDiamond7Step_eq_d6_of_not_cone8 _ (not_cone8_of_even _ (by omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 _ (not_cone7_of_even _ (by omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _ (not_cone6_of_even _ (by omega))]
      have hnc5 : ¬ isDiamond4Cone5 (36 * q + 4) := by rintro ⟨_, h32, _, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5,
          cousinDiamond3Step_even_plain_half_w8 _ (by omega) (by omega) (by omega) (by omega)]
      omega
    change cousinDiamond10Iter (m + 7) (8 * 3 ^ b0 - 7) = 1
    rw [show m + 7 = 4 + 1 + 1 + m + 1 by omega,
        cousinDiamond10Iter_add (4 + 1 + 1 + m) 1,
        cousinDiamond10Iter_add (4 + 1 + 1) m,
        cousinDiamond10Iter_add (4 + 1) 1,
        cousinDiamond10Iter_add 4 1]
    have hi4 : cousinDiamond10Iter 4 (8 * 3 ^ b0 - 7) = ur := by
      simp only [cousinDiamond10Iter, hs1, hs2, hs3, hu_eq, hs4]
    rw [hi4]
    have hiu : cousinDiamond10Iter 1 ur = wr := hsu
    rw [hiu]
    have hiw : cousinDiamond10Iter 1 wr = (9 ^ (m + 1) - 1) / 4 := hsw
    rw [hiw, cousin_diamond10_even9_spine_drain m]
    decide

theorem cousin_diamond10_a0_2_and_4_drain (b0 : Nat) (hb0 : b0 ≥ 3) :
    cousinDiamond10Iter (b0 + 3) (4 * 3 ^ b0 - 7) = 1 ∧
    cousinDiamond10Iter ((b0 - 1) / 2 + 8) (16 * 3 ^ b0 - 7) = 1 := by
  have hp3_ge27 : 3 ^ b0 ≥ 27 := by simpa using nat_pow_mono_exp_pos 3 3 b0 (by decide) hb0
  have hp3_b1_ge9 : 3 ^ (b0 - 1) ≥ 9 := by
    simpa using nat_pow_mono_exp_pos 3 2 (b0 - 1) (by decide) (by omega)
  have hp3_b2_ge3 : 3 ^ (b0 - 2) ≥ 3 := by
    simpa using nat_pow_mono_exp_pos 3 1 (b0 - 2) (by decide) (by omega)
  have h3b0_sp : 3 ^ b0 = 3 * 3 ^ (b0 - 1) := by
    conv => lhs; rw [show b0 = 1 + (b0 - 1) by omega]; rw [Nat.pow_add, Nat.pow_one]
  have h3b1_sp : 3 ^ (b0 - 1) = 3 * 3 ^ (b0 - 2) := by
    conv => lhs; rw [show b0 - 1 = 1 + (b0 - 2) by omega]; rw [Nat.pow_add, Nat.pow_one]
  have h3b0_m9 : 3 ^ b0 % 9 = 0 := by rw [h3b0_sp, h3b1_sp]; omega
  have h3b0_m8 : 3 ^ b0 % 8 = 1 ∨ 3 ^ b0 % 8 = 3 := by
    by_cases hev : b0 % 2 = 0
    · left
      rw [show b0 = 2 * (b0 / 2) by omega, ← pow9_eq_pow3_double]
      exact pow9_mod8_eq_one_w5 _
    · right
      rw [show b0 = 2 * (b0 / 2) + 1 by omega, Nat.pow_succ, ← pow9_eq_pow3_double,
          Nat.mul_mod, pow9_mod8_eq_one_w5]
  have hnc11_4 : ¬ isDiamond10Cone11 (4 * 3 ^ b0 - 7) := by
    apply not_cone11_of_mod32_ne_13
    have hdm := (Nat.div_add_mod (3 ^ b0) 8).symm
    rcases h3b0_m8 with h1 | h3 <;> omega
  have hnc11_16 : ¬ isDiamond10Cone11 (16 * 3 ^ b0 - 7) := by
    apply not_cone11_of_mod32_ne_13; have ho := pow3_odd_nat_sec8 b0; omega
  have hnc10_4 : ¬ isDiamond9Cone10 (4 * 3 ^ b0 - 7) := by
    apply not_cone10_of_mod32_ne_13
    have hdm := (Nat.div_add_mod (3 ^ b0) 8).symm
    rcases h3b0_m8 with h1 | h3 <;> omega
  have hnc10_16 : ¬ isDiamond9Cone10 (16 * 3 ^ b0 - 7) := by
    apply not_cone10_of_mod32_ne_13; have ho := pow3_odd_nat_sec8 b0; omega
  have hnc9_4 : ¬ isDiamond8Cone9 (4 * 3 ^ b0 - 7) := by
    apply not_cone9_of_mod32_ne_13
    have hdm := (Nat.div_add_mod (3 ^ b0) 8).symm
    rcases h3b0_m8 with h1 | h3 <;> omega
  have hnc9_16 : ¬ isDiamond8Cone9 (16 * 3 ^ b0 - 7) := by
    apply not_cone9_of_mod32_ne_13; have ho := pow3_odd_nat_sec8 b0; omega
  have hnc8_4 : ¬ isDiamond7Cone8 (4 * 3 ^ b0 - 7) := by
    apply not_cone8_of_mod32_ne_21
    have hdm := (Nat.div_add_mod (3 ^ b0) 8).symm
    rcases h3b0_m8 with h1 | h3 <;> omega
  have hnc8_16 : ¬ isDiamond7Cone8 (16 * 3 ^ b0 - 7) := by
    apply not_cone8_of_mod32_ne_21; have ho := pow3_odd_nat_sec8 b0; omega
  have hnc7_c : ∀ c : Nat, c ≥ 1 -> ¬ isDiamond6Cone7 (c * 3 ^ b0 - 7) := by
    intro c hc1; apply not_cone7_of_mod9_ne_8
    have hm : c * 3 ^ b0 ≥ 27 := by simpa using Nat.mul_le_mul hc1 hp3_ge27
    have hm9 : (c * 3 ^ b0) % 9 = 0 := by rw [Nat.mul_mod, h3b0_m9, Nat.mul_zero, Nat.zero_mod]
    omega
  have hnc6_c : ∀ c : Nat, c ≥ 1 -> ¬ isDiamond5Cone6 (c * 3 ^ b0 - 7) := by
    intro c hc1; apply not_cone6_of_mod9_ne_8
    have hm : c * 3 ^ b0 ≥ 27 := by simpa using Nat.mul_le_mul hc1 hp3_ge27
    have hm9 : (c * 3 ^ b0) % 9 = 0 := by rw [Nat.mul_mod, h3b0_m9, Nat.mul_zero, Nat.zero_mod]
    omega
  refine ⟨?_, ?_⟩
  · have hs1 : cousinDiamond10Step (4 * 3 ^ b0 - 7) = 6 * 3 ^ b0 - 10 := by
      rw [cousinDiamond10Step_eq_d9_of_not_cone11 _ hnc11_4,
          cousinDiamond9Step_eq_d8_of_not_cone10 _ hnc10_4,
          cousinDiamond8Step_eq_d7_of_not_cone9 _ hnc9_4,
          cousinDiamond7Step_eq_d6_of_not_cone8 _ hnc8_4,
          cousinDiamond6Step_eq_d5_of_not_cone7 _ (hnc7_c 4 (by decide)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _ (hnc6_c 4 (by decide))]
      exact cousin_diamond4_exit_step_general_odd 4 b0 (Or.inl rfl) hb0
    have hs2 : cousinDiamond10Step (6 * 3 ^ b0 - 10) = 2 * 3 ^ b0 - 4 := by
      rw [cousinDiamond10Step_eq_d9_of_not_cone11 _ (not_cone11_of_even _ (by omega)),
          cousinDiamond9Step_eq_d8_of_not_cone10 _ (not_cone10_of_even _ (by omega)),
          cousinDiamond8Step_eq_d7_of_not_cone9 _ (not_cone9_of_even _ (by omega)),
          cousinDiamond7Step_eq_d6_of_not_cone8 _ (not_cone8_of_even _ (by omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 _ (not_cone7_of_even _ (by omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _ (not_cone6_of_even _ (by omega))]
      have hnc5 : ¬ isDiamond4Cone5 (6 * 3 ^ b0 - 10) := by rintro ⟨_, h32, _, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5]
      have h18 : 6 * 3 ^ b0 = 18 * 3 ^ (b0 - 1) := by rw [h3b0_sp]; omega
      rw [cousinDiamond3Step_even_mod6_not18_w8 _ (by omega) (by omega) ⟨by omega, by omega⟩]
      omega
    have hs3 : cousinDiamond10Step (2 * 3 ^ b0 - 4) = 2 * 3 ^ (b0 - 1) - 2 := by
      rw [cousinDiamond10Step_eq_d9_of_not_cone11 _ (not_cone11_of_even _ (by omega)),
          cousinDiamond9Step_eq_d8_of_not_cone10 _ (not_cone10_of_even _ (by omega)),
          cousinDiamond8Step_eq_d7_of_not_cone9 _ (not_cone9_of_even _ (by omega)),
          cousinDiamond7Step_eq_d6_of_not_cone8 _ (not_cone8_of_even _ (by omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 _ (not_cone7_of_even _ (by omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _ (not_cone6_of_even _ (by omega))]
      have hnc5 : ¬ isDiamond4Cone5 (2 * 3 ^ b0 - 4) := by rintro ⟨_, h32, _, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5]
      have h18 : 2 * 3 ^ b0 = 18 * 3 ^ (b0 - 2) := by rw [h3b0_sp, h3b1_sp]; omega
      rw [cousinDiamond3Step_even_mod6_not18_w8 _ (by omega) (by omega) ⟨by omega, by omega⟩]
      omega
    have hs4 : cousinDiamond10Step (2 * 3 ^ (b0 - 1) - 2) = 3 ^ (b0 - 1) - 1 := by
      rw [cousinDiamond10Step_eq_d9_of_not_cone11 _ (not_cone11_of_even _ (by omega)),
          cousinDiamond9Step_eq_d8_of_not_cone10 _ (not_cone10_of_even _ (by omega)),
          cousinDiamond8Step_eq_d7_of_not_cone9 _ (not_cone9_of_even _ (by omega)),
          cousinDiamond7Step_eq_d6_of_not_cone8 _ (not_cone8_of_even _ (by omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 _ (not_cone7_of_even _ (by omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _ (not_cone6_of_even _ (by omega))]
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
        cousinDiamond10Iter_add (4 + (b0 - 2)) 1,
        cousinDiamond10Iter_add 4 (b0 - 2)]
    have hi4 : cousinDiamond10Iter 4 (4 * 3 ^ b0 - 7) = 3 ^ ((b0 - 2) + 1) - 1 := by
      simp only [cousinDiamond10Iter, hs1, hs2, hs3, hs4]
      rw [show b0 - 1 = (b0 - 2) + 1 by omega]
    rw [hi4, cousin_diamond10_pow3_sub1_drain (b0 - 2)]
    decide
  · rcases cousin_diamond10_a0_3_drain b0 hb0 with ⟨ha3_s1, ha3_s2, ha3_s3, ha3⟩
    have hs1 : cousinDiamond10Step (16 * 3 ^ b0 - 7) = 24 * 3 ^ b0 - 10 := by
      rw [cousinDiamond10Step_eq_d9_of_not_cone11 _ hnc11_16,
          cousinDiamond9Step_eq_d8_of_not_cone10 _ hnc10_16,
          cousinDiamond8Step_eq_d7_of_not_cone9 _ hnc9_16,
          cousinDiamond7Step_eq_d6_of_not_cone8 _ hnc8_16,
          cousinDiamond6Step_eq_d5_of_not_cone7 _ (hnc7_c 16 (by decide)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _ (hnc6_c 16 (by decide))]
      exact cousin_diamond4_exit_step_general_odd 16 b0 (Or.inr (Or.inr rfl)) hb0
    have hs2 : cousinDiamond10Step (24 * 3 ^ b0 - 10) = 8 * 3 ^ b0 - 4 := by
      rw [cousinDiamond10Step_eq_d9_of_not_cone11 _ (not_cone11_of_even _ (by omega)),
          cousinDiamond9Step_eq_d8_of_not_cone10 _ (not_cone10_of_even _ (by omega)),
          cousinDiamond8Step_eq_d7_of_not_cone9 _ (not_cone9_of_even _ (by omega)),
          cousinDiamond7Step_eq_d6_of_not_cone8 _ (not_cone8_of_even _ (by omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 _ (not_cone7_of_even _ (by omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _ (not_cone6_of_even _ (by omega))]
      have hnc5 : ¬ isDiamond4Cone5 (24 * 3 ^ b0 - 10) := by rintro ⟨_, h32, _, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5]
      have h18 : 24 * 3 ^ b0 = 18 * (4 * 3 ^ (b0 - 1)) := by rw [h3b0_sp]; omega
      rw [cousinDiamond3Step_even_mod6_not18_w8 _ (by omega) (by omega) ⟨by omega, by omega⟩]
      omega
    have hs3 : cousinDiamond10Step (8 * 3 ^ b0 - 4) = 8 * 3 ^ (b0 - 1) - 2 := by
      rw [cousinDiamond10Step_eq_d9_of_not_cone11 _ (not_cone11_of_even _ (by omega)),
          cousinDiamond9Step_eq_d8_of_not_cone10 _ (not_cone10_of_even _ (by omega)),
          cousinDiamond8Step_eq_d7_of_not_cone9 _ (not_cone9_of_even _ (by omega)),
          cousinDiamond7Step_eq_d6_of_not_cone8 _ (not_cone8_of_even _ (by omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 _ (not_cone7_of_even _ (by omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _ (not_cone6_of_even _ (by omega))]
      have hnc5 : ¬ isDiamond4Cone5 (8 * 3 ^ b0 - 4) := by rintro ⟨_, h32, _, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5]
      have h18 : 8 * 3 ^ b0 = 18 * (4 * 3 ^ (b0 - 2)) := by rw [h3b0_sp, h3b1_sp]; omega
      rw [cousinDiamond3Step_even_mod6_not18_w8 _ (by omega) (by omega) ⟨by omega, by omega⟩]
      omega
    have hs4 : cousinDiamond10Step (8 * 3 ^ (b0 - 1) - 2) = 4 * 3 ^ (b0 - 1) - 2 := by
      rw [cousinDiamond10Step_eq_d9_of_not_cone11 _ (not_cone11_of_even _ (by omega)),
          cousinDiamond9Step_eq_d8_of_not_cone10 _ (not_cone10_of_even _ (by omega)),
          cousinDiamond8Step_eq_d7_of_not_cone9 _ (not_cone9_of_even _ (by omega)),
          cousinDiamond7Step_eq_d6_of_not_cone8 _ (not_cone8_of_even _ (by omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 _ (not_cone7_of_even _ (by omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 _ (not_cone6_of_even _ (by omega))]
      have hnc5 : ¬ isDiamond4Cone5 (8 * 3 ^ (b0 - 1) - 2) := by rintro ⟨_, h32, _, _⟩; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 _ hnc5]
      have h18 : 8 * 3 ^ (b0 - 1) = 18 * (4 * 3 ^ (b0 - 3)) := by
        conv => lhs; rhs; rw [show b0 - 1 = 2 + (b0 - 3) by omega]
        rw [Nat.pow_add]; omega
      have hp3_b3 := pow3_pos_nat (b0 - 3)
      rw [cousinDiamond3Step_even_mod8_eq6_w8 _ (by omega) (by omega) (by omega) ⟨by omega, by omega⟩]
      omega
    rw [show (b0 - 1) / 2 + 7 = 3 + ((b0 - 1) / 2 + 4) by omega,
        cousinDiamond10Iter_add 3 ((b0 - 1) / 2 + 4)] at ha3
    have hi3 : cousinDiamond10Iter 3 (8 * 3 ^ b0 - 7) = 4 * 3 ^ (b0 - 1) - 2 := by
      simp only [cousinDiamond10Iter, ha3_s1, ha3_s2, ha3_s3]
    rw [hi3] at ha3
    rw [show (b0 - 1) / 2 + 8 = 4 + ((b0 - 1) / 2 + 4) by omega,
        cousinDiamond10Iter_add 4 ((b0 - 1) / 2 + 4)]
    have hi4 : cousinDiamond10Iter 4 (16 * 3 ^ b0 - 7) = 4 * 3 ^ (b0 - 1) - 2 := by
      simp only [cousinDiamond10Iter, hs1, hs2, hs3, hs4]
    rw [hi4]
    exact ha3

theorem cousin_diamond10_cone4_return_aux (x : Nat) (hc4 : isDiamond3Cone4 x) :
    ∃ k : Nat, k ≤ cousinDiamond2Phi x ∧ cousinDiamond10Iter k x = 1 := by
  rcases cousin_diamond3_cone4_reaches_one_exact x hc4 with ⟨r, hr_ge3, hE, _, hphi_ge⟩
  refine ⟨3 * r + 4, hphi_ge, ?_⟩
  have hnc11_x : ¬ isDiamond10Cone11 x := not_cone11_of_mod8_ne_5 x (by have h8 := hc4.2.1; omega)
  have hnc10_x : ¬ isDiamond9Cone10 x := not_cone10_of_mod8_ne_5 x (by have h8 := hc4.2.1; omega)
  have hnc9_x : ¬ isDiamond8Cone9 x := not_cone9_of_mod8_ne_5 x (by have h8 := hc4.2.1; omega)
  have hnc8_x : ¬ isDiamond7Cone8 x := not_cone8_of_mod8_ne_5 x (by have h8 := hc4.2.1; omega)
  have hnc7_x : ¬ isDiamond6Cone7 x := not_cone7_of_mod8_ne_5 x (by have h8 := hc4.2.1; omega)
  have hnc6_x : ¬ isDiamond5Cone6 x := by rintro ⟨_, h256, _, _⟩; have h8 := hc4.2.1; omega
  have hx_odd : x % 2 = 1 := by have h8 := hc4.2.1; omega
  have hs1 : cousinDiamond10Step x = 2 ^ (2 * r + 1) - 1 := by
    rw [cousinDiamond10Step_eq_d9_of_not_cone11 x hnc11_x,
        cousinDiamond9Step_eq_d8_of_not_cone10 x hnc10_x,
        cousinDiamond8Step_eq_d7_of_not_cone9 x hnc9_x,
        cousinDiamond7Step_eq_d6_of_not_cone8 x hnc8_x,
        cousinDiamond6Step_eq_d5_of_not_cone7 x hnc7_x,
        cousinDiamond5Step_eq_d4_of_not_cone6 x hnc6_x]
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
  have hglide : cousinDiamond10Iter (2 * r) (2 ^ (2 * r + 1) - 1) = zr := by
    have hf := cousin_diamond10_mersenne_scaled (2 * r) (2 * r + 1) 1 (by omega) (by decide)
    simp only [Nat.mul_one, show 2 * r + 1 - 2 * r = 1 by omega, Nat.pow_one] at hf
    rw [hf, ← pow9_eq_pow3_double r, Nat.mul_comm]
  have hp9_ge729 : 9 ^ r ≥ 729 := by simpa using nat_pow_mono_exp_pos 9 3 r (by decide) hr_ge3
  have hp9_m8 : 9 ^ r % 8 = 1 := pow9_mod8_eq_one_w5 r
  have hsz : cousinDiamond10Step zr = yr := by
    rw [cousinDiamond10Step_eq_d9_of_not_cone11 zr (not_cone11_of_mod8_ne_5 zr (by dsimp only [zr]; omega)),
        cousinDiamond9Step_eq_d8_of_not_cone10 zr (not_cone10_of_mod8_ne_5 zr (by dsimp only [zr]; omega)),
        cousinDiamond8Step_eq_d7_of_not_cone9 zr (not_cone9_of_mod8_ne_5 zr (by dsimp only [zr]; omega)),
        cousinDiamond7Step_eq_d6_of_not_cone8 zr (not_cone8_of_mod8_ne_5 zr (by dsimp only [zr]; omega)),
        cousinDiamond6Step_eq_d5_of_not_cone7 zr (not_cone7_of_mod8_ne_5 zr (by dsimp only [zr]; omega)),
        cousinDiamond5Step_eq_d4_of_not_cone6 zr (not_cone6_of_mod16_ne_13 zr (by dsimp only [zr]; omega))]
    have hnc5 : ¬ isDiamond4Cone5 zr := by rintro ⟨_, h32, _, _⟩; dsimp only [zr] at h32; omega
    rw [cousinDiamond4Step_eq_d3_of_not_cone5 zr hnc5]
    have hc3 : core3 (zr + 1) = 2 := by
      rw [show zr + 1 = 2 * 9 ^ r by dsimp only [zr]; omega,
          core3_mul2 (9 ^ r) (by omega), (pow9_eq_v3Pow_w5 r).2]
    rw [cousinDiamond3Step_of_core3_succ_two_w8 zr (by dsimp only [zr]; omega) (by dsimp only [zr]; omega) hc3]
    dsimp only [zr, yr]; omega
  have hsy : cousinDiamond10Step yr = (9 ^ (r + 1) - 1) / 4 := by
    have hyr_m3 : yr % 3 = 1 := by
      have hm3 : 9 ^ r % 3 = 0 := by rw [show r = (r - 1) + 1 by omega, Nat.pow_succ]; omega
      dsimp only [yr]; omega
    rw [cousinDiamond10Step_eq_d9_of_not_cone11 yr (not_cone11_of_mod3_ne_2 yr (by omega)),
        cousinDiamond9Step_eq_d8_of_not_cone10 yr (not_cone10_of_mod3_ne_2 yr (by omega)),
        cousinDiamond8Step_eq_d7_of_not_cone9 yr (not_cone9_of_mod3_ne_2 yr (by omega)),
        cousinDiamond7Step_eq_d6_of_not_cone8 yr (not_cone8_of_mod3_ne_2 yr (by omega)),
        cousinDiamond6Step_eq_d5_of_not_cone7 yr (not_cone7_of_mod9_ne_8 yr (by omega)),
        cousinDiamond5Step_eq_d4_of_not_cone6 yr (not_cone6_of_mod9_ne_8 yr (by omega))]
    have hnc5 : ¬ isDiamond4Cone5 yr := by rintro ⟨_, _, hm3, _⟩; omega
    rw [cousinDiamond4Step_eq_d3_of_not_cone5 yr hnc5]
    have hc3_2 : core3 (2 * yr + 1) = 1 := by
      rw [show 2 * yr + 1 = 3 * 9 ^ r by dsimp only [yr]; omega,
          core3_mul3 (9 ^ r) (by omega), (pow9_eq_v3Pow_w5 r).2]
    have hc3_1 : core3 (yr + 1) ≠ 2 := by
      rw [core3_not_div3 (yr + 1) (by omega)]; dsimp only [yr]; omega
    have hnc4 : ¬ isDiamond3Cone4 yr := by
      rintro ⟨_, _, hc2⟩
      rcases eq_pow2_of_core2_eq_one (3 * yr + 5) (by dsimp only [yr]; omega) hc2 with ⟨M0, hM0⟩
      have h9_eq : 9 ^ (r + 1) + 7 = 2 ^ (M0 + 1) := by
        have h2mul : 2 * (3 * yr + 5) = 9 ^ (r + 1) + 7 := by
          rw [Nat.pow_succ 9 r, Nat.mul_comm (9 ^ r) 9]; dsimp only [yr]; omega
        rw [← h2mul, hM0, Nat.pow_succ 2 M0, Nat.mul_comm]
      exact pow9_succ_add_seven_ne_pow2 r (M0 + 1) (by omega) h9_eq
    rw [cousinDiamond3Step_odd_half_w8 yr (by dsimp only [yr]; omega) hnc4 hc3_2 hc3_1]
    dsimp only [yr]; rw [Nat.pow_succ 9 r]; omega
  rw [show 3 * r + 4 = 1 + 2 * r + 1 + 1 + r + 1 by omega,
      cousinDiamond10Iter_add (1 + 2 * r + 1 + 1 + r) 1,
      cousinDiamond10Iter_add (1 + 2 * r + 1 + 1) r,
      cousinDiamond10Iter_add (1 + 2 * r + 1) 1,
      cousinDiamond10Iter_add (1 + 2 * r) 1,
      cousinDiamond10Iter_add 1 (2 * r)]
  have hi1 : cousinDiamond10Iter 1 x = 2 ^ (2 * r + 1) - 1 := hs1
  rw [hi1, hglide]
  have hiz : cousinDiamond10Iter 1 zr = yr := hsz
  rw [hiz]
  have hiy : cousinDiamond10Iter 1 yr = (9 ^ (r + 1) - 1) / 4 := hsy
  rw [hiy, cousin_diamond10_even9_spine_drain r]
  decide

theorem cousin_diamond10_cone5_return_aux (x : Nat) (hc5 : isDiamond4Cone5 x) :
    ∃ (a b k : Nat),
      a ≥ 5 ∧ b ≥ 1 ∧ x + 7 = 2 ^ a * 3 ^ b ∧
      k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond10Iter k x = 1 := by
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
  have hb0_ge3 : b0 ≥ 3 := by dsimp only [b0, q_c]; omega
  have ha0_234 : a0 = 2 ∨ a0 = 3 ∨ a0 = 4 := by dsimp only [a0, q_c]; omega
  have hclimb := cousin_diamond10_cone5_two_step_climb q_c a b (by dsimp only [q_c]; omega) hb1
  rw [← hx_eq] at hclimb
  change cousinDiamond10Iter (2 * q_c) x = 2 ^ a0 * 3 ^ b0 - 7 at hclimb
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
    dsimp only [q_c, b0] at hex ⊢
    omega
  have hd_3 := (cousin_diamond10_a0_3_drain b0 hb0_ge3).2.2.2
  rcases cousin_diamond10_a0_2_and_4_drain b0 hb0_ge3 with ⟨hd_2, hd_4⟩
  rcases ha0_234 with ha2 | ha3 | ha4
  · have hkx := hbound_x (b0 + 3) (by omega)
    refine ⟨a, b, 2 * q_c + (b0 + 3), ha5, hb1, hmul.symm, hkx,
      Nat.le_trans (by omega : 2 * q_c + (b0 + 3) ≤ x + 1) (cousinDiamond2Phi_ge_succ x), ?_⟩
    rw [cousinDiamond10Iter_add (2 * q_c) (b0 + 3) x, hclimb, ha2]; exact hd_2
  · have hkx := hbound_x ((b0 - 1) / 2 + 7) (by omega)
    refine ⟨a, b, 2 * q_c + ((b0 - 1) / 2 + 7), ha5, hb1, hmul.symm, hkx,
      Nat.le_trans (by omega : 2 * q_c + ((b0 - 1) / 2 + 7) ≤ x + 1) (cousinDiamond2Phi_ge_succ x), ?_⟩
    rw [cousinDiamond10Iter_add (2 * q_c) ((b0 - 1) / 2 + 7) x, hclimb, ha3]; exact hd_3
  · have hkx := hbound_x ((b0 - 1) / 2 + 8) (by omega)
    refine ⟨a, b, 2 * q_c + ((b0 - 1) / 2 + 8), ha5, hb1, hmul.symm, hkx,
      Nat.le_trans (by omega : 2 * q_c + ((b0 - 1) / 2 + 8) ≤ x + 1) (cousinDiamond2Phi_ge_succ x), ?_⟩
    rw [cousinDiamond10Iter_add (2 * q_c) ((b0 - 1) / 2 + 8) x, hclimb, ha4]; exact hd_4

theorem cousin_diamond10_cone6_return_aux (x : Nat) (hc6 : isDiamond5Cone6 x) :
    ∃ (e f k : Nat),
      e ≥ 8 ∧ f ≥ 2 ∧ x + 19 = 2 ^ e * 3 ^ f ∧
      cousinDiamond10Step x = 2 ^ (e - 3) * 3 ^ (f + 1) - 7 ∧
      isDiamond4Cone5 (cousinDiamond10Step x) ∧
      k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond10Iter k x = 1 := by
  have hnc11_x : ¬ isDiamond10Cone11 x :=
    not_cone11_of_mod256_ne_205 x (by rw [hc6.2.1]; decide)
  have hx_ge : x ≥ 2285 := hc6.1
  rcases (cousin_diamond9_cones4to10_exact_return.2.2.1 x hc6) with
    ⟨e, f, _, he8, hf2, hmul, hd9_x, _, _, _, _⟩
  let y := 2 ^ (e - 3) * 3 ^ (f + 1) - 7
  have hstep_x : cousinDiamond10Step x = y := by
    rw [cousinDiamond10Step_eq_d9_of_not_cone11 x hnc11_x]; exact hd9_x
  have hnc10_x : ¬ isDiamond9Cone10 x :=
    not_cone10_of_mod256_ne_205 x (by rw [hc6.2.1]; decide)
  have hnc9_x : ¬ isDiamond8Cone9 x :=
    not_cone9_of_mod256_ne_141 x (by rw [hc6.2.1]; decide)
  have hnc8_x : ¬ isDiamond7Cone8 x :=
    not_cone8_of_mod256_ne_213 x (by rw [hc6.2.1]; decide)
  have hnc7_x : ¬ isDiamond6Cone7 x :=
    not_cone7_of_mod256_ne_213 x (by rw [hc6.2.1]; decide)
  have hy_step : y = (3 * x + 1) / 8 :=
    hd9_x.symm.trans (by
      rw [cousinDiamond9Step_eq_d8_of_not_cone10 x hnc10_x,
          cousinDiamond8Step_eq_d7_of_not_cone9 x hnc9_x,
          cousinDiamond7Step_eq_d6_of_not_cone8 x hnc8_x,
          cousinDiamond6Step_eq_d5_of_not_cone7 x hnc7_x]
      unfold cousinDiamond5Step; simp [hc6])
  clear hc6 hnc11_x hnc10_x hnc9_x hnc8_x hnc7_x hd9_x
  have hc5_y : isDiamond4Cone5 y :=
    isDiamond4Cone5_of_pow2_pow3 (e - 3) (f + 1) (by omega) (by omega)
  rcases cousin_diamond10_cone5_return_aux y hc5_y with ⟨_, _, ky, _, _, _, hky_le_y, _, hky_1⟩
  have hy_lt_x : y + 1 ≤ x := by
    have hdiv : y * 8 ≤ 3 * x + 1 := by rw [hy_step]; exact Nat.div_mul_le_self (3 * x + 1) 8
    clear hy_step hmul hstep_x hc5_y hky_1; omega
  have h1ky_x : 1 + ky ≤ x := by clear hy_step hmul hstep_x hc5_y hky_1; omega
  have h1ky_phi : 1 + ky ≤ cousinDiamond2Phi x :=
    Nat.le_trans (by clear hy_step hmul hstep_x hc5_y hky_1; omega : 1 + ky ≤ x + 1) (cousinDiamond2Phi_ge_succ x)
  refine ⟨e, f, 1 + ky, he8, hf2, hmul, hstep_x, ?_, h1ky_x, h1ky_phi, ?_⟩
  · rw [hstep_x]; exact hc5_y
  · rw [cousinDiamond10Iter_add 1 ky x]
    have hi1 : cousinDiamond10Iter 1 x = y := hstep_x
    rw [hi1]; exact hky_1

theorem cousin_diamond10_cone7_return_aux (x : Nat) (hc7 : isDiamond6Cone7 x) :
    ∃ (g h k : Nat),
      g ≥ 15 ∧ h ≥ 2 ∧ x + 811 = 2 ^ g * 3 ^ h ∧
      cousinDiamond10Step x = 2 ^ (g - 7) * 3 ^ (h + 1) - 19 ∧
      isDiamond5Cone6 (cousinDiamond10Step x) ∧
      k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond10Iter k x = 1 := by
  have hnc11_x : ¬ isDiamond10Cone11 x := by
    apply not_cone11_of_mod32_ne_13
    have h32 : x % 32 = 31957 % 32 := by
      have h := congrArg (· % 32) hc7.2.1
      rwa [Nat.mod_mod_of_dvd x (by decide : 32 ∣ 32768)] at h
    rw [h32]; decide
  have hnc10_x : ¬ isDiamond9Cone10 x := by
    apply not_cone10_of_mod32_ne_13
    have h32 : x % 32 = 31957 % 32 := by
      have h := congrArg (· % 32) hc7.2.1
      rwa [Nat.mod_mod_of_dvd x (by decide : 32 ∣ 32768)] at h
    rw [h32]; decide
  have hnc9_x : ¬ isDiamond8Cone9 x := by
    apply not_cone9_of_mod32_ne_13
    have h32 : x % 32 = 31957 % 32 := by
      have h := congrArg (· % 32) hc7.2.1
      rwa [Nat.mod_mod_of_dvd x (by decide : 32 ∣ 32768)] at h
    rw [h32]; decide
  have hnc8_x : ¬ isDiamond7Cone8 x :=
    not_cone8_of_mod32768_ne_30933 x (by rw [hc7.2.1]; decide)
  have hx_ge : x ≥ 294101 := hc7.1
  rcases (cousin_diamond9_cones4to10_exact_return.2.2.2.1 x hc7) with
    ⟨g, h, _, hg15, hh2, hmul, hd9_x, _, _, _, _⟩
  let y := 2 ^ (g - 7) * 3 ^ (h + 1) - 19
  have hstep_x : cousinDiamond10Step x = y := by
    rw [cousinDiamond10Step_eq_d9_of_not_cone11 x hnc11_x]; exact hd9_x
  have hy_step : y = (3 * x + 1) / 128 :=
    hd9_x.symm.trans (by
      rw [cousinDiamond9Step_eq_d8_of_not_cone10 x hnc10_x,
          cousinDiamond8Step_eq_d7_of_not_cone9 x hnc9_x,
          cousinDiamond7Step_eq_d6_of_not_cone8 x hnc8_x]
      unfold cousinDiamond6Step; simp [hc7])
  clear hc7 hnc11_x hnc10_x hnc9_x hnc8_x hd9_x
  have hc6_y : isDiamond5Cone6 y :=
    isDiamond5Cone6_of_pow2_pow3 (g - 7) (h + 1) (by omega) (by omega)
  rcases cousin_diamond10_cone6_return_aux y hc6_y with ⟨_, _, ky, _, _, _, _, _, hky_le_y, _, hky_1⟩
  have hy_lt_x : y + 1 ≤ x := by
    have hdiv : y * 128 ≤ 3 * x + 1 := by rw [hy_step]; exact Nat.div_mul_le_self (3 * x + 1) 128
    clear hy_step hmul hstep_x hc6_y hky_1; omega
  have h1ky_x : 1 + ky ≤ x := by clear hy_step hmul hstep_x hc6_y hky_1; omega
  have h1ky_phi : 1 + ky ≤ cousinDiamond2Phi x :=
    Nat.le_trans (by clear hy_step hmul hstep_x hc6_y hky_1; omega : 1 + ky ≤ x + 1) (cousinDiamond2Phi_ge_succ x)
  refine ⟨g, h, 1 + ky, hg15, hh2, hmul, hstep_x, ?_, h1ky_x, h1ky_phi, ?_⟩
  · rw [hstep_x]; exact hc6_y
  · rw [cousinDiamond10Iter_add 1 ky x]
    have hi1 : cousinDiamond10Iter 1 x = y := hstep_x
    rw [hi1]; exact hky_1

theorem cousin_diamond10_cone8_return_aux (x : Nat) (hc8 : isDiamond7Cone8 x) :
    ∃ (u v k : Nat),
      u ≥ 22 ∧ v ≥ 1 ∧ x + 34603 = 2 ^ u * 3 ^ v ∧
      cousinDiamond10Step x = 2 ^ (u - 7) * 3 ^ (v + 1) - 811 ∧
      isDiamond6Cone7 (cousinDiamond10Step x) ∧
      k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond10Iter k x = 1 := by
  have hnc11_x : ¬ isDiamond10Cone11 x :=
    not_cone11_of_mod32_ne_13 x (by have h := mod32_of_cone8 x hc8; omega)
  have hnc10_x : ¬ isDiamond9Cone10 x :=
    not_cone10_of_mod32_ne_13 x (by have h := mod32_of_cone8 x hc8; omega)
  have hnc9_x : ¬ isDiamond8Cone9 x :=
    not_cone9_of_mod32_ne_13 x (by have h := mod32_of_cone8 x hc8; omega)
  have hx_ge : x ≥ 12548309 := hc8.1
  rcases (cousin_diamond9_cones4to10_exact_return.2.2.2.2.1 x hc8) with
    ⟨u, v, _, hu22, hv1, hmul, hd9_x, _, _, _, _⟩
  let y := 2 ^ (u - 7) * 3 ^ (v + 1) - 811
  have hstep_x : cousinDiamond10Step x = y := by
    rw [cousinDiamond10Step_eq_d9_of_not_cone11 x hnc11_x]; exact hd9_x
  have hy_step : y = (3 * x + 1) / 128 :=
    hd9_x.symm.trans (by
      rw [cousinDiamond9Step_eq_d8_of_not_cone10 x hnc10_x,
          cousinDiamond8Step_eq_d7_of_not_cone9 x hnc9_x]
      unfold cousinDiamond7Step; simp [hc8])
  clear hc8 hnc11_x hnc10_x hnc9_x hd9_x
  have hc7_y : isDiamond6Cone7 y :=
    isDiamond6Cone7_of_pow2_pow3 (u - 7) (v + 1) (by omega) (by omega)
  rcases cousin_diamond10_cone7_return_aux y hc7_y with ⟨_, _, ky, _, _, _, _, _, hky_le_y, _, hky_1⟩
  have hy_lt_x : y + 1 ≤ x := by
    have hdiv : y * 128 ≤ 3 * x + 1 := by rw [hy_step]; exact Nat.div_mul_le_self (3 * x + 1) 128
    clear hy_step hmul hstep_x hc7_y hky_1; omega
  have h1ky_x : 1 + ky ≤ x := by clear hy_step hmul hstep_x hc7_y hky_1; omega
  have h1ky_phi : 1 + ky ≤ cousinDiamond2Phi x :=
    Nat.le_trans (by clear hy_step hmul hstep_x hc7_y hky_1; omega : 1 + ky ≤ x + 1) (cousinDiamond2Phi_ge_succ x)
  refine ⟨u, v, 1 + ky, hu22, hv1, hmul, hstep_x, ?_, h1ky_x, h1ky_phi, ?_⟩
  · rw [hstep_x]; exact hc7_y
  · rw [cousinDiamond10Iter_add 1 ky x]
    have hi1 : cousinDiamond10Iter 1 x = y := hstep_x
    rw [hi1]; exact hky_1

theorem cousin_diamond10_cone9_return_aux (x : Nat) (hc9 : isDiamond8Cone9 x) :
    ∃ (w z k : Nat),
      w ≥ 25 ∧ z ≥ 1 ∧ x + 92275 = 2 ^ w * 3 ^ z ∧
      cousinDiamond10Step x = 2 ^ (w - 3) * 3 ^ (z + 1) - 34603 ∧
      isDiamond7Cone8 (cousinDiamond10Step x) ∧
      k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond10Iter k x = 1 := by
  have hnc11_x : ¬ isDiamond10Cone11 x :=
    not_cone11_of_mod256_ne_205 x (by rw [mod256_of_cone9 x hc9]; decide)
  have hnc10_x : ¬ isDiamond9Cone10 x :=
    not_cone10_of_mod256_ne_205 x (by rw [mod256_of_cone9 x hc9]; decide)
  have hx_ge : x ≥ 100571021 := hc9.1
  rcases (cousin_diamond9_cones4to10_exact_return.2.2.2.2.2.1 x hc9) with
    ⟨w, z, _, hw25, hz1, hmul, hd9_x, _, _, _, _⟩
  let y := 2 ^ (w - 3) * 3 ^ (z + 1) - 34603
  have hstep_x : cousinDiamond10Step x = y := by
    rw [cousinDiamond10Step_eq_d9_of_not_cone11 x hnc11_x]; exact hd9_x
  have hy_step : y = (3 * x + 1) / 8 :=
    hd9_x.symm.trans (by
      rw [cousinDiamond9Step_eq_d8_of_not_cone10 x hnc10_x]
      unfold cousinDiamond8Step; simp [hc9])
  clear hc9 hnc11_x hnc10_x hd9_x
  have hc8_y : isDiamond7Cone8 y :=
    isDiamond7Cone8_of_pow2_pow3 (w - 3) (z + 1) (by omega) (by omega)
  rcases cousin_diamond10_cone8_return_aux y hc8_y with ⟨_, _, ky, _, _, _, _, _, hky_le_y, _, hky_1⟩
  have hy_lt_x : y + 1 ≤ x := by
    have hdiv : y * 8 ≤ 3 * x + 1 := by rw [hy_step]; exact Nat.div_mul_le_self (3 * x + 1) 8
    clear hy_step hmul hstep_x hc8_y hky_1; omega
  have h1ky_x : 1 + ky ≤ x := by clear hy_step hmul hstep_x hc8_y hky_1; omega
  have h1ky_phi : 1 + ky ≤ cousinDiamond2Phi x :=
    Nat.le_trans (by clear hy_step hmul hstep_x hc8_y hky_1; omega : 1 + ky ≤ x + 1) (cousinDiamond2Phi_ge_succ x)
  refine ⟨w, z, 1 + ky, hw25, hz1, hmul, hstep_x, ?_, h1ky_x, h1ky_phi, ?_⟩
  · rw [hstep_x]; exact hc8_y
  · rw [cousinDiamond10Iter_add 1 ky x]
    have hi1 : cousinDiamond10Iter 1 x = y := hstep_x
    rw [hi1]; exact hky_1

theorem cousin_diamond10_cone10_return_aux (x : Nat) (hc10 : isDiamond9Cone10 x) :
    ∃ (p q k : Nat),
      p ≥ 28 ∧ q ≥ 1 ∧ x + 246067 = 2 ^ p * 3 ^ q ∧
      cousinDiamond10Step x = 2 ^ (p - 3) * 3 ^ (q + 1) - 92275 ∧
      isDiamond8Cone9 (cousinDiamond10Step x) ∧
      k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond10Iter k x = 1 := by
  have hnc11_x : ¬ isDiamond10Cone11 x :=
    not_cone11_of_mod268m_ne x (by rw [hc10.2.1]; decide)
  have hx_ge : x ≥ 805060301 := hc10.1
  rcases (cousin_diamond9_cones4to10_exact_return.2.2.2.2.2.2 x hc10) with
    ⟨p, q, _, hp28, hq1, hmul, hd9_x, _, _, _, _⟩
  let y := 2 ^ (p - 3) * 3 ^ (q + 1) - 92275
  have hstep_x : cousinDiamond10Step x = y := by
    rw [cousinDiamond10Step_eq_d9_of_not_cone11 x hnc11_x]; exact hd9_x
  have hy_step : y = (3 * x + 1) / 8 :=
    hd9_x.symm.trans (by unfold cousinDiamond9Step; simp [hc10])
  clear hc10 hnc11_x hd9_x
  have hc9_y : isDiamond8Cone9 y :=
    isDiamond8Cone9_of_pow2_pow3 (p - 3) (q + 1) (by omega) (by omega)
  rcases cousin_diamond10_cone9_return_aux y hc9_y with ⟨_, _, ky, _, _, _, _, _, hky_le_y, _, hky_1⟩
  have hy_lt_x : y + 1 ≤ x := by
    have hdiv : y * 8 ≤ 3 * x + 1 := by rw [hy_step]; exact Nat.div_mul_le_self (3 * x + 1) 8
    clear hy_step hmul hstep_x hc9_y hky_1; omega
  have h1ky_x : 1 + ky ≤ x := by clear hy_step hmul hstep_x hc9_y hky_1; omega
  have h1ky_phi : 1 + ky ≤ cousinDiamond2Phi x :=
    Nat.le_trans (by clear hy_step hmul hstep_x hc9_y hky_1; omega : 1 + ky ≤ x + 1) (cousinDiamond2Phi_ge_succ x)
  refine ⟨p, q, 1 + ky, hp28, hq1, hmul, hstep_x, ?_, h1ky_x, h1ky_phi, ?_⟩
  · rw [hstep_x]; exact hc9_y
  · rw [cousinDiamond10Iter_add 1 ky x]
    have hi1 : cousinDiamond10Iter 1 x = y := hstep_x
    rw [hi1]; exact hky_1

/--
  Theorem W13.3g (`cousin_diamond10_cones4to11_exact_return`, `zero custom axioms`):
  Exact 8-Tier `ω^8` Multi-Block Return Across Cones 4, 5, 6, 7, 8, 9, 10, AND 11 of `T_diamond10`:
  1–7. Every `x` in Cone 4, 5, 6, 7, 8, 9, or 10 reaches `1` in `k ≤ cousinDiamond2Phi x` steps!
  8. Every `x` in Cone 11 (`isDiamond10Cone11 x`) has `x + 656179 = 2 ^ r * 3 ^ s` (`r ≥ 31, s ≥ 1`),
     steps in 1 genuine `v_2(3x + 1) = 3` jump `(3 * x + 1) / 8` directly into the Cone-10 state
     `y = 2 ^ (r - 3) * 3 ^ (s + 1) - 246067`, and reaches `1` in `1 + k_y ≤ x` (`≤ cousinDiamond2Phi x`) steps!
-/
theorem cousin_diamond10_cones4to11_exact_return :
    (∀ x : Nat, isDiamond3Cone4 x ->
      ∃ k : Nat, k ≤ cousinDiamond2Phi x ∧ cousinDiamond10Iter k x = 1) ∧
    (∀ x : Nat, isDiamond4Cone5 x ->
      ∃ (a b k : Nat),
        a ≥ 5 ∧ b ≥ 1 ∧ x + 7 = 2 ^ a * 3 ^ b ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond10Iter k x = 1) ∧
    (∀ x : Nat, isDiamond5Cone6 x ->
      ∃ (e f k : Nat),
        e ≥ 8 ∧ f ≥ 2 ∧ x + 19 = 2 ^ e * 3 ^ f ∧
        cousinDiamond10Step x = 2 ^ (e - 3) * 3 ^ (f + 1) - 7 ∧
        isDiamond4Cone5 (cousinDiamond10Step x) ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond10Iter k x = 1) ∧
    (∀ x : Nat, isDiamond6Cone7 x ->
      ∃ (g h k : Nat),
        g ≥ 15 ∧ h ≥ 2 ∧ x + 811 = 2 ^ g * 3 ^ h ∧
        cousinDiamond10Step x = 2 ^ (g - 7) * 3 ^ (h + 1) - 19 ∧
        isDiamond5Cone6 (cousinDiamond10Step x) ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond10Iter k x = 1) ∧
    (∀ x : Nat, isDiamond7Cone8 x ->
      ∃ (u v k : Nat),
        u ≥ 22 ∧ v ≥ 1 ∧ x + 34603 = 2 ^ u * 3 ^ v ∧
        cousinDiamond10Step x = 2 ^ (u - 7) * 3 ^ (v + 1) - 811 ∧
        isDiamond6Cone7 (cousinDiamond10Step x) ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond10Iter k x = 1) ∧
    (∀ x : Nat, isDiamond8Cone9 x ->
      ∃ (w z k : Nat),
        w ≥ 25 ∧ z ≥ 1 ∧ x + 92275 = 2 ^ w * 3 ^ z ∧
        cousinDiamond10Step x = 2 ^ (w - 3) * 3 ^ (z + 1) - 34603 ∧
        isDiamond7Cone8 (cousinDiamond10Step x) ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond10Iter k x = 1) ∧
    (∀ x : Nat, isDiamond9Cone10 x ->
      ∃ (p q k : Nat),
        p ≥ 28 ∧ q ≥ 1 ∧ x + 246067 = 2 ^ p * 3 ^ q ∧
        cousinDiamond10Step x = 2 ^ (p - 3) * 3 ^ (q + 1) - 92275 ∧
        isDiamond8Cone9 (cousinDiamond10Step x) ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond10Iter k x = 1) ∧
    (∀ x : Nat, isDiamond10Cone11 x ->
      ∃ (r s k : Nat),
        r ≥ 31 ∧ s ≥ 1 ∧ x + 656179 = 2 ^ r * 3 ^ s ∧
        cousinDiamond10Step x = 2 ^ (r - 3) * 3 ^ (s + 1) - 246067 ∧
        isDiamond9Cone10 (cousinDiamond10Step x) ∧
        k ≤ x ∧ k ≤ cousinDiamond2Phi x ∧ cousinDiamond10Iter k x = 1) := by
  refine ⟨cousin_diamond10_cone4_return_aux,
          cousin_diamond10_cone5_return_aux,
          cousin_diamond10_cone6_return_aux,
          cousin_diamond10_cone7_return_aux,
          cousin_diamond10_cone8_return_aux,
          cousin_diamond10_cone9_return_aux,
          cousin_diamond10_cone10_return_aux, ?_⟩
  intro x hc11
  have hraw_step : cousinDiamond10Step x = (3 * x + 1) / 8 := by
    unfold cousinDiamond10Step; simp only [hc11, ite_true]
  rcases hc11 with ⟨hx_ge, hx2b, hx3, hg1⟩
  have hdvd2b : 2147483648 ∣ (x + 656179) :=
    Nat.dvd_of_mod_eq_zero (by rw [Nat.add_mod, hx2b])
  clear hx2b
  rcases (⟨656179 + x, rfl⟩ : ∃ N : Nat, N = 656179 + x) with ⟨N, hN_def⟩
  rw [← hN_def] at hg1
  have hN_pos : N > 0 := by clear hraw_step hdvd2b hx3 hg1; omega
  rcases decomp_2_3_exact N hN_pos with ⟨_, _, _, _, _, hmul⟩
  rw [hg1, Nat.mul_one] at hmul
  rcases eq_pow2_of_v2Pow_aux N N hN_pos (Nat.le_refl _) with ⟨r, hr⟩
  rcases eq_pow3_of_v3Pow_aux N N hN_pos (Nat.le_refl _) with ⟨s, hs⟩
  rw [hr, hs] at hmul
  have hmul_comm : x + 656179 = 2 ^ r * 3 ^ s := by
    rw [Nat.add_comm x 656179, ← hN_def, ← hmul]
  clear hg1 hr hs hN_def hmul hN_pos
  have hr31 : r ≥ 31 := by
    by_cases hlt : r < 31
    · exfalso
      have h2b_sp : 2147483648 = 2 ^ (r + 1) * 2 ^ (30 - r) := by
        have hsum31 : r + 1 + (30 - r) = 31 := by clear hraw_step hx_ge hx3 hdvd2b hmul_comm; omega
        rw [← Nat.pow_add 2 (r + 1) (30 - r), hsum31]
      rcases hdvd2b with ⟨c, hc⟩
      rw [hmul_comm, h2b_sp, Nat.mul_assoc (2 ^ (r + 1)),
          Nat.pow_succ 2 r, Nat.mul_assoc (2 ^ r) 2] at hc
      have h3s_ev : 3 ^ s = 2 * (2 ^ (30 - r) * c) :=
        nat_mul_left_cancel_pos (2 ^ r) _ _ (pow2_pos_nat r) hc
      have ho := pow3_odd_nat_sec8 s
      rw [h3s_ev, Nat.mul_mod_right] at ho
      cases ho
    · clear hraw_step hx_ge hx3 hdvd2b hmul_comm; omega
  clear hdvd2b
  have hs1 : s ≥ 1 := by
    cases s with
    | zero =>
      rw [Nat.pow_zero, Nat.mul_one] at hmul_comm
      exact False.elim (pow2_mod3_nonzero_w5 r (by rw [← hmul_comm, Nat.add_mod, hx3]))
    | succ _ => clear hraw_step hx_ge hx3 hmul_comm hr31; omega
  clear hx3
  let y := 2 ^ (r - 3) * 3 ^ (s + 1) - 246067
  have hstep_x : cousinDiamond10Step x = y := by
    rw [hraw_step]
    dsimp only [y]
    have hp8 : 2 ^ r = 8 * 2 ^ (r - 3) := by
      have hr_sp : r = 3 + (r - 3) := by clear hraw_step hx_ge hmul_comm hs1; omega
      conv => lhs; rw [hr_sp]; rw [Nat.pow_add]
    have hprod_pos : 2 ^ (r - 3) * 3 ^ s ≥ 268435456 * 3 := by
      have h1 : 268435456 ≤ 2 ^ (r - 3) := by
        have hc : (2 : Nat) ^ 28 = 268435456 := by decide
        have h28 : 28 ≤ r - 3 := by clear hraw_step hx_ge hmul_comm hs1 hp8; omega
        rw [← hc]; exact pow2_mono_nat h28
      have h2 : 3 ≤ 3 ^ s := by simpa using nat_pow_mono_exp_pos 3 1 s (by decide) hs1
      simpa using Nat.mul_le_mul h1 h2
    have h3_eq : 2 ^ (r - 3) * 3 ^ (s + 1) = 3 * (2 ^ (r - 3) * 3 ^ s) := by
      rw [Nat.pow_succ 3 s, ← Nat.mul_assoc, Nat.mul_comm _ 3]
    rw [h3_eq]
    have hx8 : x + 656179 = 8 * (2 ^ (r - 3) * 3 ^ s) := by
      rw [hmul_comm, hp8, Nat.mul_assoc]
    have h3x1 : 3 * x + 1 = (3 * (2 ^ (r - 3) * 3 ^ s) - 246067) * 8 := by
      clear hraw_step hr31 hs1 hp8 h3_eq hmul_comm
      generalize 2 ^ (r - 3) * 3 ^ s = A at hprod_pos hx8 ⊢
      omega
    rw [h3x1]
    exact Nat.mul_div_left _ (by decide : 0 < 8)
  have hc10_y : isDiamond9Cone10 y :=
    isDiamond9Cone10_of_pow2_pow3 (r - 3) (s + 1)
      (by clear hraw_step hx_ge hmul_comm hstep_x; omega)
      (by clear hraw_step hx_ge hmul_comm hstep_x; omega)
  rcases cousin_diamond10_cone10_return_aux y hc10_y with ⟨_, _, ky, _, _, _, _, _, hky_le_y, _, hky_1⟩
  have hy_lt_x : y + 1 ≤ x := by
    have hstep_eq : y = (3 * x + 1) / 8 := hstep_x.symm.trans hraw_step
    have hdiv : y * 8 ≤ 3 * x + 1 := by rw [hstep_eq]; exact Nat.div_mul_le_self (3 * x + 1) 8
    clear hraw_step hmul_comm hstep_x hc10_y hky_1 hstep_eq
    omega
  have h1ky_x : 1 + ky ≤ x := by clear hraw_step hmul_comm hstep_x hc10_y hky_1; omega
  have h1ky_phi : 1 + ky ≤ cousinDiamond2Phi x :=
    Nat.le_trans (by clear hraw_step hmul_comm hstep_x hc10_y hky_1; omega : 1 + ky ≤ x + 1)
      (cousinDiamond2Phi_ge_succ x)
  refine ⟨r, s, 1 + ky, hr31, hs1, hmul_comm, hstep_x, ?_, h1ky_x, h1ky_phi, ?_⟩
  · rw [hstep_x]; exact hc10_y
  · rw [cousinDiamond10Iter_add 1 ky x]
    have hi1 : cousinDiamond10Iter 1 x = y := hstep_x
    rw [hi1]; exact hky_1

theorem cousin_diamond10_reaches_one_within_phi :
    ∀ (B x : Nat), x > 0 -> cousinDiamond2Phi x ≤ B ->
      ∃ k : Nat, k ≤ B ∧ cousinDiamond10Iter k x = 1
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
        · rcases cousin_diamond10_cones4to11_exact_return.1 x hc4 with ⟨k, hle_phi, hk1⟩
          exact ⟨k, Nat.le_trans hle_phi hB, hk1⟩
        · by_cases hc5 : isDiamond4Cone5 x
          · rcases cousin_diamond10_cones4to11_exact_return.2.1 x hc5 with
              ⟨_, _, k, _, _, _, _, hle_phi, hk1⟩
            exact ⟨k, Nat.le_trans hle_phi hB, hk1⟩
          · by_cases hc6 : isDiamond5Cone6 x
            · rcases cousin_diamond10_cones4to11_exact_return.2.2.1 x hc6 with
                ⟨_, _, k, _, _, _, _, _, _, hle_phi, hk1⟩
              exact ⟨k, Nat.le_trans hle_phi hB, hk1⟩
            · by_cases hc7 : isDiamond6Cone7 x
              · rcases cousin_diamond10_cones4to11_exact_return.2.2.2.1 x hc7 with
                  ⟨_, _, k, _, _, _, _, _, _, hle_phi, hk1⟩
                exact ⟨k, Nat.le_trans hle_phi hB, hk1⟩
              · by_cases hc8 : isDiamond7Cone8 x
                · rcases cousin_diamond10_cones4to11_exact_return.2.2.2.2.1 x hc8 with
                    ⟨_, _, k, _, _, _, _, _, _, hle_phi, hk1⟩
                  exact ⟨k, Nat.le_trans hle_phi hB, hk1⟩
                · by_cases hc9 : isDiamond8Cone9 x
                  · rcases cousin_diamond10_cones4to11_exact_return.2.2.2.2.2.1 x hc9 with
                      ⟨_, _, k, _, _, _, _, _, _, hle_phi, hk1⟩
                    exact ⟨k, Nat.le_trans hle_phi hB, hk1⟩
                  · by_cases hc10 : isDiamond9Cone10 x
                    · rcases cousin_diamond10_cones4to11_exact_return.2.2.2.2.2.2.1 x hc10 with
                        ⟨_, _, k, _, _, _, _, _, _, hle_phi, hk1⟩
                      exact ⟨k, Nat.le_trans hle_phi hB, hk1⟩
                    · by_cases hc11 : isDiamond10Cone11 x
                      · rcases cousin_diamond10_cones4to11_exact_return.2.2.2.2.2.2.2 x hc11 with
                          ⟨_, _, k, _, _, _, _, _, _, hle_phi, hk1⟩
                        exact ⟨k, Nat.le_trans hle_phi hB, hk1⟩
                      · have hdesc := cousin_diamond10_outside_cones4to11_strict_descent x
                          (by omega) hc4 hc5 hc6 hc7 hc8 hc9 hc10 hc11
                        have hpos := cousinDiamond10Step_pos x hx
                        rcases cousin_diamond10_reaches_one_within_phi B (cousinDiamond10Step x) hpos (by omega) with
                          ⟨k, hk_le, hk_eq⟩
                        exact ⟨k + 1, by omega, hk_eq⟩

/--
  Theorem W13.3h (`cousin_diamond10_global_convergence`, `zero custom axioms`):
  Unconditional Global Convergence & Degree-5 Polynomial Stopping Bound for `T_diamond10`:
  For EVERY `x > 0`, `cousinDiamond10Iter` reaches `1` within `k ≤ (x + 1) ^ 3 + (x + 1) ^ 5` steps!
-/
theorem cousin_diamond10_global_convergence (x : Nat) (hx : x > 0) :
    ∃ k : Nat, k ≤ (x + 1) ^ 3 + (x + 1) ^ 5 ∧ cousinDiamond10Iter k x = 1 := by
  rcases cousin_diamond10_reaches_one_within_phi (cousinDiamond2Phi x) x hx (Nat.le_refl _) with
    ⟨k, hk_phi, hk1⟩
  exact ⟨k, Nat.le_trans hk_phi (cousinDiamond2Phi_upper_poly_bound x), hk1⟩

theorem exists_non_desc_along_diamond10_iter_clean :
    ∀ (terms : List LaurentTerm) (A0 B0 C0 N z : Nat),
      N ≥ 1 ->
      (∀ i : Nat, i < N ->
        cousinDiamond10Iter i z ≥ 3 ∧
        (cousinDiamond10Iter i z) % 2 = 1 ∧
        cousinDiamond10Step (cousinDiamond10Iter i z) ≥ 3) ->
      ¬ laurentDescProp terms A0 B0 C0 z (cousinDiamond10Iter N z) ->
      ∃ x : Nat,
        x ≥ 3 ∧ x % 2 = 1 ∧ cousinDiamond10Step x ≥ 3 ∧
        ¬ laurentDescProp terms A0 B0 C0 x (cousinDiamond10Step x)
  | _, _, _, _, 0, _, hN, _, _ => by omega
  | _, _, _, _, 1, z, _, hall, hnd => by
    rcases hall 0 (by decide) with ⟨hz3, hzo, hsz3⟩
    exact ⟨z, hz3, hzo, hsz3, hnd⟩
  | terms, A0, B0, C0, m + 2, z, _, hall, hnd => by
    if h0 : laurentDescProp terms A0 B0 C0 z (cousinDiamond10Step z) then
      have hnd_next : ¬ laurentDescProp terms A0 B0 C0 (cousinDiamond10Step z)
          (cousinDiamond10Iter (m + 1) (cousinDiamond10Step z)) :=
        fun hrest => hnd (laurentDescProp_trans terms A0 B0 C0 z (cousinDiamond10Step z) _ h0 hrest)
      exact exists_non_desc_along_diamond10_iter_clean terms A0 B0 C0 (m + 1) (cousinDiamond10Step z)
        (by omega) (fun i hi => hall (i + 1) (by omega)) hnd_next
    else
      rcases hall 0 (by omega) with ⟨hz3, hzo, hsz3⟩
      exact ⟨z, hz3, hzo, hsz3, h0⟩

/--
  Theorem W13.3i (`cousin_diamond10_r_block_spiral_climb_and_laurent_impossibility`,
  `zero custom axioms`):
  1. Cone-11 -> Cone-10 -> Cone-9 -> Cone-8 -> Cone-7 -> Cone-6 -> Cone-5 8-Tier Cascade & Unbounded `r`-Block Spiral Climb:
     `25769147597 -> 9663430349 -> 3623786381 -> 1358919893 -> 31849685 -> 746477 -> 279929` AND
     `cousinDiamond10Iter (2 * j) (4 * 16 ^ r - 5) = 4 * 16 ^ (r - j) * 18 ^ j - 5` for ALL `r ≥ 1, j ≤ r`!
  2. Universal `∀ L ≥ 1` Multi-Term Laurent Valuation Impossibility on `cousinDiamond10Step`!
-/
theorem cousin_diamond10_r_block_spiral_climb_and_laurent_impossibility :
    cousinDiamond10Step 25769147597 = 9663430349 ∧
    cousinDiamond10Step 9663430349 = 3623786381 ∧
    cousinDiamond10Step 3623786381 = 1358919893 ∧
    cousinDiamond10Step 1358919893 = 31849685 ∧
    cousinDiamond10Step 31849685 = 746477 ∧
    cousinDiamond10Step 746477 = 279929 ∧
    (∀ (r j : Nat), r ≥ 1 -> j ≤ r ->
      cousinDiamond10Iter (2 * j) (4 * 16 ^ r - 5) = 4 * 16 ^ (r - j) * 18 ^ j - 5) ∧
    (∀ (terms : List LaurentTerm) (A0 B0 C0 : Nat),
      (∃ t ∈ terms, t.coeff > 0) ->
      ∃ x : Nat,
        x ≥ 3 ∧ x % 2 = 1 ∧ cousinDiamond10Step x ≥ 3 ∧
        ¬ (evalLaurentSumNum terms (cousinDiamond10Step x) * laurentValDen A0 B0 C0 x <
            evalLaurentSumNum terms x * laurentValDen A0 B0 C0 (cousinDiamond10Step x))) := by
  have hspiral : ∀ (r j : Nat), r ≥ 1 -> j ≤ r ->
      cousinDiamond10Iter (2 * j) (4 * 16 ^ r - 5) = 4 * 16 ^ (r - j) * 18 ^ j - 5 := by
    intro r j hr hj
    cases j with
    | zero => simp [cousinDiamond10Iter]
    | succ j' =>
      have hp16_ge16 : 16 ^ r ≥ 16 := by
        rw [show r = (r - 1) + 1 by omega, Nat.pow_succ]
        have hp := nat_pow_pos_of_pos 16 (by decide) (r - 1); omega
      let x0 := 4 * 16 ^ r - 5
      have hx0_m4 : x0 % 4 = 3 := by dsimp only [x0]; omega
      have hx0_pow : 4 * 16 ^ r = 2 ^ (4 * r + 2) := by
        have h16 : 16 ^ r = 2 ^ (4 * r) := by
          rw [show (16 : Nat) = 2 ^ 4 from rfl, pow_pow_eq_mul_w5 2 4 r]
        rw [h16, show (4 : Nat) = 2 ^ 2 from rfl, ← Nat.pow_add 2 2 (4 * r), Nat.add_comm 2 (4 * r)]
      have hs_first : cousinDiamond10Step x0 = 2 ^ (4 * r + 1) * 3 ^ 1 - 7 := by
        rw [cousinDiamond10Step_eq_d9_of_not_cone11 x0 (not_cone11_of_mod4_eq_3 x0 hx0_m4),
            cousinDiamond9Step_eq_d8_of_not_cone10 x0 (not_cone10_of_mod4_eq_3 x0 hx0_m4),
            cousinDiamond8Step_eq_d7_of_not_cone9 x0 (not_cone9_of_mod4_eq_3 x0 hx0_m4),
            cousinDiamond7Step_eq_d6_of_not_cone8 x0 (not_cone8_of_mod4_eq_3 x0 hx0_m4),
            cousinDiamond6Step_eq_d5_of_not_cone7 x0 (not_cone7_of_mod4_eq_3 x0 hx0_m4),
            cousinDiamond5Step_eq_d4_of_not_cone6 x0 (not_cone6_of_mod4_eq_3 x0 hx0_m4),
            cousinDiamond4Step_mod4_eq_3 x0 hx0_m4]
        dsimp only [x0]
        rw [hx0_pow, show 4 * r + 2 = (4 * r + 1) + 1 by omega, Nat.pow_succ 2 (4 * r + 1)]
        have hp := pow2_pos_nat (4 * r + 1); omega
      have hclimb := cousin_diamond10_cone5_two_step_climb j' (4 * r + 1) 1 (by omega) (by decide)
      let y_end := 2 ^ (4 * r + 1 - 3 * j') * 3 ^ (1 + 2 * j') - 7
      have hy_c5 : isDiamond4Cone5 y_end :=
        isDiamond4Cone5_of_pow2_pow3 (4 * r + 1 - 3 * j') (1 + 2 * j') (by omega) (by omega)
      have hy_nc11 : ¬ isDiamond10Cone11 y_end :=
        not_cone11_of_mod32_ne_13 y_end (by have h := hy_c5.2.1; omega)
      have hy_nc10 : ¬ isDiamond9Cone10 y_end :=
        not_cone10_of_mod32_ne_13 y_end (by have h := hy_c5.2.1; omega)
      have hy_nc9 : ¬ isDiamond8Cone9 y_end :=
        not_cone9_of_mod32_ne_13 y_end (by have h := hy_c5.2.1; omega)
      have hy_nc8 : ¬ isDiamond7Cone8 y_end :=
        not_cone8_of_mod32_ne_21 y_end (by have h := hy_c5.2.1; omega)
      have hy_nc7 : ¬ isDiamond6Cone7 y_end :=
        not_cone7_of_mod32_ne_21 y_end (by have h := hy_c5.2.1; omega)
      have hy_nc6 : ¬ isDiamond5Cone6 y_end :=
        not_cone6_of_mod32_ne_13 y_end (by have h := hy_c5.2.1; omega)
      have hs_last : cousinDiamond10Step y_end = 4 * 16 ^ (r - (j' + 1)) * 18 ^ (j' + 1) - 5 := by
        rw [cousinDiamond10Step_eq_d9_of_not_cone11 y_end hy_nc11,
            cousinDiamond9Step_eq_d8_of_not_cone10 y_end hy_nc10,
            cousinDiamond8Step_eq_d7_of_not_cone9 y_end hy_nc9,
            cousinDiamond7Step_eq_d6_of_not_cone8 y_end hy_nc8,
            cousinDiamond6Step_eq_d5_of_not_cone7 y_end hy_nc7,
            cousinDiamond5Step_eq_d4_of_not_cone6 y_end hy_nc6]
        unfold cousinDiamond4Step; simp only [hy_c5, ite_true]
        dsimp only [y_end]
        have ha_sp : 4 * r + 1 - 3 * j' = 2 + (4 * (r - (j' + 1)) + (j' + 1) + 2) := by omega
        have hp2_sp : 2 ^ (4 * r + 1 - 3 * j') = 4 * (4 * 2 ^ (4 * (r - (j' + 1))) * 2 ^ (j' + 1)) := by
          rw [ha_sp, Nat.pow_add 2 2, Nat.pow_add 2 (4 * (r - (j' + 1)) + (j' + 1)) 2,
              Nat.pow_add 2 (4 * (r - (j' + 1))) (j' + 1)]
          change 4 * (2 ^ (4 * (r - (j' + 1))) * 2 ^ (j' + 1) * 4) = _
          ac_rfl
        have h16_rj : 2 ^ (4 * (r - (j' + 1))) = 16 ^ (r - (j' + 1)) := by
          rw [show (16 : Nat) = 2 ^ 4 from rfl, pow_pow_eq_mul_w5 2 4]
        have h18_j : 2 ^ (j' + 1) * 3 ^ (2 * (j' + 1)) = 18 ^ (j' + 1) := by
          rw [← pow9_eq_pow3_double (j' + 1), ← mul_pow_w13s 2 9 (j' + 1)]
        have hp3_sp : 3 * 3 ^ (1 + 2 * j') = 3 ^ (2 * (j' + 1)) := by
          rw [show 2 * (j' + 1) = (1 + 2 * j') + 1 by omega, Nat.pow_succ, Nat.mul_comm]
        have hprod_eq : 3 * (2 ^ (4 * r + 1 - 3 * j') * 3 ^ (1 + 2 * j')) =
            4 * (4 * 16 ^ (r - (j' + 1)) * 18 ^ (j' + 1)) := by
          calc
            3 * (2 ^ (4 * r + 1 - 3 * j') * 3 ^ (1 + 2 * j'))
                = 2 ^ (4 * r + 1 - 3 * j') * (3 * 3 ^ (1 + 2 * j')) := by ac_rfl
            _ = 4 * (4 * 16 ^ (r - (j' + 1)) * 2 ^ (j' + 1)) * 3 ^ (2 * (j' + 1)) := by
                  rw [hp2_sp, h16_rj, hp3_sp]
            _ = 4 * (4 * 16 ^ (r - (j' + 1)) * 18 ^ (j' + 1)) := by
                  rw [Nat.mul_assoc 4, Nat.mul_assoc (4 * 16 ^ (r - (j' + 1))), h18_j]
        have hpos_ge : 4 * 16 ^ (r - (j' + 1)) * 18 ^ (j' + 1) ≥ 72 := by
          have h1 : 1 ≤ 16 ^ (r - (j' + 1)) := nat_pow_pos_of_pos 16 (by decide) _
          have h2 : 18 ≤ 18 ^ (j' + 1) := by
            rw [Nat.pow_succ]; have hp := nat_pow_pos_of_pos 18 (by decide) j'; omega
          simpa using Nat.mul_le_mul (Nat.mul_le_mul (Nat.le_refl 4) h1) h2
        omega
      rw [show 2 * (j' + 1) = 1 + 2 * j' + 1 by omega,
          cousinDiamond10Iter_add (1 + 2 * j') 1,
          cousinDiamond10Iter_add 1 (2 * j')]
      have hi1 : cousinDiamond10Iter 1 x0 = 2 ^ (4 * r + 1) * 3 ^ 1 - 7 := hs_first
      rw [hi1, hclimb]
      exact hs_last
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, hspiral, ?_⟩
  intro terms A0 B0 C0 hnonempty
  rcases three_family_multiterm_laurent_obstruction terms A0 B0 C0 hnonempty with
    h97 | ⟨j2, hj2⟩ | ⟨r, hr_pos, hr3⟩
  · have hs97 : cousinDiamond10Step 97 = 73 := by decide
    refine ⟨97, by decide, by decide, by rw [hs97]; decide, ?_⟩
    rw [hs97]; exact h97
  · let zj := geomSpineEntry j2
    let Mj := 4 ^ (3 * j2 + 3)
    rcases geomSpineEntry_valuations_constant j2 with ⟨h3zj1, hzj_ge, _, _, _, _⟩
    change 3 * zj + 1 = 4 ^ (3 * j2 + 4) at h3zj1
    change zj ≥ 85 at hzj_ge
    have hMj_ge64 : Mj ≥ 64 := by
      dsimp only [Mj]; rw [Nat.pow_add 4 (3 * j2) 3]
      simpa using Nat.mul_le_mul_right 64 (nat_pow_pos_of_pos 4 (by decide) (3 * j2))
    have h3zj1_M : 3 * zj + 1 = 4 * Mj := by
      rw [h3zj1]; dsimp only [Mj]
      rw [show 3 * j2 + 4 = (3 * j2 + 3) + 1 by omega, Nat.pow_succ, Nat.mul_comm]
    let xj2 := 2 * zj - 1
    let yj2 := 2 * Mj - 1
    have hxj2_odd : xj2 % 2 = 1 := by dsimp only [xj2]; omega
    have hc4_xj2 : isDiamond3Cone4 xj2 := by
      refine ⟨by dsimp only [xj2]; omega, by dsimp only [xj2]; omega, ?_⟩
      have hpow2 : 3 * xj2 + 5 = 2 ^ (6 * j2 + 9) * 1 := by
        rw [Nat.mul_one, show 6 * j2 + 9 = 2 * (3 * j2 + 4) + 1 by omega,
            Nat.pow_succ, ← pow4_eq_pow2_even (3 * j2 + 4), Nat.mul_comm]
        dsimp only [xj2]; omega
      rw [hpow2]
      exact core2_pow2_mul (6 * j2 + 9) 1 (by decide) (by decide)
    have hstep_xj2 : cousinDiamond10Step xj2 = yj2 := by
      rw [cousinDiamond10Step_eq_d9_of_not_cone11 xj2
            (not_cone11_of_mod8_ne_5 xj2 (by have h := hc4_xj2.2.1; omega)),
          cousinDiamond9Step_eq_d8_of_not_cone10 xj2
            (not_cone10_of_mod8_ne_5 xj2 (by have h := hc4_xj2.2.1; omega)),
          cousinDiamond8Step_eq_d7_of_not_cone9 xj2
            (not_cone9_of_mod8_ne_5 xj2 (by have h := hc4_xj2.2.1; omega)),
          cousinDiamond7Step_eq_d6_of_not_cone8 xj2
            (not_cone8_of_mod8_ne_5 xj2 (by have h := hc4_xj2.2.1; omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 xj2
            (not_cone7_of_mod8_ne_5 xj2 (by have h := hc4_xj2.2.1; omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 xj2
            (by rintro ⟨_, h256, _, _⟩; have h := hc4_xj2.2.1; omega)]
      unfold cousinDiamond4Step
      by_cases hc5 : isDiamond4Cone5 xj2
      · simp only [hc5, ite_true]; dsimp only [xj2, yj2]; omega
      · simp only [hc5, ite_false]
        rw [cousinDiamond3Step_of_cone4_w8 xj2 hxj2_odd hc4_xj2]
        dsimp only [xj2, yj2]; omega
    refine ⟨xj2, by dsimp only [xj2]; omega, hxj2_odd, by rw [hstep_xj2]; dsimp only [yj2]; omega, ?_⟩
    rw [hstep_xj2]; exact hj2
  · let xr3 := 2 * 4 ^ r - 1
    let zr := 2 * 9 ^ r - 1
    let yr3 := (3 * 9 ^ r - 1) / 2
    have hp9_ge9 : 9 ^ r ≥ 9 := by
      rw [show r = (r - 1) + 1 by omega, Nat.pow_succ]
      have hp := nat_pow_pos_of_pos 9 (by decide) (r - 1); omega
    have hp9_m8 : 9 ^ r % 8 = 1 := pow9_mod8_eq_one_w5 r
    have hxr3_pow : xr3 = 2 ^ (2 * r + 1) * 1 - 1 := by
      dsimp only [xr3]; rw [Nat.mul_one, pow4_eq_pow2_even r, Nat.pow_succ, Nat.mul_comm]
    have hglide_i : ∀ i : Nat, i ≤ 2 * r ->
        cousinDiamond10Iter i xr3 = 3 ^ i * 2 ^ (2 * r + 1 - i) - 1 ∧
        cousinDiamond10Iter i xr3 ≥ 7 ∧
        (cousinDiamond10Iter i xr3) % 2 = 1 := by
      intro i hi
      have hf := cousin_diamond10_mersenne_scaled i (2 * r + 1) 1 (by omega) (by decide)
      rw [← hxr3_pow, Nat.mul_one] at hf
      have hprod_ge8 : 3 ^ i * 2 ^ (2 * r + 1 - i) ≥ 8 := by
        have h1 : 2 ^ i * 2 ^ (2 * r + 1 - i) ≤ 3 ^ i * 2 ^ (2 * r + 1 - i) :=
          Nat.mul_le_mul_right _ (pow2_le_pow3 i)
        rw [← Nat.pow_add, show i + (2 * r + 1 - i) = 2 * r + 1 by omega] at h1
        exact Nat.le_trans (pow2_mono_nat (by omega : 3 ≤ 2 * r + 1)) h1
      have hprod_ev : (3 ^ i * 2 ^ (2 * r + 1 - i)) % 2 = 0 := by
        rw [show 2 * r + 1 - i = (2 * r - i) + 1 by omega, Nat.pow_succ, ← Nat.mul_assoc]; omega
      exact ⟨hf, by rw [hf]; omega, by rw [hf]; omega⟩
    have hiter_2r : cousinDiamond10Iter (2 * r) xr3 = zr := by
      have hf := (hglide_i (2 * r) (Nat.le_refl _)).1
      rw [hf, show 2 * r + 1 - 2 * r = 1 by omega, Nat.pow_one,
          ← pow9_eq_pow3_double r, Nat.mul_comm]
    have hstep_zr : cousinDiamond10Step zr = yr3 := by
      rw [cousinDiamond10Step_eq_d9_of_not_cone11 zr (not_cone11_of_mod8_ne_5 zr (by dsimp only [zr]; omega)),
          cousinDiamond9Step_eq_d8_of_not_cone10 zr (not_cone10_of_mod8_ne_5 zr (by dsimp only [zr]; omega)),
          cousinDiamond8Step_eq_d7_of_not_cone9 zr (not_cone9_of_mod8_ne_5 zr (by dsimp only [zr]; omega)),
          cousinDiamond7Step_eq_d6_of_not_cone8 zr (not_cone8_of_mod8_ne_5 zr (by dsimp only [zr]; omega)),
          cousinDiamond6Step_eq_d5_of_not_cone7 zr (not_cone7_of_mod8_ne_5 zr (by dsimp only [zr]; omega)),
          cousinDiamond5Step_eq_d4_of_not_cone6 zr (not_cone6_of_mod16_ne_13 zr (by dsimp only [zr]; omega))]
      have hnc5 : ¬ isDiamond4Cone5 zr := by rintro ⟨_, h32, _, _⟩; dsimp only [zr] at h32; omega
      rw [cousinDiamond4Step_eq_d3_of_not_cone5 zr hnc5]
      have hc3 : core3 (zr + 1) = 2 := by
        rw [show zr + 1 = 2 * 9 ^ r by dsimp only [zr]; omega,
            core3_mul2 (9 ^ r) (by omega), (pow9_eq_v3Pow_w5 r).2]
      rw [cousinDiamond3Step_of_core3_succ_two_w8 zr (by dsimp only [zr]; omega) (by dsimp only [zr]; omega) hc3]
      dsimp only [zr, yr3]; omega
    have hiter_2r1 : cousinDiamond10Iter (2 * r + 1) xr3 = yr3 := by
      rw [cousinDiamond10Iter_add (2 * r) 1 xr3, hiter_2r]; exact hstep_zr
    have hall : ∀ i : Nat, i < 2 * r + 1 ->
        cousinDiamond10Iter i xr3 ≥ 3 ∧
        (cousinDiamond10Iter i xr3) % 2 = 1 ∧
        cousinDiamond10Step (cousinDiamond10Iter i xr3) ≥ 3 := by
      intro i hi
      by_cases hlt : i < 2 * r
      · rcases hglide_i i (by omega) with ⟨_, hge7, hodd_i⟩
        have hnext : cousinDiamond10Step (cousinDiamond10Iter i xr3) =
            cousinDiamond10Iter (i + 1) xr3 :=
          (cousinDiamond10Iter_add i 1 xr3).symm
        rcases hglide_i (i + 1) (by omega) with ⟨_, hge7_n, _⟩
        exact ⟨by omega, hodd_i, by rw [hnext]; omega⟩
      · have hi_eq : i = 2 * r := by omega
        rw [hi_eq, hiter_2r, hstep_zr]
        exact ⟨by dsimp only [zr]; omega, by dsimp only [zr]; omega, by dsimp only [yr3]; omega⟩
    change ¬ laurentDescProp terms A0 B0 C0 xr3 yr3 at hr3
    rw [← hiter_2r1] at hr3
    exact exists_non_desc_along_diamond10_iter_clean terms A0 B0 C0 (2 * r + 1) xr3 (by omega) hall hr3

/--
  Theorem W13.3j (`cousin_diamond10_q6_noninteger_avoids_cone11`, choice-free `zero custom axioms`):
  Universal Non-Integer Rational Exclusion from Cone 11 on `M1 = Q_(6)^+`:
  For EVERY reduced non-integer rational `(num, den)` (`Nat.gcd num den = 1` and `den > 1`),
  `core3 (core2 (656179 * den + num)) ≠ den`, so `cousinDiamond10StepQ6 (num, den)` NEVER enters
  Cone 11 and agrees identically with `cousinDiamond9StepQ6 (num, den)`!
-/
theorem cousin_diamond10_q6_noninteger_avoids_cone11 (num den : Nat)
    (hgcd : Nat.gcd num den = 1) (hden : den > 1) :
    core3 (core2 (656179 * den + num)) ≠ den ∧
    cousinDiamond10StepQ6 (num, den) = cousinDiamond9StepQ6 (num, den) := by
  have hne : core3 (core2 (656179 * den + num)) ≠ den := by
    intro heq
    have hdvd_sum : den ∣ (656179 * den + num) := by
      have hc_dvd : core3 (core2 (656179 * den + num)) ∣ (656179 * den + num) :=
        Nat.dvd_trans (core3Aux_dvd_w8 _ _) (core2Aux_dvd_w8 _ _)
      rwa [heq] at hc_dvd
    rcases hdvd_sum with ⟨k, hk⟩
    have hdvd_num : den ∣ num := ⟨k - 656179, by
      have hge : k ≥ 656179 := by
        by_cases hlt : k < 656179
        · have hm := Nat.mul_le_mul_left den (show k ≤ 656178 by omega); omega
        · omega
      rw [Nat.mul_sub_left_distrib]; omega⟩
    have hdvd_gcd : den ∣ Nat.gcd num den := Nat.dvd_gcd hdvd_num (Nat.dvd_refl den)
    rw [hgcd] at hdvd_gcd
    rcases hdvd_gcd with ⟨c, hc⟩
    cases c with
    | zero => omega
    | succ c' =>
      have hle : den * 1 ≤ den * (c' + 1) := Nat.mul_le_mul_left den (by omega)
      omega
  refine ⟨hne, ?_⟩
  unfold cousinDiamond10StepQ6
  have hcond : ¬ (num ≥ 6441794765 * den ∧ (num * invMod2147483648Odd den) % 2147483648 = 2146827469 ∧
      (num * (den % 3)) % 3 = 2 ∧ core3 (core2 (656179 * den + num)) = den) :=
    fun ⟨_, _, _, hc⟩ => hne hc
  simp only [hcond, ite_false]

private theorem hensel_inv_lift_w13 (M1 M2 S C d i1 : Nat)
    (hM2 : M2 ≥ 2) (hsq : M1 * M1 = M2 * S) (hC : C = 2 * M2 + 2)
    (h1 : (d * i1) % M1 = 1) :
    (d * ((i1 * (C - ((d % M2) * i1) % M2)) % M2)) % M2 = 1 := by
  let x := d * i1
  let r := ((d % M2) * i1) % M2
  have hr_lt : r < M2 := Nat.mod_lt _ (by omega)
  let K := (d / M2) * i1 + ((d % M2) * i1) / M2
  have hx_M2 : x = M2 * K + r := by
    have hd_div : d = M2 * (d / M2) + d % M2 := (Nat.div_add_mod d M2).symm
    have hdr_div : (d % M2) * i1 = M2 * (((d % M2) * i1) / M2) + r :=
      (Nat.div_add_mod ((d % M2) * i1) M2).symm
    calc
      x = (M2 * (d / M2) + d % M2) * i1 := by dsimp only [x]; rw [← hd_div]
      _ = M2 * ((d / M2) * i1) + (d % M2) * i1 := by rw [Nat.add_mul, Nat.mul_assoc]
      _ = M2 * ((d / M2) * i1) + (M2 * (((d % M2) * i1) / M2) + r) := by rw [← hdr_div]
      _ = M2 * K + r := by dsimp only [K]; rw [Nat.mul_add]; omega
  let q1 := x / M1
  have hx_M1 : x = M1 * q1 + 1 := by
    have hdm := (Nat.div_add_mod x M1).symm
    dsimp only [x] at hdm ⊢
    rw [h1] at hdm
    exact hdm
  have hsq_x : (M1 * q1) * (M1 * q1) + 2 * x = x * x + 1 := by
    rw [hx_M1]
    calc
      (M1 * q1) * (M1 * q1) + 2 * (M1 * q1 + 1)
          = (M1 * q1) * (M1 * q1) + (M1 * q1) + (M1 * q1 + 1) + 1 := by omega
      _ = (M1 * q1 + 1) * (M1 * q1 + 1) + 1 := by
            rw [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
  have hmain : x * (C - r) + M2 * (S * (q1 * q1)) = M2 * (x * (2 + K)) + 1 := by
    have hlhs1 : (M1 * q1) * (M1 * q1) = M2 * (S * (q1 * q1)) := by
      calc
        (M1 * q1) * (M1 * q1) = (M1 * M1) * (q1 * q1) := by ac_rfl
        _ = (M2 * S) * (q1 * q1) := by rw [hsq]
        _ = M2 * (S * (q1 * q1)) := by ac_rfl
    have hsplit_c : C - r = (2 * M2 - r) + 2 := by omega
    calc
      x * (C - r) + M2 * (S * (q1 * q1))
          = x * (2 * M2 - r) + (x * 2 + (M1 * q1) * (M1 * q1)) := by
              rw [hsplit_c, Nat.mul_add, ← hlhs1, Nat.add_assoc]
      _ = x * (2 * M2 - r) + (x * x + 1) := by
            rw [Nat.mul_comm x 2, Nat.add_comm (2 * x), hsq_x]
      _ = x * ((2 * M2 - r) + (M2 * K + r)) + 1 := by
            conv => lhs; rhs; lhs; rhs; rw [hx_M2]
            rw [← Nat.add_assoc, ← Nat.mul_add]
      _ = x * (M2 * (2 + K)) + 1 := by
            rw [show (2 * M2 - r) + (M2 * K + r) = 2 * M2 + M2 * K by omega,
                Nat.mul_add M2 2 K, Nat.mul_comm M2 2]
      _ = M2 * (x * (2 + K)) + 1 := by ac_rfl
  have hle_q : S * (q1 * q1) ≤ x * (2 + K) := by
    by_cases hle : S * (q1 * q1) ≤ x * (2 + K)
    · exact hle
    · exfalso
      have hgt : x * (2 + K) + 1 ≤ S * (q1 * q1) := by omega
      have hm := Nat.mul_le_mul_left M2 hgt
      rw [Nat.mul_add, Nat.mul_one] at hm
      omega
  have hx_mod : (x * (C - r)) % M2 = 1 := by
    have hm_sub : M2 * (x * (2 + K) - S * (q1 * q1)) + M2 * (S * (q1 * q1)) = M2 * (x * (2 + K)) := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hle_q]
    have heq : x * (C - r) = M2 * (x * (2 + K) - S * (q1 * q1)) + 1 := by
      generalize x * (C - r) = A, M2 * (S * (q1 * q1)) = B,
        M2 * (x * (2 + K)) = E, M2 * (x * (2 + K) - S * (q1 * q1)) = F at hmain hm_sub ⊢
      omega
    rw [heq, Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hM2]
  let Y := i1 * (C - r)
  have hdY : d * Y = M2 * (d * (Y / M2)) + d * (Y % M2) := by
    conv => lhs; rhs; rw [(Nat.div_add_mod Y M2).symm]
    rw [Nat.mul_add, ← Nat.mul_assoc d M2, Nat.mul_comm d M2, Nat.mul_assoc M2 d]
  have hdY_mod : (d * Y) % M2 = (d * (Y % M2)) % M2 := by
    rw [hdY, Nat.add_comm (M2 * (d * (Y / M2))), Nat.add_mul_mod_self_left]
  have hdY_eq : d * Y = x * (C - r) := by dsimp only [x, Y]; ac_rfl
  dsimp only [Y] at hdY_mod
  rw [← hdY_mod, hdY_eq, hx_mod]

private theorem core3_core2_eq_coprime23Core_w13 :
    ∀ (fuel n : Nat), n > 0 -> n ≤ fuel -> core3 (core2 n) = coprime23Core n
  | 0, _, hn, hle => by omega
  | fuel + 1, n, hn, hle => by
    by_cases hev : n % 2 = 0
    · let k := n / 2
      have hk_pos : k > 0 := by dsimp only [k]; omega
      have hn_eq : n = 2 * k := by dsimp only [k]; omega
      rw [hn_eq, core2_mul2 k hk_pos, coprime23Core_mul2 k hk_pos]
      exact core3_core2_eq_coprime23Core_w13 fuel k hk_pos (by dsimp only [k]; omega)
    · have hodd : n % 2 = 1 := by omega
      rcases core3_decomp n hn with ⟨_, _, _, _, hmul⟩
      have hc3_odd : core3 n % 2 = 1 := by
        by_cases hc3_ev : core3 n % 2 = 0
        · have hm0 : (v3Pow n * core3 n) % 2 = 0 := by
            rw [Nat.mul_mod, hc3_ev, Nat.mul_zero]
          rw [hmul] at hm0; omega
        · omega
      unfold coprime23Core
      rw [core2_of_odd n hodd, core2_of_odd (core3 n) hc3_odd]

private theorem reduceRatPair_div_exact_w13 (a m : Nat) (hm : m > 0) (hdvd : m ∣ a) :
    reduceRatPair a m = (a / m, 1) := by
  rcases hdvd with ⟨q, rfl⟩
  unfold reduceRatPair
  have hgcd : Nat.gcd (m * q) m = m :=
    Nat.dvd_antisymm (Nat.gcd_dvd_right (m * q) m) (Nat.dvd_gcd ⟨q, rfl⟩ (Nat.dvd_refl m))
  dsimp only
  rw [hgcd, Nat.div_self hm]

private theorem dvd_three_mul_add_one_of_mod_w13 (x M D Qm Qr R Qt : Nat)
    (hM : M = D * Qm) (hmod : x % M = D * Qr + R) (h3 : 3 * R + 1 = D * Qt) :
    D ∣ (3 * x + 1) := by
  refine ⟨3 * (Qm * (x / M) + Qr) + Qt, ?_⟩
  have hdiv : M * (x / M) + x % M = x := Nat.div_add_mod x M
  calc
    3 * x + 1 = 3 * (M * (x / M) + x % M) + 1 := by rw [hdiv]
    _ = 3 * ((D * Qm) * (x / M) + (D * Qr + R)) + 1 := by rw [← hM, ← hmod]
    _ = D * (3 * (Qm * (x / M) + Qr)) + (3 * R + 1) := by
          rw [Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_add]
          ac_rfl
    _ = D * (3 * (Qm * (x / M) + Qr) + Qt) := by rw [h3, ← Nat.mul_add]

/--
  Theorem W13.3j' (`invMod2147483648Odd_mul_and_q6_nat_agreement`,
  `zero custom axioms`):
  Universal 6-Step Newton–Hensel `mod 2^31` Odd-Inverse Correctness & Exact `Q_(6)^+` / `Nat`
  Step Agreement for `T_diamond10` (`Branch P5.12`):
  1. For EVERY odd `d : Nat` (`d % 2 = 1`), `(d * invMod2147483648Odd d) % 2147483648 = 1`!
  2. For EVERY `x : Nat`, `cousinDiamond10StepQ6 (x, 1) = (cousinDiamond10Step x, 1)`!
-/
theorem invMod2147483648Odd_mul_and_q6_nat_agreement :
    (∀ d : Nat, d % 2 = 1 -> (d * invMod2147483648Odd d) % 2147483648 = 1) ∧
    (∀ x : Nat, cousinDiamond10StepQ6 (x, 1) = (cousinDiamond10Step x, 1)) := by
  rcases invMod268435456Odd_mul_and_q6_nat_agreement with ⟨hinv268m, hd9_all⟩
  have hinv2b : ∀ d : Nat, d % 2 = 1 -> (d * invMod2147483648Odd d) % 2147483648 = 1 := by
    intro d hodd
    exact hensel_inv_lift_w13 268435456 2147483648 33554432 4294967298 d (invMod268435456Odd d)
      (by decide) (by decide) (by decide) (hinv268m d hodd)
  refine ⟨hinv2b, ?_⟩
  have hi2b : invMod2147483648Odd 1 = 1 := by decide
  have hm3_1 : (1 : Nat) % 3 = 1 := by decide
  intro x
  have hcc : core3 (core2 (656179 + x)) = coprime23Core (656179 + x) :=
    core3_core2_eq_coprime23Core_w13 (656179 + x) (656179 + x) (by omega) (Nat.le_refl _)
  unfold cousinDiamond10StepQ6 cousinDiamond10Step isDiamond10Cone11
  simp only [hi2b, hm3_1, Nat.mul_one, hcc]
  by_cases hc11 : x ≥ 6441794765 ∧ x % 2147483648 = 2146827469 ∧ x % 3 = 2 ∧ coprime23Core (656179 + x) = 1
  · simp only [hc11, and_self, ite_true]
    exact reduceRatPair_div_exact_w13 (3 * x + 1) 8 (by decide)
      (dvd_three_mul_add_one_of_mod_w13 x 2147483648 8 268435456 268353433 5 2
        (by decide) hc11.2.1 (by decide))
  · simp only [hc11, ite_false]; exact hd9_all x

set_option maxRecDepth 16384 in
/--
  Theorem W13.3k (`cousin_diamond10_counter_model_separation`, `[]` axioms):
  `T_diamond10` rejects ALL three Counter-Models (`M1 = Q_(6)^+` 5-cycle `(1, 7) -> ... -> (1, 7)`
  plus non-integers `(6441794765, 7)` and `(25769147597, 7)` bypassing Cone 11 by `W13.3j`,
  `M2 = Z^-` cycles `-1` and `-5 -> -7 -> -10 -> -5`, and `M3` supercritical `q = 7` 5-cycle at `5`),
  AND at the genuine `v_2(3x + 1) = 3` Cone-11 jumps `6441794765 -> 2415673037` (`20` steps to `1`) and
  `25769147597 -> 9663430349 -> 3623786381 -> 1358919893 -> 31849685 -> 746477 -> 279929`
  (`ZPOS_COUSIN_DIAMOND10_CONE11_25769147597_JUMP`, `20` steps to `1`) strictly increases
  `cousinDiamond2Phi` (`+38.44x`) directly into `Cone 10 -> Cone 9 -> Cone 8 -> Cone 7 -> Cone 6 -> Cone 5`!
-/
theorem cousin_diamond10_counter_model_separation :
    cousinDiamond10StepInt (-1) = -1 ∧
    cousinDiamond10IterInt 3 (-5) = -5 ∧
    cousinDiamond10IterParam 7 5 5 = 5 ∧
    cousinDiamond10StepQ6 (1, 7) = (5, 7) ∧
    cousinDiamond10IterQ6 5 (1, 7) = (1, 7) ∧
    cousinDiamond10StepQ6 (6441794765, 7) = cousinDiamond9StepQ6 (6441794765, 7) ∧
    cousinDiamond10StepQ6 (25769147597, 7) = cousinDiamond9StepQ6 (25769147597, 7) ∧
    isDiamond10Cone11 6441794765 ∧
    cousinDiamond10Step 6441794765 = 2415673037 ∧
    cousinDiamond10Iter 20 6441794765 = 1 ∧
    isDiamond10Cone11 25769147597 ∧
    cousinDiamond10Step 25769147597 = 9663430349 ∧
    cousinDiamond10StepInt 25769147597 = 9663430349 ∧
    cousinDiamond10StepQ6 (25769147597, 1) = (9663430349, 1) ∧
    isDiamond9Cone10 9663430349 ∧
    isDiamond8Cone9 3623786381 ∧
    isDiamond7Cone8 1358919893 ∧
    isDiamond6Cone7 31849685 ∧
    isDiamond5Cone6 746477 ∧
    isDiamond4Cone5 279929 ∧
    cousinDiamond2Phi 25769147597 < cousinDiamond2Phi 9663430349 ∧
    cousinDiamond10Iter 20 25769147597 = 1 := by
  decide

-- ============================================================================
-- SECTION 3: Front D (Branches P2.2 & P5.3) — Complete Mod-`1458` (`2 * 3^6`)
--            Markov Bijection, Automatic `|u| >= 10 -> w(u) >= 7` Lock, `M = 5`
--            Empty Surviving Window, & Unconditional Constructive Lower-Bound
--            Dyadic-Window Occupancy
-- ============================================================================

-- ----------------------------------------------------------------------------
-- Section 3A: Complete Mod-`1458` (`2 * 3^6`) Markov Bijection, Automatic
--             `|u| >= 10` Weight-`7` Lock, & `3^(w - 7)` Fiber Equidistribution (`P5.3`)
-- ----------------------------------------------------------------------------

def survivingMod1458List : List Nat :=
  (List.range 1458).filter (fun r => r % 6 == 1 || r % 6 == 3)

private theorem mem_survivingMod1458List_iff (y : Nat) :
    y ∈ survivingMod1458List ↔ (y < 1458 ∧ (y % 6 = 1 ∨ y % 6 = 3)) := by
  unfold survivingMod1458List
  rw [List.mem_filter, List.mem_range, Bool.or_eq_true, beq_iff_eq, beq_iff_eq]

private def markov6Aux (q r : Nat) : Nat :=
  match q with
  | 0 =>
    match r with
    | 0 => 1 | 1 => 393 | 2 => 1303 | 3 => 531 | 4 => 787 | 5 => 1353 | 6 => 1423 | 7 => 699 | 8 => 25
    | 9 => 1107 | 10 => 859 | 11 => 579 | 12 => 91 | 13 => 843 | 14 => 853 | 15 => 1035 | 16 => 607 | 17 => 129
    | 18 => 379 | 19 => 825 | 20 => 871 | 21 => 315 | 22 => 31 | 23 => 3 | 24 => 829 | 25 => 645 | _ => 79
  | 1 =>
    match r with
    | 0 => 405 | 1 => 589 | 2 => 201 | 3 => 1441 | 4 => 303 | 5 => 1393 | 6 => 1305 | 7 => 823 | 8 => 723
    | 9 => 757 | 10 => 1257 | 11 => 439 | 12 => 99 | 13 => 733 | 14 => 111 | 15 => 235 | 16 => 591 | 17 => 133
    | 18 => 1161 | 19 => 319 | 20 => 1281 | 21 => 1333 | 22 => 1221 | 23 => 475 | 24 => 117 | 25 => 1039 | _ => 1317
  | 2 =>
    match r with
    | 0 => 1135 | 1 => 231 | 2 => 7 | 3 => 1341 | 4 => 1435 | 5 => 219 | 6 => 1099 | 7 => 537 | 8 => 187
    | 9 => 459 | 10 => 49 | 11 => 903 | 12 => 1225 | 13 => 681 | 14 => 1015 | 15 => 387 | 16 => 1255 | 17 => 453
    | 18 => 55 | 19 => 663 | 20 => 1033 | 21 => 1125 | 22 => 679 | 23 => 327 | 24 => 505 | 25 => 483 | _ => 241
  | 3 =>
    match r with
    | 0 => 1215 | 1 => 1237 | 2 => 525 | 3 => 1117 | 4 => 141 | 5 => 97 | 6 => 657 | 7 => 13 | 8 => 1047
    | 9 => 433 | 10 => 1095 | 11 => 601 | 12 => 909 | 13 => 1381 | 14 => 435 | 15 => 1369 | 16 => 429 | 17 => 295
    | 18 => 513 | 19 => 967 | 20 => 147 | 21 => 1009 | 22 => 1059 | 23 => 637 | 24 => 927 | 25 => 229 | _ => 183
  | 4 =>
    match r with
    | 0 => 811 | 1 => 69 | 2 => 169 | 3 => 693 | 4 => 625 | 5 => 543 | 6 => 775 | 7 => 375 | 8 => 349
    | 9 => 1269 | 10 => 697 | 11 => 1227 | 12 => 901 | 13 => 519 | 14 => 1177 | 15 => 1197 | 16 => 445 | 17 => 777
    | 18 => 1189 | 19 => 501 | 20 => 1195 | 21 => 477 | 22 => 1327 | 23 => 651 | 24 => 181 | 25 => 321 | _ => 403
  | 5 =>
    match r with
    | 0 => 567 | 1 => 427 | 2 => 849 | 3 => 793 | 4 => 1437 | 5 => 259 | 6 => 9 | 7 => 661 | 8 => 1371
    | 9 => 109 | 10 => 933 | 11 => 763 | 12 => 261 | 13 => 571 | 14 => 759 | 15 => 1045 | 16 => 267 | 17 => 457
    | 18 => 1323 | 19 => 157 | 20 => 471 | 21 => 685 | 22 => 897 | 23 => 799 | 24 => 279 | 25 => 877 | _ => 507
  | 6 =>
    match r with
    | 0 => 487 | 1 => 1365 | 2 => 331 | 3 => 45 | 4 => 1273 | 5 => 867 | 6 => 451 | 7 => 213 | 8 => 511
    | 9 => 621 | 10 => 1345 | 11 => 93 | 12 => 577 | 13 => 357 | 14 => 1339 | 15 => 549 | 16 => 1093 | 17 => 1101
    | 18 => 865 | 19 => 339 | 20 => 1357 | 21 => 1287 | 22 => 517 | 23 => 975 | 24 => 1315 | 25 => 159 | _ => 565
  | 7 =>
    match r with
    | 0 => 1377 | 1 => 1075 | 2 => 1173 | 3 => 469 | 4 => 1275 | 5 => 421 | 6 => 819 | 7 => 1309 | 8 => 237
    | 9 => 1243 | 10 => 771 | 11 => 925 | 12 => 1071 | 13 => 1219 | 14 => 1083 | 15 => 721 | 16 => 105 | 17 => 619
    | 18 => 675 | 19 => 805 | 20 => 795 | 21 => 361 | 22 => 735 | 23 => 961 | 24 => 1089 | 25 => 67 | _ => 831
  | 8 =>
    match r with
    | 0 => 163 | 1 => 1203 | 2 => 493 | 3 => 855 | 4 => 463 | 5 => 1191 | 6 => 127 | 7 => 51 | 8 => 673
    | 9 => 1431 | 10 => 535 | 11 => 417 | 12 => 253 | 13 => 195 | 14 => 43 | 15 => 1359 | 16 => 283 | 17 => 1425
    | 18 => 541 | 19 => 177 | 20 => 61 | 21 => 639 | 22 => 1165 | 23 => 1299 | 24 => 991 | 25 => 1455 | _ => 727
  | 9 =>
    match r with
    | 0 => 729 | 1 => 265 | 2 => 39 | 3 => 145 | 4 => 1113 | 5 => 583 | 6 => 171 | 7 => 499 | 8 => 561
    | 9 => 919 | 10 => 609 | 11 => 1087 | 12 => 423 | 13 => 409 | 14 => 1407 | 15 => 397 | 16 => 1401 | 17 => 781
    | 18 => 27 | 19 => 1453 | 20 => 1119 | 21 => 37 | 22 => 573 | 23 => 1123 | 24 => 441 | 25 => 715 | _ => 1155
  | 10 =>
    match r with
    | 0 => 1297 | 1 => 1041 | 2 => 655 | 3 => 207 | 4 => 1111 | 5 => 57 | 6 => 1261 | 7 => 1347 | 8 => 835
    | 9 => 783 | 10 => 1183 | 11 => 741 | 12 => 1387 | 13 => 33 | 14 => 205 | 15 => 711 | 16 => 931 | 17 => 291
    | 18 => 217 | 19 => 15 | 20 => 223 | 21 => 1449 | 22 => 355 | 23 => 165 | 24 => 667 | 25 => 1293 | _ => 889
  | 11 =>
    match r with
    | 0 => 81 | 1 => 913 | 2 => 363 | 3 => 1279 | 4 => 951 | 5 => 745 | 6 => 981 | 7 => 1147 | 8 => 885
    | 9 => 595 | 10 => 447 | 11 => 1249 | 12 => 1233 | 13 => 1057 | 14 => 273 | 15 => 73 | 16 => 1239 | 17 => 943
    | 18 => 837 | 19 => 643 | 20 => 1443 | 21 => 1171 | 22 => 411 | 23 => 1285 | 24 => 1251 | 25 => 1363 | _ => 21
  | 12 =>
    match r with
    | 0 => 973 | 1 => 879 | 2 => 817 | 3 => 1017 | 4 => 301 | 5 => 381 | 6 => 937 | 7 => 1185 | 8 => 997
    | 9 => 135 | 10 => 373 | 11 => 1065 | 12 => 1063 | 13 => 1329 | 14 => 367 | 15 => 63 | 16 => 121 | 17 => 615
    | 18 => 1351 | 19 => 1311 | 20 => 385 | 21 => 801 | 22 => 1003 | 23 => 489 | 24 => 343 | 25 => 1131 | _ => 1051
  | 13 =>
    match r with
    | 0 => 891 | 1 => 103 | 2 => 687 | 3 => 955 | 4 => 789 | 5 => 907 | 6 => 333 | 7 => 337 | 8 => 1209
    | 9 => 271 | 10 => 285 | 11 => 1411 | 12 => 585 | 13 => 247 | 14 => 597 | 15 => 1207 | 16 => 1077 | 17 => 1105
    | 18 => 189 | 19 => 1291 | 20 => 309 | 21 => 847 | 22 => 249 | 23 => 1447 | 24 => 603 | 25 => 553 | _ => 345
  | 14 =>
    match r with
    | 0 => 649 | 1 => 717 | 2 => 979 | 3 => 369 | 4 => 949 | 5 => 705 | 6 => 613 | 7 => 1023 | 8 => 1159
    | 9 => 945 | 10 => 1021 | 11 => 1389 | 12 => 739 | 13 => 1167 | 14 => 529 | 15 => 873 | 16 => 769 | 17 => 939
    | 18 => 1027 | 19 => 1149 | 20 => 547 | 21 => 153 | 22 => 193 | 23 => 813 | 24 => 19 | 25 => 969 | _ => 1213
  | 15 =>
    match r with
    | 0 => 243 | 1 => 751 | 2 => 1011 | 3 => 631 | 4 => 627 | 5 => 1069 | 6 => 1143 | 7 => 985 | 8 => 75
    | 9 => 1405 | 10 => 123 | 11 => 115 | 12 => 1395 | 13 => 895 | 14 => 921 | 15 => 883 | 16 => 915 | 17 => 1267
    | 18 => 999 | 19 => 481 | 20 => 633 | 21 => 523 | 22 => 87 | 23 => 151 | 24 => 1413 | 25 => 1201 | _ => 669
  | 16 =>
    match r with
    | 0 => 325 | 1 => 555 | 2 => 1141 | 3 => 1179 | 4 => 139 | 5 => 1029 | 6 => 289 | 7 => 861 | 8 => 1321
    | 9 => 297 | 10 => 211 | 11 => 255 | 12 => 415 | 13 => 1005 | 14 => 691 | 15 => 225 | 16 => 1417 | 17 => 1263
    | 18 => 703 | 19 => 987 | 20 => 709 | 21 => 963 | 22 => 841 | 23 => 1137 | 24 => 1153 | 25 => 807 | _ => 1375
  | _ =>
    match r with
    | 0 => 1053 | 1 => 1399 | 2 => 1335 | 3 => 307 | 4 => 465 | 5 => 1231 | 6 => 495 | 7 => 175 | 8 => 399
    | 9 => 1081 | 10 => 1419 | 11 => 277 | 12 => 747 | 13 => 85 | 14 => 1245 | 15 => 559 | 16 => 753 | 17 => 1429
    | 18 => 351 | 19 => 1129 | 20 => 957 | 21 => 199 | 22 => 1383 | 23 => 313 | 24 => 765 | 25 => 391 | _ => 993

def markovShiftTrue6Mod1458Table (x : Fin 486) : Nat :=
  markov6Aux (x.val / 27) (x.val % 27)

private def invMarkov6Aux (q r : Nat) : Nat :=
  match q with
  | 0 =>
    match r with
    | 0 => 0 | 1 => 23 | 2 => 56 | 3 => 141 | 4 => 88 | 5 => 289 | 6 => 402 | 7 => 323 | 8 => 8
    | 9 => 261 | 10 => 22 | 11 => 283 | 12 => 264 | 13 => 245 | 14 => 230 | 15 => 165 | 16 => 64 | 17 => 223
    | 18 => 72 | 19 => 275 | 20 => 236 | 21 => 339 | 22 => 214 | 23 => 109 | 24 => 312 | 25 => 413 | _ => 26
  | 1 =>
    match r with
    | 0 => 297 | 1 => 472 | 2 => 427 | 3 => 12 | 4 => 173 | 5 => 86 | 6 => 39 | 7 => 352 | 8 => 205
    | 9 => 144 | 10 => 41 | 11 => 416 | 12 => 51 | 13 => 340 | 14 => 415 | 15 => 222 | 16 => 17 | 17 => 44
    | 18 => 333 | 19 => 436 | 20 => 85 | 21 => 246 | 22 => 101 | 23 => 428 | 24 => 399 | 25 => 154 | _ => 187
  | 2 =>
    match r with
    | 0 => 216 | 1 => 293 | 2 => 110 | 3 => 249 | 4 => 466 | 5 => 235 | 6 => 132 | 7 => 107 | 8 => 62
    | 9 => 369 | 10 => 400 | 11 => 229 | 12 => 480 | 13 => 29 | 14 => 284 | 15 => 273 | 16 => 442 | 17 => 169
    | 18 => 288 | 19 => 59 | 20 => 290 | 21 => 447 | 22 => 106 | 23 => 55 | 24 => 42 | 25 => 197 | _ => 80
  | 3 =>
    match r with
    | 0 => 405 | 1 => 364 | 2 => 373 | 3 => 228 | 4 => 443 | 5 => 140 | 6 => 147 | 7 => 244 | 8 => 151
    | 9 => 360 | 10 => 311 | 11 => 470 | 12 => 159 | 13 => 232 | 14 => 361 | 15 => 438 | 16 => 287 | 17 => 98
    | 18 => 441 | 19 => 328 | 20 => 31 | 21 => 462 | 22 => 371 | 23 => 482 | 24 => 21 | 25 => 46 | _ => 133
  | 4 =>
    match r with
    | 0 => 432 | 1 => 77 | 2 => 164 | 3 => 357 | 4 => 358 | 5 => 181 | 6 => 348 | 7 => 377 | 8 => 116
    | 9 => 477 | 10 => 292 | 11 => 175 | 12 => 210 | 13 => 299 | 14 => 338 | 15 => 381 | 16 => 334 | 17 => 115
    | 18 => 18 | 19 => 329 | 20 => 344 | 21 => 69 | 22 => 484 | 23 => 1 | 24 => 258 | 25 => 467 | _ => 134
  | 5 =>
    match r with
    | 0 => 27 | 1 => 256 | 2 => 319 | 3 => 444 | 4 => 227 | 5 => 194 | 6 => 255 | 7 => 136 | 8 => 97
    | 9 => 90 | 10 => 95 | 11 => 38 | 12 => 267 | 13 => 124 | 14 => 307 | 15 => 168 | 16 => 71 | 17 => 152
    | 18 => 63 | 19 => 220 | 20 => 463 | 21 => 192 | 22 => 155 | 23 => 50 | 24 => 129 | 25 => 424 | _ => 79
  | 6 =>
    match r with
    | 0 => 162 | 1 => 347 | 2 => 218 | 3 => 465 | 4 => 250 | 5 => 127 | 6 => 78 | 7 => 161 | 8 => 170
    | 9 => 99 | 10 => 184 | 11 => 121 | 12 => 426 | 13 => 83 | 14 => 392 | 15 => 3 | 16 => 226 | 17 => 61
    | 18 => 234 | 19 => 113 | 20 => 398 | 21 => 177 | 22 => 376 | 23 => 433 | 24 => 474 | 25 => 251 | _ => 188
  | 7 =>
    match r with
    | 0 => 135 | 1 => 148 | 2 => 265 | 3 => 174 | 4 => 11 | 5 => 248 | 6 => 363 | 7 => 28 | 8 => 43
    | 9 => 306 | 10 => 365 | 11 => 92 | 12 => 375 | 13 => 16 | 14 => 253 | 15 => 384 | 16 => 341 | 17 => 206
    | 18 => 171 | 19 => 112 | 20 => 409 | 21 => 408 | 22 => 425 | 23 => 104 | 24 => 237 | 25 => 316 | _ => 25
  | 8 =>
    match r with
    | 0 => 378 | 1 => 131 | 2 => 272 | 3 => 87 | 4 => 142 | 5 => 73 | 6 => 294 | 7 => 431 | 8 => 224
    | 9 => 207 | 10 => 76 | 11 => 67 | 12 => 156 | 13 => 353 | 14 => 446 | 15 => 111 | 16 => 118 | 17 => 7
    | 18 => 450 | 19 => 383 | 20 => 452 | 21 => 285 | 22 => 268 | 23 => 379 | 24 => 204 | 25 => 35 | _ => 242
  | 9 =>
    match r with
    | 0 => 243 | 1 => 40 | 2 => 211 | 3 => 390 | 4 => 281 | 5 => 302 | 6 => 471 | 7 => 406 | 8 => 475
    | 9 => 36 | 10 => 149 | 11 => 146 | 12 => 483 | 13 => 394 | 14 => 199 | 15 => 114 | 16 => 125 | 17 => 260
    | 18 => 279 | 19 => 4 | 20 => 355 | 21 => 138 | 22 => 209 | 23 => 158 | 24 => 345 | 25 => 208 | _ => 457
  | 10 =>
    match r with
    | 0 => 108 | 1 => 401 | 2 => 326 | 3 => 195 | 4 => 34 | 5 => 19 | 6 => 24 | 7 => 215 | 8 => 278
    | 9 => 315 | 10 => 454 | 11 => 13 | 12 => 372 | 13 => 137 | 14 => 14 | 15 => 219 | 16 => 10 | 17 => 439
    | 18 => 180 | 19 => 167 | 20 => 20 | 21 => 393 | 22 => 160 | 23 => 325 | 24 => 420 | 25 => 305 | _ => 296
  | 11 =>
    match r with
    | 0 => 351 | 1 => 418 | 2 => 157 | 3 => 120 | 4 => 65 | 5 => 356 | 6 => 93 | 7 => 298 | 8 => 421
    | 9 => 252 | 10 => 419 | 11 => 200 | 12 => 105 | 13 => 286 | 14 => 145 | 15 => 330 | 16 => 395 | 17 => 314
    | 18 => 387 | 19 => 382 | 20 => 301 | 21 => 354 | 22 => 479 | 23 => 212 | 24 => 453 | 25 => 100 | _ => 403
  | 12 =>
    match r with
    | 0 => 324 | 1 => 185 | 2 => 380 | 3 => 303 | 4 => 412 | 5 => 451 | 6 => 240 | 7 => 485 | 8 => 332
    | 9 => 423 | 10 => 346 | 11 => 445 | 12 => 102 | 13 => 407 | 14 => 68 | 15 => 327 | 16 => 388 | 17 => 385
    | 18 => 396 | 19 => 437 | 20 => 74 | 21 => 15 | 22 => 52 | 23 => 271 | 24 => 150 | 25 => 89 | _ => 350
  | 13 =>
    match r with
    | 0 => 459 | 1 => 310 | 2 => 103 | 3 => 336 | 4 => 335 | 5 => 410 | 6 => 201 | 7 => 190 | 8 => 367
    | 9 => 468 | 10 => 203 | 11 => 254 | 12 => 213 | 13 => 178 | 14 => 91 | 15 => 60 | 16 => 179 | 17 => 368
    | 18 => 9 | 19 => 274 | 20 => 247 | 21 => 84 | 22 => 263 | 23 => 266 | 24 => 75 | 25 => 478 | _ => 349
  | 14 =>
    match r with
    | 0 => 54 | 1 => 455 | 2 => 434 | 3 => 411 | 4 => 304 | 5 => 397 | 6 => 456 | 7 => 269 | 8 => 386
    | 9 => 45 | 10 => 238 | 11 => 391 | 12 => 318 | 13 => 191 | 14 => 122 | 15 => 435 | 16 => 280 | 17 => 331
    | 18 => 126 | 19 => 221 | 20 => 128 | 21 => 123 | 22 => 430 | 23 => 217 | 24 => 366 | 25 => 359 | _ => 404
  | 15 =>
    match r with
    | 0 => 81 | 1 => 202 | 2 => 49 | 3 => 66 | 4 => 119 | 5 => 464 | 6 => 309 | 7 => 82 | 8 => 313
    | 9 => 198 | 10 => 473 | 11 => 308 | 12 => 321 | 13 => 70 | 14 => 37 | 15 => 276 | 16 => 449 | 17 => 422
    | 18 => 117 | 19 => 166 | 20 => 193 | 21 => 300 | 22 => 47 | 23 => 320 | 24 => 183 | 25 => 370 | _ => 295
  | 16 =>
    match r with
    | 0 => 270 | 1 => 239 | 2 => 2 | 3 => 33 | 4 => 196 | 5 => 343 | 6 => 186 | 7 => 53 | 8 => 440
    | 9 => 153 | 10 => 130 | 11 => 337 | 12 => 48 | 13 => 461 | 14 => 176 | 15 => 57 | 16 => 172 | 17 => 277
    | 18 => 342 | 19 => 5 | 20 => 182 | 21 => 231 | 22 => 322 | 23 => 163 | 24 => 96 | 25 => 143 | _ => 458
  | _ =>
    match r with
    | 0 => 189 | 1 => 94 | 2 => 481 | 3 => 282 | 4 => 389 | 5 => 32 | 6 => 417 | 7 => 460 | 8 => 259
    | 9 => 414 | 10 => 257 | 11 => 362 | 12 => 429 | 13 => 448 | 14 => 469 | 15 => 6 | 16 => 233 | 17 => 476
    | 18 => 225 | 19 => 58 | 20 => 139 | 21 => 30 | 22 => 317 | 23 => 374 | 24 => 291 | 25 => 262 | _ => 241

private def invMarkov6ByIdx (idx : Nat) : Nat :=
  invMarkov6Aux (idx / 27) (idx % 27)

private def pow2Mod2187Aux : Nat -> Nat -> Nat
  | 0, _ => 1
  | fuel + 1, e =>
    if e = 0 then 1
    else
      let half := pow2Mod2187Aux fuel (e / 2)
      let sq := (half * half) % 2187
      if e % 2 = 0 then sq else (2 * sq) % 2187

private theorem pow2Mod2187Aux_eq :
    ∀ (fuel e : Nat), e < 2 ^ fuel -> pow2Mod2187Aux fuel e = 2 ^ e % 2187
  | 0, e, hlt => by
    have he0 : e = 0 := by simp at hlt; exact hlt
    subst he0; rfl
  | fuel + 1, e, hlt => by
    simp only [pow2Mod2187Aux]
    by_cases he0 : e = 0
    · subst he0; rfl
    · simp only [he0, ite_false]
      have hlt_half : e / 2 < 2 ^ fuel := by
        rw [Nat.pow_succ] at hlt; omega
      have ih := pow2Mod2187Aux_eq fuel (e / 2) hlt_half
      have he_div : 2 * (e / 2) + e % 2 = e := Nat.div_add_mod e 2
      have hsq : ((2 ^ (e / 2) % 2187) * (2 ^ (e / 2) % 2187)) % 2187 =
          2 ^ (2 * (e / 2)) % 2187 := by
        rw [← Nat.mul_mod, ← Nat.pow_add, show e / 2 + e / 2 = 2 * (e / 2) by omega]
      by_cases hev : e % 2 = 0
      · simp only [hev, ite_true, ih, hsq]
        have he_eq : 2 * (e / 2) = e := by omega
        rw [he_eq]
      · simp only [hev, ite_false, ih, hsq]
        have he_eq : 2 * (e / 2) + 1 = e := by omega
        calc
          (2 * (2 ^ (2 * (e / 2)) % 2187)) % 2187
              = ((2 % 2187) * (2 ^ (2 * (e / 2)) % 2187)) % 2187 := rfl
          _ = (2 * 2 ^ (2 * (e / 2))) % 2187 := (Nat.mul_mod 2 _ 2187).symm
          _ = 2 ^ (2 * (e / 2) + 1) % 2187 := by
                rw [Nat.pow_succ, Nat.mul_comm _ 2]
          _ = 2 ^ e % 2187 := by rw [he_eq]

set_option maxRecDepth 131072 in
private theorem markovShiftTrue6_table_cert :
    ∀ x : Fin 486,
      let t := markovShiftTrue6Mod1458Table x
      t < 1457 ∧
      (t % 6 = 1 ∨ t % 6 = 3) ∧
      pow2Mod2187Aux 11 (t + 1) = (3 * pow2Mod2187Aux 11 x.val + 1) % 2187 ∧
      invMarkov6ByIdx (2 * (t / 6) + (if t % 6 == 3 then 1 else 0)) = x.val := by
  decide

private theorem markovShiftTrue6_eq_table (x : Fin 486) :
    markovShiftTrue 6 x.val % 1458 = markovShiftTrue6Mod1458Table x := by
  rcases markovShiftTrue6_table_cert x with ⟨ht_lt, _, hpow, _⟩
  let t := markovShiftTrue6Mod1458Table x
  change t < 1457 at ht_lt
  rw [pow2Mod2187Aux_eq 11 (t + 1) (by omega),
      pow2Mod2187Aux_eq 11 x.val (by have := x.isLt; omega)] at hpow
  have h3_rhs : (3 * (2 ^ x.val % 2187) + 1) % 2187 = (3 * 2 ^ x.val + 1) % 2187 := by
    have hm : (3 * (2 ^ x.val % 2187)) % 2187 = (3 * 2 ^ x.val) % 2187 := by
      calc
        (3 * (2 ^ x.val % 2187)) % 2187
            = ((3 % 2187) * (2 ^ x.val % 2187)) % 2187 := rfl
        _ = (3 * 2 ^ x.val) % 2187 := (Nat.mul_mod 3 _ 2187).symm
    rw [Nat.add_mod, hm, ← Nat.add_mod]
  rw [h3_rhs] at hpow
  have hr_n3 : (3 * 2 ^ x.val + 1) % 3 ≠ 0 := by omega
  rcases dlog2ModPow3_spec 7 (3 * 2 ^ x.val + 1) (by decide) hr_n3 with ⟨he_lt, he_mod⟩
  have he_eq : dlog2ModPow3 7 (3 * 2 ^ x.val + 1) = t + 1 :=
    pow2_inj_mod_pow3_w8 7 _ (t + 1) (by decide) he_lt (by omega)
      (by simpa using he_mod.trans hpow.symm)
  unfold markovShiftTrue
  rw [show (6 : Nat) + 1 = 7 from rfl, he_eq, show t + 1 - 1 = t by omega]
  exact Nat.mod_eq_of_lt (by omega)

private theorem markovShiftTrue6_table_inj (x1 x2 : Fin 486)
    (heq : markovShiftTrue6Mod1458Table x1 = markovShiftTrue6Mod1458Table x2) :
    x1 = x2 := by
  have hi1 := (markovShiftTrue6_table_cert x1).2.2.2
  have hi2 := (markovShiftTrue6_table_cert x2).2.2.2
  rw [heq] at hi1
  exact Fin.ext (hi1.symm.trans hi2)

private theorem markovShiftTrue6_table_mem (x : Fin 486) :
    markovShiftTrue6Mod1458Table x ∈ survivingMod1458List := by
  rcases markovShiftTrue6_table_cert x with ⟨ht_lt, hm6, _, _⟩
  exact (mem_survivingMod1458List_iff _).mpr ⟨by omega, hm6⟩

private theorem take_drop_split_eq_w13 :
    ∀ (k : Nat) (xs : List Bool), xs.take k ++ xs.drop k = xs
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | k + 1, x :: xs => by
    simp only [List.take_succ_cons, List.drop_succ_cons, List.cons_append,
               take_drop_split_eq_w13 k xs]

private theorem take_len_of_ge_w13 :
    ∀ (k : Nat) (xs : List Bool), k ≤ xs.length -> (xs.take k).length = k
  | 0, _, _ => rfl
  | _ + 1, [], h => by simp at h
  | k + 1, _ :: xs, h => by
    simp only [List.length_cons] at h
    simp only [List.take_succ_cons, List.length_cons, take_len_of_ge_w13 k xs (by omega)]

private theorem len10_core_mod512_prefix9
    (p9 freeBits : List Bool) (q : Nat)
    (hp9_len : p9.length = 9)
    (hu : IsCoreParityWord (p9 ++ freeBits ++ [true])) :
    parityOfIter 9 (exactBackwardQuotient 1 (p9 ++ freeBits ++ [true]) q % 512) = p9 := by
  let u := p9 ++ freeBits ++ [true]
  let y := exactBackwardQuotient 1 u q
  let K := backwardOneTotalSteps u q
  let shift := canonicalSuffixShift u 1 + q * (2 * 3 ^ (parityWeight u - 1))
  have hu_len : u.length = 9 + (freeBits.length + 1) := by
    dsimp [u]; rw [List.length_append, List.length_append, hp9_len, List.length_singleton]
    omega
  have hK_ge10 : K ≥ 10 := by unfold K backwardOneTotalSteps; omega
  let v := u ++ List.replicate shift false
  have hv_len : v.length = K := by
    dsimp [v]; rw [List.length_append, List.length_replicate]; rfl
  rcases one_generator_pos_odd_and_reaches_one u q hu with ⟨_, _, heq, _⟩
  change 2 ^ K = 3 ^ parityWeight u * y + affineCarry u at heq
  rcases affineCarry_append_replicate_false u shift with ⟨hwt_v, hcar_v⟩
  have hv_aff : 2 ^ v.length * 1 = 3 ^ parityWeight v * y + affineCarry v := by
    rw [Nat.mul_one, hv_len, hwt_v, hcar_v]; exact heq
  have hv_par := eq_parityOfIter_of_nat_affine v y 1 hv_aff
  rw [hv_len] at hv_par
  have hKs9 : K = 9 + (K - 9) := by omega
  have hpar_sp := parityOfIter_append_split 9 (K - 9) y
  rw [← hKs9, ← hv_par] at hpar_sp
  have hv_p9 : v = p9 ++ (freeBits ++ [true] ++ List.replicate shift false) := by
    dsimp [v, u]
    rw [List.append_assoc p9 freeBits [true],
        List.append_assoc p9 (freeBits ++ [true]) (List.replicate shift false)]
  rw [hv_p9] at hpar_sp
  have hlen9 : p9.length = (parityOfIter 9 y).length := by
    rw [hp9_len, parityOfIter_length]
  have hp9_eq : parityOfIter 9 y = p9 :=
    (list_append_inj_left_eq_len _ _ _ _ hlen9 hpar_sp).1.symm
  have hy_div9 : y = y % 512 + 2 ^ 9 * (y / 512) := by
    have hdm := (Nat.div_add_mod y 512).symm
    rw [show (2 : Nat) ^ 9 = 512 from rfl]; omega
  have hpar9_mod : parityOfIter 9 y = parityOfIter 9 (y % 512) := by
    conv => lhs; rw [hy_div9]
    exact parityOfIter_mod_pow2_shift 9 (y % 512) (y / 512)
  rw [← hpar9_mod, hp9_eq]

set_option exponentiation.threshold 2048 in
set_option maxRecDepth 131072 in
/--
  Theorem W13.4a (`markovShift_mod1458_bijection_and_len10_weight7_lock`, `zero custom axioms`):
  Complete Mod-`1458` (`2 * 3^6`) Markov Image Bijection, `972 / 1458 = 2 / 3` Confinement Matching
  the Automatic `w(u) >= 7` Surviving-Extension Regime (`|u| >= 10`), `729 mod 1458` Suffix Lock, &
  `3^(w - 7)` (`j = 6`) Multi-Step Fiber Equidistribution (`Branch P5.3`):
  1. **Exact Mod-`1458` Contraction & Bijection onto `486` Odd Non-`5 mod 6` Classes (`forall w >= 6`)**:
     For EVERY weight `w >= 6` and `a < 2 * 3 ^ (w - 1)`,
       `markovShiftTrue w a % 1458 = markovShiftTrue 6 (a % 486) % 1458`,
     and `r |-> markovShiftTrue 6 r.val % 1458` is strictly injective on `Fin 486`, mapping `[0, 486)`
     bijectively onto the `486`-element `survivingMod1458List`!
  2. **Universal `972 / 1458 = 2 / 3` Confinement on `w(u) >= 7` & Automatic `|u| >= 10` Surviving Lock**:
     - Every core word `u` with `parityWeight u >= 7` satisfies `canonicalSuffixShift u 1 % 1458 ∈ survivingMod1458List`;
     - Furthermore, EVERY core word `u` of length `u.length >= 10` whose leaf/ray value `exactBackwardQuotient 1 u q`
       satisfies `isSurvivingMod512Bool (exactBackwardQuotient 1 u q % 512) = true` (pure `mod 512` surviving
       extension, hence also every `IsSurvivingMod373248Class` leaf/ray) AUTOMATICALLY satisfies
       `parityWeight u >= 7` AND `canonicalSuffixShift u 1 % 1458 ∈ survivingMod1458List`
       (with zero external weight or `mod 729` hypothesis!)!
  3. **Exact Mod-`1458` Suffix Locks Across Unrestricted Prefixes**:
     - For EVERY `pref : List Bool` with `parityWeight pref >= 1`:
       `canonicalSuffixShift (pref ++ List.replicate 6 true) 1 % 1458 = 729 ∨
        canonicalSuffixShift (pref ++ List.replicate 6 true) 1 % 1458 = 1215`;
     - For EVERY completely unrestricted `pref : List Bool` (including `pref = []`):
       `canonicalSuffixShift (pref ++ List.replicate 7 true) 1 % 1458 = 729` AND
       `canonicalSuffixShift (pref ++ [true, false, true, true, true, true, true, true]) 1 % 1458 = 1215`!
  4. **Mod-`1458` (`j = 6`) Multi-Step `3 ^ (w - 7)` Fiber Equidistribution (`forall tail, forall w >= 7, forall r0 < 1458`)**:
     Along any suffix `tail : List Bool` from weight `w >= 7`, `iterMarkovShift tail w` maps
     `{r0 + 1458 * t | t < 3 ^ (w - 7)}` bijectively and uniformly onto
     `{base + (2 * 3 ^ (6 + parityWeight tail)) * q | q < 3 ^ (w - 7)}`!
-/
theorem markovShift_mod1458_bijection_and_len10_weight7_lock :
    ((∀ (w a : Nat), w ≥ 6 -> a < 2 * 3 ^ (w - 1) ->
        markovShiftTrue w a % 1458 = markovShiftTrue 6 (a % 486) % 1458) ∧
     survivingMod1458List.length = 486 ∧
     (∀ x1 x2 : Fin 486,
        markovShiftTrue 6 x1.val % 1458 = markovShiftTrue 6 x2.val % 1458 -> x1 = x2) ∧
     (∀ x : Fin 486,
        markovShiftTrue 6 x.val % 1458 ∈ survivingMod1458List)) ∧
    ((∀ u : List Bool, IsCoreParityWord u -> parityWeight u ≥ 7 ->
        canonicalSuffixShift u 1 % 1458 ∈ survivingMod1458List) ∧
     (∀ (u : List Bool) (q : Nat),
        IsCoreParityWord u -> u.length ≥ 10 ->
        isSurvivingMod512Bool (exactBackwardQuotient 1 u q % 512) = true ->
        parityWeight u ≥ 7 ∧ canonicalSuffixShift u 1 % 1458 ∈ survivingMod1458List) ∧
     (∀ (u : List Bool) (q : Nat),
        IsCoreParityWord u -> u.length ≥ 10 ->
        IsSurvivingMod373248Class (exactBackwardQuotient 1 u q) ->
        parityWeight u ≥ 7 ∧ canonicalSuffixShift u 1 % 1458 ∈ survivingMod1458List)) ∧
    ((∀ pref : List Bool, parityWeight pref ≥ 1 ->
        canonicalSuffixShift (pref ++ List.replicate 6 true) 1 % 1458 = 729 ∨
        canonicalSuffixShift (pref ++ List.replicate 6 true) 1 % 1458 = 1215) ∧
     (∀ pref : List Bool,
        canonicalSuffixShift (pref ++ List.replicate 7 true) 1 % 1458 = 729 ∧
        canonicalSuffixShift (pref ++ [true, false, true, true, true, true, true, true]) 1 % 1458 = 1215)) ∧
    (∀ (tail : List Bool) (w r0 : Nat),
      w ≥ 7 -> r0 < 1458 ->
      let Mk := 2 * 3 ^ (6 + parityWeight tail)
      let N := 3 ^ (w - 7)
      let base := iterMarkovShift tail w r0 % Mk
      (∀ t : Nat, t < N ->
        ∃ q : Nat, q < N ∧ iterMarkovShift tail w (r0 + 1458 * t) = base + Mk * q) ∧
      (∀ q : Nat, q < N ->
        ∃ t : Nat, t < N ∧
          iterMarkovShift tail w (r0 + 1458 * t) = base + Mk * q ∧
          ∀ t' : Nat, t' < N ->
            iterMarkovShift tail w (r0 + 1458 * t') = base + Mk * q -> t' = t)) := by
  have hcongr1458 : ∀ (w a : Nat), w ≥ 6 -> a < 2 * 3 ^ (w - 1) ->
      markovShiftTrue w a % 1458 = markovShiftTrue 6 (a % 486) % 1458 := by
    intro w a hw6 ha_lt
    have hr_lt : a % 486 < 2 * 3 ^ (6 - 1) := Nat.mod_lt a (by decide)
    exact markovShiftTrue_contraction_mod_pow3 5 w 6 a (a % 486)
      (by omega) (by decide) ha_lt hr_lt (by simp)
  have hinj486 : ∀ x1 x2 : Fin 486,
      markovShiftTrue 6 x1.val % 1458 = markovShiftTrue 6 x2.val % 1458 -> x1 = x2 := by
    intro x1 x2 heq
    rw [markovShiftTrue6_eq_table x1, markovShiftTrue6_eq_table x2] at heq
    exact markovShiftTrue6_table_inj x1 x2 heq
  have hmem486 : ∀ x : Fin 486, markovShiftTrue 6 x.val % 1458 ∈ survivingMod1458List := by
    intro x
    rw [markovShiftTrue6_eq_table x]
    exact markovShiftTrue6_table_mem x
  have hconf7 : ∀ u : List Bool, IsCoreParityWord u -> parityWeight u ≥ 7 ->
      canonicalSuffixShift u 1 % 1458 ∈ survivingMod1458List := by
    intro u hu hw7
    rcases list_eq_append_true_of_reverse_head u hu.2 with ⟨v, rfl⟩
    have hw_v : parityWeight v ≥ 6 := by
      rw [parityWeight_append] at hw7
      have h1 : parityWeight [true] = 1 := rfl
      rw [h1] at hw7; omega
    have hrec : canonicalSuffixShift (v ++ [true]) 1 =
        markovShiftTrue (parityWeight v) (canonicalSuffixShift v 1) :=
      (canonicalSuffixShift_append_markov_recurrence.2.2 v (by omega)).2.2.1
    have ha_lt := (canonicalSuffixShift_spec_unique v 1 (by omega) (by decide)).1
    rw [hrec, hcongr1458 (parityWeight v) (canonicalSuffixShift v 1) hw_v ha_lt]
    exact hmem486 ⟨canonicalSuffixShift v 1 % 486, Nat.mod_lt _ (by decide)⟩
  have hlen10_512 : ∀ (u : List Bool) (q : Nat),
      IsCoreParityWord u -> u.length ≥ 10 ->
      isSurvivingMod512Bool (exactBackwardQuotient 1 u q % 512) = true ->
      parityWeight u ≥ 7 ∧ canonicalSuffixShift u 1 % 1458 ∈ survivingMod1458List := by
    intro u q hu hlen10 hb512
    rcases list_eq_append_true_of_reverse_head u hu.2 with ⟨pre, rfl⟩
    have hpre_ge9 : pre.length ≥ 9 := by
      rw [List.length_append, List.length_singleton] at hlen10; omega
    let p9 := pre.take 9
    let fb := pre.drop 9
    have hp9_len : p9.length = 9 := take_len_of_ge_w13 9 pre hpre_ge9
    have hpre_sp : p9 ++ fb = pre := take_drop_split_eq_w13 9 pre
    have hu' : IsCoreParityWord (p9 ++ fb ++ [true]) := by rwa [hpre_sp]
    have hb512' : isSurvivingMod512Bool (exactBackwardQuotient 1 (p9 ++ fb ++ [true]) q % 512) = true := by
      rwa [hpre_sp]
    let r := exactBackwardQuotient 1 (p9 ++ fb ++ [true]) q % 512
    have hr_lt : r < 512 := Nat.mod_lt _ (by decide)
    have hp9_eq : parityOfIter 9 r = p9 := len10_core_mod512_prefix9 p9 fb q hp9_len hu'
    have hw7_auto : parityWeight (parityOfIter 9 r ++ fb ++ [true]) ≥ 7 :=
      (surviving_mod512_nine_prefix_auto_weight_and_characterization.1 r hr_lt hb512').2.2.2 fb q |>.2.1
    rw [hp9_eq, hpre_sp] at hw7_auto
    exact ⟨hw7_auto, hconf7 (pre ++ [true]) hu hw7_auto⟩
  refine ⟨⟨hcongr1458, by decide, hinj486, hmem486⟩, ⟨hconf7, hlen10_512, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · intro u q hu hlen10 hcls
    exact hlen10_512 u q hu hlen10 (survivingMod512_imp_bool_true _ hcls.1)
  · intro pref hwp
    let t6 : List Bool := List.replicate 6 true
    have hap1 := iterMarkovShift_append_canonical t6 pref hwp
    have ha_lt := (canonicalSuffixShift_spec_unique pref 1 hwp (by decide)).1
    by_cases hpar : canonicalSuffixShift pref 1 % 2 = 0
    · right
      have hbase0 : canonicalSuffixShift [true, false] 1 % 2 = 0 := by decide
      have hap0 := iterMarkovShift_append_canonical t6 [true, false] (by decide)
      change canonicalSuffixShift ([true, false] ++ t6) 1 =
        iterMarkovShift t6 1 (canonicalSuffixShift [true, false] 1) at hap0
      have hc := iterMarkovShift_congr_mod_pow3 t6 0 (parityWeight pref) 1
        (canonicalSuffixShift pref 1) (canonicalSuffixShift [true, false] 1)
        hwp (by decide) ha_lt (by decide)
        (by simp only [Nat.pow_zero, Nat.mul_one]; exact hpar.trans hbase0.symm)
      rw [← hap1, ← hap0] at hc
      have hv : canonicalSuffixShift ([true, false] ++ t6) 1 % 1458 = 1215 := by decide
      exact hc.trans hv
    · left
      have hodd : canonicalSuffixShift pref 1 % 2 = 1 := by omega
      have hbase1 : canonicalSuffixShift [true] 1 % 2 = 1 := by decide
      have hap1' := iterMarkovShift_append_canonical t6 [true] (by decide)
      change canonicalSuffixShift ([true] ++ t6) 1 =
        iterMarkovShift t6 1 (canonicalSuffixShift [true] 1) at hap1'
      have hc := iterMarkovShift_congr_mod_pow3 t6 0 (parityWeight pref) 1
        (canonicalSuffixShift pref 1) (canonicalSuffixShift [true] 1)
        hwp (by decide) ha_lt (by decide)
        (by simp only [Nat.pow_zero, Nat.mul_one]; exact hodd.trans hbase1.symm)
      rw [← hap1, ← hap1'] at hc
      have hv : canonicalSuffixShift ([true] ++ t6) 1 % 1458 = 729 := by decide
      exact hc.trans hv
  · intro pref
    have ha1 := first_hit_q0_iff_shift_ge_three_and_pow3_ones.2.1 7 pref (by decide)
    have ha2 := canonicalSuffixShift_mod18_and_pow3_memory_annihilation.2.1 6 pref
      [true, false, true, true, true, true, true, true] (by decide)
    have hv2 : canonicalSuffixShift [true, false, true, true, true, true, true, true] 1 % 1458 = 1215 := by
      decide
    exact ⟨by simpa using ha1, by simpa using ha2.trans hv2⟩
  · intro tail w r0 hw7 hr0
    have hm1458 : (2 : Nat) * 3 ^ 6 = 1458 := by decide
    have hw_sub : w - 1 - 6 = w - 7 := by omega
    have heq := markovShift_mod18_bijection_and_multistep_fiber_equidistribution.2.2
      tail 6 w r0 (by omega) (by rw [hm1458]; exact hr0)
    dsimp only at heq ⊢
    rwa [hm1458, hw_sub] at heq

-- ----------------------------------------------------------------------------
-- Section 3B: Empty Surviving Dyadic Window `M = 5` (`[32, 64)`) vs `M = 4` (`27`)
--             & `M = 6` (`111, 127`) Complete Classification (Choice-Free, `W13_H4`)
-- ----------------------------------------------------------------------------

set_option maxRecDepth 65536 in
private theorem m5_bool_all_false :
    ∀ x : Fin 32, isSurvivingMod373248Bool (32 + x.val) = false := by
  decide

set_option maxRecDepth 65536 in
private theorem m4_bool_iff_27 :
    ∀ x : Fin 16, isSurvivingMod373248Bool (16 + x.val) = true ↔ 16 + x.val = 27 := by
  decide

set_option maxRecDepth 65536 in
private theorem m6_bool_iff_111_127 :
    ∀ x : Fin 64,
      isSurvivingMod373248Bool (64 + x.val) = true ↔ (64 + x.val = 111 ∨ 64 + x.val = 127) := by
  decide

private theorem filter_m5_empty_of_surv_map :
    ∀ ws : List (List Bool),
      ((ws.filter (fun u =>
          isFirstHitOneQ0Bool u && isSurvivingMod373248Bool (exactBackwardQuotient 1 u 0))).map
          (fun u => exactBackwardQuotient 1 u 0)).filter
        (fun y => decide (2 ^ 5 ≤ y ∧ y < 2 ^ 6)) = []
  | [] => rfl
  | u :: rest => by
    have ih := filter_m5_empty_of_surv_map rest
    simp only [List.filter]
    cases hb : (isFirstHitOneQ0Bool u && isSurvivingMod373248Bool (exactBackwardQuotient 1 u 0)) with
    | false => exact ih
    | true =>
      simp only [List.map, List.filter]
      let y := exactBackwardQuotient 1 u 0
      cases hd : decide (2 ^ 5 ≤ y ∧ y < 2 ^ 6) with
      | false => exact ih
      | true =>
        rcases of_decide_eq_true hd with ⟨hlo, hhi⟩
        have hsurv : isSurvivingMod373248Bool y = true := by
          cases h1 : isFirstHitOneQ0Bool u <;> simp [h1] at hb
          exact hb
        have hf := m5_bool_all_false ⟨y - 32, by dsimp only [y] at hlo hhi; omega⟩
        dsimp only at hf
        rw [show 32 + (y - 32) = y by dsimp only [y] at hlo; omega] at hf
        rw [hsurv] at hf
        cases hf

set_option maxRecDepth 65536 in
/--
  Theorem W13.4b (`dyadic_m5_empty_window_and_m4_m6_certs`, choice-free `zero custom axioms`):
  Universal Empty Surviving Dyadic Window `M = 5` (`[32, 64)`) Refuting All-Scale `M >= 4`
  Non-Emptiness vs Exact `M = 4` (`27`) & `M = 6` (`111, 127`) Window Classification (`Branch P5.3`, `W13_H4`):
  1. **Complete `M = 5` (`[32, 64)`) Surviving-Class Vacuum**:
     EVERY integer `y ∈ [32, 64)` violates `IsSurvivingMod373248Class y` (`isSurvivingMod373248Bool y = false`)!
  2. **Universal Length-Independent Empty Window (`forall L_max : Nat`)**:
       `dyadicWindowSurvivingQ0Leaves L_max 5 = []`!
  3. **Exact `M = 4` (`[16, 32) -> {27}`) & `M = 6` (`[64, 128) -> {111, 127}`) Window Classification**:
     - Across `[16, 32)` (`M = 4`), `27` (`collatzIter 70 27 = 1`, `firstHitStepsAux 70 27 = 70`) is the
       UNIQUE `Mod373248`-surviving integer;
     - Across `[64, 128)` (`M = 6`), `111` (`collatzIter 45 111 = 1`, `firstHitStepsAux 45 111 = 45`) and
       `127` (`collatzIter 31 127 = 1`, `firstHitStepsAux 31 127 = 31`) are the EXACT TWO `Mod373248`-surviving integers!
-/
theorem dyadic_m5_empty_window_and_m4_m6_certs :
    (∀ y : Nat, 32 ≤ y -> y < 64 ->
      ¬ IsSurvivingMod373248Class y ∧ isSurvivingMod373248Bool y = false) ∧
    (∀ L_max : Nat, dyadicWindowSurvivingQ0Leaves L_max 5 = []) ∧
    ((∀ y : Nat, 16 ≤ y -> y < 32 -> (isSurvivingMod373248Bool y = true ↔ y = 27)) ∧
     collatzIter 70 27 = 1 ∧ firstHitStepsAux 70 27 = 70 ∧
     (∀ y : Nat, 64 ≤ y -> y < 128 -> (isSurvivingMod373248Bool y = true ↔ (y = 111 ∨ y = 127))) ∧
     collatzIter 45 111 = 1 ∧ firstHitStepsAux 45 111 = 45 ∧
     collatzIter 31 127 = 1 ∧ firstHitStepsAux 31 127 = 31) := by
  refine ⟨?_, ?_, ⟨?_, by decide, by decide, ?_, by decide, by decide, by decide, by decide⟩⟩
  · intro y h32 h64
    have hbf : isSurvivingMod373248Bool y = false := by
      have h := m5_bool_all_false ⟨y - 32, by omega⟩
      dsimp only at h
      rwa [show 32 + (y - 32) = y by omega] at h
    refine ⟨?_, hbf⟩
    rintro ⟨⟨_, h64_res, _, h128_59, _, h256_39, h256_63, _⟩, ⟨_, h3_2, _⟩⟩
    have hm512 : y % 512 = y := Nat.mod_eq_of_lt (by omega)
    have hm729 : y % 729 = y := Nat.mod_eq_of_lt (by omega)
    rw [hm512] at h64_res h128_59 h256_39 h256_63
    rw [hm729] at h3_2
    have hm64 : y % 64 = y := Nat.mod_eq_of_lt h64
    rw [hm64] at h64_res
    rcases h64_res with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  · intro L_max
    unfold dyadicWindowSurvivingQ0Leaves firstHitSurvivingQ0LeavesUpToLen
    exact filter_m5_empty_of_surv_map (allCoreWordsUpToLen L_max)
  · intro y h16 h32
    have h := m4_bool_iff_27 ⟨y - 16, by omega⟩
    dsimp only at h
    rwa [show 16 + (y - 16) = y by omega] at h
  · intro y h64 h128
    have h := m6_bool_iff_111_127 ⟨y - 64, by omega⟩
    dsimp only at h
    rwa [show 64 + (y - 64) = y by omega] at h

-- ----------------------------------------------------------------------------
-- Section 3C: Unconditional Constructive Lower-Bound Dyadic-Window Occupancy
--             (`uWin M j`, `(dyadicWindowSurvivingQ0Leaves (M + 15) M).length >= R`, `W13_H4`)
-- ----------------------------------------------------------------------------

/-- Explicit two-zero-run core parity word family `1^9 ++ 0^k1 ++ [1] ++ 0^k2 ++ [1]`
    realizing `R` pairwise-distinct surviving `Mod373248` first-hit `q = 0` leaves inside `[2^M, 2^(M+1))`
    at scale `L = M + 15`, weight `w = 11`, and canonical shift `a = 3` (`y % 512 = 511, y % 81 = 1`). -/
def uWin (M j : Nat) : List Bool :=
  let S := M + 4
  let rhs14 := (5 * 2 ^ (10 + S) - 116562) % 3 ^ 14
  let e_base := dlog2ShiftModPow3 14 512 rhs14
  let k1 := e_base + j * 3188646
  let k2 := S - k1
  List.replicate 9 true ++ List.replicate k1 false ++ [true] ++ List.replicate k2 false ++ [true]

private def uTwoZero (k1 k2 : Nat) : List Bool :=
  List.replicate 9 true ++ List.replicate k1 false ++ [true] ++ List.replicate k2 false ++ [true]

set_option maxRecDepth 65536 in
private theorem uTwoZero_core_len_wt_carry (k1 k2 : Nat) :
    IsCoreParityWord (uTwoZero k1 k2) ∧
    (uTwoZero k1 k2).length = 11 + (k1 + k2) ∧
    parityWeight (uTwoZero k1 k2) = 11 ∧
    affineCarry (uTwoZero k1 k2) = 172539 + 1536 * 2 ^ k1 + 2 ^ (10 + (k1 + k2)) := by
  let p9 := List.replicate 9 true
  let s1 := p9 ++ List.replicate k1 false
  let s2 := s1 ++ [true]
  let s3 := s2 ++ List.replicate k2 false
  have hp9_len : p9.length = 9 := rfl
  have hp9_wt : parityWeight p9 = 9 := rfl
  have hp9_car : affineCarry p9 = 19171 := by decide
  rcases affineCarry_append_replicate_false p9 k1 with ⟨hs1_wt, hs1_car⟩
  change parityWeight s1 = parityWeight p9 at hs1_wt
  change affineCarry s1 = affineCarry p9 at hs1_car
  rw [hp9_wt] at hs1_wt
  rw [hp9_car] at hs1_car
  have hs1_len : s1.length = 9 + k1 := by
    dsimp only [s1]; rw [List.length_append, hp9_len, List.length_replicate]
  have hs2_wt : parityWeight s2 = 10 := by
    dsimp only [s2]; rw [parityWeight_append, hs1_wt]; rfl
  have hs2_len : s2.length = 10 + k1 := by
    dsimp only [s2]; rw [List.length_append, hs1_len, List.length_singleton]; omega
  have hs2_car : affineCarry s2 = 57513 + 512 * 2 ^ k1 := by
    dsimp only [s2]
    rw [affineCarry_append, hs1_car, hs1_len, Nat.pow_add 2 9 k1]
    have hc1 : affineCarry [true] = 1 := rfl
    have hw1 : parityWeight [true] = 1 := rfl
    rw [hc1, hw1]; omega
  rcases affineCarry_append_replicate_false s2 k2 with ⟨hs3_wt, hs3_car⟩
  change parityWeight s3 = parityWeight s2 at hs3_wt
  change affineCarry s3 = affineCarry s2 at hs3_car
  rw [hs2_wt] at hs3_wt
  rw [hs2_car] at hs3_car
  have hs3_len : s3.length = 10 + (k1 + k2) := by
    dsimp only [s3]; rw [List.length_append, hs2_len, List.length_replicate]; omega
  have hu_eq : uTwoZero k1 k2 = s3 ++ [true] := rfl
  have hcore : IsCoreParityWord (uTwoZero k1 k2) := by
    refine ⟨rfl, ?_⟩
    rw [hu_eq, List.reverse_append]; rfl
  have hlen : (uTwoZero k1 k2).length = 11 + (k1 + k2) := by
    rw [hu_eq, List.length_append, hs3_len, List.length_singleton]; omega
  have hwt : parityWeight (uTwoZero k1 k2) = 11 := by
    rw [hu_eq, parityWeight_append, hs3_wt]; rfl
  have hcar : affineCarry (uTwoZero k1 k2) = 172539 + 1536 * 2 ^ k1 + 2 ^ (10 + (k1 + k2)) := by
    rw [hu_eq, affineCarry_append, hs3_car, hs3_len]
    have hc1 : affineCarry [true] = 1 := rfl
    have hw1 : parityWeight [true] = 1 := rfl
    rw [hc1, hw1]; omega
  exact ⟨hcore, hlen, hwt, hcar⟩

private theorem isSurvivingMod373248_of_511_and_1 (y : Nat)
    (h512 : y % 512 = 511) (h81 : y % 81 = 1) :
    isSurvivingMod373248Bool y = true ∧ IsSurvivingMod373248Class y := by
  let r729 := y % 729
  have hr_lt : r729 < 729 := Nat.mod_lt y (by decide)
  have hr_m81 : r729 % 81 = 1 := by
    dsimp only [r729]
    have hdvd81 : 81 ∣ 729 := ⟨9, by decide⟩
    rw [Nat.mod_mod_of_dvd y hdvd81, h81]
  have hb729 : isSurvivingMod729Bool (y % 729) = true := by
    change isSurvivingMod729Bool r729 = true
    unfold isSurvivingMod729Bool
    simp only [Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, decide_eq_true_eq]
    omega
  have hb512 : isSurvivingMod512Bool (y % 512) = true := by rw [h512]; decide
  have hb373 : isSurvivingMod373248Bool y = true := by
    unfold isSurvivingMod373248Bool; rw [hb512, hb729]; rfl
  exact ⟨hb373, isSurvivingMod373248Bool_imp_class y hb373⟩

private def eraseAllNatW13 (b : Nat) : List Nat -> List Nat
  | [] => []
  | x :: xs => if x = b then eraseAllNatW13 b xs else x :: eraseAllNatW13 b xs

private theorem mem_eraseAllNatW13_iff (b : Nat) :
    ∀ (xs : List Nat) (v : Nat), v ∈ eraseAllNatW13 b xs ↔ (v ∈ xs ∧ v ≠ b)
  | [], _ => by simp [eraseAllNatW13]
  | x :: xs, v => by
    simp only [eraseAllNatW13]
    by_cases hxb : x = b
    · simp only [hxb, ite_true, mem_eraseAllNatW13_iff b xs v, List.mem_cons]
      constructor
      · rintro ⟨hm, hne⟩; exact ⟨Or.inr hm, hne⟩
      · rintro ⟨rfl | hm, hne⟩
        · exact False.elim (hne rfl)
        · exact ⟨hm, hne⟩
    · simp only [hxb, ite_false, List.mem_cons, mem_eraseAllNatW13_iff b xs v]
      constructor
      · rintro (rfl | ⟨hm, hne⟩)
        · exact ⟨Or.inl rfl, hxb⟩
        · exact ⟨Or.inr hm, hne⟩
      · rintro ⟨rfl | hm, hne⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨hm, hne⟩

private theorem eraseAllNatW13_of_not_mem (b : Nat) :
    ∀ (xs : List Nat), b ∉ xs -> eraseAllNatW13 b xs = xs
  | [], _ => rfl
  | x :: xs, hnm => by
    have hxb : x ≠ b := fun h => hnm (h ▸ List.Mem.head _)
    have hnm_xs : b ∉ xs := fun hm => hnm (List.mem_cons_of_mem _ hm)
    simp only [eraseAllNatW13, hxb, ite_false, eraseAllNatW13_of_not_mem b xs hnm_xs]

private theorem nodup_eraseAllNatW13_and_len (b : Nat) :
    ∀ (xs : List Nat),
      NoDupNat xs -> NoDupNat (eraseAllNatW13 b xs) ∧ xs.length ≤ (eraseAllNatW13 b xs).length + 1
  | [], _ => ⟨NoDupNat.nil, by simp [eraseAllNatW13]⟩
  | x :: xs, NoDupNat.cons _ _ hnx hnd => by
    by_cases hxb : x = b
    · subst hxb
      simp only [eraseAllNatW13, ite_true, eraseAllNatW13_of_not_mem x xs hnx, List.length_cons]
      exact ⟨hnd, Nat.le_refl _⟩
    · rcases nodup_eraseAllNatW13_and_len b xs hnd with ⟨hnd_er, hlen_er⟩
      simp only [eraseAllNatW13, hxb, ite_false, List.length_cons]
      have hnx_er : x ∉ eraseAllNatW13 b xs :=
        fun hm => hnx ((mem_eraseAllNatW13_iff b xs x).mp hm).1
      exact ⟨NoDupNat.cons x _ hnx_er hnd_er, by omega⟩

private theorem noDupNat_length_le_of_subset :
    ∀ (cands xs : List Nat),
      NoDupNat xs -> (∀ y ∈ xs, y ∈ cands) -> xs.length ≤ cands.length
  | [], [], _, _ => Nat.le_refl 0
  | [], x :: _, _, hsub => by cases hsub x (List.Mem.head _)
  | b :: bs, xs, hnd, hsub => by
    rcases nodup_eraseAllNatW13_and_len b xs hnd with ⟨hnd', hlen'⟩
    have hsub' : ∀ y ∈ eraseAllNatW13 b xs, y ∈ bs := by
      intro y hy
      rcases (mem_eraseAllNatW13_iff b xs y).mp hy with ⟨hy_xs, hne⟩
      rcases List.mem_cons.mp (hsub y hy_xs) with rfl | hbs
      · exact False.elim (hne rfl)
      · exact hbs
    have ih := noDupNat_length_le_of_subset bs (eraseAllNatW13 b xs) hnd' hsub'
    simp only [List.length_cons]; omega

private def descIdxList : Nat -> List Nat
  | 0 => []
  | r + 1 => r :: descIdxList r

private theorem descIdxList_spec :
    ∀ r : Nat,
      (descIdxList r).length = r ∧
      NoDupNat (descIdxList r) ∧
      (∀ j ∈ descIdxList r, j < r)
  | 0 => ⟨rfl, NoDupNat.nil, fun _ hm => by cases hm⟩
  | r + 1 => by
    rcases descIdxList_spec r with ⟨hlen, hnd, hlt⟩
    have hnot_mem : r ∉ descIdxList r := fun hm => Nat.lt_irrefl r (hlt r hm)
    refine ⟨by simp [descIdxList, hlen], NoDupNat.cons r _ hnot_mem hnd, ?_⟩
    intro j hj
    rcases List.mem_cons.mp hj with rfl | hm
    · omega
    · have := hlt j hm; omega

private theorem noDupNat_map_inj_on (f : Nat -> Nat) :
    ∀ (js : List Nat),
      NoDupNat js ->
      (∀ a ∈ js, ∀ b ∈ js, f a = f b -> a = b) ->
      NoDupNat (js.map f)
  | [], _, _ => NoDupNat.nil
  | j :: js, NoDupNat.cons _ _ hnj hnd, hinj => by
    refine NoDupNat.cons (f j) (js.map f) ?_
      (noDupNat_map_inj_on f js hnd (fun a ha b hb =>
        hinj a (List.mem_cons_of_mem j ha) b (List.mem_cons_of_mem j hb)))
    intro hm
    rcases List.mem_map.mp hm with ⟨j', hj', heq⟩
    have hj_eq := hinj j' (List.mem_cons_of_mem j hj') j (List.Mem.head _) heq
    exact hnj (hj_eq ▸ hj')

private theorem pow2_inj_nat_w13 (a b : Nat) (heq : 2 ^ a = 2 ^ b) : a = b := by
  by_cases hlt1 : a < b
  · exfalso
    have hsp : 2 ^ b = 2 ^ (b - a) * 2 ^ a := by
      rw [← Nat.pow_add, show b - a + a = b by omega]
    have hge2 : 2 ^ (b - a) ≥ 2 := by simpa using pow2_mono_nat (show 1 ≤ b - a by omega)
    have hp_pos : 2 ^ a ≥ 1 := pow2_pos_nat a
    have hm := Nat.mul_le_mul_right (2 ^ a) hge2
    omega
  · by_cases hlt2 : b < a
    · exfalso
      have hsp : 2 ^ a = 2 ^ (a - b) * 2 ^ b := by
        rw [← Nat.pow_add, show a - b + b = a by omega]
      have hge2 : 2 ^ (a - b) ≥ 2 := by simpa using pow2_mono_nat (show 1 ≤ a - b by omega)
      have hp_pos : 2 ^ b ≥ 1 := pow2_pos_nat b
      have hm := Nat.mul_le_mul_right (2 ^ b) hge2
      omega
    · omega

set_option maxRecDepth 131072 in
/--
  Theorem W13.4c (`dyadic_window_constructive_lower_bound_unbounded_occupancy`, `zero custom axioms`):
  Unconditional Constructive Two-Zero-Run Surviving Family `uWin M j` & Unbounded Lower-Bound
  Dyadic-Window Occupancy (`Branches P2.2 & P5.3`, `W13_H4`):
  For EVERY target occupancy `R >= 1` and EVERY dyadic window scale `M >= R * 3188646` (`3188646 = 2 * 3^13`):
  1. **Explicit Surviving First-Hit Family (`forall j < R`)**:
     Each word `u := uWin M j` satisfies:
     - `IsFirstHitOnePair u 0`, `u.length = M + 15`, `parityWeight u = 11`, `canonicalSuffixShift u 1 = 3`, AND
     - `y := exactBackwardQuotient 1 u 0` satisfies `y % 512 = 511`, `y % 81 = 1`,
       `IsSurvivingMod373248Class y`, `2 ^ M <= y ∧ y < 2 ^ (M + 1)`,
       `y ∈ dyadicWindowSurvivingQ0Leaves (M + 15) M`, and
       `∀ L_max >= M + 15, y ∈ dyadicWindowSurvivingQ0Leaves L_max M`!
  2. **Pairwise Leaf Distinctness (`forall j1 < R, forall j2 < R`)**:
     `exactBackwardQuotient 1 (uWin M j1) 0 = exactBackwardQuotient 1 (uWin M j2) 0 -> j1 = j2`!
  3. **Unconditional Unbounded Window Occupancy Lower Bound (`forall L_max >= M + 15`)**:
       `(dyadicWindowSurvivingQ0Leaves (M + 15) M).length >= R` AND
       `∀ L_max >= M + 15, (dyadicWindowSurvivingQ0Leaves L_max M).length >= R`
     — proving constructively that surviving first-hit `q = 0` occupancy inside `[2^M, 2^(M+1))` across
     every horizon `L_max >= M + 15` grows without bound as `M -> infty`!
-/
theorem dyadic_window_constructive_lower_bound_unbounded_occupancy
    (R M : Nat) (hR : R ≥ 1) (hM : M ≥ R * 3188646) :
    (∀ j : Nat, j < R ->
      let u := uWin M j
      let y := exactBackwardQuotient 1 u 0
      IsFirstHitOnePair u 0 ∧
      u.length = M + 15 ∧
      parityWeight u = 11 ∧
      canonicalSuffixShift u 1 = 3 ∧
      y % 512 = 511 ∧
      y % 81 = 1 ∧
      IsSurvivingMod373248Class y ∧
      2 ^ M ≤ y ∧ y < 2 ^ (M + 1) ∧
      y ∈ dyadicWindowSurvivingQ0Leaves (M + 15) M ∧
      (∀ L_max : Nat, L_max ≥ M + 15 -> y ∈ dyadicWindowSurvivingQ0Leaves L_max M)) ∧
    (∀ j1 j2 : Nat, j1 < R -> j2 < R ->
      exactBackwardQuotient 1 (uWin M j1) 0 = exactBackwardQuotient 1 (uWin M j2) 0 ->
      j1 = j2) ∧
    ((dyadicWindowSurvivingQ0Leaves (M + 15) M).length ≥ R ∧
     ∀ L_max : Nat, L_max ≥ M + 15 -> (dyadicWindowSurvivingQ0Leaves L_max M).length ≥ R) := by
  let S := M + 4
  let A_num := 5 * 2 ^ (10 + S) - 116562
  rcases (⟨A_num % 3 ^ 14, rfl⟩ : ∃ r0 : Nat, r0 = A_num % 3 ^ 14) with ⟨rhs14, hrhs_def⟩
  have h311_val : (3 : Nat) ^ 11 = 177147 := by decide
  have hp13_val : 2 * 3 ^ (14 - 1) = 3188646 := by decide
  have h214_val : (2 : Nat) ^ 14 = 16384 := by decide
  have h218_val : (2 : Nat) ^ 18 = 262144 := by decide
  have hM_ge6 : M ≥ 6 := by
    have hm1 : 1 * 3188646 ≤ R * 3188646 := Nat.mul_le_mul_right 3188646 hR
    rw [Nat.one_mul] at hm1
    exact Nat.le_trans (by decide : 6 ≤ 3188646) (Nat.le_trans hm1 hM)
  have hPM_ge64 : 2 ^ M ≥ 64 := by
    have hc : (2 : Nat) ^ 6 = 64 := by decide
    rw [← hc]; exact pow2_mono_nat hM_ge6
  have hp10S_eq : 2 ^ (10 + S) = 16384 * 2 ^ M := by
    dsimp only [S]
    rw [show 10 + (M + 4) = 14 + M by omega, Nat.pow_add 2 14 M, h214_val]
  have hp10S_gt : 5 * 2 ^ (10 + S) > 116562 := by
    rw [hp10S_eq]
    have hm64 : 16384 * 64 ≤ 16384 * 2 ^ M := Nat.mul_le_mul_left 16384 hPM_ge64
    have hm5 : 5 * (16384 * 64) ≤ 5 * (16384 * 2 ^ M) := Nat.mul_le_mul_left 5 hm64
    exact Nat.lt_of_lt_of_le (by decide : 116562 < 5 * (16384 * 64)) hm5
  have hrhs_n3 : rhs14 % 3 ≠ 0 := by
    have hA_m3 : A_num % 3 ≠ 0 := by
      have hp_m3 := pow2_mod3_nonzero_w5 (10 + S)
      have h116 : (116562 : Nat) = 3 * 38854 := by decide
      have hrew : 5 * 2 ^ (10 + S) = A_num + 3 * 38854 := by
        dsimp only [A_num]
        rw [← h116, Nat.sub_add_cancel (Nat.le_of_lt hp10S_gt)]
      intro h0
      have hm5 : (5 * 2 ^ (10 + S)) % 3 = 0 := by
        rw [hrew, Nat.add_mul_mod_self_left, h0]
      rw [Nat.mul_mod] at hm5
      have hlt3 : 2 ^ (10 + S) % 3 < 3 := Nat.mod_lt _ (by decide)
      have h12 : 2 ^ (10 + S) % 3 = 1 ∨ 2 ^ (10 + S) % 3 = 2 := by
        clear hrhs_def h311_val hp13_val h214_val h218_val hp10S_eq hp10S_gt h116 hrew hm5 h0
        omega
      rcases h12 with h1 | h2
      · rw [h1] at hm5; cases hm5
      · rw [h2] at hm5; cases hm5
    have hdvd3_14 : 3 ∣ 3 ^ 14 := ⟨3 ^ 13, by decide⟩
    rw [hrhs_def, Nat.mod_mod_of_dvd A_num hdvd3_14]
    exact hA_m3
  have hspec14 := dlog2ShiftModPow3_spec_unique 14 512 rhs14 (by decide) (by decide) hrhs_n3
  dsimp only at hspec14
  rcases hspec14 with ⟨heb_lt_raw, _, heb_per_raw, _⟩
  rcases (⟨dlog2ShiftModPow3 14 512 rhs14, rfl⟩ :
      ∃ eb : Nat, eb = dlog2ShiftModPow3 14 512 rhs14) with ⟨e_base, heb_def⟩
  have heb_lt' : e_base < 3188646 := by
    rw [← heb_def, hp13_val] at heb_lt_raw; exact heb_lt_raw
  have heb_per : ∀ q : Nat, (2 ^ (e_base + q * 3188646) * 512) % 3 ^ 14 = rhs14 % 3 ^ 14 := by
    intro q
    have hp := heb_per_raw q
    rwa [← heb_def, hp13_val] at hp
  have huWin_eq : ∀ j : Nat,
      uWin M j = uTwoZero (e_base + j * 3188646) (S - (e_base + j * 3188646)) := by
    intro j; unfold uWin uTwoZero; dsimp only; rw [← hrhs_def, ← heb_def]
  clear heb_lt_raw heb_per_raw heb_def
  have hper_j : ∀ j : Nat, j < R ->
      let k1 := e_base + j * 3188646
      let u := uWin M j
      let y := exactBackwardQuotient 1 u 0
      k1 < M ∧
      u = uTwoZero k1 (S - k1) ∧
      IsFirstHitOnePair u 0 ∧
      u.length = M + 15 ∧
      parityWeight u = 11 ∧
      canonicalSuffixShift u 1 = 3 ∧
      y % 512 = 511 ∧
      y % 81 = 1 ∧
      isSurvivingMod373248Bool y = true ∧
      IsSurvivingMod373248Class y ∧
      2 ^ M ≤ y ∧ y < 2 ^ (M + 1) ∧
      (∀ L_max : Nat, L_max ≥ M + 15 -> y ∈ dyadicWindowSurvivingQ0Leaves L_max M) := by
    intro j hj_lt
    dsimp only
    let k1 := e_base + j * 3188646
    let k2 := S - k1
    have hk1_lt_M : k1 < M := by
      have hj1_le : (j + 1) * 3188646 ≤ R * 3188646 := Nat.mul_le_mul_right 3188646 (by omega)
      rw [Nat.add_mul, Nat.one_mul] at hj1_le
      have hlt_step : e_base + j * 3188646 < j * 3188646 + 3188646 := by
        rw [Nat.add_comm (j * 3188646)]
        exact Nat.add_lt_add_right heb_lt' (j * 3188646)
      exact Nat.lt_of_lt_of_le hlt_step (Nat.le_trans hj1_le hM)
    have hk_sum : k1 + k2 = S := by dsimp only [k2, S]; omega
    have hu_def : uWin M j = uTwoZero k1 k2 := huWin_eq j
    rcases uTwoZero_core_len_wt_carry k1 k2 with ⟨hcore, hlen_tz, hwt_tz, hcar_tz⟩
    rw [← hu_def] at hcore hlen_tz hwt_tz hcar_tz
    rw [hk_sum] at hlen_tz hcar_tz
    have hlen_u : (uWin M j).length = M + 15 := by rw [hlen_tz]; dsimp only [S]; omega
    have hmod14 : (2 ^ k1 * 512) % 3 ^ 14 = A_num % 3 ^ 14 := by
      have hp := heb_per j
      rw [hrhs_def, Nat.mod_mod] at hp
      exact hp
    have hPk_le_PM : 2 ^ k1 ≤ 2 ^ M := pow2_mono_nat (Nat.le_of_lt hk1_lt_M)
    have hB_lt_A : 2 ^ k1 * 512 < A_num := by
      dsimp only [A_num]
      rw [hp10S_eq]
      have hm1 : 2 ^ k1 * 512 ≤ 2 ^ M * 512 := Nat.mul_le_mul_right 512 hPk_le_PM
      have hm2 : 2 ^ M * 512 + 116562 < 5 * (16384 * 2 ^ M) := by
        have hc116 : 116562 < 2000 * 64 := by decide
        have hc_pm : 116562 < 2000 * 2 ^ M :=
          Nat.lt_of_lt_of_le hc116 (Nat.mul_le_mul_left 2000 hPM_ge64)
        have hsum_le : 2 ^ M * 512 + 2000 * 2 ^ M ≤ 5 * (16384 * 2 ^ M) := by
          rw [Nat.mul_comm (2 ^ M) 512, ← Nat.add_mul, ← Nat.mul_assoc 5 16384]
          exact Nat.mul_le_mul_right (2 ^ M) (by decide : 512 + 2000 ≤ 5 * 16384)
        exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hc_pm _) hsum_le
      exact Nat.lt_sub_of_add_lt (Nat.lt_of_le_of_lt (Nat.add_le_add_right hm1 116562) hm2)
    have hdiff_mod14 : (A_num - 2 ^ k1 * 512) % 3 ^ 14 = 0 := by
      rcases (⟨3 ^ 14, rfl⟩ : ∃ P14 : Nat, P14 = 3 ^ 14) with ⟨P14, hP14⟩
      rw [← hP14] at hmod14 ⊢
      have hdmA := (Nat.div_add_mod A_num P14).symm
      have hdmB := (Nat.div_add_mod (2 ^ k1 * 512) P14).symm
      rw [hmod14] at hdmB
      have hq_le : (2 ^ k1 * 512) / P14 ≤ A_num / P14 :=
        Nat.div_le_div_right (Nat.le_of_lt hB_lt_A)
      have hsub_eq : A_num - 2 ^ k1 * 512 =
          P14 * (A_num / P14 - (2 ^ k1 * 512) / P14) := by
        rw [Nat.mul_sub_left_distrib]
        generalize P14 * (A_num / P14) = QA,
          P14 * ((2 ^ k1 * 512) / P14) = QB,
          A_num % P14 = rem, A_num = AN, 2 ^ k1 * 512 = BN at hdmA hdmB hB_lt_A ⊢
        omega
      rw [hsub_eq, Nat.mul_mod_right]
    rcases Nat.dvd_of_mod_eq_zero hdiff_mod14 with ⟨m, hm_eq⟩
    have hkey_eq : 2 ^ ((uWin M j).length + 3) =
        3 ^ 11 * (81 * m + 1) + affineCarry (uWin M j) := by
      have hp_lhs : 2 ^ ((uWin M j).length + 3) = 16 * 2 ^ (10 + S) := by
        rw [hlen_tz, show 11 + S + 3 = 4 + (10 + S) by omega, Nat.pow_add 2 4 (10 + S)]
      have hA_rec : A_num = 3 ^ 14 * m + 2 ^ k1 * 512 := by
        rw [← hm_eq, Nat.sub_add_cancel (Nat.le_of_lt hB_lt_A)]
      have h3A_lhs : 3 * A_num + 349686 = 15 * 2 ^ (10 + S) := by
        dsimp only [A_num]
        rw [Nat.mul_sub_left_distrib]
        have h3_116 : 3 * 116562 = 349686 := by decide
        have h3_5 : 3 * (5 * 2 ^ (10 + S)) = 15 * 2 ^ (10 + S) := by
          rw [← Nat.mul_assoc]
        rw [h3_116, h3_5]
        have hgt3 : 349686 ≤ 15 * 2 ^ (10 + S) := by
          rw [← h3_116, ← h3_5]
          exact Nat.mul_le_mul_left 3 (Nat.le_of_lt hp10S_gt)
        exact Nat.sub_add_cancel hgt3
      have h3_pow14 : 3 * (3 ^ 14 * m) = 3 ^ 11 * (81 * m) := by
        have hp15 : 3 * 3 ^ 14 = 3 ^ 11 * 81 := by decide
        rw [← Nat.mul_assoc 3 (3 ^ 14) m, hp15, Nat.mul_assoc]
      have h3_512 : 3 * (2 ^ k1 * 512) = 1536 * 2 ^ k1 := by
        rw [Nat.mul_comm (2 ^ k1) 512, ← Nat.mul_assoc]
      have h3A_rhs : 3 * A_num = 3 ^ 11 * (81 * m) + 1536 * 2 ^ k1 := by
        rw [hA_rec, Nat.mul_add, h3_pow14, h3_512]
      have h349_sp : (349686 : Nat) = 3 ^ 11 + 172539 := by decide
      rw [hp_lhs, hcar_tz]
      calc
        16 * 2 ^ (10 + S)
            = 15 * 2 ^ (10 + S) + 2 ^ (10 + S) := by
                rw [show (16 : Nat) = 15 + 1 from rfl, Nat.add_mul, Nat.one_mul]
        _ = (3 * A_num + 349686) + 2 ^ (10 + S) := by rw [← h3A_lhs]
        _ = (3 ^ 11 * (81 * m) + 1536 * 2 ^ k1) + (3 ^ 11 + 172539) + 2 ^ (10 + S) := by
              rw [h3A_rhs, h349_sp]
        _ = 3 ^ 11 * (81 * m + 1) + (172539 + 1536 * 2 ^ k1 + 2 ^ (10 + S)) := by
              rw [Nat.mul_add (3 ^ 11) (81 * m) 1, Nat.mul_one]
              ac_rfl
    have hsh3 : canonicalSuffixShift (uWin M j) 1 = 3 := by
      rcases canonicalSuffixShift_spec_unique (uWin M j) 1
        (by rw [hwt_tz]; decide) (by decide) with ⟨_, _, huniq⟩
      symm
      apply huniq 3
      · rw [hwt_tz]
        have hp10 := pow3_pos_nat 10
        omega
      · rw [Nat.mul_one, hwt_tz, hkey_eq, Nat.add_comm]
        exact Nat.add_mul_mod_self_left _ _ _
    have hfh : IsFirstHitOnePair (uWin M j) 0 :=
      (first_hit_q0_iff_shift_ge_three_and_pow3_ones.2.2 (uWin M j) hcore).mpr (by rw [hsh3]; decide)
    rcases (⟨exactBackwardQuotient 1 (uWin M j) 0, rfl⟩ :
        ∃ y0 : Nat, y0 = exactBackwardQuotient 1 (uWin M j) 0) with ⟨y, hy_def⟩
    have hy_81m1 : y = 81 * m + 1 := by
      rcases one_generator_pos_odd_and_reaches_one (uWin M j) 0 hcore with ⟨_, _, heq_bw, _⟩
      have hbw_steps : backwardOneTotalSteps (uWin M j) 0 = (uWin M j).length + 3 := by
        unfold backwardOneTotalSteps; rw [hsh3]; omega
      rw [hbw_steps, hwt_tz, ← hy_def] at heq_bw
      have hcomb : 3 ^ 11 * y = 3 ^ 11 * (81 * m + 1) :=
        Nat.add_right_cancel (heq_bw.symm.trans hkey_eq)
      exact Nat.eq_of_mul_eq_mul_left (pow3_pos_nat 11) hcomb
    have hy_m81 : y % 81 = 1 := by rw [hy_81m1]; omega
    have hy_m512 : y % 512 = 511 := by
      let fb_mid := List.replicate k1 false ++ [true] ++ List.replicate k2 false
      have hp9_511 : parityOfIter 9 511 = List.replicate 9 true := by decide
      have hu_split : uWin M j = parityOfIter 9 511 ++ fb_mid ++ [true] := by
        rw [hp9_511, hu_def]
        dsimp only [uTwoZero, fb_mid]
        simp only [List.append_assoc]
      have hm := (surviving_mod512_nine_prefix_auto_weight_and_characterization.1 511
        (by decide) (by decide)).2.2.2 fb_mid 0 |>.2.2.1
      rwa [← hu_split, ← hy_def] at hm
    rcases isSurvivingMod373248_of_511_and_1 y hy_m512 hy_m81 with ⟨hb_surv, hcls_surv⟩
    have hy_win : 2 ^ M ≤ y ∧ y < 2 ^ (M + 1) := by
      have hlhs_18 : 2 ^ ((uWin M j).length + 3) = 262144 * 2 ^ M := by
        rw [hlen_u, show M + 15 + 3 = 18 + M by omega, Nat.pow_add 2 18 M, h218_val]
      have heq_y : 177147 * y + (172539 + 1536 * 2 ^ k1 + 16384 * 2 ^ M) = 262144 * 2 ^ M := by
        have hk2 := hkey_eq.symm
        rwa [← hy_81m1, hlhs_18, h311_val, hcar_tz, hp10S_eq] at hk2
      have hPM_pos : 0 < 2 ^ M := pow2_pos_nat M
      refine ⟨?_, ?_⟩
      · by_cases hge : 2 ^ M ≤ y
        · exact hge
        · exfalso
          have hy_le : y ≤ 2 ^ M := Nat.le_of_lt (Nat.lt_of_not_le hge)
          have t1 : 177147 * y ≤ 177147 * 2 ^ M := Nat.mul_le_mul_left 177147 hy_le
          have t2 : 172539 ≤ 2769 * 2 ^ M :=
            Nat.le_trans (by decide : 172539 ≤ 2769 * 64) (Nat.mul_le_mul_left 2769 hPM_ge64)
          have t3 : 1536 * 2 ^ k1 ≤ 1536 * 2 ^ M := Nat.mul_le_mul_left 1536 hPk_le_PM
          have tsum : 262144 * 2 ^ M ≤ 197836 * 2 ^ M := by
            calc
              262144 * 2 ^ M
                  = 177147 * y + (172539 + 1536 * 2 ^ k1 + 16384 * 2 ^ M) := heq_y.symm
              _ ≤ 177147 * 2 ^ M + (2769 * 2 ^ M + 1536 * 2 ^ M + 16384 * 2 ^ M) :=
                    Nat.add_le_add t1 (Nat.add_le_add (Nat.add_le_add t2 t3) (Nat.le_refl _))
              _ = (177147 + 2769 + 1536 + 16384) * 2 ^ M := by
                    simp only [Nat.add_mul, Nat.add_assoc]
              _ = 197836 * 2 ^ M := by
                    rw [show (177147 : Nat) + 2769 + 1536 + 16384 = 197836 by decide]
          have hbad : 262144 ≤ 197836 := Nat.le_of_mul_le_mul_right tsum hPM_pos
          exact absurd hbad (by decide)
      · rw [Nat.pow_succ, Nat.mul_comm (2 ^ M) 2]
        by_cases hlt : y < 2 * 2 ^ M
        · exact hlt
        · exfalso
          have hy_ge : 2 * 2 ^ M ≤ y := Nat.le_of_not_lt hlt
          have t1 : 354294 * 2 ^ M ≤ 177147 * y := by
            have hmul : 177147 * (2 * 2 ^ M) ≤ 177147 * y := Nat.mul_le_mul_left 177147 hy_ge
            have h354 : (354294 : Nat) = 177147 * 2 := by decide
            rwa [← Nat.mul_assoc, ← h354] at hmul
          have t2 : 177147 * y ≤ 262144 * 2 ^ M := by
            rw [← heq_y]; exact Nat.le_add_right _ _
          have hbad : 354294 ≤ 262144 :=
            Nat.le_of_mul_le_mul_right (Nat.le_trans t1 t2) hPM_pos
          exact absurd hbad (by decide)
    have hy_mem_win : ∀ L_max : Nat, L_max ≥ M + 15 ->
        y ∈ dyadicWindowSurvivingQ0Leaves L_max M := by
      intro L_max hL_ge
      have hy_mem_fh : y ∈ firstHitSurvivingQ0LeavesUpToLen L_max :=
        (multiscale_first_hit_surviving_q0_leaves_nodup L_max).2.2 y |>.mpr
          ⟨uWin M j, hfh, by omega, hb_surv, hy_def.symm⟩
      unfold dyadicWindowSurvivingQ0Leaves
      exact List.mem_filter.mpr ⟨hy_mem_fh, decide_eq_true hy_win⟩
    rw [← hy_def]
    exact ⟨hk1_lt_M, hu_def, hfh, hlen_u, hwt_tz, hsh3, hy_m512, hy_m81,
           hb_surv, hcls_surv, hy_win.1, hy_win.2, hy_mem_win⟩
  have hinj_j : ∀ j1 j2 : Nat, j1 < R -> j2 < R ->
      exactBackwardQuotient 1 (uWin M j1) 0 = exactBackwardQuotient 1 (uWin M j2) 0 ->
      j1 = j2 := by
    intro j1 j2 hj1 hj2 hy_eq
    rcases hper_j j1 hj1 with ⟨hk1_1, hu1_eq, hfh1, _⟩
    rcases hper_j j2 hj2 with ⟨hk1_2, hu2_eq, hfh2, _⟩
    have hu_eq : uWin M j1 = uWin M j2 :=
      (first_hit_one_pair_sound_and_injective (uWin M j1) (uWin M j2) 0 0 hfh1 hfh2).2.2.2 hy_eq |>.1
    let k1_1 := e_base + j1 * 3188646
    let k1_2 := e_base + j2 * 3188646
    have hc1 := (uTwoZero_core_len_wt_carry k1_1 (S - k1_1)).2.2.2
    have hc2 := (uTwoZero_core_len_wt_carry k1_2 (S - k1_2)).2.2.2
    have hk1_1' : k1_1 < M := hk1_1
    have hk1_2' : k1_2 < M := hk1_2
    rw [show k1_1 + (S - k1_1) = S by dsimp only [S]; omega] at hc1
    rw [show k1_2 + (S - k1_2) = S by dsimp only [S]; omega] at hc2
    have hcar_eq : affineCarry (uTwoZero k1_1 (S - k1_1)) = affineCarry (uTwoZero k1_2 (S - k1_2)) := by
      rw [← hu1_eq, ← hu2_eq, hu_eq]
    rw [hc1, hc2] at hcar_eq
    have hp2_eq : 2 ^ k1_1 = 2 ^ k1_2 :=
      Nat.eq_of_mul_eq_mul_left (by decide : 0 < 1536)
        (Nat.add_left_cancel (Nat.add_right_cancel hcar_eq))
    have hk_eq : k1_1 = k1_2 := pow2_inj_nat_w13 k1_1 k1_2 hp2_eq
    dsimp only [k1_1, k1_2] at hk_eq
    exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 3188646) (Nat.add_left_cancel hk_eq)
  refine ⟨?_, hinj_j, ?_⟩
  · intro j hj
    rcases hper_j j hj with ⟨_, _, hfh, hlen, hwt, hsh, h512, h81, _, hcls, hlo, hhi, hmem⟩
    exact ⟨hfh, hlen, hwt, hsh, h512, h81, hcls, hlo, hhi, hmem (M + 15) (Nat.le_refl _), hmem⟩
  · rcases descIdxList_spec R with ⟨hd_len, hd_nd, hd_lt⟩
    let leavesR := (descIdxList R).map (fun j => exactBackwardQuotient 1 (uWin M j) 0)
    have hnd_R : NoDupNat leavesR :=
      noDupNat_map_inj_on _ (descIdxList R) hd_nd
        (fun a ha b hb heq => hinj_j a b (hd_lt a ha) (hd_lt b hb) heq)
    have hlen_R : leavesR.length = R := by dsimp only [leavesR]; rw [List.length_map, hd_len]
    have hall_L : ∀ L_max : Nat, L_max ≥ M + 15 ->
        (dyadicWindowSurvivingQ0Leaves L_max M).length ≥ R := by
      intro L_max hL_ge
      have hsub_R : ∀ y ∈ leavesR, y ∈ dyadicWindowSurvivingQ0Leaves L_max M := by
        intro y hy
        rcases List.mem_map.mp hy with ⟨j, hj, rfl⟩
        exact (hper_j j (hd_lt j hj)).2.2.2.2.2.2.2.2.2.2.2.2 L_max hL_ge
      have hle := noDupNat_length_le_of_subset
        (dyadicWindowSurvivingQ0Leaves L_max M) leavesR hnd_R hsub_R
      omega
    exact ⟨hall_L (M + 15) (Nat.le_refl _), hall_L⟩

end CollatzFormal
