/-
  CollatzFormal.lean
  Lean 4 Kernel-Verified Formalization of Core Algebraic, Inductive, Diophantine,
  Potential-Merger, Coalescence, Reflective Hensel, and Multi-Step Orbit-Drop Certificates
  for the `collatz_analysis` Proof Suite (Theorems 1–25).

  Zero external dependencies (pure Lean 4 Core), zero `sorry`, zero custom `axiom`.
-/

namespace CollatzFormal

-- ============================================================================
-- 1. Compressed Collatz Dynamics (over Nat and over Int) & Affine Carry
-- ============================================================================

/-- One step of the compressed Collatz (Terras) map T : Nat -> Nat -/
def collatzStep (n : Nat) : Nat :=
  if n % 2 == 0 then n / 2 else (3 * n + 1) / 2

/-- k-step iteration of the compressed Collatz map on Nat (tail-recursive) -/
def collatzIter : Nat -> Nat -> Nat
  | 0, n => n
  | k + 1, n => collatzIter k (collatzStep n)

/-- One step of the compressed Collatz (Terras) map T : Int -> Int (covers Z^+ and Z^-) -/
def collatzStepInt (x : Int) : Int :=
  if x % 2 == 0 then x / 2 else (3 * x + 1) / 2

/-- k-step iteration of the compressed Collatz map on Int (tail-recursive) -/
def collatzIterInt : Nat -> Int -> Int
  | 0, x => x
  | k + 1, x => collatzIterInt k (collatzStepInt x)

/-- Weight w(v) = number of odd steps (true entries) in a parity vector v -/
def parityWeight : List Bool -> Nat
  | [] => 0
  | false :: rest => parityWeight rest
  | true :: rest => 1 + parityWeight rest

/-- Inductive predicate asserting that x : Int realizes parity vector v step-by-step -/
def matchesParity : List Bool -> Int -> Prop
  | [], _ => True
  | false :: rest, x => x % 2 = 0 ∧ matchesParity rest (collatzStepInt x)
  | true :: rest, x => x % 2 = 1 ∧ matchesParity rest (collatzStepInt x)

/-- Affine Carry Polynomial C_k(v) over Nat -/
def affineCarryAux : List Bool -> Nat -> Nat -> Nat
  | [], _, acc => acc
  | false :: rest, j, acc => affineCarryAux rest (j + 1) acc
  | true :: rest, j, acc => affineCarryAux rest (j + 1) (3 * acc + 2 ^ j)

def affineCarry (v : List Bool) : Nat :=
  affineCarryAux v 0 0

/-- Affine Carry Polynomial C_k(v) over Int -/
def affineCarryAuxInt : List Bool -> Nat -> Int -> Int
  | [], _, acc => acc
  | false :: rest, j, acc => affineCarryAuxInt rest (j + 1) acc
  | true :: rest, j, acc => affineCarryAuxInt rest (j + 1) (3 * acc + (2 : Int) ^ j)

def affineCarryInt (v : List Bool) : Int :=
  affineCarryAuxInt v 0 0

/-- 1-Cycle parity vector of length k with w leading odd steps -/
def oneCycleVector (w k : Nat) : List Bool :=
  List.replicate w true ++ List.replicate (k - w) false

-- ============================================================================
-- 2. Inductive Exponential Inequalities (2^m <= 3^m and 2^(k+1) < 3^k)
-- ============================================================================

theorem pow2_le_pow3 : ∀ m : Nat, 2 ^ m ≤ 3 ^ m
  | 0 => by decide
  | m + 1 => by
    have ih := pow2_le_pow3 m
    have h1 : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ]; omega
    have h2 : 3 ^ (m + 1) = 3 * 3 ^ m := by rw [Nat.pow_succ]; omega
    omega

theorem pow2_succ_lt_pow3_shifted : ∀ n : Nat, 2 ^ (n + 3) < 3 ^ (n + 2)
  | 0 => by decide
  | n + 1 => by
    have ih := pow2_succ_lt_pow3_shifted n
    have h1 : 2 ^ (n + 1 + 3) = 2 * 2 ^ (n + 3) := by
      have heq : n + 1 + 3 = (n + 3) + 1 := by omega
      rw [heq, Nat.pow_succ]
      omega
    have h2 : 3 ^ (n + 1 + 2) = 3 * 3 ^ (n + 2) := by
      have heq : n + 1 + 2 = (n + 2) + 1 := by omega
      rw [heq, Nat.pow_succ]
      omega
    omega

theorem pow2_succ_lt_pow3 (k : Nat) (hk : k ≥ 2) : 2 ^ (k + 1) < 3 ^ k := by
  have h := pow2_succ_lt_pow3_shifted (k - 2)
  have hk1 : k - 2 + 3 = k + 1 := by omega
  have hk2 : k - 2 + 2 = k := by omega
  rw [hk1, hk2] at h
  exact h

-- ============================================================================
-- 3. Theorem 1.1, 1.3, 3, & 9: Universal k-Step Affine Decomposition over Z
-- ============================================================================

theorem collatzStepInt_even (y : Int) (h : y % 2 = 0) :
    2 * collatzStepInt y = y := by
  unfold collatzStepInt
  have hb : (y % 2 == 0) = true := by simp [h]
  rw [hb]
  simp
  omega

theorem collatzStepInt_odd (y : Int) (h : y % 2 = 1) :
    2 * collatzStepInt y = 3 * y + 1 := by
  unfold collatzStepInt
  have hne : y % 2 ≠ 0 := by omega
  have hb : (y % 2 == 0) = false := beq_false_of_ne hne
  rw [hb]
  simp
  omega

/-- Universal step-accumulator invariant for the k-step Collatz affine decomposition -/
theorem affine_aux_invariant :
    ∀ (v : List Bool) (j w0 : Nat) (x y acc : Int),
      matchesParity v y ->
      (2 : Int) ^ j * y = (3 : Int) ^ w0 * x + acc ->
      (2 : Int) ^ (j + v.length) * collatzIterInt v.length y =
        (3 : Int) ^ (w0 + parityWeight v) * x + affineCarryAuxInt v j acc
  | [], j, w0, x, y, acc, _, hinv => by
    simp [collatzIterInt, parityWeight, affineCarryAuxInt, hinv]
  | false :: rest, j, w0, x, y, acc, hpar, hinv => by
    rcases hpar with ⟨heven, hrest⟩
    have hstep : 2 * collatzStepInt y = y := collatzStepInt_even y heven
    have hnext : (2 : Int) ^ (j + 1) * collatzStepInt y = (3 : Int) ^ w0 * x + acc := by
      calc
        (2 : Int) ^ (j + 1) * collatzStepInt y
            = (2 : Int) ^ j * (2 * collatzStepInt y) := by rw [Int.pow_succ, Int.mul_assoc]
        _ = (2 : Int) ^ j * y := by rw [hstep]
        _ = (3 : Int) ^ w0 * x + acc := hinv
    have ih := affine_aux_invariant rest (j + 1) w0 x (collatzStepInt y) acc hrest hnext
    have hlen : j + (false :: rest).length = j + 1 + rest.length := by simp; omega
    simp only [parityWeight, affineCarryAuxInt]
    rw [hlen]
    exact ih
  | true :: rest, j, w0, x, y, acc, hpar, hinv => by
    rcases hpar with ⟨hodd, hrest⟩
    have hstep : 2 * collatzStepInt y = 3 * y + 1 := collatzStepInt_odd y hodd
    have hnext :
        (2 : Int) ^ (j + 1) * collatzStepInt y =
          (3 : Int) ^ (w0 + 1) * x + (3 * acc + (2 : Int) ^ j) := by
      calc
        (2 : Int) ^ (j + 1) * collatzStepInt y
            = (2 : Int) ^ j * (2 * collatzStepInt y) := by rw [Int.pow_succ, Int.mul_assoc]
        _ = (2 : Int) ^ j * (3 * y + 1) := by rw [hstep]
        _ = 3 * ((2 : Int) ^ j * y) + (2 : Int) ^ j := by
          rw [Int.mul_add, Int.mul_one, ← Int.mul_assoc, Int.mul_comm ((2 : Int) ^ j) 3, Int.mul_assoc]
        _ = 3 * ((3 : Int) ^ w0 * x + acc) + (2 : Int) ^ j := by rw [hinv]
        _ = (3 : Int) ^ (w0 + 1) * x + (3 * acc + (2 : Int) ^ j) := by
          rw [Int.mul_add, Int.pow_succ, Int.mul_comm ((3 : Int) ^ w0) 3, Int.mul_assoc, Int.add_assoc]
    have ih :=
      affine_aux_invariant rest (j + 1) (w0 + 1) x (collatzStepInt y)
        (3 * acc + (2 : Int) ^ j) hrest hnext
    have hlen : j + (true :: rest).length = j + 1 + rest.length := by simp; omega
    have hw : w0 + parityWeight (true :: rest) = w0 + 1 + parityWeight rest := by
      simp [parityWeight]; omega
    simp only [affineCarryAuxInt]
    rw [hlen, hw]
    exact ih

/--
  Theorem 1.1 (Universal Affine Decomposition over Z):
  For EVERY parity vector v and EVERY integer x in Z (positive or negative),
  if x realizes parity vector v, then 2^|v| * T^|v|(x) = 3^w(v) * x + C(v).
-/
theorem affine_decomposition_universal (v : List Bool) (x : Int) (h : matchesParity v x) :
    (2 : Int) ^ v.length * collatzIterInt v.length x =
      (3 : Int) ^ parityWeight v * x + affineCarryInt v := by
  have h0 : (2 : Int) ^ 0 * x = (3 : Int) ^ 0 * x + 0 := by simp
  have hmain := affine_aux_invariant v 0 0 x x 0 h h0
  simpa [affineCarryInt] using hmain

/--
  Theorem 1.3 (Universal Bohm-Sontacchi Cycle Equation over Z):
  Every periodic integer x in Z with parity period v satisfies
  (2^|v| - 3^w(v)) * x = C(v).
-/
theorem bohm_sontacchi_cycle_equation_universal (v : List Bool) (x : Int)
    (hpar : matchesParity v x) (hcyc : collatzIterInt v.length x = x) :
    ((2 : Int) ^ v.length - (3 : Int) ^ parityWeight v) * x = affineCarryInt v := by
  have hdec := affine_decomposition_universal v x hpar
  rw [hcyc] at hdec
  rw [Int.sub_mul]
  omega

/--
  Theorem 9 (Universal One-Equation Diophantine Identity):
  Every integer n reaching 1 in |v| compressed steps with parity vector v satisfies
  2^|v| = 3^w(v) * n + C(v).
-/
theorem one_equation_forward_universal (v : List Bool) (n : Int)
    (hpar : matchesParity v n) (hone : collatzIterInt v.length n = 1) :
    (2 : Int) ^ v.length = (3 : Int) ^ parityWeight v * n + affineCarryInt v := by
  have hdec := affine_decomposition_universal v n hpar
  rw [hone, Int.mul_one] at hdec
  exact hdec

/-- Algebraic telescoping step for the 1-cycle carry over Nat (using pow2_le_pow3) -/
theorem one_cycle_telescoping_step (m : Nat) :
    3 * (3 ^ m - 2 ^ m) + 2 ^ m = 3 * 3 ^ m - 2 * 2 ^ m := by
  have h := pow2_le_pow3 m
  omega

theorem replicate_false_carry_preserve :
    ∀ (a j : Nat) (acc : Int),
      affineCarryAuxInt (List.replicate a false) j acc = acc
  | 0, _, _ => rfl
  | a + 1, j, acc => replicate_false_carry_preserve a (j + 1) acc

theorem replicate_true_carry_invariant :
    ∀ (w j : Nat) (acc : Int),
      affineCarryAuxInt (List.replicate w true) j acc =
        (3 : Int) ^ w * acc + (2 : Int) ^ j * ((3 : Int) ^ w - (2 : Int) ^ w)
  | 0, j, acc => by simp [affineCarryAuxInt]
  | w + 1, j, acc => by
    simp only [List.replicate_succ, affineCarryAuxInt]
    rw [replicate_true_carry_invariant w (j + 1) (3 * acc + (2 : Int) ^ j)]
    have hp3 : (3 : Int) ^ (w + 1) = (3 : Int) ^ w * 3 := Int.pow_succ 3 w
    have hp2j : (2 : Int) ^ (j + 1) = (2 : Int) ^ j * 2 := Int.pow_succ 2 j
    have hp2w : (2 : Int) ^ (w + 1) = (2 : Int) ^ w * 2 := Int.pow_succ 2 w
    rw [hp3, hp2j, hp2w]
    -- Pure linear combination of A = 3^w * acc, B = 2^j * 3^w, C = 2^j * 2^w
    have h1 : (3 : Int) ^ w * (3 * acc + (2 : Int) ^ j) =
        3 * ((3 : Int) ^ w * acc) + (2 : Int) ^ j * (3 : Int) ^ w := by
      rw [Int.mul_add, ← Int.mul_assoc, Int.mul_comm ((3 : Int) ^ w) 3, Int.mul_assoc,
          Int.mul_comm ((3 : Int) ^ w) ((2 : Int) ^ j)]
    have h2 : (2 : Int) ^ j * 2 * ((3 : Int) ^ w - (2 : Int) ^ w) =
        2 * ((2 : Int) ^ j * (3 : Int) ^ w) - 2 * ((2 : Int) ^ j * (2 : Int) ^ w) := by
      rw [Int.mul_sub]
      have ha : (2 : Int) ^ j * 2 * (3 : Int) ^ w = 2 * ((2 : Int) ^ j * (3 : Int) ^ w) := by
        rw [Int.mul_comm ((2 : Int) ^ j) 2, Int.mul_assoc]
      have hb : (2 : Int) ^ j * 2 * (2 : Int) ^ w = 2 * ((2 : Int) ^ j * (2 : Int) ^ w) := by
        rw [Int.mul_comm ((2 : Int) ^ j) 2, Int.mul_assoc]
      rw [ha, hb]
    have h3 : (2 : Int) ^ j * ((3 : Int) ^ w * 3 - (2 : Int) ^ w * 2) =
        3 * ((2 : Int) ^ j * (3 : Int) ^ w) - 2 * ((2 : Int) ^ j * (2 : Int) ^ w) := by
      rw [Int.mul_sub]
      have hc : (2 : Int) ^ j * ((3 : Int) ^ w * 3) = 3 * ((2 : Int) ^ j * (3 : Int) ^ w) := by
        rw [← Int.mul_assoc, Int.mul_comm _ 3]
      have hd : (2 : Int) ^ j * ((2 : Int) ^ w * 2) = 2 * ((2 : Int) ^ j * (2 : Int) ^ w) := by
        rw [← Int.mul_assoc, Int.mul_comm _ 2]
      rw [hc, hd]
    have h4 : (3 : Int) ^ w * 3 * acc = 3 * ((3 : Int) ^ w * acc) := by
      rw [Int.mul_comm ((3 : Int) ^ w) 3, Int.mul_assoc]
    rw [h1, h2, h3, h4]
    omega

theorem affineCarryAuxInt_append :
    ∀ (u v : List Bool) (j : Nat) (acc : Int),
      affineCarryAuxInt (u ++ v) j acc =
        affineCarryAuxInt v (j + u.length) (affineCarryAuxInt u j acc)
  | [], v, j, acc => by simp [affineCarryAuxInt]
  | false :: rest, v, j, acc => by
    simp only [List.cons_append, affineCarryAuxInt, List.length_cons]
    have hlen : j + (rest.length + 1) = j + 1 + rest.length := by omega
    rw [hlen]
    exact affineCarryAuxInt_append rest v (j + 1) acc
  | true :: rest, v, j, acc => by
    simp only [List.cons_append, affineCarryAuxInt, List.length_cons]
    have hlen : j + (rest.length + 1) = j + 1 + rest.length := by omega
    rw [hlen]
    exact affineCarryAuxInt_append rest v (j + 1) (3 * acc + (2 : Int) ^ j)

/--
  Theorem 3 Helper (Universal 1-Cycle Carry Closed Form):
  For ALL w, a in Nat, C(1^w 0^a) = 3^w - 2^w.
-/
theorem one_cycle_carry_closed_form_universal (w a : Nat) :
    affineCarryInt (List.replicate w true ++ List.replicate a false) =
      (3 : Int) ^ w - (2 : Int) ^ w := by
  unfold affineCarryInt
  rw [affineCarryAuxInt_append, replicate_false_carry_preserve, replicate_true_carry_invariant]
  simp

-- ============================================================================
-- 4. Concrete Witnesses for Theorems 2, 6, 7, 9, 14, 15, 17, 20, & 22
-- ============================================================================

theorem trivial_1cycle_carry : affineCarry [true, false] = 1 := rfl
theorem trivial_1cycle_denominator : 2 ^ 2 - 3 ^ 1 = 1 := rfl
theorem weight_2_1cycle_carry : affineCarry [true, true, false] = 5 := rfl
theorem weight_3_1cycle_carry : affineCarry [true, true, true, false, false] = 19 := rfl
theorem weight_4_1cycle_carry : affineCarry [true, true, true, true, false, false, false] = 65 := rfl
theorem sturmian_w4_carry : affineCarry [true, true, false, true, true] = 85 := rfl

theorem contractive_coalescence_k6_t0 :
    collatzIter 6 15 = collatzIter 1 13 ∧ collatzIter 6 15 = 20 := by
  decide

theorem contractive_coalescence_k6_t1 :
    collatzIter 6 79 = collatzIter 1 67 ∧ collatzIter 6 79 = 101 := by
  decide

theorem surviving_diamond_k34_carry_diff :
    165490842749 - 39966604313 = 4 * (3 ^ 22) := rfl

theorem surviving_diamond_k34_affine_image :
    ((3 ^ 22) * 7435082751 + 39966604313) / (2 ^ 34) = 13581056558 ∧
    ((3 ^ 22) * 7435082747 + 165490842749) / (2 ^ 34) = 13581056558 := by
  decide

theorem one_equation_n7_witness :
    affineCarry [true, true, true, false, true, false, false, true, false, false, false] = 347 ∧
    7 * (3 ^ 5) + 347 = 2 ^ 11 := by
  decide

theorem odd_step_plus_one_scaling (m : Nat) :
    2 * (((3 * (2 * m + 1) + 1) / 2) + 1) = 3 * ((2 * m + 1) + 1) := by
  omega

theorem hercher_collatz_merger_algebraic (q : Nat) :
    (3 * ((4 * q + 2) / 2) + 1) / 2 = (((3 * (8 * q + 5) + 1) / 2) / 2) / 2 ∧
    (3 * ((4 * q + 2) / 2) + 1) / 2 = 3 * q + 2 := by
  omega

theorem hercher_collatz_merger_x13_witness :
    collatzIter 2 6 = collatzIter 3 13 ∧ collatzIter 2 6 = 5 := by
  decide

theorem brox_minus17_2cycle_compression :
    affineCarry [true, true, true, true, false, true, true, true, false, false, false] = 2363 ∧
    (2 ^ 1 - 1) * (3 ^ 3) + (2 ^ 4) * (2 ^ 3 - 1) = 139 ∧
    2363 + (2 ^ 11) = (3 ^ 7) + (2 ^ 4) * 139 := by
  decide

theorem affine_commutator_cleared_denom (x : Nat) :
    (3 * x + 2) - (3 * x + 1) = 1 := by
  omega

-- ============================================================================
-- 5. Theorem 19.1: Entry Merger & All 3 Cases of Potential-Telescoping Bound
-- ============================================================================

theorem entry_collatz_merger_k2_algebraic (q : Nat) :
    (3 * (((3 * (8 * q + 1) + 1) / 2) / 2) + 1) / 2 =
      ((((3 * ((3 * (16 * q + 3) + 1) / 2) + 1) / 2) / 2) / 2) ∧
    (3 * (((3 * (8 * q + 1) + 1) / 2) / 2) + 1) / 2 = 9 * q + 2 := by
  omega

/-- Case 1 (k = 1): 1 / (3 * xNext) < 2 / (3 * n0) cleared of denominators -/
theorem potential_telescoping_case1_cleared_denom (n0 xNext : Nat)
    (_hn0 : n0 ≥ 1) (hnext : xNext ≥ n0 + 1) :
    3 * n0 < 6 * xNext := by
  omega

/--
  Case 2 (l = 1, k >= 2):
  2^(k+1) * (xNext + 1) = 3^k * (x + 1) implies 2^(k+1) * xNext > 3^k * x (via pow2_succ_lt_pow3),
  which yields the cleared-denominator step bound:
    n0 * ((2 * 3^k - 3 * 2^k) * xNext + 3^k * x) < 2 * (3^k * (x * xNext)).
-/
theorem potential_telescoping_case2_cleared_denom (k n0 x xNext : Nat)
    (hk : k ≥ 2) (hn0 : n0 ≥ 1) (hx : x ≥ n0 + 1)
    (hstep : 2 ^ (k + 1) * (xNext + 1) = 3 ^ k * (x + 1)) :
    n0 * ((2 * 3 ^ k - 3 * 2 ^ k) * xNext + 3 ^ k * x) < 2 * (3 ^ k * (x * xNext)) := by
  have hpow : 2 ^ (k + 1) < 3 ^ k := pow2_succ_lt_pow3 k hk
  have hp2 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
  have hxnext_pos : xNext ≥ 1 := by
    cases xNext with
    | zero =>
      have hge : 3 ^ k * (x + 1) ≥ 3 ^ k * 2 := Nat.mul_le_mul_left (3 ^ k) (by omega)
      omega
    | succ xn => omega
  have hgt : 3 ^ k * x < 2 * 2 ^ k * xNext := by
    have hxp : 3 ^ k * (x + 1) = 3 ^ k * x + 3 ^ k := by rw [Nat.mul_add, Nat.mul_one]
    have hyn : 2 ^ (k + 1) * (xNext + 1) = 2 * 2 ^ k * xNext + 2 ^ (k + 1) := by
      rw [Nat.mul_add, Nat.mul_one, hp2]
    omega
  have h3gt : 3 * 2 ^ k ≤ 2 * 3 ^ k := by omega
  have hsum : (2 * 3 ^ k - 3 * 2 ^ k) * xNext + 3 ^ k * x < 2 * 3 ^ k * xNext := by
    have hd : (2 * 3 ^ k - 3 * 2 ^ k) * xNext + 3 * 2 ^ k * xNext = 2 * 3 ^ k * xNext := by
      rw [← Nat.add_mul]
      have hsub : 2 * 3 ^ k - 3 * 2 ^ k + 3 * 2 ^ k = 2 * 3 ^ k := Nat.sub_add_cancel h3gt
      rw [hsub]
    have h2lt3 : 2 * 2 ^ k * xNext ≤ 3 * 2 ^ k * xNext :=
      Nat.mul_le_mul_right xNext (by omega)
    omega
  have hmul1 :
      n0 * ((2 * 3 ^ k - 3 * 2 ^ k) * xNext + 3 ^ k * x) < n0 * (2 * 3 ^ k * xNext) :=
    Nat.mul_lt_mul_of_pos_left hsum (by omega)
  have hmul2 : n0 * (2 * 3 ^ k * xNext) < x * (2 * 3 ^ k * xNext) :=
    Nat.mul_lt_mul_of_pos_right (by omega) (by
      have hp3_pos : 3 ^ k ≥ 1 := by omega
      have h2p3_pos : 2 * 3 ^ k ≥ 1 := by omega
      exact Nat.mul_pos h2p3_pos hxnext_pos)
  have hassoc : x * (2 * 3 ^ k * xNext) = 2 * (3 ^ k * (x * xNext)) := by
    calc
      x * (2 * 3 ^ k * xNext) = x * (2 * (3 ^ k * xNext)) := by rw [Nat.mul_assoc]
      _ = 2 * (x * (3 ^ k * xNext)) := by
        rw [← Nat.mul_assoc, Nat.mul_comm x 2, Nat.mul_assoc]
      _ = 2 * (3 ^ k * (x * xNext)) := by
        rw [← Nat.mul_assoc x (3 ^ k) xNext, Nat.mul_comm x (3 ^ k), Nat.mul_assoc]
  omega

/-- Case 3 (l >= 2, k >= 2): (2/3)/x + 1/(3*xNext) < 2/(3*n0) cleared of denominators -/
theorem potential_telescoping_case3_cleared_denom (n0 x xNext : Nat)
    (hn0 : n0 ≥ 1) (hx : x ≥ 2 * n0 + 3) (hnext : xNext ≥ n0 + 1) :
    2 * n0 * xNext + n0 * x < 2 * (x * xNext) := by
  have h1 : 2 * n0 * xNext < x * xNext := Nat.mul_lt_mul_of_pos_right (by omega) (by omega)
  have h2 : n0 * x < x * xNext := by
    rw [Nat.mul_comm n0 x]
    exact Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
  omega

-- ============================================================================
-- 6. Theorem 19.2: Kernel-Checked Orbit-Drop Certificate for All 32 Survivors
-- ============================================================================

/--
  The complete set of 32 distinct arithmetic multi-step 2-adic Hensel survivors
  across 92 <= m <= 95 (5 at m=94 u=1, 25 at m=95 u=2, 2 at m=95 u=3), paired
  with the exact number of compressed Collatz steps each takes to drop <= 2^71.
-/
def henselSurvivors92To95 : List (Nat × Nat) := [
  (128932779112854022258687, 304),
  (150148540639431337443327, 388),
  (150417804975740953821183, 339),
  (179507528690102354051071, 309),
  (184292880188988234661887, 183),
  (3043056996432649454896063935, 522),
  (4564585494648974182344095903, 521),
  (40390864820245125463559531007, 445),
  (60586297230367688195339296511, 444),
  (80781729640490250927119062015, 446),
  (80896492308699435453147774975, 490),
  (81382151907816510442931486719, 552),
  (90879445845551532293008944767, 443),
  (107666254683307549761322643071, 443),
  (118590899805286057887739609087, 389),
  (121019381962425623133141598207, 562),
  (121172594460735376390678593023, 445),
  (121344738463049153179721662463, 489),
  (122073227861724765664397230079, 551),
  (122834388093427971696718966783, 402),
  (125280393861289108189638295551, 533),
  (126778321893609356677628297215, 498),
  (134877338994778624923617198079, 429),
  (136319168768327298439513417151, 442),
  (140683356142945381137080385535, 492),
  (141389811227252306261634351103, 435),
  (142353197350388373522137219071, 500),
  (161499382024961324641983964607, 442),
  (161792984617398870906295549951, 491),
  (162764303815633020885862973439, 553),
  (168640316132962311354812727295, 645),
  (169398243281367919978820403199, 491)
]

def checkSurvivorDrop (n0 : Nat) (zk : Nat × Nat) : Bool :=
  let z := zk.1
  let k := zk.2
  (z % 2 == 1) && (z > n0) && (collatzIter k z ≤ n0)

set_option maxRecDepth 20000 in
/--
  Lean 4 Kernel Proof (`by decide`) that ALL 32 arithmetic Hensel survivors
  above 2^71 across 92 <= m <= 95 drop <= 2^71 under `collatzIter`, hence
  cannot lie on any non-trivial Collatz cycle above Barina's 2^71 bound!
-/
theorem all_32_hensel_survivors_drop_below_2_pow_71 :
    henselSurvivors92To95.length = 32 ∧
    henselSurvivors92To95.all (checkSurvivorDrop (2 ^ 71)) = true := by
  decide

-- ============================================================================
-- 7. Theorems 20B, 22A, & 22B: S-Integer 2-Cycle, 5-Adic Units, & Coalescence
-- ============================================================================

theorem s_integer_positive_2cycle_29_over_5_witness :
    affineCarry [true, false, true, true, false] = 29 ∧
    (2 ^ 1 - 1) * (3 ^ 2) + (2 ^ 3) * (2 ^ 1 - 1) = 17 ∧
    (2 ^ 1 - 1) * (3 ^ 1) + (2 ^ 2) * (2 ^ 1 - 1) = 7 ∧
    29 + (2 ^ 5) = (3 ^ 3) + (2 ^ 1) * 17 := by
  decide

theorem five_adic_unit_denominators_eight_witnesses :
    (3 ^ 1) - (2 ^ 1) = 5 ^ 0 ∧
    (2 ^ 2) - (3 ^ 1) = 5 ^ 0 ∧
    (3 ^ 2) - (2 ^ 3) = 5 ^ 0 ∧
    (3 ^ 2) - (2 ^ 2) = 5 ^ 1 ∧
    (2 ^ 3) - (3 ^ 1) = 5 ^ 1 ∧
    (2 ^ 5) - (3 ^ 3) = 5 ^ 1 ∧
    (3 ^ 3) - (2 ^ 1) = 5 ^ 2 ∧
    (2 ^ 7) - (3 ^ 1) = 5 ^ 3 := by
  decide

/--
  Theorem 22.2 (Universal Contractive Coalescence Partner Theorem):
  Whenever 3^w = 3^wp * 3^(w - wp), b_v = 3^wp * q0 + b_vp, 1 <= r_vp,
  3^(w - wp) * t + q0 >= 0, and (2^k - 2^kp * 3^(w - wp)) * t > 2^kp * q0 + r_vp - r_v,
  the partner n' = 2^kp * (3^(w - wp) * t + q0) + r_vp satisfies 1 <= n' < n0
  and exact affine image equality 3^w * t + b_v = 3^wp * (3^(w - wp) * t + q0) + b_vp.
-/
theorem minimal_divergent_coalescence_universal
    (p2k p2kp p3w p3wp p3diff rv rvp bv bvp q0 t : Int)
    (hp2kp : p2kp ≥ 1)
    (hpow3 : p3w = p3wp * p3diff)
    (hmod3 : bv = p3wp * q0 + bvp)
    (hrvp : rvp ≥ 1)
    (hpos : p3diff * t + q0 ≥ 0)
    (hcontr : p2k * t - p2kp * (p3diff * t) > p2kp * q0 + rvp - rv) :
    let n0 := p2k * t + rv
    let nPrime := p2kp * (p3diff * t + q0) + rvp
    (1 ≤ nPrime ∧ nPrime < n0) ∧
    (p3w * t + bv = p3wp * (p3diff * t + q0) + bvp) := by
  dsimp only
  have hnonneg : p2kp * (p3diff * t + q0) ≥ 0 := Int.mul_nonneg (by omega) hpos
  have hexp1 : p2kp * (p3diff * t + q0) = p2kp * (p3diff * t) + p2kp * q0 :=
    Int.mul_add p2kp (p3diff * t) q0
  have hexp2 : p3wp * (p3diff * t + q0) = p3w * t + p3wp * q0 := by
    rw [Int.mul_add, ← Int.mul_assoc, ← hpow3]
  constructor
  · constructor
    · omega
    · omega
  · omega

-- ============================================================================
-- 8. Theorem 15, 19.2, & 21.1: Universal r-Step Spiral Hensel Identity,
--    Unimodular Convergent Determinants, & Quadratic Peak Floor
-- ============================================================================

/--
  Inductive predicate for a valid r-step spiral-minimum trajectory z_1 -> ... -> z_{r+1}
  with block step parameters [(k_1, l_1), ..., (k_r, l_r)]:
  at each block step, 2^(k + l) * (zNext + 1) = 3^k * (z + 1) + 2^k * (2^l - 1).
-/
inductive SpiralPath : List (Nat × Nat) -> Int -> Int -> Prop where
  | nil (z : Int) : SpiralPath [] z z
  | cons (k l : Nat) (rest : List (Nat × Nat)) (z1 z2 zEnd : Int)
      (hstep : (2 : Int) ^ (k + l) * (z2 + 1) =
               (3 : Int) ^ k * (z1 + 1) + (2 : Int) ^ k * ((2 : Int) ^ l - 1))
      (hrest : SpiralPath rest z2 zEnd) :
      SpiralPath ((k, l) :: rest) z1 zEnd

def spiralCarryAux : List (Nat × Nat) -> Nat -> Int -> Int
  | [], _, g => g
  | (k, l) :: rest, kAcc, g =>
    spiralCarryAux rest (kAcc + (k + l))
      ((3 : Int) ^ k * g + (2 : Int) ^ (kAcc + k) * ((2 : Int) ^ l - 1))

def spiralTotalK : List (Nat × Nat) -> Nat
  | [] => 0
  | (k, l) :: rest => (k + l) + spiralTotalK rest

def spiralTotalW : List (Nat × Nat) -> Nat
  | [] => 0
  | (k, _) :: rest => k + spiralTotalW rest

theorem spiral_hensel_aux_invariant :
    ∀ (steps : List (Nat × Nat)) (zCur zEnd zRoot g : Int) (kAcc wAcc : Nat),
      SpiralPath steps zCur zEnd ->
      (2 : Int) ^ kAcc * (zCur + 1) = (3 : Int) ^ wAcc * (zRoot + 1) + g ->
      (2 : Int) ^ (kAcc + spiralTotalK steps) * (zEnd + 1) =
        (3 : Int) ^ (wAcc + spiralTotalW steps) * (zRoot + 1) +
        spiralCarryAux steps kAcc g
  | [], zCur, zEnd, zRoot, g, kAcc, wAcc, hp, hinv => by
    cases hp
    simpa [spiralTotalK, spiralTotalW, spiralCarryAux] using hinv
  | (k, l) :: rest, zCur, zEnd, zRoot, g, kAcc, wAcc, hp, hinv => by
    cases hp with
    | cons _ _ _ _ z2 _ hstep hrest =>
      have hnext :
          (2 : Int) ^ (kAcc + (k + l)) * (z2 + 1) =
            (3 : Int) ^ (wAcc + k) * (zRoot + 1) +
            ((3 : Int) ^ k * g + (2 : Int) ^ (kAcc + k) * ((2 : Int) ^ l - 1)) := by
        calc
          (2 : Int) ^ (kAcc + (k + l)) * (z2 + 1)
              = (2 : Int) ^ kAcc * ((2 : Int) ^ (k + l) * (z2 + 1)) := by
                rw [Int.pow_add, Int.mul_assoc]
          _ = (2 : Int) ^ kAcc * ((3 : Int) ^ k * (zCur + 1) + (2 : Int) ^ k * ((2 : Int) ^ l - 1)) := by
                rw [hstep]
          _ = (3 : Int) ^ k * ((2 : Int) ^ kAcc * (zCur + 1)) +
              (2 : Int) ^ (kAcc + k) * ((2 : Int) ^ l - 1) := by
                rw [Int.mul_add, ← Int.mul_assoc ((2 : Int) ^ kAcc) ((3 : Int) ^ k),
                    Int.mul_comm ((2 : Int) ^ kAcc) ((3 : Int) ^ k), Int.mul_assoc,
                    ← Int.mul_assoc ((2 : Int) ^ kAcc) ((2 : Int) ^ k), ← Int.pow_add]
          _ = (3 : Int) ^ k * ((3 : Int) ^ wAcc * (zRoot + 1) + g) +
              (2 : Int) ^ (kAcc + k) * ((2 : Int) ^ l - 1) := by
                rw [hinv]
          _ = (3 : Int) ^ (wAcc + k) * (zRoot + 1) +
              ((3 : Int) ^ k * g + (2 : Int) ^ (kAcc + k) * ((2 : Int) ^ l - 1)) := by
                rw [Int.mul_add, ← Int.mul_assoc ((3 : Int) ^ k) ((3 : Int) ^ wAcc),
                    Int.mul_comm ((3 : Int) ^ k) ((3 : Int) ^ wAcc), ← Int.pow_add,
                    Int.add_assoc]
      have ih :=
        spiral_hensel_aux_invariant rest z2 zEnd zRoot
          ((3 : Int) ^ k * g + (2 : Int) ^ (kAcc + k) * ((2 : Int) ^ l - 1))
          (kAcc + (k + l)) (wAcc + k) hrest hnext
      have hk : kAcc + spiralTotalK ((k, l) :: rest) = kAcc + (k + l) + spiralTotalK rest := by
        simp [spiralTotalK]; omega
      have hw : wAcc + spiralTotalW ((k, l) :: rest) = wAcc + k + spiralTotalW rest := by
        simp [spiralTotalW]; omega
      simp only [spiralCarryAux]
      rw [hk, hw]
      exact ih

/--
  Theorem 19.2 Algebraic Core (Universal r-Step Spiral Hensel Identity):
  Along ANY r-step spiral-minimum sequence z1 -> ... -> zEnd with block parameters `steps`,
  2^(K_r) * (zEnd + 1) = 3^(W_r) * (z1 + 1) + G_r identically.
-/
theorem spiral_hensel_identity_universal
    (steps : List (Nat × Nat)) (z1 zEnd : Int) (hp : SpiralPath steps z1 zEnd) :
    (2 : Int) ^ spiralTotalK steps * (zEnd + 1) =
      (3 : Int) ^ spiralTotalW steps * (z1 + 1) + spiralCarryAux steps 0 0 := by
  have h0 : (2 : Int) ^ 0 * (z1 + 1) = (3 : Int) ^ 0 * (z1 + 1) + 0 := by simp
  have hmain := spiral_hensel_aux_invariant steps z1 zEnd z1 0 0 0 hp h0
  simpa using hmain

/--
  Theorems 15.1 & 19.1 Unimodular Lattice Basis Determinants:
  p_43 * q_42 - p_42 * q_43 = +1 and p_45 * q_44 - p_44 * q_45 = +1.
-/
theorem convergents_43_and_45_unimodular :
    (325919355854421968365 : Int) * 127940101513462006853 -
      202780263237295321099 * 205632218873398596256 = 1 ∧
    (49373105075258054570781 : Int) * 7736332199829210068325 -
      12261796429850908150604 * 31150961018190238869556 = 1 := by
  decide

/--
  Theorem 21.1 Algebraic Core (Cleared-Square Quadratic Running-Maximum Peak Floor):
  Whenever 3 * (mPeak - n) * mPeak > n * w, completing the square gives
  3 * (2 * mPeak - n)^2 > 3 * n^2 + 4 * n * w
  (i.e. mPeak > (n + sqrt(n^2 + (4/3) * n * w)) / 2).
-/
theorem quadratic_peak_floor_cleared_square (n w mPeak : Int)
    (hunc : 3 * ((mPeak - n) * mPeak) > n * w) :
    3 * ((2 * mPeak - n) * (2 * mPeak - n)) > 3 * (n * n) + 4 * (n * w) := by
  have h1 : (mPeak - n) * mPeak = mPeak * mPeak - n * mPeak := Int.sub_mul mPeak n mPeak
  have h2 : (2 * mPeak - n) * (2 * mPeak - n) =
      4 * (mPeak * mPeak) - 4 * (n * mPeak) + n * n := by
    calc
      (2 * mPeak - n) * (2 * mPeak - n)
          = 2 * mPeak * (2 * mPeak - n) - n * (2 * mPeak - n) := Int.sub_mul _ _ _
      _ = 2 * mPeak * (2 * mPeak) - 2 * mPeak * n - (n * (2 * mPeak) - n * n) := by
            rw [Int.mul_sub, Int.mul_sub]
      _ = 4 * (mPeak * mPeak) - 4 * (n * mPeak) + n * n := by
            have ha : 2 * mPeak * (2 * mPeak) = 4 * (mPeak * mPeak) := by
              calc
                2 * mPeak * (2 * mPeak) = 2 * (mPeak * (2 * mPeak)) := Int.mul_assoc _ _ _
                _ = 2 * (2 * (mPeak * mPeak)) := by
                  rw [← Int.mul_assoc mPeak 2 mPeak, Int.mul_comm mPeak 2, Int.mul_assoc]
                _ = 4 * (mPeak * mPeak) := by rw [← Int.mul_assoc]; rfl
            have hb : 2 * mPeak * n = 2 * (n * mPeak) := by
              rw [Int.mul_assoc, Int.mul_comm mPeak n]
            have hc : n * (2 * mPeak) = 2 * (n * mPeak) := by
              rw [← Int.mul_assoc, Int.mul_comm n 2, Int.mul_assoc]
            rw [ha, hb, hc]
            omega
  rw [h1] at hunc
  rw [h2]
  omega

-- ============================================================================
-- 9. Formal Definitions of the Collatz Conjecture & Canonical Equivalences
--    (Aligned with `google-deepmind/formal-conjectures` & Erdős Problem #1135)
-- ============================================================================

/--
  Standard (uncompressed) Collatz step on `Nat`, matching
  `FormalConjectures/Wikipedia/CollatzConjecture.lean` (`if Even n then n / 2 else 3 * n + 1`).
-/
def collatzStepStandard (n : Nat) : Nat :=
  if n % 2 == 0 then n / 2 else 3 * n + 1

/--
  m-step iteration of the standard Collatz map on `Nat` (matches `collatzStep^[m] n`).
-/
def collatzIterStandard : Nat -> Nat -> Nat
  | 0, n => n
  | m + 1, n => collatzIterStandard m (collatzStepStandard n)

/--
  Canonical Formal Statement of the **Collatz Conjecture** (Erdős Problem #1135),
  matching `google-deepmind/formal-conjectures`:
  For every positive integer `n > 0`, some iterate of `collatzStepStandard` reaches `1`.
-/
def CollatzConjectureStandard : Prop :=
  ∀ n : Nat, n > 0 -> ∃ m : Nat, collatzIterStandard m n = 1

/--
  Compressed (Terras) formulation of the Collatz Conjecture:
  For every positive integer `n > 0`, some iterate of `collatzStep` reaches `1`.
-/
def CollatzConjectureCompressed : Prop :=
  ∀ n : Nat, n > 0 -> ∃ k : Nat, collatzIter k n = 1

/--
  Strict-Descent (Stopping-Time) formulation of the Collatz Conjecture:
  Every integer `n > 1` eventually drops strictly below `n` under `collatzIter`.
-/
def StrictDescentHypothesis : Prop :=
  ∀ n : Nat, n > 1 -> ∃ k : Nat, 0 < collatzIter k n ∧ collatzIter k n < n

/--
  Open Problem A (No Divergent / Unbounded Positive Orbits):
  Every positive Collatz trajectory is bounded above in `Nat`.
-/
def NoDivergentPositiveOrbits : Prop :=
  ∀ n : Nat, n > 0 -> ∃ B : Nat, ∀ k : Nat, collatzIter k n ≤ B

/--
  Open Problem B (No Non-Trivial Positive Cycles):
  Every periodic positive integer under compressed `collatzIter` lies in the
  unique trivial `{1, 2}` cycle.
-/
def NoNontrivialPositiveCycles : Prop :=
  ∀ x p : Nat, x > 0 -> p > 0 -> collatzIter p x = x -> (x = 1 ∨ x = 2)

/--
  One-Equation (2,3)-Bilinear Diophantine formulation (Theorem 9):
  For every positive integer `n > 0`, there exists a parity word `v : List Bool`
  solving `2^|v| = 3^w(v) * n + C(v)` (with zero side-conditions on `v`).
-/
def CollatzOneEquationConjecture : Prop :=
  ∀ n : Nat, n > 0 ->
    ∃ v : List Bool,
      (2 : Int) ^ v.length = (3 : Int) ^ parityWeight v * (n : Int) + affineCarryInt v

theorem collatzIter_add : ∀ (a b n : Nat),
    collatzIter (a + b) n = collatzIter b (collatzIter a n)
  | 0, b, n => by simp [collatzIter]
  | a + 1, b, n => by
    have heq : a + 1 + b = (a + b) + 1 := by omega
    rw [heq]
    simp only [collatzIter]
    exact collatzIter_add a b (collatzStep n)

theorem collatzIterStandard_add : ∀ (a b n : Nat),
    collatzIterStandard (a + b) n = collatzIterStandard b (collatzIterStandard a n)
  | 0, b, n => by simp [collatzIterStandard]
  | a + 1, b, n => by
    have heq : a + 1 + b = (a + b) + 1 := by omega
    rw [heq]
    simp only [collatzIterStandard]
    exact collatzIterStandard_add a b (collatzStepStandard n)

theorem collatzStep_pos (n : Nat) (hn : n > 0) : collatzStep n > 0 := by
  unfold collatzStep
  cases h : (n % 2 == 0) with
  | true =>
    have hm : n % 2 = 0 := of_decide_eq_true h
    simp
    omega
  | false =>
    simp
    omega

theorem collatzIter_pos : ∀ (k n : Nat), n > 0 -> collatzIter k n > 0
  | 0, _, hn => hn
  | k + 1, n, hn => collatzIter_pos k (collatzStep n) (collatzStep_pos n hn)

theorem compressed_step_to_standard (n : Nat) :
    ∃ m : Nat, collatzIterStandard m n = collatzStep n := by
  cases h : (n % 2 == 0) with
  | true =>
    refine ⟨1, ?_⟩
    simp [collatzIterStandard, collatzStepStandard, collatzStep, h]
  | false =>
    refine ⟨2, ?_⟩
    have hm : n % 2 ≠ 0 := of_decide_eq_false h
    have hev : ((3 * n + 1) % 2 == 0) = true := decide_eq_true (by omega)
    simp [collatzIterStandard, collatzStepStandard, collatzStep, h, hev]

theorem compressed_iter_to_standard : ∀ (k n : Nat),
    ∃ m : Nat, collatzIterStandard m n = collatzIter k n
  | 0, n => ⟨0, rfl⟩
  | k + 1, n => by
    rcases compressed_step_to_standard n with ⟨m1, hm1⟩
    rcases compressed_iter_to_standard k (collatzStep n) with ⟨m2, hm2⟩
    refine ⟨m1 + m2, ?_⟩
    rw [collatzIterStandard_add, hm1]
    exact hm2

theorem standard_reaches_one_to_compressed_aux : ∀ (fuel m n : Nat),
    m ≤ fuel -> n > 0 -> collatzIterStandard m n = 1 -> ∃ k : Nat, collatzIter k n = 1
  | 0, m, n, hm, _, h1 => by
    have hm0 : m = 0 := by omega
    subst hm0
    exact ⟨0, h1⟩
  | fuel + 1, 0, _, _, _, h1 => ⟨0, h1⟩
  | fuel + 1, 1, n, _, hn, h1 => by
    simp only [collatzIterStandard, collatzStepStandard] at h1
    cases h : (n % 2 == 0) with
    | true =>
      rw [h] at h1
      simp at h1
      refine ⟨1, ?_⟩
      simp [collatzIter, collatzStep, h, h1]
    | false =>
      rw [h] at h1
      simp at h1
      omega
  | fuel + 1, m' + 2, n, hm, hn, h1 => by
    cases h : (n % 2 == 0) with
    | true =>
      have hmod : n % 2 = 0 := of_decide_eq_true h
      have hstep_std : collatzStepStandard n = collatzStep n := by
        simp [collatzStepStandard, collatzStep, h]
      have hiter : collatzIterStandard (m' + 1) (collatzStep n) = 1 := by
        have hdef : collatzIterStandard (m' + 2) n =
            collatzIterStandard (m' + 1) (collatzStepStandard n) := rfl
        rw [hdef, hstep_std] at h1
        exact h1
      have hpos : collatzStep n > 0 := collatzStep_pos n hn
      rcases standard_reaches_one_to_compressed_aux fuel (m' + 1) (collatzStep n)
          (by omega) hpos hiter with ⟨k, hk⟩
      exact ⟨k + 1, hk⟩
    | false =>
      have hmod : n % 2 ≠ 0 := of_decide_eq_false h
      have hev : ((3 * n + 1) % 2 == 0) = true := decide_eq_true (by omega)
      have h2steps : collatzStepStandard (collatzStepStandard n) = collatzStep n := by
        simp [collatzStepStandard, collatzStep, h, hev]
      have hiter : collatzIterStandard m' (collatzStep n) = 1 := by
        have hdef : collatzIterStandard (m' + 2) n =
            collatzIterStandard m' (collatzStepStandard (collatzStepStandard n)) := rfl
        rw [hdef, h2steps] at h1
        exact h1
      have hpos : collatzStep n > 0 := collatzStep_pos n hn
      rcases standard_reaches_one_to_compressed_aux fuel m' (collatzStep n)
          (by omega) hpos hiter with ⟨k, hk⟩
      exact ⟨k + 1, hk⟩

/--
  Canonical Equivalence 1:
  The standard uncompressed Collatz Conjecture (`google-deepmind/formal-conjectures`)
  is logically equivalent to the compressed Terras Collatz Conjecture.
-/
theorem collatz_standard_iff_compressed :
    CollatzConjectureStandard ↔ CollatzConjectureCompressed := by
  constructor
  · intro hstd n hn
    rcases hstd n hn with ⟨m, hm⟩
    exact standard_reaches_one_to_compressed_aux m m n (Nat.le_refl m) hn hm
  · intro hcomp n hn
    rcases hcomp n hn with ⟨k, hk⟩
    rcases compressed_iter_to_standard k n with ⟨m, hm⟩
    exact ⟨m, by rw [hm, hk]⟩

theorem strict_descent_implies_compressed_aux : ∀ (fuel n : Nat),
    StrictDescentHypothesis -> 0 < n -> n ≤ fuel -> ∃ k : Nat, collatzIter k n = 1
  | 0, n, _, hn, hle => by omega
  | fuel + 1, n, hdesc, hn, hle => by
    by_cases hn1 : n = 1
    · subst hn1
      exact ⟨0, rfl⟩
    · have hgt1 : n > 1 := by omega
      rcases hdesc n hgt1 with ⟨k1, hpos1, hlt1⟩
      rcases strict_descent_implies_compressed_aux fuel (collatzIter k1 n)
          hdesc hpos1 (by omega) with ⟨k2, hk2⟩
      refine ⟨k1 + k2, ?_⟩
      rw [collatzIter_add]
      exact hk2

/--
  Canonical Equivalence 2:
  The standard Collatz Conjecture is logically equivalent to the Strict-Descent
  (finite stopping time) hypothesis for all `n > 1`.
-/
theorem collatz_iff_strict_descent :
    CollatzConjectureStandard ↔ StrictDescentHypothesis := by
  rw [collatz_standard_iff_compressed]
  constructor
  · intro hcomp n hn1
    rcases hcomp n (by omega) with ⟨k, hk⟩
    exact ⟨k, by rw [hk]; omega, by rw [hk]; omega⟩
  · intro hdesc n hn
    exact strict_descent_implies_compressed_aux n n hdesc hn (Nat.le_refl n)

/-- Finite pigeonhole principle on `[0, B]` for bounded `Nat` sequences -/
theorem bounded_seq_repeats : ∀ (B : Nat) (f : Nat -> Nat),
    (∀ i : Nat, f i ≤ B) -> ∃ i j : Nat, i < j ∧ f i = f j
  | 0, f, hB => by
    have h0 := hB 0
    have h1 := hB 1
    exact ⟨0, 1, by omega, by omega⟩
  | B + 1, f, hB => by
    cases Classical.em (∃ a b : Nat, a < b ∧ f a = B + 1 ∧ f b = B + 1) with
    | inl hdup =>
      rcases hdup with ⟨a, b, hab, hfa, hfb⟩
      exact ⟨a, b, hab, by omega⟩
    | inr hnodup =>
      cases Classical.em (∃ a : Nat, f a = B + 1) with
      | inl hex =>
        rcases hex with ⟨a, hfa⟩
        let g : Nat -> Nat := fun t => f (a + 1 + t)
        have hgB : ∀ t : Nat, g t ≤ B := by
          intro t
          have hle := hB (a + 1 + t)
          have hne : f (a + 1 + t) ≠ B + 1 := by
            intro heq
            exact hnodup ⟨a, a + 1 + t, by omega, hfa, heq⟩
          dsimp [g]
          omega
        rcases bounded_seq_repeats B g hgB with ⟨t1, t2, htt, hgeq⟩
        exact ⟨a + 1 + t1, a + 1 + t2, by omega, hgeq⟩
      | inr hnone =>
        have hfB : ∀ i : Nat, f i ≤ B := by
          intro i
          have hle := hB i
          have hne : f i ≠ B + 1 := fun heq => hnone ⟨i, heq⟩
          omega
        exact bounded_seq_repeats B f hfB

theorem collatzIter_trivial_cycle : ∀ (t x : Nat),
    (x = 1 ∨ x = 2) -> (collatzIter t x = 1 ∨ collatzIter t x = 2)
  | 0, x, hx => hx
  | t + 1, x, hx => by
    rcases hx with rfl | rfl
    · exact collatzIter_trivial_cycle t 2 (Or.inr rfl)
    · exact collatzIter_trivial_cycle t 1 (Or.inl rfl)

theorem collatzIter_mul_period : ∀ (q p x : Nat),
    collatzIter p x = x -> collatzIter (q * p) x = x
  | 0, _, _, _ => by simp [collatzIter]
  | q + 1, p, x, hp => by
    have hm : (q + 1) * p = p + q * p := by
      rw [Nat.succ_mul, Nat.add_comm]
    rw [hm, collatzIter_add, hp]
    exact collatzIter_mul_period q p x hp

def prefixBoundIter : Nat -> Nat -> Nat
  | 0, n => n + 2
  | K + 1, n => collatzIter (K + 1) n + prefixBoundIter K n

theorem two_le_prefixBoundIter : ∀ (K n : Nat), 2 ≤ prefixBoundIter K n
  | 0, n => by simp [prefixBoundIter]
  | K + 1, n => by
    have ih := two_le_prefixBoundIter K n
    simp only [prefixBoundIter]
    omega

theorem le_prefixBoundIter : ∀ (K j n : Nat),
    j ≤ K -> collatzIter j n ≤ prefixBoundIter K n
  | 0, j, n, hj => by
    have hj0 : j = 0 := by omega
    subst hj0
    simp only [collatzIter, prefixBoundIter]
    omega
  | K + 1, j, n, hj => by
    by_cases hjk : j = K + 1
    · subst hjk
      simp only [prefixBoundIter]
      omega
    · have hprev := le_prefixBoundIter K j n (by omega)
      simp only [prefixBoundIter]
      omega

/--
  Canonical Equivalence 3 (The Two-Barrier Decomposition Theorem):
  The standard Collatz Conjecture holds IF AND ONLY IF:
    (A) `NoDivergentPositiveOrbits` (Open Problem A), AND
    (B) `NoNontrivialPositiveCycles` (Open Problem B).
-/
theorem collatz_iff_two_barriers :
    CollatzConjectureStandard ↔ (NoDivergentPositiveOrbits ∧ NoNontrivialPositiveCycles) := by
  rw [collatz_standard_iff_compressed]
  constructor
  · intro hcomp
    constructor
    · intro n hn
      rcases hcomp n hn with ⟨K, hK⟩
      refine ⟨prefixBoundIter K n, ?_⟩
      intro j
      by_cases hjK : j ≤ K
      · exact le_prefixBoundIter K j n hjK
      · have h2 := two_le_prefixBoundIter K n
        have htail : collatzIter j n = collatzIter (j - K) 1 := by
          have hsplit : K + (j - K) = j := by omega
          calc
            collatzIter j n = collatzIter (K + (j - K)) n := by rw [hsplit]
            _ = collatzIter (j - K) (collatzIter K n) := collatzIter_add K (j - K) n
            _ = collatzIter (j - K) 1 := by rw [hK]
        have htriv := collatzIter_trivial_cycle (j - K) 1 (Or.inl rfl)
        rw [htail]
        rcases htriv with h1 | h2 <;> omega
    · intro x p hx hp hcyc
      rcases hcomp x hx with ⟨k, hk⟩
      by_cases hk0 : k = 0
      · subst hk0
        exact Or.inl hk
      · have hkp : k ≤ k * p := by
          have hp1 : 1 ≤ p := by omega
          have hm := Nat.mul_le_mul_left k hp1
          omega
        have hperiodic : collatzIter (k * p) x = x := collatzIter_mul_period k p x hcyc
        have hsplit : k * p = k + (k * p - k) := by omega
        rw [hsplit, collatzIter_add, hk] at hperiodic
        have htriv := collatzIter_trivial_cycle (k * p - k) 1 (Or.inl rfl)
        rw [hperiodic] at htriv
        exact htriv
  · rintro ⟨hbdd, hnocyc⟩ n hn
    rcases hbdd n hn with ⟨B, hB⟩
    rcases bounded_seq_repeats B (fun k => collatzIter k n) hB with ⟨i, j, hij, heq⟩
    have hsplit : j = i + (j - i) := by omega
    rw [hsplit, collatzIter_add] at heq
    have hxpos : collatzIter i n > 0 := collatzIter_pos i n hn
    have htriv := hnocyc (collatzIter i n) (j - i) hxpos (by omega) heq.symm
    rcases htriv with h1 | h2
    · exact ⟨i, h1⟩
    · refine ⟨i + 1, ?_⟩
      rw [collatzIter_add, h2]
      rfl

theorem collatzStepInt_ofNat (n : Nat) :
    collatzStepInt (n : Int) = (collatzStep n : Int) := by
  unfold collatzStepInt collatzStep
  cases h : (n % 2 == 0) with
  | true =>
    have hm : n % 2 = 0 := of_decide_eq_true h
    have hi : ((n : Int) % 2 == 0) = true := decide_eq_true (by omega)
    rw [hi]
    simp
  | false =>
    have hm : n % 2 ≠ 0 := of_decide_eq_false h
    have hi : ((n : Int) % 2 == 0) = false := decide_eq_false (by omega)
    rw [hi]
    simp

theorem collatzIterInt_ofNat : ∀ (k n : Nat),
    collatzIterInt k (n : Int) = (collatzIter k n : Int)
  | 0, _ => rfl
  | k + 1, n => by
    simp only [collatzIterInt, collatzIter]
    rw [collatzStepInt_ofNat]
    exact collatzIterInt_ofNat k (collatzStep n)

def parityOfIter : Nat -> Nat -> List Bool
  | 0, _ => []
  | k + 1, n => (if n % 2 == 0 then false else true) :: parityOfIter k (collatzStep n)

theorem parityOfIter_length : ∀ (k n : Nat), (parityOfIter k n).length = k
  | 0, _ => rfl
  | k + 1, n => by simp [parityOfIter, parityOfIter_length k (collatzStep n)]

theorem parityOfIter_matches : ∀ (k n : Nat),
    matchesParity (parityOfIter k n) (n : Int)
  | 0, _ => trivial
  | k + 1, n => by
    simp only [parityOfIter]
    cases h : (n % 2 == 0) with
    | true =>
      have hm : n % 2 = 0 := of_decide_eq_true h
      dsimp [matchesParity]
      refine ⟨by omega, ?_⟩
      rw [collatzStepInt_ofNat]
      exact parityOfIter_matches k (collatzStep n)
    | false =>
      have hm : n % 2 ≠ 0 := of_decide_eq_false h
      dsimp [matchesParity]
      refine ⟨by omega, ?_⟩
      rw [collatzStepInt_ofNat]
      exact parityOfIter_matches k (collatzStep n)

theorem affineCarryAuxInt_shift : ∀ (u : List Bool) (j : Nat) (acc : Int),
    affineCarryAuxInt u j acc =
      (3 : Int) ^ parityWeight u * acc + (2 : Int) ^ j * affineCarryAuxInt u 0 0
  | [], j, acc => by simp [affineCarryAuxInt, parityWeight]
  | false :: rest, j, acc => by
    simp only [affineCarryAuxInt, parityWeight]
    rw [affineCarryAuxInt_shift rest (j + 1) acc]
    rw [affineCarryAuxInt_shift rest 1 0]
    have hp : (2 : Int) ^ (j + 1) = (2 : Int) ^ j * 2 := Int.pow_succ 2 j
    have hz : (3 : Int) ^ parityWeight rest * 0 + (2 : Int) ^ 1 * affineCarryAuxInt rest 0 0 =
        2 * affineCarryAuxInt rest 0 0 := by omega
    rw [hz, hp, Int.mul_assoc]
  | true :: rest, j, acc => by
    simp only [affineCarryAuxInt, parityWeight]
    rw [affineCarryAuxInt_shift rest (j + 1) (3 * acc + (2 : Int) ^ j)]
    have h10 : 3 * (0 : Int) + (2 : Int) ^ 0 = 1 := rfl
    have h01 : 0 + 1 = 1 := rfl
    rw [h01, h10, affineCarryAuxInt_shift rest 1 1]
    have hp3 : (3 : Int) ^ (1 + parityWeight rest) = (3 : Int) ^ parityWeight rest * 3 := by
      rw [Nat.add_comm 1, Int.pow_succ]
    have hp2 : (2 : Int) ^ (j + 1) = (2 : Int) ^ j * 2 := Int.pow_succ 2 j
    rw [hp3, hp2]
    have ha : (3 : Int) ^ parityWeight rest * (3 * acc + (2 : Int) ^ j) =
        (3 : Int) ^ parityWeight rest * 3 * acc + (2 : Int) ^ j * (3 : Int) ^ parityWeight rest := by
      rw [Int.mul_add, ← Int.mul_assoc ((3 : Int) ^ parityWeight rest) 3 acc,
          Int.mul_comm ((3 : Int) ^ parityWeight rest) ((2 : Int) ^ j)]
    have hb1 : (3 : Int) ^ parityWeight rest * 1 + (2 : Int) ^ 1 * affineCarryAuxInt rest 0 0 =
        (3 : Int) ^ parityWeight rest + 2 * affineCarryAuxInt rest 0 0 := by omega
    rw [hb1]
    have hb : (2 : Int) ^ j * ((3 : Int) ^ parityWeight rest + 2 * affineCarryAuxInt rest 0 0) =
        (2 : Int) ^ j * (3 : Int) ^ parityWeight rest +
        (2 : Int) ^ j * 2 * affineCarryAuxInt rest 0 0 := by
      rw [Int.mul_add, ← Int.mul_assoc ((2 : Int) ^ j) 2]
    rw [ha, hb]
    omega

theorem pow3_mod2 : ∀ w : Nat, (3 : Int) ^ w % 2 = 1
  | 0 => rfl
  | w + 1 => by
    have ih := pow3_mod2 w
    rw [Int.pow_succ, Int.mul_emod, ih]
    rfl

theorem odd_mul_even_iff (a y : Int) (ha : a % 2 = 1) (he : (a * y) % 2 = 0) :
    y % 2 = 0 := by
  rw [Int.mul_emod, ha] at he
  omega

/--
  Theorem 9 Converse (Universal 2-Adic Hensel Parity Forcing over Z):
  Any integer `x : Int` satisfying `2^|v| = 3^w(v) * x + C(v)` AUTOMATICALLY
  realizes parity vector `v` step-by-step and reaches `collatzIterInt |v| x = 1`!
-/
theorem one_equation_converse_universal : ∀ (v : List Bool) (x : Int),
    (2 : Int) ^ v.length = (3 : Int) ^ parityWeight v * x + affineCarryInt v ->
    matchesParity v x ∧ collatzIterInt v.length x = 1
  | [], x, heq => by
    simp [parityWeight, affineCarryInt, affineCarryAuxInt] at heq
    exact ⟨trivial, by simp [collatzIterInt]; omega⟩
  | false :: rest, x, heq => by
    have hc : affineCarryInt (false :: rest) = 2 * affineCarryInt rest := by
      unfold affineCarryInt
      simp only [affineCarryAuxInt]
      have h01 : 0 + 1 = 1 := rfl
      rw [h01]
      have hs := affineCarryAuxInt_shift rest 1 0
      omega
    have hp2 : (2 : Int) ^ (false :: rest).length = 2 * (2 : Int) ^ rest.length := by
      simp only [List.length_cons, Int.pow_succ]
      omega
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
    have hnext : (2 : Int) ^ rest.length =
        (3 : Int) ^ parityWeight rest * collatzStepInt x + affineCarryInt rest := by
      omega
    rcases one_equation_converse_universal rest (collatzStepInt x) hnext with ⟨hm, hi⟩
    exact ⟨⟨hx_ev, hm⟩, hi⟩
  | true :: rest, x, heq => by
    have hc : affineCarryInt (true :: rest) =
        (3 : Int) ^ parityWeight rest + 2 * affineCarryInt rest := by
      unfold affineCarryInt
      simp only [affineCarryAuxInt]
      have h10 : 3 * (0 : Int) + (2 : Int) ^ 0 = 1 := rfl
      have h01 : 0 + 1 = 1 := rfl
      rw [h01, h10]
      have hs := affineCarryAuxInt_shift rest 1 1
      omega
    have hp2 : (2 : Int) ^ (true :: rest).length = 2 * (2 : Int) ^ rest.length := by
      simp only [List.length_cons, Int.pow_succ]
      omega
    have hp3 : (3 : Int) ^ parityWeight (true :: rest) * x + (3 : Int) ^ parityWeight rest =
        (3 : Int) ^ parityWeight rest * (3 * x + 1) := by
      simp only [parityWeight]
      have hpw : 1 + parityWeight rest = parityWeight rest + 1 := by omega
      rw [hpw, Int.pow_succ, Int.mul_add, Int.mul_one, Int.mul_assoc]
    rw [hc, hp2] at heq
    have hcomb : 2 * (2 : Int) ^ rest.length =
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
    have hnext : (2 : Int) ^ rest.length =
        (3 : Int) ^ parityWeight rest * collatzStepInt x + affineCarryInt rest := by
      omega
    rcases one_equation_converse_universal rest (collatzStepInt x) hnext with ⟨hm, hi⟩
    exact ⟨⟨hx_odd, hm⟩, hi⟩

/--
  Canonical Equivalence 4 (Theorem 9 Full Diophantine Equivalence):
  The standard Collatz Conjecture is logically equivalent to the pure
  One-Equation Diophantine solvability `CollatzOneEquationConjecture`!
-/
theorem collatz_iff_one_equation_diophantine :
    CollatzConjectureStandard ↔ CollatzOneEquationConjecture := by
  rw [collatz_standard_iff_compressed]
  constructor
  · intro hcomp n hn
    rcases hcomp n hn with ⟨k, hk⟩
    refine ⟨parityOfIter k n, ?_⟩
    have hm := parityOfIter_matches k n
    have hlen := parityOfIter_length k n
    have h1 : collatzIterInt (parityOfIter k n).length (n : Int) = 1 := by
      rw [hlen, collatzIterInt_ofNat, hk]
      rfl
    exact one_equation_forward_universal (parityOfIter k n) (n : Int) hm h1
  · intro hone n hn
    rcases hone n hn with ⟨v, hv⟩
    rcases one_equation_converse_universal v (n : Int) hv with ⟨_, hi⟩
    rw [collatzIterInt_ofNat] at hi
    exact ⟨v.length, by omega⟩

-- ============================================================================
-- 10. Theorem 23 (Attack Line A): Minimal Non-Descending Counterexample
--     Rigidity, Hercher Entry Merger, Unique q=3 Merger, & S_infty Obstructions
-- ============================================================================

/--
  Theorem 23.1a (Minimal Counterexample Coalescence Contradiction):
  Suppose `nMin > 1` is a minimal counterexample to `StrictDescentHypothesis`,
  so no `K` gives `0 < collatzIter K nMin < nMin`, while some smaller positive
  integer `nPrime` (`1 <= nPrime < nMin`) reaches `1` (`collatzIter k1 nPrime = 1`).
  Then `nMin` CANNOT coalesce with `nPrime` at ANY pair of step counts `(k, kp)`
  (covering both `kp <= k1` and `kp > k1` in the `{1, 2}` trivial cycle).
-/
theorem strict_descent_minimal_counterexample_coalescence_contradiction
    (nMin nPrime k kp : Nat)
    (hnMin : nMin > 1)
    (_hnPrimePos : 1 ≤ nPrime)
    (_hnPrimeLt : nPrime < nMin)
    (hnoDesc : ∀ K : Nat, ¬ (0 < collatzIter K nMin ∧ collatzIter K nMin < nMin))
    (hreach : ∃ k1 : Nat, collatzIter k1 nPrime = 1)
    (hcoal : collatzIter k nMin = collatzIter kp nPrime) :
    False := by
  rcases hreach with ⟨k1, hk1⟩
  by_cases hle : kp ≤ k1
  · have hsplit : k1 = kp + (k1 - kp) := by omega
    have h1 : collatzIter (k + (k1 - kp)) nMin = 1 := by
      rw [collatzIter_add, hcoal, ← collatzIter_add, ← hsplit, hk1]
    exact hnoDesc (k + (k1 - kp)) ⟨by rw [h1]; omega, by rw [h1]; omega⟩
  · have hsplit : kp = k1 + (kp - k1) := by omega
    have htriv : collatzIter kp nPrime = 1 ∨ collatzIter kp nPrime = 2 := by
      rw [hsplit, collatzIter_add, hk1]
      exact collatzIter_trivial_cycle (kp - k1) 1 (Or.inl rfl)
    rcases htriv with h1 | h2
    · have hc1 : collatzIter k nMin = 1 := by rw [hcoal, h1]
      exact hnoDesc k ⟨by rw [hc1]; omega, by rw [hc1]; omega⟩
    · have hc2 : collatzIter (k + 1) nMin = 1 := by
        rw [collatzIter_add, hcoal, h2]
        rfl
      exact hnoDesc (k + 1) ⟨by rw [hc2]; omega, by rw [hc2]; omega⟩

/--
  Theorem 23.1b (Mod-4 Rigidity of Any Non-Descending `n > 1`):
  If `n > 1` neither descends in 1 compressed step nor in 2 compressed steps,
  then necessarily `n % 4 = 3` (forcing initial odd-run length `w_1 >= 2`).
-/
theorem minimal_counterexample_mod4_eq_3 (n : Nat)
    (hn : n > 1)
    (h1 : collatzIter 1 n ≥ n)
    (h2 : collatzIter 2 n ≥ n) :
    n % 4 = 3 := by
  cases hev : (n % 2 == 0) with
  | true =>
    have hm : n % 2 = 0 := of_decide_eq_true hev
    have hs1 : collatzIter 1 n = n / 2 := by
      simp [collatzIter, collatzStep, hev]
    omega
  | false =>
    have hm : n % 2 ≠ 0 := of_decide_eq_false hev
    have hs1 : collatzStep n = (3 * n + 1) / 2 := by
      simp [collatzStep, hev]
    by_cases hmod1 : n % 4 = 1
    · have hs1_ev : ((3 * n + 1) / 2 % 2 == 0) = true := decide_eq_true (by omega)
      have hs2 : collatzIter 2 n = ((3 * n + 1) / 2) / 2 := by
        change collatzStep (collatzStep n) = _
        rw [hs1]
        unfold collatzStep
        rw [hs1_ev]
        simp
      omega
    · omega

theorem pow2_pos_nat : ∀ k : Nat, 2 ^ k ≥ 1
  | 0 => by decide
  | k + 1 => by
    have ih := pow2_pos_nat k
    rw [Nat.pow_succ]
    omega

theorem pow3_pos_nat : ∀ k : Nat, 3 ^ k ≥ 1
  | 0 => by decide
  | k + 1 => by
    have ih := pow3_pos_nat k
    rw [Nat.pow_succ]
    omega

/-- Exact compressed trajectory across an initial odd block `n = 2^m * u - 1` -/
theorem odd_run_iter : ∀ (m u : Nat), u ≥ 1 ->
    collatzIter m (2 ^ m * u - 1) = 3 ^ m * u - 1
  | 0, u, _ => by simp [collatzIter]
  | m + 1, u, hu => by
    have hp2 : 2 ^ m ≥ 1 := pow2_pos_nat m
    have hX : 2 ^ m * u ≥ 1 := Nat.mul_pos hp2 hu
    have hmul : 2 ^ (m + 1) * u = 2 * (2 ^ m * u) := by
      rw [Nat.pow_succ]
      calc
        2 ^ m * 2 * u = 2 * 2 ^ m * u := by rw [Nat.mul_comm (2 ^ m) 2]
        _ = 2 * (2 ^ m * u) := by rw [Nat.mul_assoc]
    have hodd : ((2 ^ (m + 1) * u - 1) % 2 == 0) = false := decide_eq_false (by omega)
    have hstep : collatzStep (2 ^ (m + 1) * u - 1) = 2 ^ m * (3 * u) - 1 := by
      simp only [collatzStep, hodd]
      simp
      have h3u : 2 ^ m * (3 * u) = 3 * (2 ^ m * u) := by
        rw [← Nat.mul_assoc, Nat.mul_comm (2 ^ m) 3, Nat.mul_assoc]
      omega
    simp only [collatzIter, hstep]
    rw [odd_run_iter m (3 * u) (by omega)]
    have hp3 : 3 ^ m * (3 * u) = 3 ^ (m + 1) * u := by
      rw [Nat.pow_succ, ← Nat.mul_assoc]
    rw [hp3]

/--
  Theorem 23.1c (Hercher Entry Merger Forcing `a_1 = 1` on `n_min`):
  For ANY `n` with `n + 1 = 2^w * u` (`w >= 2, u >= 1`) whose first even run
  has length `a_1 >= 2` (i.e. `(3^w * u - 1) % 4 = 0`), the strictly smaller
  positive partner `n' = (n - 1) / 2` (`1 <= n' < n`) merges identically with `n`:
    `collatzIter (w + 1) ((n - 1) / 2) = collatzIter (w + 2) n`.
-/
theorem hercher_entry_merger_a1_ge_2 (n w u : Nat)
    (hw : w ≥ 2) (hu : u ≥ 1)
    (hn : n + 1 = 2 ^ w * u)
    (ha1 : (3 ^ w * u - 1) % 4 = 0) :
    1 ≤ (n - 1) / 2 ∧ (n - 1) / 2 < n ∧
    collatzIter (w + 1) ((n - 1) / 2) = collatzIter (w + 2) n := by
  have hp2w2 : 2 ^ (w - 2) ≥ 1 := pow2_pos_nat (w - 2)
  have hp2w1 : 2 ^ (w - 1) ≥ 2 := by
    have heq : w - 1 = (w - 2) + 1 := by omega
    rw [heq, Nat.pow_succ]
    omega
  have hXw1 : 2 ^ (w - 1) * u ≥ 2 := Nat.mul_le_mul hp2w1 hu
  have hXw : 2 ^ w * u = 2 * (2 ^ (w - 1) * u) := by
    have heq : w = (w - 1) + 1 := by omega
    rw [heq, Nat.pow_succ]
    calc
      2 ^ (w - 1) * 2 * u = 2 * 2 ^ (w - 1) * u := by rw [Nat.mul_comm _ 2]
      _ = 2 * (2 ^ (w - 1) * u) := by rw [Nat.mul_assoc]
  have hn_eq : n = 2 ^ w * u - 1 := by omega
  have hp_eq : (n - 1) / 2 = 2 ^ (w - 1) * u - 1 := by omega
  refine ⟨by omega, by omega, ?_⟩
  let z := 3 ^ (w - 1) * u
  have hz_pos : z ≥ 1 := Nat.mul_pos (pow3_pos_nat (w - 1)) hu
  have h3z : 3 ^ w * u = 3 * z := by
    have heq : w = (w - 1) + 1 := by omega
    rw [heq, Nat.pow_succ]
    calc
      3 ^ (w - 1) * 3 * u = 3 * 3 ^ (w - 1) * u := by rw [Nat.mul_comm _ 3]
      _ = 3 * z := by rw [Nat.mul_assoc]
  rw [h3z] at ha1
  have hw1_split : w + 1 = (w - 1) + 2 := by omega
  rw [hw1_split, collatzIter_add (w - 1) 2 ((n - 1) / 2), hp_eq, odd_run_iter (w - 1) u hu]
  rw [collatzIter_add w 2 n, hn_eq, odd_run_iter w u hu, h3z]
  have hz1_ev : ((z - 1) % 2 == 0) = true := decide_eq_true (by omega)
  have hz1_s1 : collatzStep (z - 1) = (z - 1) / 2 := by simp [collatzStep, hz1_ev]
  have hz1_odd : (((z - 1) / 2) % 2 == 0) = false := decide_eq_false (by omega)
  have hz1_s2 : collatzStep ((z - 1) / 2) = (3 * ((z - 1) / 2) + 1) / 2 := by
    simp [collatzStep, hz1_odd]
  have h3z_ev1 : ((3 * z - 1) % 2 == 0) = true := decide_eq_true (by omega)
  have h3z_s1 : collatzStep (3 * z - 1) = (3 * z - 1) / 2 := by simp [collatzStep, h3z_ev1]
  have h3z_ev2 : (((3 * z - 1) / 2) % 2 == 0) = true := decide_eq_true (by omega)
  have h3z_s2 : collatzStep ((3 * z - 1) / 2) = ((3 * z - 1) / 2) / 2 := by
    simp [collatzStep, h3z_ev2]
  change collatzStep (collatzStep (z - 1)) = collatzStep (collatzStep (3 * z - 1))
  rw [hz1_s1, hz1_s2, h3z_s1, h3z_s2]
  omega

/--
  Theorem 23.2 (Uniqueness of `(q, r) = (3, 5)` Predecessor Merger):
  Among all odd multipliers `q >= 3` and odd mod-8 residues `r in {1, 3, 5, 7}`,
  the polynomial merger condition `q * (r - 4) = 3` (`T_q^2(4t + 2) = T_q^3(8t + r)`)
  holds IF AND ONLY IF `q = 3` and `r = 5` (discriminating `3n + 1` from `5n + 1`).
-/
theorem odd_multiplier_merger_unique_q3 (q r : Int)
    (hq : q ≥ 3) (_hq_odd : q % 2 = 1)
    (hr : r = 1 ∨ r = 3 ∨ r = 5 ∨ r = 7) :
    (q * (r - 4) = 3) ↔ (q = 3 ∧ r = 5) := by
  rcases hr with rfl | rfl | rfl | rfl <;> omega

theorem pow2_lt_pow3_pos : ∀ m : Nat, m ≥ 1 -> 2 ^ m < 3 ^ m
  | 0, hm => by omega
  | 1, _ => by decide
  | m + 2, _ => by
    have ih := pow2_lt_pow3_pos (m + 1) (by omega)
    rw [Nat.pow_succ 2 (m + 1), Nat.pow_succ 3 (m + 1)]
    omega

theorem pow3_mono_nat_aux : ∀ a d : Nat, 3 ^ a ≤ 3 ^ (a + d)
  | _, 0 => by simp
  | a, d + 1 => by
    have ih := pow3_mono_nat_aux a d
    rw [show a + (d + 1) = (a + d) + 1 by omega, Nat.pow_succ]
    omega

/--
  Theorem 23.4a (`Z^-` `-1` Cycle Anti-Contractivity):
  Along the all-ones parity prefix `1^k` (`w = k`) of `-1`, for every target
  length `kp < k` and weight `wp <= kp`, `2^(k - kp) < 3^(k - wp)` strictly,
  violating `2^k > 2^kp * 3^(k - wp)` for ALL `1 <= kp < k`.
-/
theorem neg_one_cycle_anti_contractive (k kp wp : Nat)
    (hwp : wp ≤ kp) (hkp : kp < k) :
    2 ^ (k - kp) < 3 ^ (k - wp) := by
  have h1 : 2 ^ (k - kp) < 3 ^ (k - kp) := pow2_lt_pow3_pos (k - kp) (by omega)
  have h2 : 3 ^ (k - kp) ≤ 3 ^ (k - wp) := by
    have hle := pow3_mono_nat_aux (k - kp) (kp - wp)
    rwa [show (k - kp) + (kp - wp) = k - wp by omega] at hle
  omega

/--
  Theorem 23.4b (Sturmian `w' = 2` Mod-9 Disjointness Obstruction):
  Isolated zeros (`s, d in {1, 2}`) in the balanced Sturmian word `v*(infty)` force
  `5 * 2^s != 3 + 2^d (mod 9)` across all 4 pairs, blocking all `w' = 2` coalescences.
-/
theorem sturmian_w2_mod9_disjoint (s d : Nat)
    (hs : s = 1 ∨ s = 2) (hd : d = 1 ∨ d = 2) :
    (5 * 2 ^ s) % 9 ≠ (3 + 2 ^ d) % 9 := by
  rcases hs with rfl | rfl <;> rcases hd with rfl | rfl <;> decide

theorem parityWeight_append : ∀ (u v : List Bool),
    parityWeight (u ++ v) = parityWeight u + parityWeight v
  | [], v => by simp [parityWeight]
  | false :: rest, v => by simp [parityWeight, parityWeight_append rest v]
  | true :: rest, v => by
    simp only [List.cons_append, parityWeight, parityWeight_append rest v]
    omega

theorem affineCarryAuxInt_append_acc : ∀ (u v : List Bool) (j : Nat) (acc : Int),
    affineCarryAuxInt (u ++ v) j acc =
      affineCarryAuxInt v (j + u.length) (affineCarryAuxInt u j acc)
  | [], v, j, acc => by simp [affineCarryAuxInt]
  | false :: rest, v, j, acc => by
    simp only [List.cons_append, affineCarryAuxInt, List.length_cons]
    have hlen : j + (rest.length + 1) = (j + 1) + rest.length := by omega
    rw [hlen]
    exact affineCarryAuxInt_append_acc rest v (j + 1) acc
  | true :: rest, v, j, acc => by
    simp only [List.cons_append, affineCarryAuxInt, List.length_cons]
    have hlen : j + (rest.length + 1) = (j + 1) + rest.length := by omega
    rw [hlen]
    exact affineCarryAuxInt_append_acc rest v (j + 1) (3 * acc + (2 : Int) ^ j)

theorem affineCarryInt_append (u s : List Bool) :
    affineCarryInt (u ++ s) =
      (3 : Int) ^ parityWeight s * affineCarryInt u + (2 : Int) ^ u.length * affineCarryInt s := by
  unfold affineCarryInt
  rw [affineCarryAuxInt_append_acc u s 0 0, Nat.zero_add]
  exact affineCarryAuxInt_shift s u.length (affineCarryAuxInt u 0 0)

theorem mul_left_cancel_pow2_int : ∀ (m : Nat) (a b : Int),
    (2 : Int) ^ m * a = (2 : Int) ^ m * b -> a = b
  | 0, a, b, h => by simpa using h
  | m + 1, a, b, h => by
    rw [Int.pow_succ, Int.mul_assoc, Int.mul_assoc] at h
    have h1 := mul_left_cancel_pow2_int m (2 * a) (2 * b) h
    omega

/--
  Theorem 23.3 (Universal Minimum-Drift Suffix Reduction on the End-Expanding Cone `E`):
  For any parity-word concatenation `u ++ s` with net-shrinking prefix `3^w(u) <= 2^|u|`,
  if `yPrime` is the `|u|`-step affine image of `nPrime` and `z` is the `|u ++ s|`-step
  affine image of `nPrime`, then `z` is identically the `|s|`-step affine image of `yPrime`
  along `s`, `C(u ++ s) ≡ 2^|u| * C(s) (mod 3^w(s))`, and contractivity along `u ++ s`
  implies strict contractivity along `s` (proving `S = E` without cyclic-shift fallacy).
-/
theorem end_expanding_coalescence_reduces_to_suffix
    (u s : List Bool) (k w : Nat) (nPrime yPrime z : Int)
    (hshrink : 3 ^ parityWeight u ≤ 2 ^ u.length)
    (hy : (2 : Int) ^ u.length * yPrime = (3 : Int) ^ parityWeight u * nPrime + affineCarryInt u)
    (hz : (2 : Int) ^ (u ++ s).length * z =
            (3 : Int) ^ parityWeight (u ++ s) * nPrime + affineCarryInt (u ++ s)) :
    ((2 : Int) ^ s.length * z = (3 : Int) ^ parityWeight s * yPrime + affineCarryInt s) ∧
    ((3 : Int) ^ parityWeight s ∣
      (affineCarryInt (u ++ s) - (2 : Int) ^ u.length * affineCarryInt s)) ∧
    (2 ^ (u ++ s).length * 3 ^ w < 2 ^ k * 3 ^ parityWeight (u ++ s) ->
      2 ^ s.length * 3 ^ w < 2 ^ k * 3 ^ parityWeight s) := by
  refine ⟨?_, ?_, ?_⟩
  · apply mul_left_cancel_pow2_int u.length
    have hlhs : (2 : Int) ^ u.length * ((2 : Int) ^ s.length * z) =
        (2 : Int) ^ (u ++ s).length * z := by
      rw [List.length_append, Int.pow_add, Int.mul_assoc]
    rw [hlhs, hz, parityWeight_append, Int.pow_add, affineCarryInt_append]
    have h1 : (3 : Int) ^ parityWeight u * (3 : Int) ^ parityWeight s * nPrime =
        (3 : Int) ^ parityWeight s * ((3 : Int) ^ parityWeight u * nPrime) := by
      rw [Int.mul_comm ((3 : Int) ^ parityWeight u) ((3 : Int) ^ parityWeight s), Int.mul_assoc]
    have h2 : (3 : Int) ^ parityWeight s * ((2 : Int) ^ u.length * yPrime) =
        (2 : Int) ^ u.length * ((3 : Int) ^ parityWeight s * yPrime) := by
      rw [← Int.mul_assoc, Int.mul_comm ((3 : Int) ^ parityWeight s) ((2 : Int) ^ u.length),
          Int.mul_assoc]
    calc
      (3 : Int) ^ parityWeight u * (3 : Int) ^ parityWeight s * nPrime +
          ((3 : Int) ^ parityWeight s * affineCarryInt u + (2 : Int) ^ u.length * affineCarryInt s)
          = (3 : Int) ^ parityWeight s * ((3 : Int) ^ parityWeight u * nPrime) +
              (3 : Int) ^ parityWeight s * affineCarryInt u +
              (2 : Int) ^ u.length * affineCarryInt s := by rw [h1, Int.add_assoc]
      _ = (3 : Int) ^ parityWeight s * ((3 : Int) ^ parityWeight u * nPrime + affineCarryInt u) +
              (2 : Int) ^ u.length * affineCarryInt s := by rw [← Int.mul_add]
      _ = (3 : Int) ^ parityWeight s * ((2 : Int) ^ u.length * yPrime) +
              (2 : Int) ^ u.length * affineCarryInt s := by rw [← hy]
      _ = (2 : Int) ^ u.length * ((3 : Int) ^ parityWeight s * yPrime + affineCarryInt s) := by
              rw [h2, ← Int.mul_add]
  · refine ⟨affineCarryInt u, ?_⟩
    rw [affineCarryInt_append]
    omega
  · intro hlt
    rw [List.length_append, Nat.pow_add, Nat.mul_assoc, parityWeight_append, Nat.pow_add] at hlt
    have hrhs : 2 ^ k * (3 ^ parityWeight u * 3 ^ parityWeight s) =
        3 ^ parityWeight u * (2 ^ k * 3 ^ parityWeight s) := by
      rw [← Nat.mul_assoc, Nat.mul_comm (2 ^ k) (3 ^ parityWeight u), Nat.mul_assoc]
    rw [hrhs] at hlt
    have hle : 3 ^ parityWeight u * (2 ^ k * 3 ^ parityWeight s) ≤
        2 ^ u.length * (2 ^ k * 3 ^ parityWeight s) :=
      Nat.mul_le_mul_right (2 ^ k * 3 ^ parityWeight s) hshrink
    apply Classical.byContradiction
    intro hge
    have hm : 2 ^ u.length * (2 ^ k * 3 ^ parityWeight s) ≤
        2 ^ u.length * (2 ^ s.length * 3 ^ w) :=
      Nat.mul_le_mul_left (2 ^ u.length) (by omega)
    omega

-- ============================================================================
-- 11. Theorem 24 (Attack Line B): Cyclic-Shift Carry GCD Collapse, Rational
--     Convergents, Recursive Multi-Step Hensel Verifier (`m = 92, 93`), & `m <= 95`
-- ============================================================================

/--
  Theorem 24.1a (Even Cyclic-Rotation Carry Identity):
  Rotating a leading `0` (`false`) to the back halves `C(false :: u) = 2 * C(u ++ [false])`.
-/
theorem affineCarryInt_rotate_false (u : List Bool) :
    affineCarryInt (false :: u) = 2 * affineCarryInt (u ++ [false]) := by
  have hlhs : affineCarryInt (false :: u) = 2 * affineCarryInt u := by
    unfold affineCarryInt
    simp only [affineCarryAuxInt]
    have h01 : 0 + 1 = 1 := rfl
    rw [h01, affineCarryAuxInt_shift u 1 0]
    omega
  have hrhs : affineCarryInt (u ++ [false]) = affineCarryInt u := by
    unfold affineCarryInt
    rw [affineCarryAuxInt_append_acc u [false] 0 0]
    rfl
  rw [hlhs, hrhs]

/--
  Theorem 24.1b (Odd Cyclic-Rotation Carry Identity):
  Rotating a leading `1` (`true`) to the back satisfies the exact cycle-determinant law:
    `2 * C(u ++ [true]) - 3 * C(true :: u) = 2^(|u| + 1) - 3^(w(u) + 1)`.
-/
theorem affineCarryInt_rotate_true (u : List Bool) :
    2 * affineCarryInt (u ++ [true]) - 3 * affineCarryInt (true :: u) =
      (2 : Int) ^ (u.length + 1) - (3 : Int) ^ (parityWeight u + 1) := by
  have hlhs : affineCarryInt (u ++ [true]) = 3 * affineCarryInt u + (2 : Int) ^ u.length := by
    unfold affineCarryInt
    rw [affineCarryAuxInt_append_acc u [true] 0 0]
    simp [affineCarryAuxInt]
  have hrhs : affineCarryInt (true :: u) = (3 : Int) ^ parityWeight u + 2 * affineCarryInt u := by
    unfold affineCarryInt
    simp only [affineCarryAuxInt]
    have h10 : 3 * (0 : Int) + (2 : Int) ^ 0 = 1 := rfl
    have h01 : 0 + 1 = 1 := rfl
    rw [h01, h10, affineCarryAuxInt_shift u 1 1]
    omega
  have hp2 : (2 : Int) ^ (u.length + 1) = 2 * (2 : Int) ^ u.length := by
    rw [Int.pow_succ, Int.mul_comm]
  have hp3 : (3 : Int) ^ (parityWeight u + 1) = 3 * (3 : Int) ^ parityWeight u := by
    rw [Int.pow_succ, Int.mul_comm]
  rw [hlhs, hrhs, hp2, hp3]
  omega

theorem pow4_mod3 : ∀ k : Nat, (2 : Int) ^ (2 * k) % 3 = 1
  | 0 => rfl
  | k + 1 => by
    have heq : 2 * (k + 1) = 2 * k + 2 := by omega
    have hp : (2 : Int) ^ (2 * k + 2) = (2 : Int) ^ (2 * k) * 4 := by
      rw [Int.pow_succ, Int.pow_succ, Int.mul_assoc]
      rfl
    rw [heq, hp, Int.mul_emod, pow4_mod3 k]
    rfl

theorem cancel_two_of_dvd_pow2_sub_pow3 (d A : Int) (k w : Nat)
    (hk : k ≥ 1)
    (hd : d ∣ ((2 : Int) ^ k - (3 : Int) ^ w))
    (h2 : d ∣ 2 * A) :
    d ∣ A := by
  have hp2 : (2 : Int) ^ k = 2 * (2 : Int) ^ (k - 1) := by
    cases k with
    | zero => omega
    | succ k' => simp [Int.pow_succ, Int.mul_comm]
  have hp3 : (3 : Int) ^ w % 2 = 1 := pow3_mod2 w
  let u2 : Int := ((3 : Int) ^ w + 1) / 2 - (2 : Int) ^ (k - 1)
  have hbez : 2 * u2 + ((2 : Int) ^ k - (3 : Int) ^ w) = 1 := by
    dsimp [u2]
    omega
  rcases hd with ⟨q1, hq1⟩
  rcases h2 with ⟨q2, hq2⟩
  refine ⟨u2 * q2 + A * q1, ?_⟩
  have hlin : d * (u2 * q2 + A * q1) = u2 * (2 * A) + A * ((2 : Int) ^ k - (3 : Int) ^ w) := by
    rw [Int.mul_add]
    have ha : d * (u2 * q2) = u2 * (2 * A) := by
      rw [← Int.mul_assoc, Int.mul_comm d u2, Int.mul_assoc, ← hq2]
    have hb : d * (A * q1) = A * ((2 : Int) ^ k - (3 : Int) ^ w) := by
      rw [← Int.mul_assoc, Int.mul_comm d A, Int.mul_assoc, ← hq1]
    rw [ha, hb]
  have hrhs : u2 * (2 * A) + A * ((2 : Int) ^ k - (3 : Int) ^ w) =
      A * (2 * u2 + ((2 : Int) ^ k - (3 : Int) ^ w)) := by
    rw [Int.mul_add, ← Int.mul_assoc u2 2 A, Int.mul_comm (u2 * 2) A, Int.mul_comm u2 2]
  rw [hlin, hrhs, hbez, Int.mul_one]

theorem cancel_three_of_dvd_pow2_sub_pow3 (d A : Int) (k w : Nat)
    (hw : w ≥ 1)
    (hd : d ∣ ((2 : Int) ^ k - (3 : Int) ^ w))
    (h3 : d ∣ 3 * A) :
    d ∣ A := by
  have hp3 : (3 : Int) ^ w = 3 * (3 : Int) ^ (w - 1) := by
    cases w with
    | zero => omega
    | succ w' => simp [Int.pow_succ, Int.mul_comm]
  have hp4 : (2 : Int) ^ (2 * k) = (2 : Int) ^ k * (2 : Int) ^ k := by
    rw [Nat.two_mul, Int.pow_add]
  have hm3 : (2 : Int) ^ (2 * k) % 3 = 1 := pow4_mod3 k
  let u3 : Int := (2 : Int) ^ k * (3 : Int) ^ (w - 1) - ((2 : Int) ^ (2 * k) - 1) / 3
  have hbez : 3 * u3 + (2 : Int) ^ k * ((2 : Int) ^ k - (3 : Int) ^ w) = 1 := by
    dsimp [u3]
    have hmul1 : 3 * ((2 : Int) ^ k * (3 : Int) ^ (w - 1)) = (2 : Int) ^ k * (3 : Int) ^ w := by
      rw [← Int.mul_assoc, Int.mul_comm 3 ((2 : Int) ^ k), Int.mul_assoc, ← hp3]
    have hmul2 : (2 : Int) ^ k * ((2 : Int) ^ k - (3 : Int) ^ w) =
        (2 : Int) ^ (2 * k) - (2 : Int) ^ k * (3 : Int) ^ w := by
      rw [Int.mul_sub, ← hp4]
    rw [Int.mul_sub, hmul1, hmul2]
    omega
  rcases hd with ⟨q1, hq1⟩
  rcases h3 with ⟨q3, hq3⟩
  refine ⟨u3 * q3 + A * ((2 : Int) ^ k * q1), ?_⟩
  have hlin : d * (u3 * q3 + A * ((2 : Int) ^ k * q1)) =
      u3 * (3 * A) + A * ((2 : Int) ^ k * ((2 : Int) ^ k - (3 : Int) ^ w)) := by
    rw [Int.mul_add]
    have ha : d * (u3 * q3) = u3 * (3 * A) := by
      rw [← Int.mul_assoc, Int.mul_comm d u3, Int.mul_assoc, ← hq3]
    have hb : d * (A * ((2 : Int) ^ k * q1)) =
        A * ((2 : Int) ^ k * ((2 : Int) ^ k - (3 : Int) ^ w)) := by
      calc
        d * (A * ((2 : Int) ^ k * q1))
            = A * ((2 : Int) ^ k * (d * q1)) := by
              rw [← Int.mul_assoc, Int.mul_comm d A, Int.mul_assoc,
                  ← Int.mul_assoc d ((2 : Int) ^ k) q1, Int.mul_comm d ((2 : Int) ^ k), Int.mul_assoc]
        _ = A * ((2 : Int) ^ k * ((2 : Int) ^ k - (3 : Int) ^ w)) := by rw [← hq1]
    rw [ha, hb]
  have hrhs : u3 * (3 * A) + A * ((2 : Int) ^ k * ((2 : Int) ^ k - (3 : Int) ^ w)) =
      A * (3 * u3 + (2 : Int) ^ k * ((2 : Int) ^ k - (3 : Int) ^ w)) := by
    rw [Int.mul_add, ← Int.mul_assoc u3 3 A, Int.mul_comm (u3 * 3) A, Int.mul_comm u3 3]
  rw [hlin, hrhs, hbez, Int.mul_one]

def rotateLeft1 : List Bool -> List Bool
  | [] => []
  | b :: u => u ++ [b]

def rotateLeft : Nat -> List Bool -> List Bool
  | 0, v => v
  | j + 1, v => rotateLeft j (rotateLeft1 v)

theorem rotateLeft1_length : ∀ v : List Bool, (rotateLeft1 v).length = v.length
  | [] => rfl
  | b :: u => by simp [rotateLeft1]

theorem rotateLeft1_weight : ∀ v : List Bool, parityWeight (rotateLeft1 v) = parityWeight v
  | [] => rfl
  | false :: u => by simp [rotateLeft1, parityWeight, parityWeight_append]
  | true :: u => by
    simp only [rotateLeft1, parityWeight, parityWeight_append]
    omega

theorem cyclic_shift_carry_dvd_step (v : List Bool) (d : Int)
    (hw : parityWeight v ≥ 1)
    (hd : d ∣ ((2 : Int) ^ v.length - (3 : Int) ^ parityWeight v)) :
    d ∣ affineCarryInt v ↔ d ∣ affineCarryInt (rotateLeft1 v) := by
  cases v with
  | nil => simp [parityWeight] at hw
  | cons b u =>
    cases b with
    | false =>
      simp only [rotateLeft1]
      rw [affineCarryInt_rotate_false u]
      constructor
      · intro h2
        exact cancel_two_of_dvd_pow2_sub_pow3 d (affineCarryInt (u ++ [false]))
          (u.length + 1) (parityWeight (false :: u)) (by omega) hd h2
      · rintro ⟨q, hq⟩
        exact ⟨2 * q, by rw [hq, ← Int.mul_assoc, Int.mul_comm 2 d, Int.mul_assoc]⟩
    | true =>
      simp only [rotateLeft1]
      have hrot := affineCarryInt_rotate_true u
      have hlen : (true :: u).length = u.length + 1 := rfl
      have hwt : parityWeight (true :: u) = parityWeight u + 1 := by simp [parityWeight]; omega
      rw [← hlen, ← hwt] at hrot
      rcases hd with ⟨qD, hqD⟩
      constructor
      · rintro ⟨qC, hqC⟩
        have h2 : d ∣ 2 * affineCarryInt (u ++ [true]) := by
          refine ⟨qD + 3 * qC, ?_⟩
          rw [Int.mul_add, ← Int.mul_assoc d 3 qC, Int.mul_comm d 3, Int.mul_assoc,
              ← hqD, ← hqC]
          omega
        exact cancel_two_of_dvd_pow2_sub_pow3 d (affineCarryInt (u ++ [true]))
          (true :: u).length (parityWeight (true :: u)) (by simp) ⟨qD, hqD⟩ h2
      · rintro ⟨qR, hqR⟩
        have h3 : d ∣ 3 * affineCarryInt (true :: u) := by
          refine ⟨2 * qR - qD, ?_⟩
          rw [Int.mul_sub, ← Int.mul_assoc d 2 qR, Int.mul_comm d 2, Int.mul_assoc,
              ← hqR, ← hqD]
          omega
        exact cancel_three_of_dvd_pow2_sub_pow3 d (affineCarryInt (true :: u))
          (true :: u).length (parityWeight (true :: u)) hw ⟨qD, hqD⟩ h3

/--
  Theorem 24.1c (Universal Cyclic-Shift Carry Divisor Collapse):
  For EVERY parity word `v` with `w(v) >= 1`, EVERY divisor `d` of `2^|v| - 3^w(v)`,
  and EVERY cyclic shift `j`, `d` divides `C(v)` IF AND ONLY IF `d` divides `C(v^(j))`!
  Hence cyclic-shift GCD / primitive-prime-divisor filters CANNOT eliminate any
  fractional cycle once a single shift satisfies `d | C(v)`.
-/
theorem cyclic_shift_carry_dvd_iff : ∀ (j : Nat) (v : List Bool) (d : Int),
    parityWeight v ≥ 1 ->
    d ∣ ((2 : Int) ^ v.length - (3 : Int) ^ parityWeight v) ->
    (d ∣ affineCarryInt v ↔ d ∣ affineCarryInt (rotateLeft j v))
  | 0, _, _, _, _ => Iff.rfl
  | j + 1, v, d, hw, hd => by
    simp only [rotateLeft]
    have hstep := cyclic_shift_carry_dvd_step v d hw hd
    have hw1 : parityWeight (rotateLeft1 v) ≥ 1 := by rw [rotateLeft1_weight]; exact hw
    have hd1 : d ∣ ((2 : Int) ^ (rotateLeft1 v).length - (3 : Int) ^ parityWeight (rotateLeft1 v)) := by
      rw [rotateLeft1_length, rotateLeft1_weight]
      exact hd
    exact Iff.trans hstep (cyclic_shift_carry_dvd_iff j (rotateLeft1 v) d hw1 hd1)

set_option exponentiation.threshold 2000 in
/--
  Theorem 24.2a (Kernel-Verified Rational Convergent Bounds on `log_2(3)`):
  Certifies `1054/665 < log_2(3) < 1539/971 < 485/306` (`p_8/q_8 < log_2(3) < (p_8+p_7)/(q_8+q_7) < p_7/q_7`).
-/
theorem rational_log2_3_convergent_bounds :
    3 ^ 306 < 2 ^ 485 ∧
    2 ^ 1054 < 3 ^ 665 ∧
    3 ^ 971 < 2 ^ 1539 := by
  decide

/-- Reflective certificate record for a 2-step Hensel band `(k1, [lo1, hi1])` -/
structure HenselBandCert where
  k1 : Nat
  lo1 : Nat
  hi1 : Nat
  l1Min : Nat
  maxExp : Nat
  inv3 : Nat
  k2Mins : List Nat

def minNat (a b : Nat) : Nat :=
  if a ≤ b then a else b

def checkL1Entry (b2 k1 lo1 hi1 maxExp inv3 numHi l1 k2Min : Nat) : Bool :=
  let z2Hi := minNat b2 (numHi / 2 ^ (k1 + l1))
  let k2BoundOk := (k2Min ≥ 1) &&
    ((k2Min ≤ 1) || (3 ^ (k2Min - 1) * (z2Hi + 1) < 2 ^ (k2Min - 1) * (2 * (b2 + 1) + 1)))
  let exp := k1 + l1 + k2Min
  let g1 := 2 ^ k1 * (2 ^ l1 - 1)
  let rem := (inv3 * g1 + (lo1 + 1)) % (2 ^ exp)
  k2BoundOk && (exp ≤ maxExp) && (rem > 0) && (rem + (hi1 - lo1) < 2 ^ exp)

def checkBandL1List (b1 b2 k1 lo1 hi1 maxExp inv3 numHi l1Cur : Nat) : List Nat -> Bool
  | [] => numHi < 2 ^ (k1 + l1Cur) * (b1 + 1)
  | k2Min :: rest =>
    checkL1Entry b2 k1 lo1 hi1 maxExp inv3 numHi l1Cur k2Min &&
    checkBandL1List b1 b2 k1 lo1 hi1 maxExp inv3 numHi (l1Cur + 1) rest

def verifyTwoStepHenselBand (b1 b2 : Nat) (band : HenselBandCert) : Bool :=
  let numLo := 3 ^ band.k1 * (band.lo1 + 1) - 2 ^ band.k1
  let numHi := 3 ^ band.k1 * (band.hi1 + 1) - 2 ^ band.k1
  (band.k1 ≥ 1) &&
  (band.lo1 ≤ band.hi1) &&
  (band.l1Min ≥ 1) &&
  ((band.l1Min ≤ 1) || (numLo > 2 ^ (band.k1 + (band.l1Min - 1)) * b2)) &&
  ((3 ^ band.k1 * band.inv3) % (2 ^ band.maxExp) == 1) &&
  checkBandL1List b1 b2 band.k1 band.lo1 band.hi1 band.maxExp band.inv3 numHi band.l1Min band.k2Mins

def verifyTwoStepHenselCert (b1 b2 : Nat) (bands : List HenselBandCert) : Bool :=
  bands.all (verifyTwoStepHenselBand b1 b2)

/-- Two-step spiral fragment `z1 -> z2 -> z3` across thresholds `(b1, b2)` -/
def ValidTwoStepSpiral (b1 b2 k1 l1 k2 l2 : Nat) (z1 z2 z3 : Int) : Prop :=
  l1 ≥ 1 ∧ k2 ≥ 1 ∧ l2 ≥ 1 ∧
  (b1 + 1 : Int) ≤ z2 ∧ z2 ≤ (b2 : Int) ∧ (b2 + 1 : Int) ≤ z3 ∧
  (2 : Int) ^ (k1 + l1) * (z2 + 1) =
    (3 : Int) ^ k1 * (z1 + 1) + (2 : Int) ^ k1 * ((2 : Int) ^ l1 - 1) ∧
  (2 : Int) ^ (k2 + l2) * (z3 + 1) =
    (3 : Int) ^ k2 * (z2 + 1) + (2 : Int) ^ k2 * ((2 : Int) ^ l2 - 1)

theorem validTwoStepSpiral_implies_spiralPath
    (b1 b2 k1 l1 k2 l2 : Nat) (z1 z2 z3 : Int)
    (hv : ValidTwoStepSpiral b1 b2 k1 l1 k2 l2 z1 z2 z3) :
    SpiralPath [(k1, l1), (k2, l2)] z1 z3 := by
  rcases hv with ⟨_, _, _, _, _, _, hs1, hs2⟩
  exact SpiralPath.cons k1 l1 [(k2, l2)] z1 z2 z3 hs1
    (SpiralPath.cons k2 l2 [] z2 z3 z3 hs2 (SpiralPath.nil z3))

theorem natCast_add (a b : Nat) : ((a + b : Nat) : Int) = (a : Int) + (b : Int) := by
  omega

theorem natCast_mul : ∀ (a b : Nat), ((a * b : Nat) : Int) = (a : Int) * (b : Int)
  | 0, _ => by simp
  | a + 1, b => by
    rw [Nat.add_mul, Nat.one_mul, natCast_add, natCast_mul a b]
    have h1 : ((a + 1 : Nat) : Int) = (a : Int) + 1 := by omega
    rw [h1, Int.add_mul, Int.one_mul]

theorem natCast_pow2 : ∀ k : Nat, ((2 ^ k : Nat) : Int) = (2 : Int) ^ k
  | 0 => rfl
  | k + 1 => by
    rw [Nat.pow_succ, Int.pow_succ, natCast_mul, natCast_pow2 k]
    have h2 : ((2 : Nat) : Int) = 2 := by omega
    rw [h2]

theorem natCast_pow3 : ∀ k : Nat, ((3 ^ k : Nat) : Int) = (3 : Int) ^ k
  | 0 => rfl
  | k + 1 => by
    rw [Nat.pow_succ, Int.pow_succ, natCast_mul, natCast_pow3 k]
    have h3 : ((3 : Nat) : Int) = 3 := by omega
    rw [h3]

theorem pow_pos_int : ∀ (b : Int) (k : Nat), b ≥ 1 -> b ^ k ≥ 1
  | _, 0, _ => by simp
  | b, k + 1, hb => by
    have ih := pow_pos_int b k hb
    rw [Int.pow_succ]
    have hm : b ^ k * b ≥ b ^ k * 1 := Int.mul_le_mul_of_nonneg_left hb (by omega)
    omega

theorem pow2_mono_nat_aux : ∀ a d : Nat, 2 ^ a ≤ 2 ^ (a + d)
  | _, 0 => by simp
  | a, d + 1 => by
    have ih := pow2_mono_nat_aux a d
    rw [show a + (d + 1) = (a + d) + 1 by omega, Nat.pow_succ]
    omega

theorem pow2_mono_nat {a b : Nat} (hab : a ≤ b) : 2 ^ a ≤ 2 ^ b := by
  have h := pow2_mono_nat_aux a (b - a)
  rwa [show a + (b - a) = b by omega] at h

theorem pow3_mul_lt_pow2_mul_down : ∀ (d m A B : Nat),
    3 ^ (m + d) * A < 2 ^ (m + d) * B -> 3 ^ m * A < 2 ^ m * B
  | 0, _, _, _, h => by simpa using h
  | d + 1, m, A, B, h => by
    have h3 : 3 ^ (m + (d + 1)) * A = 3 * (3 ^ (m + d) * A) := by
      rw [show m + (d + 1) = (m + d) + 1 by omega, Nat.pow_succ]
      calc
        3 ^ (m + d) * 3 * A = 3 * 3 ^ (m + d) * A := by rw [Nat.mul_comm _ 3]
        _ = 3 * (3 ^ (m + d) * A) := by rw [Nat.mul_assoc]
    have h2 : 2 ^ (m + (d + 1)) * B = 2 * (2 ^ (m + d) * B) := by
      rw [show m + (d + 1) = (m + d) + 1 by omega, Nat.pow_succ]
      calc
        2 ^ (m + d) * 2 * B = 2 * 2 ^ (m + d) * B := by rw [Nat.mul_comm _ 2]
        _ = 2 * (2 ^ (m + d) * B) := by rw [Nat.mul_assoc]
    rw [h3, h2] at h
    exact pow3_mul_lt_pow2_mul_down d m A B (by omega)

theorem pow3_mod2_nat : ∀ k : Nat, 3 ^ k % 2 = 1
  | 0 => rfl
  | k + 1 => by rw [Nat.pow_succ, Nat.mul_mod, pow3_mod2_nat k]

theorem pow2_dvd_of_pow2_dvd_pow3_mul_nat : ∀ (e k X : Nat),
    2 ^ e ∣ 3 ^ k * X -> 2 ^ e ∣ X
  | 0, _, X, _ => ⟨X, by simp⟩
  | e + 1, k, X, ⟨q, hq⟩ => by
    have hp2 : 2 ^ (e + 1) * q = 2 * (2 ^ e * q) := by
      rw [Nat.pow_succ]
      calc
        2 ^ e * 2 * q = 2 * 2 ^ e * q := by rw [Nat.mul_comm _ 2]
        _ = 2 * (2 ^ e * q) := by rw [Nat.mul_assoc]
    have hev_prod : (3 ^ k * X) % 2 = 0 := by rw [hq, hp2]; omega
    have hm3 : 3 ^ k % 2 = 1 := pow3_mod2_nat k
    have hev_X : X % 2 = 0 := by rw [Nat.mul_mod, hm3] at hev_prod; omega
    have hX2 : X = 2 * (X / 2) := by omega
    have hmul2 : 3 ^ k * (2 * (X / 2)) = 2 * (3 ^ k * (X / 2)) := by
      rw [← Nat.mul_assoc, Nat.mul_comm (3 ^ k) 2, Nat.mul_assoc]
    rw [hX2, hmul2, hp2] at hq
    have hdiv : 2 ^ e ∣ 3 ^ k * (X / 2) := ⟨q, by omega⟩
    rcases pow2_dvd_of_pow2_dvd_pow3_mul_nat e k (X / 2) hdiv with ⟨q', hq'⟩
    refine ⟨q', ?_⟩
    rw [hX2, hq', Nat.pow_succ]
    calc
      2 * (2 ^ e * q') = (2 * 2 ^ e) * q' := by rw [Nat.mul_assoc]
      _ = (2 ^ e * 2) * q' := by rw [Nat.mul_comm 2 (2 ^ e)]

theorem le_div_of_mul_le {n num P : Nat} (hP : P > 0) (hle : P * n ≤ num) : n ≤ num / P := by
  apply Classical.byContradiction
  intro hgt
  have hge : num / P + 1 ≤ n := by omega
  have hmul : P * (num / P + 1) ≤ P * n := Nat.mul_le_mul_left P hge
  rw [Nat.mul_add, Nat.mul_one] at hmul
  have hdm := Nat.div_add_mod num P
  have hlt := Nat.mod_lt num hP
  omega

theorem mod_span_contradiction_nat
    (M A B delta rem span : Nat)
    (hrem_pos : rem > 0)
    (hrem_lt : rem + span < M)
    (hdelta_le : delta ≤ span)
    (hmul : M * A = M * B + (delta + rem)) :
    False := by
  have hBA : B ≤ A := by
    apply Classical.byContradiction
    intro hlt
    have hle : A + 1 ≤ B := by omega
    have hm : M * (A + 1) ≤ M * B := Nat.mul_le_mul_left M hle
    rw [Nat.mul_add, Nat.mul_one] at hm
    omega
  have hAB : M * A = M * B + M * (A - B) := by
    have hsplit : A = B + (A - B) := by omega
    conv => lhs; rw [hsplit]
    exact Nat.mul_add M B (A - B)
  have hdvd : delta + rem = M * (A - B) := by omega
  cases hdiff : A - B with
  | zero =>
    rw [hdiff, Nat.mul_zero] at hdvd
    omega
  | succ q' =>
    rw [hdiff, Nat.mul_add, Nat.mul_one] at hdvd
    omega

theorem checkL1Entry_sound
    (b2 k1 lo1 hi1 maxExp inv3 numHi l1 k2Min k2 l2 n1 n2 n3 : Nat)
    (_hl1 : l1 ≥ 1) (hk2 : k2 ≥ 1) (hl2 : l2 ≥ 1)
    (hn1_lo : lo1 ≤ n1) (hn1_hi : n1 ≤ hi1)
    (hn2_hi : n2 ≤ b2) (hn3_lo : b2 + 1 ≤ n3)
    (hnumHi : 2 ^ (k1 + l1) * n2 ≤ numHi)
    (hinv : (3 ^ k1 * inv3) % 2 ^ maxExp = 1)
    (hstep1 : 2 ^ (k1 + l1) * (n2 + 1) = 3 ^ k1 * (n1 + 1) + 2 ^ k1 * (2 ^ l1 - 1))
    (hstep2 : 2 ^ (k2 + l2) * (n3 + 1) = 3 ^ k2 * (n2 + 1) + 2 ^ k2 * (2 ^ l2 - 1))
    (hok : checkL1Entry b2 k1 lo1 hi1 maxExp inv3 numHi l1 k2Min = true) :
    False := by
  unfold checkL1Entry at hok
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hok
  rcases hok with ⟨⟨⟨⟨hk2m_ge1, hk2_bound⟩, hexp_le⟩, hrem_pos⟩, hrem_lt⟩
  let P := 2 ^ (k1 + l1)
  have hP_pos : P ≥ 1 := pow2_pos_nat (k1 + l1)
  have hn2_div : n2 ≤ numHi / P := le_div_of_mul_le (by omega) hnumHi
  let z2Hi := minNat b2 (numHi / P)
  have hn2_z2Hi : n2 ≤ z2Hi := by
    dsimp [z2Hi, minNat]
    by_cases hb : b2 ≤ numHi / P <;> simp [hb] <;> omega
  -- Establish k2 >= k2Min from hstep2
  have hk2_ge_min : k2Min ≤ k2 := by
    rcases hk2_bound with hk2m1 | hlt_prev
    · omega
    · apply Classical.byContradiction
      intro hlt_k2
      have hk2_le : k2 ≤ k2Min - 1 := by omega
      have hsmall : 3 ^ k2 * (z2Hi + 1) < 2 ^ k2 * (2 * (b2 + 1) + 1) := by
        have hdown := pow3_mul_lt_pow2_mul_down ((k2Min - 1) - k2) k2
          (z2Hi + 1) (2 * (b2 + 1) + 1)
        rw [show k2 + ((k2Min - 1) - k2) = k2Min - 1 by omega] at hdown
        exact hdown hlt_prev
      have h3le : 3 ^ k2 * (n2 + 1) ≤ 3 ^ k2 * (z2Hi + 1) :=
        Nat.mul_le_mul_left (3 ^ k2) (by omega)
      have hp2l2 : 2 ≤ 2 ^ l2 := by
        have hm := pow2_mono_nat hl2
        simpa using hm
      have h2ge : 2 * (b2 + 1) + 2 ≤ 2 ^ l2 * (n3 + 1) := by
        have hm := Nat.mul_le_mul hp2l2 (show b2 + 2 ≤ n3 + 1 by omega)
        omega
      have hlhs2 : 2 ^ (k2 + l2) * (n3 + 1) = 2 ^ k2 * (2 ^ l2 * (n3 + 1)) := by
        rw [Nat.pow_add, Nat.mul_assoc]
      have hbig : 2 ^ k2 * (2 * (b2 + 1) + 2) ≤ 2 ^ (k2 + l2) * (n3 + 1) := by
        rw [hlhs2]
        exact Nat.mul_le_mul_left (2 ^ k2) h2ge
      have hp2l2_pos : 2 ^ l2 ≥ 1 := pow2_pos_nat l2
      have hrhs2_sub : 2 ^ k2 * (2 * (b2 + 1) + 1) ≤ 3 ^ k2 * (n2 + 1) := by
        have hexp_add : 2 ^ k2 * (2 * (b2 + 1) + 2) =
            2 ^ k2 * (2 * (b2 + 1) + 1) + 2 ^ k2 := by
          rw [show 2 * (b2 + 1) + 2 = (2 * (b2 + 1) + 1) + 1 by omega, Nat.mul_add, Nat.mul_one]
        have hrhs_ge : 2 ^ k2 * (2 ^ l2 - 1) + 2 ^ k2 = 2 ^ k2 * 2 ^ l2 := by
          calc
            2 ^ k2 * (2 ^ l2 - 1) + 2 ^ k2
                = 2 ^ k2 * (2 ^ l2 - 1) + 2 ^ k2 * 1 := by rw [Nat.mul_one]
            _ = 2 ^ k2 * ((2 ^ l2 - 1) + 1) := by rw [← Nat.mul_add]
            _ = 2 ^ k2 * 2 ^ l2 := by rw [show (2 ^ l2 - 1) + 1 = 2 ^ l2 by omega]
        have hlhs_ge : 2 ^ k2 * 2 ^ l2 * (b2 + 2) ≤ 2 ^ (k2 + l2) * (n3 + 1) := by
          rw [Nat.pow_add]
          exact Nat.mul_le_mul_left (2 ^ k2 * 2 ^ l2) (by omega)
        have hb2_pos : 2 ^ k2 * 2 ^ l2 * (b2 + 2) =
            2 ^ k2 * 2 ^ l2 * (b2 + 1) + 2 ^ k2 * 2 ^ l2 := by
          rw [show b2 + 2 = (b2 + 1) + 1 by omega, Nat.mul_add, Nat.mul_one]
        have h1 : 2 ^ k2 * (2 * (b2 + 1)) ≤ 2 ^ k2 * 2 ^ l2 * (b2 + 1) := by
          rw [Nat.mul_assoc (2 ^ k2) (2 ^ l2) (b2 + 1)]
          exact Nat.mul_le_mul_left (2 ^ k2) (Nat.mul_le_mul_right (b2 + 1) hp2l2)
        have h2 : 2 ^ k2 * (2 ^ l2 - 1) + 2 ^ k2 ≤ 2 ^ k2 * 2 ^ l2 := by omega
        have h3 : 2 ^ k2 * (2 * (b2 + 1) + 1) = 2 ^ k2 * (2 * (b2 + 1)) + 2 ^ k2 := by
          rw [Nat.mul_add, Nat.mul_one]
        omega
      omega
  -- Establish 2^exp | 3^k1 * (n1 + 1) + g1
  let exp := k1 + l1 + k2Min
  let g1 := 2 ^ k1 * (2 ^ l1 - 1)
  have hp2l2_pos : 2 ^ l2 ≥ 1 := pow2_pos_nat l2
  have hl2_ge : 2 ^ l2 - 1 ≤ 2 ^ l2 * (n3 + 1) := by
    have hm : 2 ^ l2 * 1 ≤ 2 ^ l2 * (n3 + 1) := Nat.mul_le_mul_left (2 ^ l2) (by omega)
    omega
  let Q2 := 2 ^ l2 * (n3 + 1) - (2 ^ l2 - 1)
  have hstep2_div : 3 ^ k2 * (n2 + 1) = 2 ^ k2 * Q2 := by
    have hlhs : 2 ^ (k2 + l2) * (n3 + 1) = 2 ^ k2 * (2 ^ l2 * (n3 + 1)) := by
      rw [Nat.pow_add, Nat.mul_assoc]
    have hsplit : 2 ^ l2 * (n3 + 1) = Q2 + (2 ^ l2 - 1) := by dsimp [Q2]; omega
    rw [hlhs, hsplit, Nat.mul_add] at hstep2
    omega
  have hcomb_div : 2 ^ exp ∣ 3 ^ k2 * (3 ^ k1 * (n1 + 1) + g1) := by
    refine ⟨2 ^ (k2 - k2Min) * Q2, ?_⟩
    have hm1 := congrArg (fun t => 3 ^ k2 * t) hstep1.symm
    dsimp [g1] at hm1 ⊢
    rw [hm1]
    calc
      3 ^ k2 * (2 ^ (k1 + l1) * (n2 + 1))
          = 2 ^ (k1 + l1) * (3 ^ k2 * (n2 + 1)) := by
            rw [← Nat.mul_assoc, Nat.mul_comm (3 ^ k2) (2 ^ (k1 + l1)), Nat.mul_assoc]
      _ = 2 ^ (k1 + l1) * (2 ^ k2 * Q2) := by rw [hstep2_div]
      _ = 2 ^ (k1 + l1 + k2) * Q2 := by rw [← Nat.mul_assoc, ← Nat.pow_add]
      _ = 2 ^ (exp + (k2 - k2Min)) * Q2 := by
            rw [show k1 + l1 + k2 = exp + (k2 - k2Min) by dsimp [exp]; omega]
      _ = 2 ^ exp * (2 ^ (k2 - k2Min) * Q2) := by rw [Nat.pow_add, Nat.mul_assoc]
  rcases pow2_dvd_of_pow2_dvd_pow3_mul_nat exp k2 (3 ^ k1 * (n1 + 1) + g1) hcomb_div with ⟨Q1, hQ1⟩
  -- Multiply by inv3 and reduce modulo M = 2^exp
  let M := 2 ^ exp
  have hinv_eq : 3 ^ k1 * inv3 = M * (2 ^ (maxExp - exp) * ((3 ^ k1 * inv3) / 2 ^ maxExp)) + 1 := by
    have hdm := (Nat.div_add_mod (3 ^ k1 * inv3) (2 ^ maxExp)).symm
    have hp : 2 ^ maxExp = M * 2 ^ (maxExp - exp) := by
      dsimp [M]
      rw [← Nat.pow_add, show exp + (maxExp - exp) = maxExp by omega]
    calc
      3 ^ k1 * inv3
          = 2 ^ maxExp * ((3 ^ k1 * inv3) / 2 ^ maxExp) + (3 ^ k1 * inv3) % 2 ^ maxExp := hdm
      _ = 2 ^ maxExp * ((3 ^ k1 * inv3) / 2 ^ maxExp) + 1 := by rw [hinv]
      _ = (M * 2 ^ (maxExp - exp)) * ((3 ^ k1 * inv3) / 2 ^ maxExp) + 1 :=
            congrArg (fun t => t * ((3 ^ k1 * inv3) / 2 ^ maxExp) + 1) hp
      _ = M * (2 ^ (maxExp - exp) * ((3 ^ k1 * inv3) / 2 ^ maxExp)) + 1 := by rw [Nat.mul_assoc]
  let qInv := 2 ^ (maxExp - exp) * ((3 ^ k1 * inv3) / 2 ^ maxExp)
  let S := inv3 * g1 + (lo1 + 1)
  let qRem := S / M
  let rem := S % M
  have hS_dm : M * qRem + rem = S := Nat.div_add_mod S M
  let delta := n1 - lo1
  have hn1_split : n1 + 1 = delta + (lo1 + 1) := by dsimp [delta]; omega
  have hmul_inv : M * (inv3 * Q1) = M * (qInv * (n1 + 1) + qRem) + (delta + rem) := by
    have h1 := congrArg (fun t => inv3 * t) hQ1.symm
    have hlhs : inv3 * (M * Q1) = M * (inv3 * Q1) := by
      rw [← Nat.mul_assoc, Nat.mul_comm inv3 M, Nat.mul_assoc]
    have hrhs1 : inv3 * (3 ^ k1 * (n1 + 1) + g1) =
        (3 ^ k1 * inv3) * (n1 + 1) + inv3 * g1 := by
      rw [Nat.mul_add, ← Nat.mul_assoc inv3 (3 ^ k1), Nat.mul_comm inv3 (3 ^ k1)]
    rw [hlhs, hrhs1, hinv_eq] at h1
    change M * (inv3 * Q1) = (M * qInv + 1) * (n1 + 1) + inv3 * g1 at h1
    have hexp1 : (M * qInv + 1) * (n1 + 1) + inv3 * g1 =
        M * (qInv * (n1 + 1)) + delta + S := by
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc, hn1_split]
      dsimp [S]
      omega
    have hexp2 : M * (qInv * (n1 + 1) + qRem) = M * (qInv * (n1 + 1)) + M * qRem :=
      Nat.mul_add M (qInv * (n1 + 1)) qRem
    rw [hexp1] at h1
    omega
  exact mod_span_contradiction_nat M (inv3 * Q1) (qInv * (n1 + 1) + qRem)
    delta rem (hi1 - lo1) hrem_pos hrem_lt (by dsimp [delta]; omega) hmul_inv

theorem checkBandL1List_sound :
    ∀ (k2Mins : List Nat) (b1 b2 k1 lo1 hi1 maxExp inv3 numHi l1Cur l1 k2 l2 n1 n2 n3 : Nat),
      l1Cur ≤ l1 ->
      l1 ≥ 1 -> k2 ≥ 1 -> l2 ≥ 1 ->
      lo1 ≤ n1 -> n1 ≤ hi1 ->
      b1 + 1 ≤ n2 -> n2 ≤ b2 -> b2 + 1 ≤ n3 ->
      2 ^ (k1 + l1) * n2 ≤ numHi ->
      (3 ^ k1 * inv3) % 2 ^ maxExp = 1 ->
      2 ^ (k1 + l1) * (n2 + 1) = 3 ^ k1 * (n1 + 1) + 2 ^ k1 * (2 ^ l1 - 1) ->
      2 ^ (k2 + l2) * (n3 + 1) = 3 ^ k2 * (n2 + 1) + 2 ^ k2 * (2 ^ l2 - 1) ->
      checkBandL1List b1 b2 k1 lo1 hi1 maxExp inv3 numHi l1Cur k2Mins = true ->
      False
  | [], b1, _, k1, _, _, _, _, numHi, l1Cur, l1, _, _, _, n2, _,
      hl1_ge, _, _, _, _, _, hn2_lo, _, _, hnumHi, _, _, _, hok => by
    unfold checkBandL1List at hok
    have hlt : numHi < 2 ^ (k1 + l1Cur) * (b1 + 1) := of_decide_eq_true hok
    have hp : 2 ^ (k1 + l1Cur) ≤ 2 ^ (k1 + l1) := pow2_mono_nat (by omega)
    have hm : 2 ^ (k1 + l1Cur) * (b1 + 1) ≤ 2 ^ (k1 + l1) * n2 :=
      Nat.mul_le_mul hp hn2_lo
    omega
  | k2Min :: rest, b1, b2, k1, lo1, hi1, maxExp, inv3, numHi, l1Cur, l1, k2, l2, n1, n2, n3,
      hl1_ge, hl1, hk2, hl2, hn1_lo, hn1_hi, hn2_lo, hn2_hi, hn3_lo, hnumHi, hinv, hs1, hs2, hok => by
    unfold checkBandL1List at hok
    simp only [Bool.and_eq_true] at hok
    rcases hok with ⟨hhead, htail⟩
    by_cases heq : l1 = l1Cur
    · subst heq
      exact checkL1Entry_sound b2 k1 lo1 hi1 maxExp inv3 numHi l1 k2Min k2 l2 n1 n2 n3
        hl1 hk2 hl2 hn1_lo hn1_hi hn2_hi hn3_lo hnumHi hinv hs1 hs2 hhead
    · exact checkBandL1List_sound rest b1 b2 k1 lo1 hi1 maxExp inv3 numHi (l1Cur + 1)
        l1 k2 l2 n1 n2 n3 (by omega) hl1 hk2 hl2 hn1_lo hn1_hi hn2_lo hn2_hi hn3_lo
        hnumHi hinv hs1 hs2 htail

/--
  Theorem 24.2b (Universal Soundness of the Reflective 2-Step Hensel Band Verifier):
  Whenever `verifyTwoStepHenselBand b1 b2 band = true`, NO integers `z1 in [lo1, hi1]`,
  `z2 in [b1 + 1, b2]`, `z3 >= b2 + 1`, and step exponents `l1, k2, l2 >= 1` can satisfy
  `ValidTwoStepSpiral b1 b2 band.k1 l1 k2 l2 z1 z2 z3`.
-/
theorem verifyTwoStepHenselBand_sound
    (b1 b2 : Nat) (band : HenselBandCert)
    (hok : verifyTwoStepHenselBand b1 b2 band = true)
    (l1 k2 l2 : Nat) (z1 z2 z3 : Int)
    (hz1_lo : (band.lo1 : Int) ≤ z1) (hz1_hi : z1 ≤ (band.hi1 : Int))
    (hvalid : ValidTwoStepSpiral b1 b2 band.k1 l1 k2 l2 z1 z2 z3) :
    False := by
  unfold verifyTwoStepHenselBand at hok
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hok
  rcases hok with ⟨⟨⟨⟨⟨_hk1, _hlo_hi⟩, _hl1m_ge1⟩, hl1m_bound⟩, hinv_beq⟩, hlist⟩
  have hinv : (3 ^ band.k1 * band.inv3) % 2 ^ band.maxExp = 1 := of_decide_eq_true hinv_beq
  rcases hvalid with ⟨hl1, hk2, hl2, hz2_lo, hz2_hi, hz3_lo, hs1_int, hs2_int⟩
  let n1 := z1.toNat
  let n2 := z2.toNat
  let n3 := z3.toNat
  have hz1_nat : z1 = (n1 : Int) := by dsimp [n1]; omega
  have hz2_nat : z2 = (n2 : Int) := by dsimp [n2]; omega
  have hz3_nat : z3 = (n3 : Int) := by dsimp [n3]; omega
  have hn1_lo : band.lo1 ≤ n1 := by omega
  have hn1_hi : n1 ≤ band.hi1 := by omega
  have hn2_lo : b1 + 1 ≤ n2 := by omega
  have hn2_hi : n2 ≤ b2 := by omega
  have hn3_lo : b2 + 1 ≤ n3 := by omega
  have hs1_nat : 2 ^ (band.k1 + l1) * (n2 + 1) =
      3 ^ band.k1 * (n1 + 1) + 2 ^ band.k1 * (2 ^ l1 - 1) := by
    have hp2l1 : 2 ^ l1 ≥ 1 := pow2_pos_nat l1
    have hlhs_c : ((2 ^ (band.k1 + l1) * (n2 + 1) : Nat) : Int) =
        (2 : Int) ^ (band.k1 + l1) * (z2 + 1) := by
      rw [natCast_mul, natCast_pow2]
      have hz2p : ((n2 + 1 : Nat) : Int) = z2 + 1 := by omega
      rw [hz2p]
    have hrhs_c : ((3 ^ band.k1 * (n1 + 1) + 2 ^ band.k1 * (2 ^ l1 - 1) : Nat) : Int) =
        (3 : Int) ^ band.k1 * (z1 + 1) + (2 : Int) ^ band.k1 * ((2 : Int) ^ l1 - 1) := by
      rw [natCast_add, natCast_mul, natCast_mul, natCast_pow3, natCast_pow2]
      have hz1p : ((n1 + 1 : Nat) : Int) = z1 + 1 := by omega
      have hsub : ((2 ^ l1 - 1 : Nat) : Int) = (2 : Int) ^ l1 - 1 := by
        rw [← natCast_pow2 l1]
        omega
      rw [hz1p, hsub]
    have hcast : ((2 ^ (band.k1 + l1) * (n2 + 1) : Nat) : Int) =
        ((3 ^ band.k1 * (n1 + 1) + 2 ^ band.k1 * (2 ^ l1 - 1) : Nat) : Int) := by
      rw [hlhs_c, hrhs_c]
      exact hs1_int
    omega
  have hs2_nat : 2 ^ (k2 + l2) * (n3 + 1) =
      3 ^ k2 * (n2 + 1) + 2 ^ k2 * (2 ^ l2 - 1) := by
    have hp2l2 : 2 ^ l2 ≥ 1 := pow2_pos_nat l2
    have hlhs_c : ((2 ^ (k2 + l2) * (n3 + 1) : Nat) : Int) =
        (2 : Int) ^ (k2 + l2) * (z3 + 1) := by
      rw [natCast_mul, natCast_pow2]
      have hz3p : ((n3 + 1 : Nat) : Int) = z3 + 1 := by omega
      rw [hz3p]
    have hrhs_c : ((3 ^ k2 * (n2 + 1) + 2 ^ k2 * (2 ^ l2 - 1) : Nat) : Int) =
        (3 : Int) ^ k2 * (z2 + 1) + (2 : Int) ^ k2 * ((2 : Int) ^ l2 - 1) := by
      rw [natCast_add, natCast_mul, natCast_mul, natCast_pow3, natCast_pow2]
      have hz2p : ((n2 + 1 : Nat) : Int) = z2 + 1 := by omega
      have hsub : ((2 ^ l2 - 1 : Nat) : Int) = (2 : Int) ^ l2 - 1 := by
        rw [← natCast_pow2 l2]
        omega
      rw [hz2p, hsub]
    have hcast : ((2 ^ (k2 + l2) * (n3 + 1) : Nat) : Int) =
        ((3 ^ k2 * (n2 + 1) + 2 ^ k2 * (2 ^ l2 - 1) : Nat) : Int) := by
      rw [hlhs_c, hrhs_c]
      exact hs2_int
    omega
  -- Establish 2^(k1 + l1) * n2 + 2^k1 = 3^k1 * (n1 + 1)
  have hstep1_sub : 2 ^ (band.k1 + l1) * n2 + 2 ^ band.k1 = 3 ^ band.k1 * (n1 + 1) := by
    have hlhs : 2 ^ (band.k1 + l1) * (n2 + 1) = 2 ^ (band.k1 + l1) * n2 + 2 ^ band.k1 * 2 ^ l1 := by
      rw [Nat.mul_add, Nat.mul_one, Nat.pow_add]
    have hrhs : 2 ^ band.k1 * (2 ^ l1 - 1) + 2 ^ band.k1 = 2 ^ band.k1 * 2 ^ l1 := by
      have hp2l1 : 2 ^ l1 ≥ 1 := pow2_pos_nat l1
      calc
        2 ^ band.k1 * (2 ^ l1 - 1) + 2 ^ band.k1
            = 2 ^ band.k1 * (2 ^ l1 - 1) + 2 ^ band.k1 * 1 := by rw [Nat.mul_one]
        _ = 2 ^ band.k1 * ((2 ^ l1 - 1) + 1) := by rw [← Nat.mul_add]
        _ = 2 ^ band.k1 * 2 ^ l1 := by rw [show (2 ^ l1 - 1) + 1 = 2 ^ l1 by omega]
    omega
  let numLo := 3 ^ band.k1 * (band.lo1 + 1) - 2 ^ band.k1
  let numHi := 3 ^ band.k1 * (band.hi1 + 1) - 2 ^ band.k1
  have h3ge2 : 2 ^ band.k1 ≤ 3 ^ band.k1 := pow2_le_pow3 band.k1
  have hnumLo_le : numLo ≤ 2 ^ (band.k1 + l1) * n2 := by
    have hm : 3 ^ band.k1 * (band.lo1 + 1) ≤ 3 ^ band.k1 * (n1 + 1) :=
      Nat.mul_le_mul_left (3 ^ band.k1) (by omega)
    have hge : 2 ^ band.k1 ≤ 3 ^ band.k1 * (band.lo1 + 1) := by
      have h1 : 3 ^ band.k1 * 1 ≤ 3 ^ band.k1 * (band.lo1 + 1) :=
        Nat.mul_le_mul_left (3 ^ band.k1) (by omega)
      omega
    dsimp [numLo]
    omega
  have hnumHi_ge : 2 ^ (band.k1 + l1) * n2 ≤ numHi := by
    have hm : 3 ^ band.k1 * (n1 + 1) ≤ 3 ^ band.k1 * (band.hi1 + 1) :=
      Nat.mul_le_mul_left (3 ^ band.k1) (by omega)
    dsimp [numHi]
    omega
  have hl1_ge_min : band.l1Min ≤ l1 := by
    rcases hl1m_bound with hl1m1 | hlo_gt
    · omega
    · apply Classical.byContradiction
      intro hlt_l1
      have hl1_le : band.k1 + l1 ≤ band.k1 + (band.l1Min - 1) := by omega
      have hp : 2 ^ (band.k1 + l1) ≤ 2 ^ (band.k1 + (band.l1Min - 1)) := pow2_mono_nat hl1_le
      have hm : 2 ^ (band.k1 + l1) * n2 ≤ 2 ^ (band.k1 + (band.l1Min - 1)) * b2 :=
        Nat.mul_le_mul hp hn2_hi
      dsimp [numLo] at hnumLo_le
      omega
  exact checkBandL1List_sound band.k2Mins b1 b2 band.k1 band.lo1 band.hi1
    band.maxExp band.inv3 numHi band.l1Min l1 k2 l2 n1 n2 n3
    hl1_ge_min hl1 hk2 hl2 hn1_lo hn1_hi hn2_lo hn2_hi hn3_lo hnumHi_ge hinv hs1_nat hs2_nat hlist

/--
  Theorem 24.2c (Universal Soundness over Certificate Lists):
  Whenever `verifyTwoStepHenselCert b1 b2 bands = true`, EVERY band in `bands` is
  devoid of valid 2-step spiral trajectories `z1 -> z2 -> z3`.
-/
theorem verifyTwoStepHenselCert_sound :
    ∀ (bands : List HenselBandCert) (b1 b2 : Nat) (band : HenselBandCert),
      verifyTwoStepHenselCert b1 b2 bands = true ->
      band ∈ bands ->
      ∀ (l1 k2 l2 : Nat) (z1 z2 z3 : Int),
        (band.lo1 : Int) ≤ z1 -> z1 ≤ (band.hi1 : Int) ->
        ¬ ValidTwoStepSpiral b1 b2 band.k1 l1 k2 l2 z1 z2 z3
  | [], _, _, _, _, hmem, _, _, _, _, _, _, _, _, _ => by cases hmem
  | b :: rest, b1, b2, band, hok, hmem, l1, k2, l2, z1, z2, z3, hlo, hhi, hv => by
    unfold verifyTwoStepHenselCert at hok
    simp only [List.all_cons, Bool.and_eq_true] at hok
    rcases hok with ⟨hb, hrest⟩
    cases hmem with
    | head =>
      exact verifyTwoStepHenselBand_sound b1 b2 b hb l1 k2 l2 z1 z2 z3 hlo hhi hv
    | tail _ htail =>
      exact verifyTwoStepHenselCert_sound rest b1 b2 band hrest htail
        l1 k2 l2 z1 z2 z3 hlo hhi hv

def m92B1 : Nat := 186580408057834151310110
def m92B2 : Nat := 3823138529586028606781976423433193969

/-- All 61 active 2-step Hensel bands for the `m = 92` (`u = 1`) bottleneck (`1,120` leaves) -/
def m92HenselBands : List HenselBandCert := [
  ⟨9, 10942753514197241808856, 11643894518029529678343, 1, 87, 147250272670675027618126027, [77]⟩,
  ⟨10, 11040169573162501625004, 11747552369180245502510, 1, 87, 100664259193782520660172185, [76]⟩,
  ⟨11, 11105113612472674835770, 11816657603280722718621, 1, 90, 1013590617498853557848530739, [75, 77]⟩,
  ⟨12, 11148409638679456976280, 11862727759347707529362, 1, 93, 3226390297498838494047466769, [74, 76, 78]⟩,
  ⟨13, 11177273656150645069954, 11893441196725697403189, 1, 93, 7677810308688307630811151451, [73, 75, 77]⟩,
  ⟨14, 11196516334464770465736, 11913916821644357319074, 1, 95, 15763963855273492142527708873, [72, 74, 76, 77]⟩,
  ⟨15, 11209344786674187396258, 11927567238256797262997, 1, 95, 18459348370801886979766561347, [71, 73, 75, 76]⟩,
  ⟨16, 11217897088147132016605, 11936667515998423892279, 1, 98, 6153116123600628993255520449, [70, 72, 74, 75, 77]⟩,
  ⟨17, 11223598622462428430171, 11942734367826174978467, 1, 98, 2051038707866876331085173483, [69, 71, 73, 74, 76]⟩,
  ⟨18, 11227399645339292705881, 11946778935711342369259, 1, 101, 1585246929854575710647907397881, [68, 70, 72, 73, 75, 77]⟩,
  ⟨19, 11229933660590535556354, 11949475314301453963121, 1, 104, 8134319244654234979196188364883, [67, 69, 71, 72, 74, 76, 78]⟩,
  ⟨20, 11231623004091364123336, 11951272900028195025695, 1, 104, 2711439748218078326398729454961, [66, 68, 70, 71, 73, 75, 77]⟩,
  ⟨21, 11232749233091916501325, 11952471290512689067411, 1, 106, 61751042060361037380641330343035, [65, 67, 69, 70, 72, 74, 76, 77]⟩,
  ⟨22, 11233500052425618086650, 11953270217502351761889, 1, 106, 47626893491655906358810111829033, [64, 66, 68, 69, 71, 73, 75, 76]⟩,
  ⟨23, 11234000598648085810200, 11953802835495460224874, 1, 109, 529696674456394286192933736522083, [63, 65, 67, 68, 70, 72, 74, 75, 77]⟩,
  ⟨24, 11234334296129730959234, 11954157914157532533530, 1, 112, 1258294070346887184674831314094881, [62, 64, 66, 67, 69, 71, 73, 74, 76, 78]⟩,
  ⟨25, 11234556761117494391923, 11954394633265580739301, 1, 112, 3880962595805514147245274657511691, [61, 63, 65, 66, 68, 70, 72, 73, 75, 77]⟩,
  ⟨26, 11234705071109336680382, 11954552446004279543149, 1, 114, 3024419818113447258591923662243929, [60, 62, 64, 65, 67, 69, 71, 72, 74, 76, 77]⟩,
  ⟨27, 11234803944437231539355, 11954657654496745412380, 1, 114, 1008139939371149086197307887414643, [59, 61, 63, 64, 66, 68, 70, 71, 73, 75, 76]⟩,
  ⟨28, 11234869859989161445337, 11954727793491722658535, 1, 117, 159566483641525096970334323391887825, [58, 60, 62, 63, 65, 67, 69, 70, 72, 74, 75, 77]⟩,
  ⟨29, 11234913803690448049325, 11954774552821707489304, 1, 117, 163957827529251355065428696153991323, [57, 59, 61, 62, 64, 66, 68, 69, 71, 73, 74, 76]⟩,
  ⟨30, 11234943099491305785317, 11954805725708364043151, 1, 120, 1162342605663847012441648782284950921, [56, 58, 60, 61, 63, 65, 67, 68, 70, 72, 73, 75, 77]⟩,
  ⟨31, 11234962630025210942645, 11954826507632801745715, 1, 123, 10578195502905637363076403722910958723, [55, 57, 59, 60, 62, 64, 66, 67, 69, 71, 72, 74, 76, 78]⟩,
  ⟨32, 11234975650381147714197, 11954840362249093547425, 1, 123, 7070673156394988115435620068384571777, [54, 56, 58, 59, 61, 63, 65, 66, 68, 70, 71, 73, 75, 77]⟩,
  ⟨33, 11234984330618438895232, 11954849598659954748564, 1, 125, 9446107029651214027298844344290028331, [53, 55, 57, 58, 60, 62, 64, 65, 67, 69, 70, 72, 74, 76, 77]⟩,
  ⟨34, 11234990117443299682588, 11954855756267195549324, 1, 125, 3148702343217071342432948114763342777, [52, 54, 56, 57, 59, 61, 63, 64, 66, 68, 69, 71, 73, 75, 76]⟩,
  ⟨35, 11234993975326540207492, 11954859861338689416497, 1, 128, 171190750908208255512498286420805219987, [51, 53, 55, 56, 58, 60, 62, 63, 65, 67, 68, 70, 72, 74, 75, 77]⟩,
  ⟨36, 11234996547248700557429, 11954862598053018661279, 1, 131, 1531620506960136093512122727677930656305, [50, 52, 54, 55, 57, 59, 61, 62, 64, 66, 67, 69, 71, 73, 74, 76, 78]⟩,
  ⟨37, 11234998261863474124053, 11954864422529238157801, 1, 131, 2325379459231717169642038815528740679867, [49, 51, 53, 54, 56, 58, 60, 61, 63, 65, 66, 68, 70, 72, 73, 75, 77]⟩,
  ⟨38, 11234999404939989835135, 11954865638846717822148, 1, 133, 3497385421778080097587676464630392584937, [48, 50, 52, 53, 55, 57, 59, 60, 62, 64, 65, 67, 69, 71, 72, 74, 76, 77]⟩,
  ⟨39, 11235000166991000309191, 11954866449725037598380, 1, 133, 1165795140592693365862558821543464194979, [47, 49, 51, 52, 54, 56, 58, 59, 61, 63, 64, 66, 68, 70, 71, 73, 75, 76]⟩,
  ⟨40, 11235000675025007291894, 11954866990310584115868, 1, 136, 51204098507057708332484794316991874309089, [46, 48, 50, 51, 53, 55, 57, 58, 60, 62, 63, 65, 67, 69, 70, 72, 74, 75, 77]⟩,
  ⟨41, 11235001013714345280363, 11954867350700948460860, 1, 139, 452629462494487136010614428951660602100043, [45, 47, 49, 50, 52, 54, 56, 57, 59, 61, 62, 64, 66, 68, 69, 71, 73, 74, 76, 78]⟩,
  ⟨42, 11235001239507237272676, 11954867590961191357521, 1, 139, 615475345800883694118865606997394398741273, [44, 46, 48, 49, 51, 53, 55, 56, 58, 60, 61, 63, 65, 67, 68, 70, 72, 73, 75, 77]⟩,
  ⟨43, 11235001390035831934217, 11954867751134686621962, 1, 141, 2063553881811179826500931725053161591745459, [43, 45, 47, 48, 50, 52, 54, 55, 57, 59, 60, 62, 64, 66, 67, 69, 71, 72, 74, 76, 77]⟩,
  ⟨44, 11235001490388228375245, 11954867857917016798256, 1, 141, 1617049010542502573064298836378068926664337, [42, 44, 46, 47, 49, 51, 53, 54, 56, 58, 59, 61, 63, 65, 66, 68, 70, 71, 73, 75, 76]⟩,
  ⟨45, 11235001557289826002597, 11954867929105236915785, 1, 144, 20052168385561796106531853100693339293287643, [41, 43, 45, 46, 48, 50, 52, 53, 55, 57, 58, 60, 62, 64, 65, 67, 69, 70, 72, 74, 75, 77]⟩,
  ⟨46, 11235001601890891087498, 11954867976564050327471, 1, 144, 21551219594207680796534429881996687435082825, [40, 42, 44, 45, 47, 49, 51, 52, 54, 56, 57, 59, 61, 63, 64, 66, 68, 69, 71, 73, 74, 76]⟩,
  ⟨47, 11235001631624934477433, 11954868008203259268595, 1, 147, 59218811994640680929094819263511739325648579, [39, 41, 43, 44, 46, 48, 50, 51, 53, 55, 56, 58, 60, 62, 63, 65, 67, 68, 70, 72, 73, 75, 77]⟩,
  ⟨48, 11235001651447630070722, 11954868029296065229345, 1, 150, 138676911723710217064555437208628507807111745, [38, 40, 42, 43, 45, 47, 49, 50, 52, 54, 55, 57, 59, 61, 62, 64, 66, 67, 69, 71, 72, 74, 76, 78]⟩,
  ⟨49, 11235001664662760466248, 11954868043357935869844, 1, 150, 46225637241236739021518479069542835935703915, [37, 39, 41, 42, 44, 46, 48, 49, 51, 53, 54, 56, 58, 60, 61, 63, 65, 66, 68, 70, 71, 73, 75, 77]⟩,
  ⟨50, 11235001673472847396599, 11954868052732516296844, 1, 152, 5248650085668931810220888047671329778715305593, [36, 38, 40, 41, 43, 45, 47, 48, 50, 52, 53, 55, 57, 59, 60, 62, 64, 65, 67, 69, 70, 72, 74, 76, 77]⟩,
  ⟨51, 11235001679346238683500, 11954868058982236581511, 1, 152, 3652546952164257111484677308489770108082097363, [35, 37, 39, 40, 42, 44, 46, 47, 49, 51, 52, 54, 56, 58, 59, 61, 63, 64, 66, 68, 69, 71, 73, 75, 76]⟩,
  ⟨52, 11235001683261832874767, 11954868063148716771288, 1, 155, 6926506421545258561394702980627903914891685617, [34, 36, 38, 39, 41, 43, 45, 46, 48, 50, 51, 53, 55, 57, 58, 60, 62, 63, 65, 67, 68, 70, 72, 74, 75, 77]⟩,
  ⟨53, 11235001685872229002278, 11954868065926370231140, 1, 158, 276340392473392716683655807127845700823784580347, [33, 35, 37, 38, 40, 42, 44, 45, 47, 49, 50, 52, 54, 56, 57, 59, 61, 62, 64, 66, 67, 69, 71, 73, 74, 76, 78]⟩,
  ⟨54, 11235001687612493087286, 11954868067778139204374, 1, 158, 92113464157797572227885269042615233607928193449, [32, 34, 36, 37, 39, 41, 43, 44, 46, 48, 49, 51, 53, 55, 56, 58, 60, 61, 63, 65, 66, 68, 70, 72, 73, 75, 77]⟩,
  ⟨55, 11235001688772669143958, 11954868069012651853198, 1, 160, 1370414322272593532429339519670797845887247562211, [31, 33, 35, 36, 38, 40, 42, 43, 45, 47, 48, 50, 52, 54, 55, 57, 59, 60, 62, 64, 65, 67, 69, 71, 72, 74, 76, 77]⟩,
  ⟨56, 11235001689546119848405, 11954868069835660285746, 1, 160, 456804774090864510809779839890265948629082520737, [30, 32, 34, 35, 37, 39, 41, 42, 44, 46, 47, 49, 51, 53, 54, 56, 58, 59, 61, 63, 64, 66, 68, 70, 71, 73, 75, 76]⟩,
  ⟨57, 11235001690061753651371, 11954868070384332574112, 1, 163, 5998274807353899843084665944161887394833424345483, [29, 31, 33, 34, 36, 38, 40, 41, 43, 45, 46, 48, 50, 52, 53, 55, 57, 58, 60, 62, 63, 65, 67, 69, 70, 72, 74, 75, 77]⟩,
  ⟨58, 11235001690405509520014, 11954868070750114099689, 1, 163, 1999424935784633281028221981387295798277808115161, [28, 30, 32, 33, 35, 37, 39, 40, 42, 44, 45, 47, 49, 51, 52, 54, 56, 57, 59, 61, 62, 64, 66, 68, 69, 71, 73, 74, 76]⟩,
  ⟨59, 11235001690634680099110, 11954868070993968450074, 1, 166, 63023878171380068937033293523023840771412391205363, [27, 29, 31, 32, 34, 36, 38, 39, 41, 43, 44, 46, 48, 50, 51, 53, 55, 56, 58, 60, 61, 63, 65, 67, 68, 70, 72, 73, 75, 77]⟩,
  ⟨60, 11235001690787460485173, 11954868071156538016997, 1, 169, 706939394511097125922607179329183444148988470571857, [26, 28, 30, 31, 33, 35, 37, 38, 40, 42, 43, 45, 47, 49, 50, 52, 54, 55, 57, 59, 60, 62, 64, 66, 67, 69, 71, 72, 74, 76, 78]⟩,
  ⟨61, 11235001690889314075883, 11954868071264917728279, 1, 169, 485076077608173140014297937893306783404275310858523, [25, 27, 29, 30, 32, 34, 36, 37, 39, 41, 42, 44, 46, 48, 49, 51, 53, 54, 56, 58, 59, 61, 63, 65, 66, 68, 70, 71, 73, 75, 77]⟩,
  ⟨62, 11235001690957216469689, 11954868071337170869134, 1, 171, 2655988153580798693739054760466891948014216643631881, [24, 26, 28, 29, 31, 33, 35, 36, 38, 40, 41, 43, 45, 47, 48, 50, 52, 53, 55, 57, 58, 60, 62, 64, 65, 67, 69, 70, 72, 74, 76, 77]⟩,
  ⟨63, 11235001691002484732226, 11954868071385339629704, 1, 171, 2880766286696059015567115945090929065508305446553859, [23, 25, 27, 28, 30, 32, 34, 35, 37, 39, 40, 42, 44, 46, 47, 49, 51, 52, 54, 56, 57, 59, 61, 63, 64, 66, 68, 69, 71, 73, 75, 76]⟩,
  ⟨64, 11235001691032663573918, 11954868071417452136750, 1, 174, 1957973879983249397349420827497958896587885098189569, [22, 24, 26, 27, 29, 31, 33, 34, 36, 38, 39, 41, 43, 45, 46, 48, 50, 51, 53, 55, 56, 58, 60, 62, 63, 65, 67, 68, 70, 72, 74, 75, 77]⟩,
  ⟨65, 11235001691052782801712, 11954868071438860474781, 1, 177, 16616153177347425407015921808648373628224494222142379, [21, 23, 25, 26, 28, 30, 32, 33, 35, 37, 38, 40, 42, 44, 45, 47, 49, 50, 52, 54, 55, 57, 59, 61, 62, 64, 66, 67, 69, 71, 73, 74, 76, 78]⟩,
  ⟨66, 11235001691066195620242, 11954868071453132700135, 1, 177, 133246679464606546665534226198741889844303091589347641, [20, 22, 24, 25, 27, 29, 31, 32, 34, 36, 37, 39, 41, 43, 44, 46, 48, 49, 51, 53, 54, 56, 58, 60, 61, 63, 65, 66, 68, 70, 72, 73, 75, 77]⟩,
  ⟨67, 11235001691075137499261, 11954868071462647517038, 1, 179, 44415559821535515555178075399580629948101030529782547, [19, 21, 23, 24, 26, 28, 30, 31, 33, 35, 36, 38, 40, 42, 43, 45, 47, 48, 50, 52, 53, 55, 57, 59, 60, 62, 64, 65, 67, 69, 71, 72, 74, 76, 77]⟩,
  ⟨68, 11235001691081098751941, 11954868071468990728307, 1, 179, 270221110084826648244783862991578407252490197207194545, [18, 20, 22, 23, 25, 27, 29, 30, 32, 34, 35, 37, 39, 41, 42, 44, 46, 47, 49, 51, 52, 54, 56, 58, 59, 61, 63, 64, 66, 68, 70, 71, 73, 75, 76]⟩,
  ⟨71, 11235001691089488663120, 11954868071477918210833, 1, 185, 48397135914750188088842060166986302127489910809582520355, [15, 17, 19, 20, 22, 24, 26, 27, 29, 31, 32, 34, 36, 38, 39, 41, 43, 44, 46, 48, 49, 51, 53, 55, 56, 58, 60, 61, 63, 65, 67, 68, 70, 72, 73, 75, 77]⟩
]

set_option maxRecDepth 20000 in
/--
  Theorem 24.2d (Zero-Trust-Gap Lean 4 Kernel Proof of `m = 92` 2-Step Hensel Elimination):
  All 61 active `(k1, [lo1, hi1])` bands (1,120 collapsed 2-adic congruences) for the
  `m = 92, u = 1` convergent bottleneck pass `verifyTwoStepHenselCert` inside the Lean 4
  kernel (`by decide`); see `m92_all_k1_hensel_complete` below for exhaustive coverage
  across EVERY `k1 >= 1` (including `1 <= k1 <= 8`, `{69, 70, 72, 73}`, and `k1 >= 74`).
-/
theorem m92_two_step_hensel_kernel_verified :
    m92HenselBands.length = 61 ∧
    3 ^ 1 * (m92B1 + 1) < 2 ^ 1 * (2 * (m92B1 + 1) + 1) ∧
    m92B1 + 1 < 2 ^ 78 ∧
    verifyTwoStepHenselCert m92B1 m92B2 m92HenselBands = true := by
  decide

-- ============================================================================
-- 11D. Exhaustive All-`k1 >= 1` `m = 92` Theorem & Recursive Arbitrary-Depth
--      (`r`-Step) Reflective Multi-Step Hensel Verifier (`m = 93` Kernel Proof)
-- ============================================================================

theorem mul_left_cancel_pow2_nat : ∀ (m a b : Nat), 2 ^ m * a = 2 ^ m * b -> a = b
  | 0, a, b, h => by simpa using h
  | m + 1, a, b, h => by
    rw [Nat.pow_succ, Nat.mul_assoc, Nat.mul_assoc] at h
    have h1 := mul_left_cancel_pow2_nat m (2 * a) (2 * b) h
    omega

/-- Exact spiral-step multiplicative ratio law in `Nat`: `2^(k + l) * n2 + 2^k = 3^k * (n1 + 1)` -/
theorem spiral_step_mul_ratio_nat (k l n1 n2 : Nat)
    (_hl : l ≥ 1)
    (hstep : 2 ^ (k + l) * (n2 + 1) = 3 ^ k * (n1 + 1) + 2 ^ k * (2 ^ l - 1)) :
    2 ^ (k + l) * n2 + 2 ^ k = 3 ^ k * (n1 + 1) := by
  have hlhs : 2 ^ (k + l) * (n2 + 1) = 2 ^ (k + l) * n2 + 2 ^ k * 2 ^ l := by
    rw [Nat.mul_add, Nat.mul_one, Nat.pow_add]
  have hp2l : 2 ^ l ≥ 1 := pow2_pos_nat l
  have hrhs : 2 ^ k * (2 ^ l - 1) + 2 ^ k = 2 ^ k * 2 ^ l := by
    calc
      2 ^ k * (2 ^ l - 1) + 2 ^ k
          = 2 ^ k * (2 ^ l - 1) + 2 ^ k * 1 := by rw [Nat.mul_one]
      _ = 2 ^ k * ((2 ^ l - 1) + 1) := by rw [← Nat.mul_add]
      _ = 2 ^ k * 2 ^ l := by rw [show (2 ^ l - 1) + 1 = 2 ^ l by omega]
  omega

/-- Every spiral step `(k, l)` with `l >= 1` forces `n1 + 1 = 2^k * u` with `u` ODD -/
theorem spiral_step_odd_quotient_nat (k l n1 n2 : Nat)
    (hl : l ≥ 1)
    (hstep : 2 ^ (k + l) * (n2 + 1) = 3 ^ k * (n1 + 1) + 2 ^ k * (2 ^ l - 1)) :
    ∃ u : Nat, u % 2 = 1 ∧ n1 + 1 = 2 ^ k * u ∧ 2 ^ l * n2 + 1 = 3 ^ k * u := by
  have hsub := spiral_step_mul_ratio_nat k l n1 n2 hl hstep
  have hfac : 2 ^ (k + l) * n2 + 2 ^ k = 2 ^ k * (2 ^ l * n2 + 1) := by
    rw [Nat.pow_add, Nat.mul_assoc, Nat.mul_add, Nat.mul_one]
  have hdvd3 : 2 ^ k ∣ 3 ^ k * (n1 + 1) := ⟨2 ^ l * n2 + 1, by omega⟩
  rcases pow2_dvd_of_pow2_dvd_pow3_mul_nat k k (n1 + 1) hdvd3 with ⟨u, hu⟩
  have hmul_u : 2 ^ k * (2 ^ l * n2 + 1) = 2 ^ k * (3 ^ k * u) := by
    rw [← hfac, hsub, hu, ← Nat.mul_assoc, Nat.mul_comm (3 ^ k) (2 ^ k), Nat.mul_assoc]
  have hu_eq : 2 ^ l * n2 + 1 = 3 ^ k * u := mul_left_cancel_pow2_nat k _ _ hmul_u
  have hp2l : 2 ^ l = 2 * 2 ^ (l - 1) := by
    conv => lhs; rw [show l = (l - 1) + 1 by omega]
    rw [Nat.pow_succ, Nat.mul_comm]
  have hlhs_odd : (2 ^ l * n2 + 1) % 2 = 1 := by
    rw [hp2l, Nat.mul_assoc]
    omega
  have hrhs_mod : (3 ^ k * u) % 2 = u % 2 := by
    rw [Nat.mul_mod, pow3_mod2_nat k]
    omega
  exact ⟨u, by omega, hu, hu_eq⟩

theorem no_spiral_step_of_pow3_lt_target
    (k kMax l hi targetMin n1 n2 : Nat)
    (hk_le : k ≤ kMax) (hl : l ≥ 1)
    (hn1_hi : n1 ≤ hi) (hn2_lo : targetMin ≤ n2)
    (hlt : 3 ^ kMax * (hi + 1) < 2 ^ kMax * (2 * targetMin + 1))
    (hstep : 2 ^ (k + l) * (n2 + 1) = 3 ^ k * (n1 + 1) + 2 ^ k * (2 ^ l - 1)) :
    False := by
  have hsmall : 3 ^ k * (hi + 1) < 2 ^ k * (2 * targetMin + 1) := by
    have hdown := pow3_mul_lt_pow2_mul_down (kMax - k) k (hi + 1) (2 * targetMin + 1)
    rw [show k + (kMax - k) = kMax by omega] at hdown
    exact hdown hlt
  have hsub := spiral_step_mul_ratio_nat k l n1 n2 hl hstep
  have h3le : 3 ^ k * (n1 + 1) ≤ 3 ^ k * (hi + 1) :=
    Nat.mul_le_mul_left (3 ^ k) (by omega)
  have hp2l : 2 ≤ 2 ^ l := by simpa using pow2_mono_nat hl
  have h2ge : 2 * targetMin ≤ 2 ^ l * n2 := Nat.mul_le_mul hp2l hn2_lo
  have hbig : 2 ^ k * (2 * targetMin + 1) ≤ 2 ^ (k + l) * n2 + 2 ^ k := by
    rw [Nat.mul_add, Nat.mul_one, Nat.pow_add, Nat.mul_assoc]
    have hm := Nat.mul_le_mul_left (2 ^ k) h2ge
    omega
  omega

theorem no_spiral_step_of_odd_gap
    (k l lo hi uOdd n1 n2 : Nat)
    (hl : l ≥ 1) (hn1_lo : lo ≤ n1) (hn1_hi : n1 ≤ hi)
    (hu_odd : uOdd % 2 = 1)
    (hlo_gt : 2 ^ k * uOdd < lo + 1)
    (hhi_lt : hi + 1 < 2 ^ k * (uOdd + 2))
    (hstep : 2 ^ (k + l) * (n2 + 1) = 3 ^ k * (n1 + 1) + 2 ^ k * (2 ^ l - 1)) :
    False := by
  rcases spiral_step_odd_quotient_nat k l n1 n2 hl hstep with ⟨u, hu_mod, hu_eq, _⟩
  by_cases hle : u ≤ uOdd
  · have hm := Nat.mul_le_mul_left (2 ^ k) hle
    omega
  · have hge2 : uOdd + 2 ≤ u := by omega
    have hm := Nat.mul_le_mul_left (2 ^ k) hge2
    omega

theorem no_spiral_step_of_hi_lt_pow2
    (k kMin l hi n1 n2 : Nat)
    (hk_ge : kMin ≤ k) (hl : l ≥ 1) (hn1_hi : n1 ≤ hi)
    (hhi_lt : hi + 1 < 2 ^ kMin)
    (hstep : 2 ^ (k + l) * (n2 + 1) = 3 ^ k * (n1 + 1) + 2 ^ k * (2 ^ l - 1)) :
    False := by
  rcases spiral_step_odd_quotient_nat k l n1 n2 hl hstep with ⟨u, hu_mod, hu_eq, _⟩
  have hu_ge1 : 1 ≤ u := by omega
  have hp : 2 ^ kMin ≤ 2 ^ k := pow2_mono_nat hk_ge
  have hm : 2 ^ k * 1 ≤ 2 ^ k * u := Nat.mul_le_mul_left (2 ^ k) hu_ge1
  omega

def m92GlobalHi1 : Nat := 11954868071481462849280

def m92NoOddMulBands : List (Nat × Nat × Nat × Nat) := [
  (69, 11235001691085072920395, 11954868071473219535819, 19),
  (70, 11235001691087722366030, 11954868071476038740827, 9),
  (72, 11235001691090666194514, 11954868071479171190836, 1),
  (73, 11235001691091451215443, 11954868071480006510839, 1)
]

def lookupActiveBand : Nat -> List HenselBandCert -> Option HenselBandCert
  | _, [] => none
  | k, b :: rest => if b.k1 == k then some b else lookupActiveBand k rest

def lookupOddGapBand : Nat -> List (Nat × Nat × Nat × Nat) -> Option (Nat × Nat × Nat × Nat)
  | _, [] => none
  | k, e :: rest => if e.1 == k then some e else lookupOddGapBand k rest

def checkOddGapEntry (e : Nat × Nat × Nat × Nat) : Bool :=
  let (k, lo, hi, uOdd) := e
  (lo ≤ hi) && (uOdd % 2 == 1) && (2 ^ k * uOdd < lo + 1) && (hi + 1 < 2 ^ k * (uOdd + 2))

def checkM92MidRange : Nat -> Bool
  | 0 => true
  | d + 1 =>
    let k := d + 9
    ((lookupActiveBand k m92HenselBands).isSome || (lookupOddGapBand k m92NoOddMulBands).isSome) &&
    checkM92MidRange d

def m92BandBounds (k1 : Nat) : Nat × Nat :=
  match lookupActiveBand k1 m92HenselBands with
  | some b => (b.lo1, b.hi1)
  | none =>
    match lookupOddGapBand k1 m92NoOddMulBands with
    | some (_, lo1, hi1, _) => (lo1, hi1)
    | none => (2 ^ 71 + 1, m92GlobalHi1)

theorem lookupActiveBand_mem : ∀ (bs : List HenselBandCert) (k : Nat) (b : HenselBandCert),
    lookupActiveBand k bs = some b -> b ∈ bs ∧ b.k1 = k
  | [], _, _, h => by simp [lookupActiveBand] at h
  | hd :: tl, k, b, h => by
    unfold lookupActiveBand at h
    cases heq : (hd.k1 == k) with
    | true =>
      rw [heq] at h
      simp at h
      subst h
      exact ⟨List.Mem.head tl, of_decide_eq_true heq⟩
    | false =>
      rw [heq] at h
      simp at h
      rcases lookupActiveBand_mem tl k b h with ⟨hm, hk⟩
      exact ⟨List.Mem.tail hd hm, hk⟩

theorem lookupOddGapBand_mem :
    ∀ (es : List (Nat × Nat × Nat × Nat)) (k : Nat) (e : Nat × Nat × Nat × Nat),
      lookupOddGapBand k es = some e -> e ∈ es ∧ e.1 = k
  | [], _, _, h => by simp [lookupOddGapBand] at h
  | hd :: tl, k, e, h => by
    unfold lookupOddGapBand at h
    cases heq : (hd.1 == k) with
    | true =>
      rw [heq] at h
      simp at h
      subst h
      exact ⟨List.Mem.head tl, of_decide_eq_true heq⟩
    | false =>
      rw [heq] at h
      simp at h
      rcases lookupOddGapBand_mem tl k e h with ⟨hm, hk⟩
      exact ⟨List.Mem.tail hd hm, hk⟩

theorem all_oddGap_mem :
    ∀ (es : List (Nat × Nat × Nat × Nat)) (e : Nat × Nat × Nat × Nat),
      es.all checkOddGapEntry = true -> e ∈ es -> checkOddGapEntry e = true
  | [], _, _, hm => by cases hm
  | _ :: _, _, hok, .head _ => by
    simp only [List.all_cons, Bool.and_eq_true] at hok
    exact hok.1
  | _ :: tl, e, hok, .tail _ hm => by
    simp only [List.all_cons, Bool.and_eq_true] at hok
    exact all_oddGap_mem tl e hok.2 hm

theorem checkM92MidRange_covered : ∀ (n k : Nat),
    checkM92MidRange n = true -> 9 ≤ k -> k < 9 + n ->
    (lookupActiveBand k m92HenselBands).isSome = true ∨
    (lookupOddGapBand k m92NoOddMulBands).isSome = true
  | 0, _, _, h9, hlt => by omega
  | d + 1, k, hok, h9, hlt => by
    unfold checkM92MidRange at hok
    simp only [Bool.and_eq_true, Bool.or_eq_true] at hok
    by_cases htop : k = d + 9
    · subst htop
      exact hok.1
    · exact checkM92MidRange_covered d k hok.2 h9 (by omega)

set_option maxRecDepth 20000 in
theorem m92_nonactive_bounds_kernel_verified :
    3 ^ 8 * (m92GlobalHi1 + 1) < 2 ^ 8 * (2 * (m92B1 + 1) + 1) ∧
    m92GlobalHi1 + 1 < 2 ^ 74 ∧
    m92NoOddMulBands.all checkOddGapEntry = true ∧
    checkM92MidRange 65 = true := by
  decide

/--
  Theorem 24.2e (Complete All-`k1 >= 1` Zero-Trust-Gap `m = 92` Elimination Theorem):
  Across EVERY exponent `k1 >= 1` (covering `1 <= k1 <= 8` via `(3/2)^8` growth insufficiency,
  `9 <= k1 <= 68` and `k1 = 71` via the 61 reflective 2-step Hensel bands, `k1 in {69, 70, 72, 73}`
  via odd-multiple interval exclusion, and all `k1 >= 74` via `hi1 + 1 < 2^74 <= 2^k1`),
  NO integer `z1` in `m92BandBounds k1` admits a `ValidTwoStepSpiral`!
-/
theorem m92_all_k1_hensel_complete
    (k1 l1 k2 l2 : Nat) (z1 z2 z3 : Int)
    (_hk1 : k1 ≥ 1)
    (hz1_lo : ((m92BandBounds k1).1 : Int) ≤ z1)
    (hz1_hi : z1 ≤ ((m92BandBounds k1).2 : Int)) :
    ¬ ValidTwoStepSpiral m92B1 m92B2 k1 l1 k2 l2 z1 z2 z3 := by
  intro hvalid
  have hcert := m92_two_step_hensel_kernel_verified
  have hnon := m92_nonactive_bounds_kernel_verified
  unfold m92BandBounds at hz1_lo hz1_hi
  cases hact : lookupActiveBand k1 m92HenselBands with
  | some b =>
    simp only [hact] at hz1_lo hz1_hi
    rcases lookupActiveBand_mem m92HenselBands k1 b hact with ⟨hb_mem, hb_k1⟩
    rw [← hb_k1] at hvalid
    exact verifyTwoStepHenselCert_sound m92HenselBands m92B1 m92B2 b hcert.2.2.2 hb_mem
      l1 k2 l2 z1 z2 z3 hz1_lo hz1_hi hvalid
  | none =>
    simp only [hact] at hz1_lo hz1_hi
    rcases hvalid with ⟨hl1, _hk2, _hl2, hz2_lo, _hz2_hi, _hz3_lo, hs1_int, _hs2_int⟩
    let n1 := z1.toNat
    let n2 := z2.toNat
    have hn2_lo : m92B1 + 1 ≤ n2 := by dsimp [n2]; omega
    have hs1_nat : 2 ^ (k1 + l1) * (n2 + 1) =
        3 ^ k1 * (n1 + 1) + 2 ^ k1 * (2 ^ l1 - 1) := by
      have hp2l1 : 2 ^ l1 ≥ 1 := pow2_pos_nat l1
      have hlhs_c : ((2 ^ (k1 + l1) * (n2 + 1) : Nat) : Int) =
          (2 : Int) ^ (k1 + l1) * (z2 + 1) := by
        rw [natCast_mul, natCast_pow2, show ((n2 + 1 : Nat) : Int) = z2 + 1 by omega]
      have hrhs_c : ((3 ^ k1 * (n1 + 1) + 2 ^ k1 * (2 ^ l1 - 1) : Nat) : Int) =
          (3 : Int) ^ k1 * (z1 + 1) + (2 : Int) ^ k1 * ((2 : Int) ^ l1 - 1) := by
        rw [natCast_add, natCast_mul, natCast_mul, natCast_pow3, natCast_pow2]
        have hz1p : ((n1 + 1 : Nat) : Int) = z1 + 1 := by
          cases hgap_tmp : lookupOddGapBand k1 m92NoOddMulBands with
          | some e =>
            rcases e with ⟨_, _, _, _⟩
            simp only [hgap_tmp] at hz1_lo
            dsimp [n1]
            omega
          | none =>
            simp only [hgap_tmp] at hz1_lo
            dsimp [n1]
            omega
        have hsub : ((2 ^ l1 - 1 : Nat) : Int) = (2 : Int) ^ l1 - 1 := by
          rw [← natCast_pow2 l1]; omega
        rw [hz1p, hsub]
      have hcast : ((2 ^ (k1 + l1) * (n2 + 1) : Nat) : Int) =
          ((3 ^ k1 * (n1 + 1) + 2 ^ k1 * (2 ^ l1 - 1) : Nat) : Int) := by
        rw [hlhs_c, hrhs_c]; exact hs1_int
      omega
    cases hgap : lookupOddGapBand k1 m92NoOddMulBands with
    | some e =>
      rcases e with ⟨ke, loe, hie, uOdd⟩
      simp only [hgap] at hz1_lo hz1_hi
      rcases lookupOddGapBand_mem m92NoOddMulBands k1 (ke, loe, hie, uOdd) hgap with ⟨he_mem, he_k⟩
      dsimp at he_k
      subst he_k
      have he_ok := all_oddGap_mem m92NoOddMulBands (ke, loe, hie, uOdd) hnon.2.2.1 he_mem
      unfold checkOddGapEntry at he_ok
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at he_ok
      exact no_spiral_step_of_odd_gap ke l1 loe hie uOdd n1 n2 hl1
        (by dsimp [n1]; omega) (by dsimp [n1]; omega)
        he_ok.1.1.2 he_ok.1.2 he_ok.2 hs1_nat
    | none =>
      simp only [hgap] at hz1_lo hz1_hi
      have hn1_hi : n1 ≤ m92GlobalHi1 := by dsimp [n1]; omega
      by_cases hk8 : k1 ≤ 8
      · exact no_spiral_step_of_pow3_lt_target k1 8 l1 m92GlobalHi1 (m92B1 + 1) n1 n2
          hk8 hl1 hn1_hi hn2_lo hnon.1 hs1_nat
      · by_cases hk74 : 74 ≤ k1
        · exact no_spiral_step_of_hi_lt_pow2 k1 74 l1 m92GlobalHi1 n1 n2
            hk74 hl1 hn1_hi hnon.2.1 hs1_nat
        · have hcov := checkM92MidRange_covered 65 k1 hnon.2.2.2 (by omega) (by omega)
          rw [hact, hgap] at hcov
          simp [Option.isSome] at hcov

/--
  Inductive predicate for an arbitrary-depth (`r`-step, `r >= 1`) windowed spiral trajectory
  `z_1 -> z_2 -> ... -> z_{r+1} -> z_{r+2}` across intermediate windows `windows`
  (`|windows| = r`) and final exit `zExit >= bExit + 1`.
  Supports both standard `I_1 = [b1 + 1, b2]` spirals (`windows = List.replicate r (b1 + 1, b2)`)
  and Theorem 24.3's `(r + 1)`-way disjoint first-hit `Lambda`-squeeze partitions!
-/
inductive SpiralWindowedPath (bExit : Nat) :
    List (Nat × Nat) -> List (Nat × Nat) -> Int -> Int -> Prop where
  | exit (kLast lLast : Nat) (zCur zExit : Int)
      (hk : kLast ≥ 1) (hl : lLast ≥ 1)
      (hexit : (bExit + 1 : Int) ≤ zExit)
      (hstep : (2 : Int) ^ (kLast + lLast) * (zExit + 1) =
               (3 : Int) ^ kLast * (zCur + 1) + (2 : Int) ^ kLast * ((2 : Int) ^ lLast - 1)) :
      SpiralWindowedPath bExit [] [(kLast, lLast)] zCur zExit
  | step (wLo wHi k l : Nat) (winRest stepsRest : List (Nat × Nat)) (zCur zNext zExit : Int)
      (hk : k ≥ 1) (hl : l ≥ 1)
      (hlo : (wLo : Int) ≤ zNext) (hhi : zNext ≤ (wHi : Int))
      (hstep : (2 : Int) ^ (k + l) * (zNext + 1) =
               (3 : Int) ^ k * (zCur + 1) + (2 : Int) ^ k * ((2 : Int) ^ l - 1))
      (hrest : SpiralWindowedPath bExit winRest stepsRest zNext zExit) :
      SpiralWindowedPath bExit ((wLo, wHi) :: winRest) ((k, l) :: stepsRest) zCur zExit

theorem spiralWindowedPath_implies_spiralPath :
    ∀ {bExit : Nat} {windows steps : List (Nat × Nat)} {zCur zExit : Int},
      SpiralWindowedPath bExit windows steps zCur zExit ->
      SpiralPath steps zCur zExit
  | _, _, _, _, _, .exit kLast lLast zCur zExit _ _ _ hstep =>
    SpiralPath.cons kLast lLast [] zCur zExit zExit hstep (SpiralPath.nil zExit)
  | _, _, _, _, _, .step _ _ k l _ stepsRest zCur zNext zExit _ _ _ _ hstep hrest =>
    SpiralPath.cons k l stepsRest zCur zNext zExit hstep
      (spiralWindowedPath_implies_spiralPath hrest)

/-- First-order recursive certificate tree for arbitrary-depth (`r`-step) Hensel pruning -/
inductive HenselTree where
  | emptyRange : HenselTree
  | collapse (kMin : Nat) : HenselTree
  | hiLtPow2 (kMin : Nat) : HenselTree
  | exactK (kMin : Nat) (restK : HenselTree) : HenselTree
  | skipOddGapK (kMin uOdd : Nat) (restK : HenselTree) : HenselTree
  | branchK (kMin uMin uMax lMin : Nat) (lNode : HenselTree) (restK : HenselTree) : HenselTree
  | lDone : HenselTree
  | lStep (child : HenselTree) (moreL : HenselTree) : HenselTree

/-- Multi-step Hensel band certificate for arbitrary depth `r = windows.length >= 1` -/
structure MultiStepBandCert where
  k1 : Nat
  lo1 : Nat
  hi1 : Nat
  uMin : Nat
  uMax : Nat
  l1Min : Nat
  wMax : Nat
  maxExp : Nat
  inv3Max : Nat
  tree : HenselTree

def maxNat (a b : Nat) : Nat :=
  if a ≤ b then b else a

def ceilDiv (a P : Nat) : Nat :=
  (a + P - 1) / P

def nextWindowFloor (bExit : Nat) : List (Nat × Nat) -> Nat
  | [] => bExit + 1
  | (wLo, _) :: _ => wLo

def firstStepK : List (Nat × Nat) -> Nat
  | [] => 0
  | (k, _) :: _ => k

def memNatList (x : Nat) : List Nat -> Bool
  | [] => false
  | y :: rest => (x == y) || memNatList x rest

theorem memNatList_sound : ∀ (xs : List Nat) (x : Nat),
    memNatList x xs = true -> ∃ s ∈ xs, x = s
  | [], _, h => by simp [memNatList] at h
  | y :: rest, x, h => by
    unfold memNatList at h
    simp only [Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | hrest
    · exact ⟨x, List.Mem.head rest, rfl⟩
    · rcases memNatList_sound rest x hrest with ⟨s, hs, hxs⟩
      exact ⟨s, List.Mem.tail y hs, hxs⟩

def checkCongruenceSpan
    (lo1 hi1 wMax maxExp inv3Max : Nat) (exemptIds : List Nat)
    (exp w g : Nat) : Bool :=
  let M := 2 ^ exp
  let span := hi1 - lo1
  let invAt := 3 ^ (wMax - w) * inv3Max
  let rem := (invAt * g + (lo1 + 1)) % M
  let off := (M - rem) % M
  (w ≤ wMax) && (exp ≤ maxExp) && (span < M) &&
  ((off > span) || memNatList (lo1 + off) exemptIds)

def checkKMinFloor (kMin kFloor hiCur targetMin : Nat) : Bool :=
  (kMin ≥ 1) &&
  ((kMin ≤ kFloor) || (3 ^ (kMin - 1) * (hiCur + 1) < 2 ^ (kMin - 1) * (2 * targetMin + 1)))

def checkHenselNode
    (bExit lo1 hi1 wMax maxExp inv3Max : Nat) (exemptIds : List Nat)
    (mode : Option (Nat × Nat × Nat × Nat))
    (windows : List (Nat × Nat))
    (kAcc wAcc gAcc loCur hiCur kFloor : Nat) : HenselTree -> Bool
  | .emptyRange =>
    match mode with
    | none => loCur > hiCur
    | some _ => false
  | .collapse kMin =>
    match mode with
    | none =>
      let targetMin := nextWindowFloor bExit windows
      checkKMinFloor kMin kFloor hiCur targetMin &&
      checkCongruenceSpan lo1 hi1 wMax maxExp inv3Max exemptIds (kAcc + kMin) wAcc gAcc
    | some _ => false
  | .hiLtPow2 kMin =>
    match mode with
    | none =>
      let targetMin := nextWindowFloor bExit windows
      checkKMinFloor kMin kFloor hiCur targetMin && (hiCur + 1 < 2 ^ kMin)
    | some _ => false
  | .exactK kMin restK =>
    match mode with
    | none =>
      let targetMin := nextWindowFloor bExit windows
      let gExact := 3 ^ kMin * gAcc + 2 ^ (kAcc + kMin)
      checkKMinFloor kMin kFloor hiCur targetMin &&
      checkCongruenceSpan lo1 hi1 wMax maxExp inv3Max exemptIds
        (kAcc + kMin + 1) (wAcc + kMin) gExact &&
      checkHenselNode bExit lo1 hi1 wMax maxExp inv3Max exemptIds
        none windows kAcc wAcc gAcc loCur hiCur (kMin + 1) restK
    | some _ => false
  | .skipOddGapK kMin uOdd restK =>
    match mode with
    | none =>
      let targetMin := nextWindowFloor bExit windows
      checkKMinFloor kMin kFloor hiCur targetMin &&
      (uOdd % 2 == 1) && (2 ^ kMin * uOdd < loCur + 1) && (hiCur + 1 < 2 ^ kMin * (uOdd + 2)) &&
      checkHenselNode bExit lo1 hi1 wMax maxExp inv3Max exemptIds
        none windows kAcc wAcc gAcc loCur hiCur (kMin + 1) restK
    | some _ => false
  | .branchK kMin uMin uMax lMin lNode restK =>
    match mode, windows with
    | none, (wLo, wHi) :: _ =>
      let evMin := 3 ^ kMin * uMin - 1
      let evMax := 3 ^ kMin * uMax - 1
      checkKMinFloor kMin kFloor hiCur wLo &&
      (uMin % 2 == 1) && ((uMin ≤ 1) || (2 ^ kMin * (uMin - 2) < loCur + 1)) &&
      (uMax % 2 == 1) && (hiCur + 1 < 2 ^ kMin * (uMax + 2)) &&
      (lMin ≥ 1) && ((lMin ≤ 1) || (evMin > 2 ^ (lMin - 1) * wHi)) &&
      checkHenselNode bExit lo1 hi1 wMax maxExp inv3Max exemptIds
        (some (kMin, evMin, evMax, lMin)) windows kAcc wAcc gAcc loCur hiCur 1 lNode &&
      checkHenselNode bExit lo1 hi1 wMax maxExp inv3Max exemptIds
        none windows kAcc wAcc gAcc loCur hiCur (kMin + 1) restK
    | _, _ => false
  | .lDone =>
    match mode, windows with
    | some (_, _, evMax, lCur), (wLo, _) :: _ => evMax < 2 ^ lCur * wLo
    | _, _ => false
  | .lStep child moreL =>
    match mode, windows with
    | some (kFixed, evMin, evMax, lCur), (wLo, wHi) :: winRest =>
      let P := 2 ^ lCur
      let loNext := maxNat wLo (ceilDiv evMin P)
      let hiNext := minNat wHi (evMax / P)
      let gNext := 3 ^ kFixed * gAcc + 2 ^ (kAcc + kFixed) * (P - 1)
      checkHenselNode bExit lo1 hi1 wMax maxExp inv3Max exemptIds
        none winRest (kAcc + kFixed + lCur) (wAcc + kFixed) gNext loNext hiNext 1 child &&
      checkHenselNode bExit lo1 hi1 wMax maxExp inv3Max exemptIds
        (some (kFixed, evMin, evMax, lCur + 1)) windows kAcc wAcc gAcc loCur hiCur 1 moreL
    | _, _ => false

def verifyMultiStepHenselBand
    (windows : List (Nat × Nat)) (bExit : Nat) (exemptIds : List Nat)
    (band : MultiStepBandCert) : Bool :=
  match windows with
  | [] => false
  | (_, wHi) :: _ =>
    let evMin := 3 ^ band.k1 * band.uMin - 1
    let evMax := 3 ^ band.k1 * band.uMax - 1
    (band.k1 ≥ 1) &&
    (band.lo1 ≤ band.hi1) &&
    (band.uMin % 2 == 1) && ((band.uMin ≤ 1) || (2 ^ band.k1 * (band.uMin - 2) < band.lo1 + 1)) &&
    (band.uMax % 2 == 1) && (band.hi1 + 1 < 2 ^ band.k1 * (band.uMax + 2)) &&
    (band.l1Min ≥ 1) && ((band.l1Min ≤ 1) || (evMin > 2 ^ (band.l1Min - 1) * wHi)) &&
    ((3 ^ band.wMax * band.inv3Max) % (2 ^ band.maxExp) == 1) &&
    checkHenselNode bExit band.lo1 band.hi1 band.wMax band.maxExp band.inv3Max exemptIds
      (some (band.k1, evMin, evMax, band.l1Min)) windows 0 0 0 band.lo1 band.hi1 1 band.tree

theorem div_le_of_lt_mul_succ {Y P n : Nat} (_hP : P > 0) (hlt : Y < P * (n + 1)) :
    Y / P ≤ n := by
  apply Classical.byContradiction
  intro hgt
  have hge : n + 1 ≤ Y / P := by omega
  have hmul : P * (n + 1) ≤ P * (Y / P) := Nat.mul_le_mul_left P hge
  have hdm := Nat.div_add_mod Y P
  omega

theorem ceilDiv_le_of_le_mul {a P n : Nat} (hP : P > 0) (hle : a ≤ P * n) :
    ceilDiv a P ≤ n := by
  unfold ceilDiv
  apply div_le_of_lt_mul_succ hP
  rw [Nat.mul_add, Nat.mul_one]
  omega

theorem exit_step_exact_mod_dvd (k l nCur nNext : Nat)
    (hl : l ≥ 1)
    (hstep : 2 ^ (k + l) * (nNext + 1) = 3 ^ k * (nCur + 1) + 2 ^ k * (2 ^ l - 1)) :
    2 ^ (k + 1) ∣ 3 ^ k * (nCur + 1) + 2 ^ k := by
  have hp2lm1 : 2 ^ (l - 1) ≥ 1 := pow2_pos_nat (l - 1)
  have hp2l : 2 ^ l = 2 * 2 ^ (l - 1) := by
    conv => lhs; rw [show l = (l - 1) + 1 by omega]
    rw [Nat.pow_succ, Nat.mul_comm]
  have hlhs : 2 ^ (k + l) * (nNext + 1) = 2 ^ (k + 1) * (2 ^ (l - 1) * (nNext + 1)) := by
    rw [show k + l = (k + 1) + (l - 1) by omega, Nat.pow_add, Nat.mul_assoc]
  have hsub_l : 2 ^ l - 1 = 2 * (2 ^ (l - 1) - 1) + 1 := by omega
  have hrhs : 2 ^ k * (2 ^ l - 1) = 2 ^ (k + 1) * (2 ^ (l - 1) - 1) + 2 ^ k := by
    rw [hsub_l, Nat.mul_add, Nat.mul_one, ← Nat.mul_assoc, ← Nat.pow_succ]
  let A := 2 ^ (l - 1) * (nNext + 1)
  let B := 2 ^ (l - 1) - 1
  have hBA : B ≤ A := by
    have hm : 2 ^ (l - 1) * 1 ≤ 2 ^ (l - 1) * (nNext + 1) :=
      Nat.mul_le_mul_left (2 ^ (l - 1)) (by omega)
    dsimp [A, B]; omega
  refine ⟨A - B, ?_⟩
  have hAB : 2 ^ (k + 1) * A = 2 ^ (k + 1) * (A - B) + 2 ^ (k + 1) * B := by
    rw [← Nat.mul_add, show (A - B) + B = A by omega]
  rw [hlhs, hrhs] at hstep
  change 2 ^ (k + 1) * A = 3 ^ k * (nCur + 1) + (2 ^ (k + 1) * B + 2 ^ k) at hstep
  omega

theorem checkCongruenceSpan_sound
    (lo1 hi1 wMax maxExp inv3Max : Nat) (exemptIds : List Nat)
    (exp w g n1 : Nat)
    (hn1_lo : lo1 ≤ n1) (hn1_hi : n1 ≤ hi1)
    (hinv : (3 ^ wMax * inv3Max) % 2 ^ maxExp = 1)
    (hdvd : 2 ^ exp ∣ 3 ^ w * (n1 + 1) + g)
    (hok : checkCongruenceSpan lo1 hi1 wMax maxExp inv3Max exemptIds exp w g = true) :
    ∃ s ∈ exemptIds, n1 = s := by
  unfold checkCongruenceSpan at hok
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hok
  rcases hok with ⟨⟨⟨hw_le, hexp_le⟩, hspan_lt⟩, hoff_or⟩
  let M := 2 ^ exp
  have hM_pos : M ≥ 1 := pow2_pos_nat exp
  let invAt := 3 ^ (wMax - w) * inv3Max
  have h3inv : 3 ^ w * invAt = 3 ^ wMax * inv3Max := by
    dsimp [invAt]
    rw [← Nat.mul_assoc, ← Nat.pow_add, show w + (wMax - w) = wMax by omega]
  have hinv_eq : 3 ^ w * invAt = M * (2 ^ (maxExp - exp) * ((3 ^ wMax * inv3Max) / 2 ^ maxExp)) + 1 := by
    have hdm := (Nat.div_add_mod (3 ^ wMax * inv3Max) (2 ^ maxExp)).symm
    have hp : 2 ^ maxExp = M * 2 ^ (maxExp - exp) := by
      dsimp [M]; rw [← Nat.pow_add, show exp + (maxExp - exp) = maxExp by omega]
    calc
      3 ^ w * invAt = 3 ^ wMax * inv3Max := h3inv
      _ = 2 ^ maxExp * ((3 ^ wMax * inv3Max) / 2 ^ maxExp) + (3 ^ wMax * inv3Max) % 2 ^ maxExp := hdm
      _ = 2 ^ maxExp * ((3 ^ wMax * inv3Max) / 2 ^ maxExp) + 1 := by rw [hinv]
      _ = (M * 2 ^ (maxExp - exp)) * ((3 ^ wMax * inv3Max) / 2 ^ maxExp) + 1 :=
            congrArg (fun t => t * ((3 ^ wMax * inv3Max) / 2 ^ maxExp) + 1) hp
      _ = M * (2 ^ (maxExp - exp) * ((3 ^ wMax * inv3Max) / 2 ^ maxExp)) + 1 := by rw [Nat.mul_assoc]
  rcases hdvd with ⟨Q, hQ⟩
  let qInv := 2 ^ (maxExp - exp) * ((3 ^ wMax * inv3Max) / 2 ^ maxExp)
  let S := invAt * g + (lo1 + 1)
  let qRem := S / M
  let rem := S % M
  have hS_dm : M * qRem + rem = S := Nat.div_add_mod S M
  have hrem_lt_M : rem < M := Nat.mod_lt S (by omega)
  let delta := n1 - lo1
  have hn1_split : n1 + 1 = delta + (lo1 + 1) := by dsimp [delta]; omega
  have hmul : M * (invAt * Q) = M * (qInv * (n1 + 1) + qRem) + (delta + rem) := by
    have h1 := congrArg (fun t => invAt * t) hQ.symm
    have hlhs : invAt * (M * Q) = M * (invAt * Q) := by
      rw [← Nat.mul_assoc, Nat.mul_comm invAt M, Nat.mul_assoc]
    have hrhs1 : invAt * (3 ^ w * (n1 + 1) + g) = (3 ^ w * invAt) * (n1 + 1) + invAt * g := by
      rw [Nat.mul_add, ← Nat.mul_assoc invAt (3 ^ w), Nat.mul_comm invAt (3 ^ w)]
    rw [hlhs, hrhs1, hinv_eq] at h1
    change M * (invAt * Q) = (M * qInv + 1) * (n1 + 1) + invAt * g at h1
    have hexp1 : (M * qInv + 1) * (n1 + 1) + invAt * g = M * (qInv * (n1 + 1)) + delta + S := by
      rw [Nat.add_mul, Nat.one_mul, Nat.mul_assoc, hn1_split]; dsimp [S]; omega
    have hexp2 : M * (qInv * (n1 + 1) + qRem) = M * (qInv * (n1 + 1)) + M * qRem :=
      Nat.mul_add M (qInv * (n1 + 1)) qRem
    rw [hexp1] at h1
    omega
  let A := invAt * Q
  let B := qInv * (n1 + 1) + qRem
  have hBA : B ≤ A := by
    apply Classical.byContradiction
    intro hlt
    have hm : M * (A + 1) ≤ M * B := Nat.mul_le_mul_left M (by omega)
    rw [Nat.mul_add, Nat.mul_one] at hm
    dsimp [A, B] at hm
    omega
  have hAB : M * A = M * B + M * (A - B) := by
    have hsp : A = B + (A - B) := by omega
    conv => lhs; rw [hsp]
    exact Nat.mul_add M B (A - B)
  change M * A = M * B + (delta + rem) at hmul
  have hdvd_dr : delta + rem = M * (A - B) := by omega
  let off := (M - rem) % M
  have hdelta_eq_off : delta = off := by
    by_cases hrem0 : rem = 0
    · have hoff0 : off = 0 := by dsimp [off]; rw [hrem0, Nat.sub_zero, Nat.mod_self]
      cases hdiff : A - B with
      | zero => rw [hdiff, Nat.mul_zero] at hdvd_dr; omega
      | succ q' => rw [hdiff, Nat.mul_add, Nat.mul_one] at hdvd_dr; dsimp [delta, M] at *; omega
    · have hoff_val : off = M - rem := by
        dsimp [off]; exact Nat.mod_eq_of_lt (by omega)
      cases hdiff : A - B with
      | zero => rw [hdiff, Nat.mul_zero] at hdvd_dr; omega
      | succ q' =>
        cases q' with
        | zero => rw [hdiff, Nat.mul_one] at hdvd_dr; omega
        | succ q'' =>
          rw [hdiff, show q'' + 1 + 1 = (q'' + 1) + 1 by rfl, Nat.mul_add, Nat.mul_add,
              Nat.mul_one] at hdvd_dr
          dsimp [delta, M] at *; omega
  rcases hoff_or with hoff_gt | hmem
  · dsimp [delta, M, rem, S, invAt] at hdelta_eq_off
    dsimp [off, M, rem, S, invAt] at hoff_gt hdelta_eq_off
    omega
  · rcases memNatList_sound exemptIds (lo1 + off) hmem with ⟨s, hs, hseq⟩
    refine ⟨s, hs, ?_⟩
    dsimp [delta, M, rem, S, invAt, off] at *
    omega

theorem spiral_int_step_to_nat
    (k l : Nat) (zCur zAfter : Int)
    (hzCur : 0 ≤ zCur) (hzAfter : 0 ≤ zAfter)
    (hstep : (2 : Int) ^ (k + l) * (zAfter + 1) =
             (3 : Int) ^ k * (zCur + 1) + (2 : Int) ^ k * ((2 : Int) ^ l - 1)) :
    2 ^ (k + l) * (zAfter.toNat + 1) =
      3 ^ k * (zCur.toNat + 1) + 2 ^ k * (2 ^ l - 1) := by
  have hp2l : 2 ^ l ≥ 1 := pow2_pos_nat l
  have hlhs_c : ((2 ^ (k + l) * (zAfter.toNat + 1) : Nat) : Int) =
      (2 : Int) ^ (k + l) * (zAfter + 1) := by
    rw [natCast_mul, natCast_pow2, show ((zAfter.toNat + 1 : Nat) : Int) = zAfter + 1 by omega]
  have hrhs_c : ((3 ^ k * (zCur.toNat + 1) + 2 ^ k * (2 ^ l - 1) : Nat) : Int) =
      (3 : Int) ^ k * (zCur + 1) + (2 : Int) ^ k * ((2 : Int) ^ l - 1) := by
    rw [natCast_add, natCast_mul, natCast_mul, natCast_pow3, natCast_pow2]
    have hcur : ((zCur.toNat + 1 : Nat) : Int) = zCur + 1 := by omega
    have hsub : ((2 ^ l - 1 : Nat) : Int) = (2 : Int) ^ l - 1 := by
      rw [← natCast_pow2 l]; omega
    rw [hcur, hsub]
  have hcast : ((2 ^ (k + l) * (zAfter.toNat + 1) : Nat) : Int) =
      ((3 ^ k * (zCur.toNat + 1) + 2 ^ k * (2 ^ l - 1) : Nat) : Int) := by
    rw [hlhs_c, hrhs_c]; exact hstep
  omega

theorem spiralWindowedPath_first_step_nat
    {bExit : Nat} {windows steps : List (Nat × Nat)} {zCur zExit : Int}
    (hzCur : 0 ≤ zCur)
    (hpath : SpiralWindowedPath bExit windows steps zCur zExit) :
    ∃ (k l nAfter : Nat) (stepsRest : List (Nat × Nat)),
      steps = (k, l) :: stepsRest ∧ k ≥ 1 ∧ l ≥ 1 ∧
      nextWindowFloor bExit windows ≤ nAfter ∧
      2 ^ (k + l) * (nAfter + 1) = 3 ^ k * (zCur.toNat + 1) + 2 ^ k * (2 ^ l - 1) := by
  cases hpath with
  | exit kLast lLast _ _ hk hl hexit hstep =>
    refine ⟨kLast, lLast, zExit.toNat, [], rfl, hk, hl, ?_, ?_⟩
    · simp only [nextWindowFloor]; omega
    · exact spiral_int_step_to_nat kLast lLast zCur zExit hzCur (by omega) hstep
  | step wLo _ k l _ stepsRest _ zNext _ hk hl hlo _ hstep _ =>
    refine ⟨k, l, zNext.toNat, stepsRest, rfl, hk, hl, ?_, ?_⟩
    · simp only [nextWindowFloor]; omega
    · exact spiral_int_step_to_nat k l zCur zNext hzCur (by omega) hstep

theorem checkKMinFloor_sound
    (kMin kFloor k l hiCur targetMin nCur nAfter : Nat)
    (hkFloor : kFloor ≤ k) (hl : l ≥ 1)
    (hnCur_hi : nCur ≤ hiCur) (hnAfter_lo : targetMin ≤ nAfter)
    (hstep : 2 ^ (k + l) * (nAfter + 1) = 3 ^ k * (nCur + 1) + 2 ^ k * (2 ^ l - 1))
    (hok : checkKMinFloor kMin kFloor hiCur targetMin = true) :
    kMin ≤ k := by
  unfold checkKMinFloor at hok
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hok
  rcases hok with ⟨_hkMin1, hle_or_lt⟩
  rcases hle_or_lt with hle | hlt
  · omega
  · apply Classical.byContradiction
    intro hgt
    exact no_spiral_step_of_pow3_lt_target k (kMin - 1) l hiCur targetMin nCur nAfter
      (by omega) hl hnCur_hi hnAfter_lo hlt hstep

def ModeInvariant
    (bExit : Nat) (mode : Option (Nat × Nat × Nat × Nat))
    (windows steps : List (Nat × Nat)) (zCur zExit : Int) (kFloor : Nat) : Prop :=
  match mode with
  | none => kFloor ≤ firstStepK steps
  | some (kFixed, evMin, evMax, lCur) =>
    ∃ (wLo wHi l : Nat) (winRest stepsRest : List (Nat × Nat)) (zNext : Int),
      windows = (wLo, wHi) :: winRest ∧
      steps = (kFixed, l) :: stepsRest ∧
      kFixed ≥ 1 ∧ l ≥ 1 ∧ lCur ≤ l ∧
      (wLo : Int) ≤ zNext ∧ zNext ≤ (wHi : Int) ∧
      evMin ≤ 2 ^ l * zNext.toNat ∧ 2 ^ l * zNext.toNat ≤ evMax ∧
      (2 : Int) ^ (kFixed + l) * (zNext + 1) =
        (3 : Int) ^ kFixed * (zCur + 1) + (2 : Int) ^ kFixed * ((2 : Int) ^ l - 1) ∧
      SpiralWindowedPath bExit winRest stepsRest zNext zExit

theorem odd_bounds_ev_range
    (k l loCur hiCur uMin uMax nCur nNext : Nat)
    (hl : l ≥ 1) (hnCur_lo : loCur ≤ nCur) (hnCur_hi : nCur ≤ hiCur)
    (huMin_odd : uMin % 2 = 1)
    (huMin_bound : uMin ≤ 1 ∨ 2 ^ k * (uMin - 2) < loCur + 1)
    (huMax_odd : uMax % 2 = 1)
    (huMax_bound : hiCur + 1 < 2 ^ k * (uMax + 2))
    (hstep : 2 ^ (k + l) * (nNext + 1) = 3 ^ k * (nCur + 1) + 2 ^ k * (2 ^ l - 1)) :
    3 ^ k * uMin - 1 ≤ 2 ^ l * nNext ∧ 2 ^ l * nNext ≤ 3 ^ k * uMax - 1 := by
  rcases spiral_step_odd_quotient_nat k l nCur nNext hl hstep with ⟨u, hu_odd, hu_eq, hl_eq⟩
  have hu_ge : uMin ≤ u := by
    rcases huMin_bound with h1 | hlt
    · omega
    · apply Classical.byContradiction
      intro hlt_u
      have hm := Nat.mul_le_mul_left (2 ^ k) (show u ≤ uMin - 2 by omega)
      omega
  have hu_le : u ≤ uMax := by
    apply Classical.byContradiction
    intro hgt_u
    have hm := Nat.mul_le_mul_left (2 ^ k) (show uMax + 2 ≤ u by omega)
    omega
  have hm_lo : 3 ^ k * uMin ≤ 3 ^ k * u := Nat.mul_le_mul_left (3 ^ k) hu_ge
  have hm_hi : 3 ^ k * u ≤ 3 ^ k * uMax := Nat.mul_le_mul_left (3 ^ k) hu_le
  omega

theorem checkHenselNode_sound :
    ∀ (t : HenselTree)
      (bExit lo1 hi1 wMax maxExp inv3Max : Nat) (exemptIds : List Nat)
      (mode : Option (Nat × Nat × Nat × Nat))
      (windows steps : List (Nat × Nat))
      (kAcc wAcc gAcc loCur hiCur kFloor n1 : Nat)
      (zCur zExit : Int),
      lo1 ≤ n1 -> n1 ≤ hi1 ->
      (3 ^ wMax * inv3Max) % 2 ^ maxExp = 1 ->
      0 ≤ zCur ->
      loCur ≤ zCur.toNat -> zCur.toNat ≤ hiCur ->
      2 ^ kAcc * (zCur.toNat + 1) = 3 ^ wAcc * (n1 + 1) + gAcc ->
      SpiralWindowedPath bExit windows steps zCur zExit ->
      ModeInvariant bExit mode windows steps zCur zExit kFloor ->
      checkHenselNode bExit lo1 hi1 wMax maxExp inv3Max exemptIds
        mode windows kAcc wAcc gAcc loCur hiCur kFloor t = true ->
      ∃ s ∈ exemptIds, n1 = s
  | .emptyRange, _, _, _, _, _, _, _, mode, _, _, _, _, _, loCur, hiCur, _, _, _, _,
      _, _, _, _, hnCur_lo, hnCur_hi, _, _, _, hok => by
    unfold checkHenselNode at hok
    cases mode with
    | some _ => simp at hok
    | none =>
      simp only [decide_eq_true_eq] at hok
      omega
  | .collapse kMin, bExit, lo1, hi1, wMax, maxExp, inv3Max, exemptIds, mode,
      windows, steps, kAcc, wAcc, gAcc, _loCur, hiCur, kFloor, n1, zCur, zExit,
      hn1_lo, hn1_hi, hinv, hzCur, _hnCur_lo, hnCur_hi, hhensel, hpath, hmode, hok => by
    unfold checkHenselNode at hok
    cases mode with
    | some _ => simp at hok
    | none =>
      simp only [Bool.and_eq_true] at hok
      rcases spiralWindowedPath_first_step_nat hzCur hpath with
        ⟨k, l, nAfter, _stepsRest, hsteps_eq, _hk1, hl1, hnAfter_lo, hstep⟩
      dsimp [ModeInvariant] at hmode
      rw [hsteps_eq] at hmode
      dsimp [firstStepK] at hmode
      have hk_ge := checkKMinFloor_sound kMin kFloor k l hiCur
        (nextWindowFloor bExit windows) zCur.toNat nAfter hmode hl1 hnCur_hi hnAfter_lo hstep hok.1
      rcases spiral_step_odd_quotient_nat k l zCur.toNat nAfter hl1 hstep with ⟨u, _, hu_eq, _⟩
      have hdvd_cur : 2 ^ (kAcc + kMin) ∣ 3 ^ wAcc * (n1 + 1) + gAcc := by
        refine ⟨2 ^ (k - kMin) * u, ?_⟩
        calc
          3 ^ wAcc * (n1 + 1) + gAcc
              = 2 ^ kAcc * (zCur.toNat + 1) := hhensel.symm
          _ = 2 ^ kAcc * (2 ^ k * u) := by rw [hu_eq]
          _ = 2 ^ (kAcc + k) * u := by rw [← Nat.mul_assoc, ← Nat.pow_add]
          _ = 2 ^ ((kAcc + kMin) + (k - kMin)) * u := by
                rw [show kAcc + k = (kAcc + kMin) + (k - kMin) by omega]
          _ = 2 ^ (kAcc + kMin) * (2 ^ (k - kMin) * u) := by rw [Nat.pow_add, Nat.mul_assoc]
      exact checkCongruenceSpan_sound lo1 hi1 wMax maxExp inv3Max exemptIds
        (kAcc + kMin) wAcc gAcc n1 hn1_lo hn1_hi hinv hdvd_cur hok.2
  | .hiLtPow2 kMin, bExit, _, _, _, _, _, _, mode,
      windows, steps, _, _, _, _, hiCur, kFloor, _, zCur, zExit,
      _, _, _, hzCur, _, hnCur_hi, _, hpath, hmode, hok => by
    unfold checkHenselNode at hok
    cases mode with
    | some _ => simp at hok
    | none =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
      rcases spiralWindowedPath_first_step_nat hzCur hpath with
        ⟨k, l, nAfter, _stepsRest, hsteps_eq, _, hl1, hnAfter_lo, hstep⟩
      dsimp [ModeInvariant] at hmode
      rw [hsteps_eq] at hmode
      dsimp [firstStepK] at hmode
      have hk_ge := checkKMinFloor_sound kMin kFloor k l hiCur
        (nextWindowFloor bExit windows) zCur.toNat nAfter hmode hl1 hnCur_hi hnAfter_lo hstep hok.1
      exact False.elim (no_spiral_step_of_hi_lt_pow2 k kMin l hiCur zCur.toNat nAfter
        hk_ge hl1 hnCur_hi hok.2 hstep)
  | .exactK kMin restK, bExit, lo1, hi1, wMax, maxExp, inv3Max, exemptIds, mode,
      windows, steps, kAcc, wAcc, gAcc, loCur, hiCur, kFloor, n1, zCur, zExit,
      hn1_lo, hn1_hi, hinv, hzCur, hnCur_lo, hnCur_hi, hhensel, hpath, hmode, hok => by
    unfold checkHenselNode at hok
    cases mode with
    | some _ => simp at hok
    | none =>
      simp only [Bool.and_eq_true] at hok
      rcases hok with ⟨⟨hkf, hcong⟩, hrest⟩
      rcases spiralWindowedPath_first_step_nat hzCur hpath with
        ⟨k, l, nAfter, _stepsRest, hsteps_eq, _, hl1, hnAfter_lo, hstep⟩
      dsimp [ModeInvariant] at hmode
      rw [hsteps_eq] at hmode
      dsimp [firstStepK] at hmode
      have hk_ge := checkKMinFloor_sound kMin kFloor k l hiCur
        (nextWindowFloor bExit windows) zCur.toNat nAfter hmode hl1 hnCur_hi hnAfter_lo hstep hkf
      by_cases heq : k = kMin
      · subst heq
        rcases exit_step_exact_mod_dvd k l zCur.toNat nAfter hl1 hstep with ⟨Q, hQ⟩
        have hdvd_ex : 2 ^ (kAcc + k + 1) ∣
            3 ^ (wAcc + k) * (n1 + 1) + (3 ^ k * gAcc + 2 ^ (kAcc + k)) := by
          refine ⟨Q, ?_⟩
          have hm := congrArg (fun x => 2 ^ kAcc * x) hQ
          calc
            3 ^ (wAcc + k) * (n1 + 1) + (3 ^ k * gAcc + 2 ^ (kAcc + k))
                = 3 ^ k * (3 ^ wAcc * (n1 + 1) + gAcc) + 2 ^ (kAcc + k) := by
                  rw [Nat.pow_add, Nat.mul_comm (3 ^ wAcc) (3 ^ k), Nat.mul_assoc,
                      ← Nat.add_assoc, ← Nat.mul_add (3 ^ k)]
            _ = 3 ^ k * (2 ^ kAcc * (zCur.toNat + 1)) + 2 ^ kAcc * 2 ^ k := by
                  rw [← hhensel, Nat.pow_add]
            _ = 2 ^ kAcc * (3 ^ k * (zCur.toNat + 1) + 2 ^ k) := by
                  rw [← Nat.mul_assoc, Nat.mul_comm (3 ^ k) (2 ^ kAcc), Nat.mul_assoc,
                      ← Nat.mul_add]
            _ = 2 ^ kAcc * (2 ^ (k + 1) * Q) := hm
            _ = 2 ^ (kAcc + k + 1) * Q := by
                  rw [← Nat.mul_assoc, ← Nat.pow_add, show kAcc + (k + 1) = kAcc + k + 1 by omega]
        exact checkCongruenceSpan_sound lo1 hi1 wMax maxExp inv3Max exemptIds
          (kAcc + k + 1) (wAcc + k) (3 ^ k * gAcc + 2 ^ (kAcc + k)) n1
          hn1_lo hn1_hi hinv hdvd_ex hcong
      · exact checkHenselNode_sound restK bExit lo1 hi1 wMax maxExp inv3Max exemptIds
          none windows steps kAcc wAcc gAcc loCur hiCur (kMin + 1) n1 zCur zExit
          hn1_lo hn1_hi hinv hzCur hnCur_lo hnCur_hi hhensel hpath
          (by dsimp [ModeInvariant]; rw [hsteps_eq]; dsimp [firstStepK]; omega) hrest
  | .skipOddGapK kMin uOdd restK, bExit, lo1, hi1, wMax, maxExp, inv3Max, exemptIds, mode,
      windows, steps, kAcc, wAcc, gAcc, loCur, hiCur, kFloor, n1, zCur, zExit,
      hn1_lo, hn1_hi, hinv, hzCur, hnCur_lo, hnCur_hi, hhensel, hpath, hmode, hok => by
    unfold checkHenselNode at hok
    cases mode with
    | some _ => simp at hok
    | none =>
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
      rcases hok with ⟨⟨⟨⟨hkf, hu_odd⟩, hlo_gt⟩, hhi_lt⟩, hrest⟩
      rcases spiralWindowedPath_first_step_nat hzCur hpath with
        ⟨k, l, nAfter, _stepsRest, hsteps_eq, _, hl1, hnAfter_lo, hstep⟩
      dsimp [ModeInvariant] at hmode
      rw [hsteps_eq] at hmode
      dsimp [firstStepK] at hmode
      have hk_ge := checkKMinFloor_sound kMin kFloor k l hiCur
        (nextWindowFloor bExit windows) zCur.toNat nAfter hmode hl1 hnCur_hi hnAfter_lo hstep hkf
      by_cases heq : k = kMin
      · subst heq
        exact False.elim (no_spiral_step_of_odd_gap k l loCur hiCur uOdd zCur.toNat nAfter
          hl1 hnCur_lo hnCur_hi hu_odd hlo_gt hhi_lt hstep)
      · exact checkHenselNode_sound restK bExit lo1 hi1 wMax maxExp inv3Max exemptIds
          none windows steps kAcc wAcc gAcc loCur hiCur (kMin + 1) n1 zCur zExit
          hn1_lo hn1_hi hinv hzCur hnCur_lo hnCur_hi hhensel hpath
          (by dsimp [ModeInvariant]; rw [hsteps_eq]; dsimp [firstStepK]; omega) hrest
  | .branchK kMin uMin uMax lMin lNode restK, bExit, lo1, hi1, wMax, maxExp, inv3Max, exemptIds,
      mode, windows, _steps, kAcc, wAcc, gAcc, loCur, hiCur, kFloor, n1, zCur, zExit,
      hn1_lo, hn1_hi, hinv, hzCur, hnCur_lo, hnCur_hi, hhensel, hpath, hmode, hok => by
    unfold checkHenselNode at hok
    cases mode with
    | some _ => simp at hok
    | none =>
      cases windows with
      | nil => simp at hok
      | cons wPair winRest =>
        rcases wPair with ⟨wLo, wHi⟩
        simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
        rcases hok with ⟨⟨⟨⟨⟨⟨⟨⟨hkf, huMin_odd⟩, huMin_bd⟩, huMax_odd⟩, huMax_bd⟩,
          _hlMin1⟩, hlMin_bd⟩, hlNode⟩, hrestK⟩
        cases hpath with
        | step _ _ k l _ stepsRest _ zNext _ hk1 hl1 hzNext_lo hzNext_hi hstep_int hpath_rest =>
          have hstep_nat := spiral_int_step_to_nat k l zCur zNext hzCur (by omega) hstep_int
          dsimp [ModeInvariant, firstStepK] at hmode
          have hk_ge := checkKMinFloor_sound kMin kFloor k l hiCur wLo zCur.toNat zNext.toNat
            hmode hl1 hnCur_hi (by omega) hstep_nat hkf
          by_cases heq : k = kMin
          · subst heq
            rcases odd_bounds_ev_range k l loCur hiCur uMin uMax zCur.toNat zNext.toNat
              hl1 hnCur_lo hnCur_hi huMin_odd huMin_bd huMax_odd huMax_bd hstep_nat with
              ⟨hev_lo, hev_hi⟩
            have hl_ge : lMin ≤ l := by
              rcases hlMin_bd with hl1_le | hev_gt
              · omega
              · apply Classical.byContradiction
                intro hlt_l
                have hp : 2 ^ l ≤ 2 ^ (lMin - 1) := pow2_mono_nat (by omega)
                have hm : 2 ^ l * zNext.toNat ≤ 2 ^ (lMin - 1) * wHi :=
                  Nat.mul_le_mul hp (by omega)
                omega
            exact checkHenselNode_sound lNode bExit lo1 hi1 wMax maxExp inv3Max exemptIds
              (some (k, 3 ^ k * uMin - 1, 3 ^ k * uMax - 1, lMin))
              ((wLo, wHi) :: winRest) ((k, l) :: stepsRest)
              kAcc wAcc gAcc loCur hiCur 1 n1 zCur zExit
              hn1_lo hn1_hi hinv hzCur hnCur_lo hnCur_hi hhensel
              (SpiralWindowedPath.step wLo wHi k l winRest stepsRest zCur zNext zExit
                hk1 hl1 hzNext_lo hzNext_hi hstep_int hpath_rest)
              ⟨wLo, wHi, l, winRest, stepsRest, zNext, rfl, rfl, hk1, hl1, hl_ge,
                hzNext_lo, hzNext_hi, hev_lo, hev_hi, hstep_int, hpath_rest⟩
              hlNode
          · exact checkHenselNode_sound restK bExit lo1 hi1 wMax maxExp inv3Max exemptIds
              none ((wLo, wHi) :: winRest) ((k, l) :: stepsRest)
              kAcc wAcc gAcc loCur hiCur (kMin + 1) n1 zCur zExit
              hn1_lo hn1_hi hinv hzCur hnCur_lo hnCur_hi hhensel
              (SpiralWindowedPath.step wLo wHi k l winRest stepsRest zCur zNext zExit
                hk1 hl1 hzNext_lo hzNext_hi hstep_int hpath_rest)
              (by dsimp [ModeInvariant, firstStepK]; omega) hrestK
  | .lDone, _, _, _, _, _, _, _, mode, windows, _, _, _, _, _, _, _, _, _, _,
      _, _, _, _, _, _, _, _, hmode, hok => by
    unfold checkHenselNode at hok
    cases mode with
    | none => simp at hok
    | some mTuple =>
      rcases mTuple with ⟨_, _, evMax, lCur⟩
      cases windows with
      | nil => simp at hok
      | cons wPair _ =>
        rcases wPair with ⟨wLo, _⟩
        simp only [decide_eq_true_eq] at hok
        rcases hmode with ⟨_, _, l, _, _, zNext,
          hwin_eq, _, _, _, hl_ge, hzNext_lo, _, _, hev_hi, _, _⟩
        injection hwin_eq with hwPair _
        injection hwPair with hwLo _
        subst hwLo
        have hp : 2 ^ lCur ≤ 2 ^ l := pow2_mono_nat hl_ge
        have hm : 2 ^ lCur * wLo ≤ 2 ^ l * zNext.toNat := Nat.mul_le_mul hp (by omega)
        omega
  | .lStep child moreL, bExit, lo1, hi1, wMax, maxExp, inv3Max, exemptIds,
      mode, windows, steps, kAcc, wAcc, gAcc, loCur, hiCur, _kFloor, n1, zCur, zExit,
      hn1_lo, hn1_hi, hinv, hzCur, hnCur_lo, hnCur_hi, hhensel, hpath, hmode, hok => by
    unfold checkHenselNode at hok
    cases mode with
    | none => simp at hok
    | some mTuple =>
      rcases mTuple with ⟨kFixed, evMin, evMax, lCur⟩
      cases windows with
      | nil => simp at hok
      | cons wPair winRest =>
        rcases wPair with ⟨wLo, wHi⟩
        simp only [Bool.and_eq_true] at hok
        rcases hok with ⟨hchild, hmore⟩
        rcases hmode with ⟨_wLo', _wHi', l, _winRest', stepsRest, zNext,
          hwin_eq, hsteps_eq, hk1, hl1, hl_ge, hzNext_lo, hzNext_hi, hev_lo, hev_hi,
          hstep_int, hpath_rest⟩
        injection hwin_eq with hwPair hwin_tl
        injection hwPair with hwLo hwHi
        subst hwLo; subst hwHi; subst hwin_tl
        by_cases heq_l : l = lCur
        · subst heq_l
          let P := 2 ^ l
          have hP_pos : P ≥ 1 := pow2_pos_nat l
          have hceil : ceilDiv evMin P ≤ zNext.toNat := ceilDiv_le_of_le_mul (by omega) hev_lo
          have hflr : zNext.toNat ≤ evMax / P := le_div_of_mul_le (by omega) hev_hi
          have hloNext : maxNat wLo (ceilDiv evMin P) ≤ zNext.toNat := by
            dsimp [maxNat]
            by_cases hc : wLo ≤ ceilDiv evMin P <;> simp [hc] <;> omega
          have hhiNext : zNext.toNat ≤ minNat wHi (evMax / P) := by
            dsimp [minNat]
            by_cases hc : wHi ≤ evMax / P <;> simp [hc] <;> omega
          have hstep_nat := spiral_int_step_to_nat kFixed l zCur zNext hzCur (by omega) hstep_int
          have hhensel_next :
              2 ^ (kAcc + kFixed + l) * (zNext.toNat + 1) =
                3 ^ (wAcc + kFixed) * (n1 + 1) +
                (3 ^ kFixed * gAcc + 2 ^ (kAcc + kFixed) * (P - 1)) := by
            calc
              2 ^ (kAcc + kFixed + l) * (zNext.toNat + 1)
                  = 2 ^ kAcc * (2 ^ (kFixed + l) * (zNext.toNat + 1)) := by
                    rw [show kAcc + kFixed + l = kAcc + (kFixed + l) by omega,
                        Nat.pow_add, Nat.mul_assoc]
              _ = 2 ^ kAcc * (3 ^ kFixed * (zCur.toNat + 1) + 2 ^ kFixed * (P - 1)) := by
                    dsimp [P]; rw [hstep_nat]
              _ = 3 ^ kFixed * (2 ^ kAcc * (zCur.toNat + 1)) +
                  2 ^ (kAcc + kFixed) * (P - 1) := by
                    rw [Nat.mul_add, ← Nat.mul_assoc (2 ^ kAcc) (3 ^ kFixed),
                        Nat.mul_comm (2 ^ kAcc) (3 ^ kFixed), Nat.mul_assoc,
                        ← Nat.mul_assoc (2 ^ kAcc) (2 ^ kFixed), ← Nat.pow_add]
              _ = 3 ^ kFixed * (3 ^ wAcc * (n1 + 1) + gAcc) +
                  2 ^ (kAcc + kFixed) * (P - 1) := by rw [hhensel]
              _ = 3 ^ (wAcc + kFixed) * (n1 + 1) +
                  (3 ^ kFixed * gAcc + 2 ^ (kAcc + kFixed) * (P - 1)) := by
                    rw [Nat.mul_add, ← Nat.mul_assoc (3 ^ kFixed) (3 ^ wAcc),
                        Nat.mul_comm (3 ^ kFixed) (3 ^ wAcc), ← Nat.pow_add, Nat.add_assoc]
          rcases spiralWindowedPath_first_step_nat (by omega) hpath_rest with
            ⟨_kN, _, _, _stepsRest2, hs2, hkN1, _, _, _⟩
          exact checkHenselNode_sound child bExit lo1 hi1 wMax maxExp inv3Max exemptIds
            none winRest stepsRest (kAcc + kFixed + l) (wAcc + kFixed)
            (3 ^ kFixed * gAcc + 2 ^ (kAcc + kFixed) * (P - 1))
            (maxNat wLo (ceilDiv evMin P)) (minNat wHi (evMax / P)) 1 n1 zNext zExit
            hn1_lo hn1_hi hinv (by omega) hloNext hhiNext hhensel_next hpath_rest
            (by dsimp [ModeInvariant]; rw [hs2]; dsimp [firstStepK]; exact hkN1) hchild
        · exact checkHenselNode_sound moreL bExit lo1 hi1 wMax maxExp inv3Max exemptIds
            (some (kFixed, evMin, evMax, lCur + 1)) ((wLo, wHi) :: winRest) steps
            kAcc wAcc gAcc loCur hiCur 1 n1 zCur zExit
            hn1_lo hn1_hi hinv hzCur hnCur_lo hnCur_hi hhensel hpath
            ⟨wLo, wHi, l, winRest, stepsRest, zNext, rfl, hsteps_eq, hk1, hl1,
              by omega, hzNext_lo, hzNext_hi, hev_lo, hev_hi, hstep_int, hpath_rest⟩
            hmore

/--
  Theorem 24.3a (Universal Arbitrary-Depth Soundness of `verifyMultiStepHenselBand`):
  For ANY depth `r = windows.length >= 1` (`2`-step, `3`-step, `4`-step, `5`-step, or higher),
  whenever `verifyMultiStepHenselBand windows bExit exemptIds band = true`, ANY integer
  `z1 in [band.lo1, band.hi1]` admitting a valid `(r + 1)`-step windowed spiral trajectory
  `SpiralWindowedPath bExit windows ((band.k1, l1) :: stepsRest) z1 zExit` MUST belong to
  `exemptIds` (so when `exemptIds = []`, NO such trajectory exists; and when `exemptIds`
  consists of certified orbit-drop survivors `<= n0`, `z1` cannot lie on any cycle `> n0`)!
-/
theorem verifyMultiStepHenselBand_sound
    (windows : List (Nat × Nat)) (bExit : Nat) (exemptIds : List Nat)
    (band : MultiStepBandCert)
    (hok : verifyMultiStepHenselBand windows bExit exemptIds band = true)
    (l1 : Nat) (stepsRest : List (Nat × Nat)) (z1 zExit : Int)
    (hz1_lo : (band.lo1 : Int) ≤ z1) (hz1_hi : z1 ≤ (band.hi1 : Int))
    (hpath : SpiralWindowedPath bExit windows ((band.k1, l1) :: stepsRest) z1 zExit) :
    ∃ s ∈ exemptIds, z1 = (s : Int) := by
  unfold verifyMultiStepHenselBand at hok
  cases windows with
  | nil => simp at hok
  | cons wPair winRest =>
    rcases wPair with ⟨wLo, wHi⟩
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
    rcases hok with ⟨⟨⟨⟨⟨⟨⟨⟨⟨_hk1, _hlo_hi⟩, huMin_odd⟩, huMin_bd⟩, huMax_odd⟩, huMax_bd⟩,
      _hl1Min1⟩, hl1Min_bd⟩, hinv⟩, htree⟩
    cases hpath with
    | step _ _ _ _ _ _ _ z2 _ hk1_p hl1_p hz2_lo hz2_hi hstep1_int hpath_rest =>
      let n1 := z1.toNat
      have hz1_nonneg : 0 ≤ z1 := by omega
      have hn1_lo : band.lo1 ≤ n1 := by dsimp [n1]; omega
      have hn1_hi : n1 ≤ band.hi1 := by dsimp [n1]; omega
      have hstep1_nat := spiral_int_step_to_nat band.k1 l1 z1 z2 hz1_nonneg (by omega) hstep1_int
      rcases odd_bounds_ev_range band.k1 l1 band.lo1 band.hi1 band.uMin band.uMax
        n1 z2.toNat hl1_p hn1_lo hn1_hi huMin_odd huMin_bd huMax_odd huMax_bd hstep1_nat with
        ⟨hev_lo, hev_hi⟩
      have hl1_ge : band.l1Min ≤ l1 := by
        rcases hl1Min_bd with hl1_1 | hev_gt
        · omega
        · apply Classical.byContradiction
          intro hlt_l
          have hp : 2 ^ l1 ≤ 2 ^ (band.l1Min - 1) := pow2_mono_nat (by omega)
          have hm : 2 ^ l1 * z2.toNat ≤ 2 ^ (band.l1Min - 1) * wHi :=
            Nat.mul_le_mul hp (by omega)
          omega
      rcases checkHenselNode_sound band.tree bExit band.lo1 band.hi1 band.wMax band.maxExp
        band.inv3Max exemptIds
        (some (band.k1, 3 ^ band.k1 * band.uMin - 1, 3 ^ band.k1 * band.uMax - 1, band.l1Min))
        ((wLo, wHi) :: winRest) ((band.k1, l1) :: stepsRest)
        0 0 0 band.lo1 band.hi1 1 n1 z1 zExit
        hn1_lo hn1_hi hinv hz1_nonneg hn1_lo hn1_hi rfl
        (SpiralWindowedPath.step wLo wHi band.k1 l1 winRest stepsRest z1 z2 zExit
          hk1_p hl1_p hz2_lo hz2_hi hstep1_int hpath_rest)
        ⟨wLo, wHi, l1, winRest, stepsRest, z2, rfl, rfl, hk1_p, hl1_p, hl1_ge,
          hz2_lo, hz2_hi, hev_lo, hev_hi, hstep1_int, hpath_rest⟩
        htree with ⟨s, hs_mem, hn1_eq⟩
      refine ⟨s, hs_mem, ?_⟩
      dsimp [n1] at hn1_eq
      omega

def m93U2B1 : Nat := 169748887054766119338576174538
def m93U2B2 : Nat := 10644319466430191210376801209508200033830663093

/-- Complete active `m = 93, u = 2` (`r = 1`) multi-step Hensel bands (`k1 = 45, 46, 47`) -/
def m93U2Bands : List MultiStepBandCert := [
  ⟨45, 5617500778644913001298, 5617500964544903073340, 159658975, 159658979, 1, 45, 143,
    8901795786296484535763993964369158540297435,
    (.lStep (.collapse 97) .lDone)⟩,
  ⟨46, 5617500800945445543749, 5617500986845436353783, 79829489, 79829489, 1, 46, 145,
    43851964792738303938070148154645048941063241,
    (.lStep (.collapse 96) (.lStep (.collapse 97) .lDone))⟩,
  ⟨47, 5617500815812467238716, 5617501001712458540744, 39914745, 39914745, 1, 47, 143,
    3466948998314123075255523581890835560697539,
    (.lStep (.collapse 95) (.lStep .emptyRange .lDone))⟩
]

def m93U1B1 : Nat := 186580408057834147634799
def m93U1B2 : Nat := 3823138529586028419141319555512320798

/-- Survivor-bearing `m = 93, u = 1, s >= 2, k1 = 45` band (`179507528690102354051071`, 309 steps) -/
def m93U1S2Band45 : MultiStepBandCert :=
  ⟨45, 11235001557289826002597, 186580408057834147634799, 319317951, 5302934143, 1, 45, 148,
    176157384775276158097281881009231869835150555,
    (.lStep (.collapse 35) (.lStep (.collapse 36) (.lStep (.collapse 38) (.lStep (.collapse 40)
    (.lStep (.collapse 41) (.lStep (.collapse 43) (.lStep (.collapse 45) (.lStep (.collapse 46)
    (.lStep (.collapse 48) (.lStep (.collapse 50) (.lStep (.collapse 52) (.lStep (.collapse 53)
    (.lStep (.collapse 55) (.lStep (.collapse 57) (.lStep (.collapse 58) (.lStep (.collapse 60)
    (.lStep (.collapse 62) (.lStep (.collapse 64) (.lStep (.collapse 65) (.lStep (.collapse 67)
    (.lStep (.collapse 69) (.lStep (.collapse 70) (.lStep (.collapse 72) (.lStep (.collapse 74)
    (.lStep (.collapse 76) (.lStep (.collapse 77) .lDone))))))))))))))))))))))))))⟩

def repeatEmptyL : Nat -> HenselTree
  | 0 => .lDone
  | n + 1 => .lStep .emptyRange (repeatEmptyL n)

/-- `m = 93, u = 1, s = 1, k1 = 71` depth-1 (`z1 -> z2 -> z3`) and depth-2 (`z1 -> z2 -> z3 -> z4`) bands -/
def m93U1S1Band71R1 : MultiStepBandCert :=
  ⟨71, 11235001691089488663120, 12773298586383179822095, 5, 5, 1, 71, 87,
    43603680578760566741813283,
    (.lStep (.collapse 15) (repeatEmptyL 36))⟩

def m93U1S1Band71R2 : MultiStepBandCert :=
  ⟨71, 11235001691089488663120, 12773298586383179822095, 5, 5, 1, 73, 90,
    314329863218985131696093643,
    (.lStep
      (.skipOddGapK 1 9386833143724656004933394947821933
        (.branchK 2 4693416571862328002466697473910967 4693416571862328002466697473910967 1
          (.lStep (.collapse 15) (repeatEmptyL 36))
          (.collapse 3)))
      (repeatEmptyL 36))⟩

set_option maxRecDepth 20000 in
/--
  Theorem 24.3b (Zero-Trust-Gap Lean 4 Kernel Proof of Recursive Multi-Step `m = 93` Certificates):
  Certifies inside the Lean 4.35.0 kernel (`by decide`, pure Lean 4 Core):
    (1) All 3 active bands of `m = 93, u = 2` (`r = 1`) with `0` survivors;
    (2) Both `r = 1` (`z1 -> z2 -> z3`) AND genuine `r = 2` (`z1 -> z2 -> z3 -> z4`, 3-step spiral!)
        recursive tree certificates on `m = 93, u = 1, s = 1, k1 = 71`;
    (3) Non-vacuity & exact survivor detection on `m = 93, u = 1, s >= 2, k1 = 45`:
        `verifyMultiStepHenselBand` REJECTS (`= false`) with `exemptIds = []`, ACCEPTS (`= true`)
        with `exemptIds = [179507528690102354051071]`, and certifies `checkSurvivorDrop (2^71)`
        at 309 compressed steps!
-/
theorem m93_multistep_hensel_kernel_verified :
    m93U2Bands.all (verifyMultiStepHenselBand [(m93U2B1 + 1, m93U2B2)] m93U2B2 []) = true ∧
    verifyMultiStepHenselBand [(m93U1B1 + 1, m93U1B2)] m93U1B2 [] m93U1S1Band71R1 = true ∧
    verifyMultiStepHenselBand [(m93U1B1 + 1, m93U1B2), (m93U1B1 + 1, m93U1B2)]
      m93U1B2 [] m93U1S1Band71R2 = true ∧
    verifyMultiStepHenselBand [(m93U1B1 + 1, m93U1B2)] m93U1B2 [] m93U1S2Band45 = false ∧
    verifyMultiStepHenselBand [(m93U1B1 + 1, m93U1B2)] m93U1B2
      [179507528690102354051071] m93U1S2Band45 = true ∧
    checkSurvivorDrop (2 ^ 71) (179507528690102354051071, 309) = true := by
  decide

/--
  The 55 newly discovered arithmetic multi-step Hensel survivors at `m = 95, u = 1, s >= 2`
  (completing all `32 + 55 = 87` distinct arithmetic survivors across `1 <= m <= 95`),
  paired with the exact compressed step count each takes to drop `<= 2^71`.
-/
def henselSurvivors95New55 : List (Nat × Nat) := [
  (59907013082369465778175, 392),
  (60411933919894174695423, 233),
  (71670149792337688788991, 338),
  (73852302447220611727359, 308),
  (89860519623554198667263, 391),
  (90617900879841262043135, 232),
  (104160846239067149434879, 252),
  (107505224688506533183487, 337),
  (107823322797873917370367, 372),
  (110778453670830917591039, 307),
  (114507656073401864290303, 282),
  (119814026164738931556351, 393),
  (119955432058033641881599, 440),
  (120823867839788349390847, 234),
  (122763081810537066004479, 268),
  (124427828405595315109887, 361),
  (125500315877988427104255, 318),
  (128807859955239879704575, 374),
  (132556311293340569987583, 391),
  (132853199061641515038879, 293),
  (134790779435331298000895, 390),
  (135926851319761893064703, 231),
  (136982089588472132141055, 388),
  (139813721821710785708031, 376),
  (141399454168681703014399, 254),
  (143340299584675377577983, 339),
  (145039106777724581355519, 341),
  (146605754261550804238335, 342),
  (147704604894441223454719, 309),
  (148997016003352210481151, 317),
  (149841535372565973827583, 360),
  (154209476375835576369151, 285),
  (156241269358600724152319, 251),
  (156533166824387703287655, 306),
  (157988005008520578596863, 309),
  (161238491446741700734591, 366),
  (161257837032759799775231, 336),
  (161734984196810876055551, 371),
  (166167680506246376386559, 306),
  (166397226865631715917823, 401),
  (168508003970472765861735, 252),
  (170909446401641809550335, 506),
  (171761484110102796435455, 281),
  (176333315357828567793663, 412),
  (177093811385379046399743, 357),
  (179721039247108397334527, 392),
  (179933148087050462822399, 439),
  (181235801759682524086271, 233),
  (181498566091316682293247, 341),
  (182698738749160304189439, 401),
  (183174981928129881079807, 314),
  (183449267168839050199039, 371),
  (183763036408780057112191, 322),
  (184144622715805599006719, 267),
  (184462799697925088739327, 349)
]

set_option maxRecDepth 20000 in
/--
  Theorem 24.3 (Lean 4 Kernel Proof for All 55 New `m = 95, u = 1` Survivors):
  Combined with `all_32_hensel_survivors_drop_below_2_pow_71`, ALL `32 + 55 = 87`
  distinct arithmetic Hensel survivors across `1 <= m <= 95` are certified in the
  Lean 4 kernel (`by decide`) to drop `<= 2^71`!
-/
theorem all_55_new_m95_hensel_survivors_drop_below_2_pow_71 :
    henselSurvivors95New55.length = 55 ∧
    henselSurvivors95New55.all (checkSurvivorDrop (2 ^ 71)) = true := by
  decide

-- ============================================================================
-- 12. Theorem 25 (Attack Line C): One-Equation Sign-Separation, `4^w(v)`
--     Polylogarithmic Horizon Obstruction, & Infinite Parametric Families
-- ============================================================================

theorem collatzStepInt_nonpos (x : Int) (hx : x ≤ 0) : collatzStepInt x ≤ 0 := by
  unfold collatzStepInt
  cases h : (x % 2 == 0) with
  | true =>
    simp
    omega
  | false =>
    have hm : x % 2 ≠ 0 := of_decide_eq_false h
    simp
    omega

theorem collatzIterInt_nonpos : ∀ (k : Nat) (x : Int), x ≤ 0 -> collatzIterInt k x ≤ 0
  | 0, _, hx => hx
  | k + 1, x, hx => collatzIterInt_nonpos k (collatzStepInt x) (collatzStepInt_nonpos x hx)

/--
  Theorem 25.1a (Automatic Sign-Separation of the One-Equation Identity):
  Every integer `x : Int` satisfying `2^|v| = 3^w(v) * x + C(v)` AUTOMATICALLY
  satisfies `x >= 1` (`0` and all negative integers `Z^-` are algebraically excluded).
-/
theorem one_equation_forces_pos (v : List Bool) (x : Int)
    (heq : (2 : Int) ^ v.length = (3 : Int) ^ parityWeight v * x + affineCarryInt v) :
    x ≥ 1 := by
  rcases one_equation_converse_universal v x heq with ⟨_, hi⟩
  apply Classical.byContradiction
  intro hnp
  have hle : x ≤ 0 := by omega
  have hiter_np := collatzIterInt_nonpos v.length x hle
  omega

/--
  Theorem 25.1b (Universal Non-Divisibility of `C(v) - 2^|v|` by `3^w(v)`):
  Whenever `C(v) >= 2^|v|`, `3^w(v)` NEVER divides `C(v) - 2^|v|`.
-/
theorem carry_sub_pow2_not_dvd_pow3 (v : List Bool)
    (hge : affineCarryInt v ≥ (2 : Int) ^ v.length) :
    ¬ ((3 : Int) ^ parityWeight v ∣ (affineCarryInt v - (2 : Int) ^ v.length)) := by
  rintro ⟨m, hm⟩
  have hp3 : (3 : Int) ^ parityWeight v ≥ 1 := pow_pos_int 3 (parityWeight v) (by omega)
  have hm_nonneg : m ≥ 0 := by
    apply Classical.byContradiction
    intro hneg
    have hm_le : m ≤ -1 := by omega
    have hprod_neg : (3 : Int) ^ parityWeight v * m < 0 := by
      have hpos_neg : (3 : Int) ^ parityWeight v * (-m) ≥ (3 : Int) ^ parityWeight v * 1 :=
        Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
      rw [Int.mul_neg] at hpos_neg
      omega
    omega
  have hone : (2 : Int) ^ v.length = (3 : Int) ^ parityWeight v * (-m) + affineCarryInt v := by
    rw [Int.mul_neg]
    omega
  have hpos := one_equation_forces_pos v (-m) hone
  omega

/--
  Theorem 25.2 (Universal `2^|v| <= 4^w(v) * x` Horizon Inequality):
  Every solution `(v, x)` to `2^|v| = 3^w(v) * x + C(v)` satisfies
  `2^|v| <= 4^w(v) * x`, proving that ANY bounded-weight family `w(v) <= W_0`
  has `|v| <= log_2(x) + 2 * W_0` and covers at most `O((log X)^(W_0 + 1))`
  integers `<= X` (natural density `0`, falsifying finite-weight covering systems).
-/
theorem one_equation_pow2_le_pow4_mul : ∀ (v : List Bool) (x : Int),
    (2 : Int) ^ v.length = (3 : Int) ^ parityWeight v * x + affineCarryInt v ->
    (2 : Int) ^ v.length ≤ (4 : Int) ^ parityWeight v * x
  | [], x, heq => by
    simp [parityWeight, affineCarryInt, affineCarryAuxInt] at heq
    simp [parityWeight]
    omega
  | false :: rest, x, heq => by
    have hc : affineCarryInt (false :: rest) = 2 * affineCarryInt rest := by
      unfold affineCarryInt
      simp only [affineCarryAuxInt]
      have h01 : 0 + 1 = 1 := rfl
      rw [h01]
      have hs := affineCarryAuxInt_shift rest 1 0
      omega
    have hp2 : (2 : Int) ^ (false :: rest).length = 2 * (2 : Int) ^ rest.length := by
      simp only [List.length_cons, Int.pow_succ]
      omega
    simp only [parityWeight] at heq ⊢
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
    have hnext : (2 : Int) ^ rest.length =
        (3 : Int) ^ parityWeight rest * collatzStepInt x + affineCarryInt rest := by
      omega
    have ih := one_equation_pow2_le_pow4_mul rest (collatzStepInt x) hnext
    rw [hp2, ← hstep]
    have hrhs : (4 : Int) ^ parityWeight rest * (2 * collatzStepInt x) =
        2 * ((4 : Int) ^ parityWeight rest * collatzStepInt x) := by
      rw [← Int.mul_assoc, Int.mul_comm ((4 : Int) ^ parityWeight rest) 2, Int.mul_assoc]
    rw [hrhs]
    omega
  | true :: rest, x, heq => by
    have hx_pos : x ≥ 1 := one_equation_forces_pos (true :: rest) x heq
    have hc : affineCarryInt (true :: rest) =
        (3 : Int) ^ parityWeight rest + 2 * affineCarryInt rest := by
      unfold affineCarryInt
      simp only [affineCarryAuxInt]
      have h10 : 3 * (0 : Int) + (2 : Int) ^ 0 = 1 := rfl
      have h01 : 0 + 1 = 1 := rfl
      rw [h01, h10]
      have hs := affineCarryAuxInt_shift rest 1 1
      omega
    have hp2 : (2 : Int) ^ (true :: rest).length = 2 * (2 : Int) ^ rest.length := by
      simp only [List.length_cons, Int.pow_succ]
      omega
    have hp3 : (3 : Int) ^ parityWeight (true :: rest) * x + (3 : Int) ^ parityWeight rest =
        (3 : Int) ^ parityWeight rest * (3 * x + 1) := by
      simp only [parityWeight]
      have hpw : 1 + parityWeight rest = parityWeight rest + 1 := by omega
      rw [hpw, Int.pow_succ, Int.mul_add, Int.mul_one, Int.mul_assoc]
    rw [hc, hp2] at heq
    have hcomb : 2 * (2 : Int) ^ rest.length =
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
    have hnext : (2 : Int) ^ rest.length =
        (3 : Int) ^ parityWeight rest * collatzStepInt x + affineCarryInt rest := by
      omega
    have ih := one_equation_pow2_le_pow4_mul rest (collatzStepInt x) hnext
    have hp4_pos : (4 : Int) ^ parityWeight rest ≥ 1 := pow_pos_int 4 (parityWeight rest) (by omega)
    have hp4_nonneg : (4 : Int) ^ parityWeight rest ≥ 0 := by omega
    have hstep_mul : 2 * ((4 : Int) ^ parityWeight rest * collatzStepInt x) =
        (4 : Int) ^ parityWeight rest * (3 * x + 1) := by
      rw [← Int.mul_assoc 2, Int.mul_comm 2 ((4 : Int) ^ parityWeight rest),
          Int.mul_assoc, hstep]
    have h3x1_le_4x : (4 : Int) ^ parityWeight rest * (3 * x + 1) ≤
        (4 : Int) ^ parityWeight rest * (4 * x) :=
      Int.mul_le_mul_of_nonneg_left (by omega) hp4_nonneg
    have hp4_succ : (4 : Int) ^ parityWeight (true :: rest) * x =
        (4 : Int) ^ parityWeight rest * (4 * x) := by
      simp only [parityWeight]
      rw [show 1 + parityWeight rest = parityWeight rest + 1 by omega,
          Int.pow_succ, Int.mul_assoc]
    rw [hp2, hp4_succ]
    omega

theorem parityWeight_replicate_false : ∀ a : Nat, parityWeight (List.replicate a false) = 0
  | 0 => rfl
  | a + 1 => parityWeight_replicate_false a

/-- Theorem 25.3a (Power-of-Two Parametric Family `n = 2^a`, `v = 0^a`) -/
theorem one_equation_pow2_family (a : Nat) :
    let v := List.replicate a false
    (2 : Int) ^ v.length = (3 : Int) ^ parityWeight v * (2 : Int) ^ a + affineCarryInt v := by
  dsimp only
  rw [List.length_replicate, parityWeight_replicate_false]
  have hc : affineCarryInt (List.replicate a false) = 0 := replicate_false_carry_preserve a 0 0
  rw [hc]
  simp

/-- Theorem 25.3b (Even Doubling Closure `x -> 2*x`, `v -> 0 :: v`) -/
theorem one_equation_even_double_closure (v : List Bool) (x : Int)
    (heq : (2 : Int) ^ v.length = (3 : Int) ^ parityWeight v * x + affineCarryInt v) :
    (2 : Int) ^ (false :: v).length =
      (3 : Int) ^ parityWeight (false :: v) * (2 * x) + affineCarryInt (false :: v) := by
  have hc : affineCarryInt (false :: v) = 2 * affineCarryInt v := by
    unfold affineCarryInt
    simp only [affineCarryAuxInt]
    have h01 : 0 + 1 = 1 := rfl
    rw [h01]
    have hs := affineCarryAuxInt_shift v 1 0
    omega
  have hp2 : (2 : Int) ^ (false :: v).length = 2 * (2 : Int) ^ v.length := by
    simp only [List.length_cons, Int.pow_succ]
    omega
  simp only [parityWeight]
  rw [hc, hp2]
  have hmul : (3 : Int) ^ parityWeight v * (2 * x) =
      2 * ((3 : Int) ^ parityWeight v * x) := by
    rw [← Int.mul_assoc, Int.mul_comm ((3 : Int) ^ parityWeight v) 2, Int.mul_assoc]
  rw [hmul]
  omega

/--
  Theorem 25.3c (Odd Predecessor Lift `(3*m + 2) -> (2*m + 1)`, `v -> 1 :: v`):
  Whenever `3*m + 2` solves the One-Equation identity with `v`, its odd predecessor
  `2*m + 1` solves the One-Equation identity with `true :: v` (note `m = 3*r` has NO
  odd predecessor in `Z`, manifesting the 3-adic Garden-of-Eden branching obstruction).
-/
theorem one_equation_odd_predecessor_lift (v : List Bool) (m : Int)
    (heq : (2 : Int) ^ v.length = (3 : Int) ^ parityWeight v * (3 * m + 2) + affineCarryInt v) :
    (2 : Int) ^ (true :: v).length =
      (3 : Int) ^ parityWeight (true :: v) * (2 * m + 1) + affineCarryInt (true :: v) := by
  have hc : affineCarryInt (true :: v) =
      (3 : Int) ^ parityWeight v + 2 * affineCarryInt v := by
    unfold affineCarryInt
    simp only [affineCarryAuxInt]
    have h10 : 3 * (0 : Int) + (2 : Int) ^ 0 = 1 := rfl
    have h01 : 0 + 1 = 1 := rfl
    rw [h01, h10]
    have hs := affineCarryAuxInt_shift v 1 1
    omega
  have hp2 : (2 : Int) ^ (true :: v).length = 2 * (2 : Int) ^ v.length := by
    simp only [List.length_cons, Int.pow_succ]
    omega
  have hp3 : (3 : Int) ^ parityWeight (true :: v) * (2 * m + 1) + (3 : Int) ^ parityWeight v =
      2 * ((3 : Int) ^ parityWeight v * (3 * m + 2)) := by
    simp only [parityWeight]
    have hpw : 1 + parityWeight v = parityWeight v + 1 := by omega
    rw [hpw, Int.pow_succ]
    calc
      (3 : Int) ^ parityWeight v * 3 * (2 * m + 1) + (3 : Int) ^ parityWeight v
          = (3 : Int) ^ parityWeight v * (3 * (2 * m + 1)) + (3 : Int) ^ parityWeight v * 1 := by
            rw [Int.mul_assoc, Int.mul_one]
      _ = (3 : Int) ^ parityWeight v * (3 * (2 * m + 1) + 1) := by
            rw [← Int.mul_add]
      _ = (3 : Int) ^ parityWeight v * (2 * (3 * m + 2)) := by
            have hlin : 3 * (2 * m + 1) + 1 = 2 * (3 * m + 2) := by omega
            rw [hlin]
      _ = 2 * ((3 : Int) ^ parityWeight v * (3 * m + 2)) := by
            rw [← Int.mul_assoc, Int.mul_comm ((3 : Int) ^ parityWeight v) 2, Int.mul_assoc]
  rw [hc, hp2]
  omega

/-- Odd geometric predecessor sequence `g_0 = 0`, `g_{d+1} = 4 * g_d + 1 = (4^{d+1} - 1) / 3` -/
def geomOddSeq : Nat -> Nat
  | 0 => 0
  | d + 1 => 4 * geomOddSeq d + 1

theorem three_mul_geomOddSeq_add_one : ∀ d : Nat, 3 * geomOddSeq d + 1 = 2 ^ (2 * d)
  | 0 => rfl
  | d + 1 => by
    have ih := three_mul_geomOddSeq_add_one d
    simp only [geomOddSeq]
    have hp : 2 ^ (2 * (d + 1)) = 4 * 2 ^ (2 * d) := by
      have heq : 2 * (d + 1) = (2 * d) + 2 := by omega
      rw [heq, Nat.pow_succ, Nat.pow_succ]
      omega
    rw [hp]
    omega

/--
  Theorem 25.3d (Infinite Weight-1 Geometric Family `g_{d+1} = (4^(d+1) - 1) / 3`):
  For every `d : Nat`, `v = true :: replicate (2*d + 1) false` (`|v| = 2*d + 2, w(v) = 1`)
  solves `2^(2*d + 2) = 3^1 * g_{d+1} + C(v)` unconditionally!
-/
theorem one_equation_geometric_family (d : Nat) :
    let v := true :: List.replicate (2 * d + 1) false
    (2 : Int) ^ v.length =
      (3 : Int) ^ parityWeight v * (geomOddSeq (d + 1) : Int) + affineCarryInt v := by
  dsimp only
  have hlen : (true :: List.replicate (2 * d + 1) false).length = 2 * (d + 1) := by
    simp [List.length_replicate]
    omega
  have hwt : parityWeight (true :: List.replicate (2 * d + 1) false) = 1 := by
    simp [parityWeight, parityWeight_replicate_false]
  have hc : affineCarryInt (true :: List.replicate (2 * d + 1) false) = 1 := by
    unfold affineCarryInt
    simp only [affineCarryAuxInt]
    have h10 : 3 * (0 : Int) + (2 : Int) ^ 0 = 1 := rfl
    have h01 : 0 + 1 = 1 := rfl
    rw [h01, h10, replicate_false_carry_preserve (2 * d + 1) 1 1]
  rw [hlen, hwt, hc]
  have hp31 : (3 : Int) ^ 1 = 3 := rfl
  rw [hp31]
  have hid := three_mul_geomOddSeq_add_one (d + 1)
  have hcast : ((3 * geomOddSeq (d + 1) + 1 : Nat) : Int) = ((2 ^ (2 * (d + 1)) : Nat) : Int) :=
    congrArg Int.ofNat hid
  rw [natCast_add, natCast_mul, natCast_pow2] at hcast
  omega


theorem even_run_iter : ∀ (a m : Nat), collatzIter a (2 ^ a * m) = m
  | 0, m => by simp [collatzIter]
  | a + 1, m => by
    have hmul : 2 ^ (a + 1) * m = 2 * (2 ^ a * m) := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ a) 2, Nat.mul_assoc]
    have hev : ((2 ^ (a + 1) * m) % 2 == 0) = true := decide_eq_true (by rw [hmul]; omega)
    have hstep : collatzStep (2 ^ (a + 1) * m) = 2 ^ a * m := by
      simp only [collatzStep, hev]; simp; omega
    simp only [collatzIter, hstep]
    exact even_run_iter a m

theorem syracuse_block_iter (x xNext w a u : Nat)
    (hu : u ≥ 1) (hx : x + 1 = 2 ^ w * u) (ha : 3 ^ w * u - 1 = 2 ^ a * xNext) :
    collatzIter (w + a) x = xNext := by
  have hx_eq : x = 2 ^ w * u - 1 := by omega
  rw [collatzIter_add w a x, hx_eq, odd_run_iter w u hu, ha, even_run_iter a xNext]

theorem subdouble_entry_block_merger (x xNext w a u : Nat)
    (hw : w ≥ 2) (ha_ge : a ≥ 2) (hu : u ≥ 1)
    (hx : x + 1 = 2 ^ w * u) (ha : 3 ^ w * u - 1 = 2 ^ a * xNext) :
    let nPrime := (x - 1) / 2
    collatzIter ((w - 1) + (a - 2) + 2) nPrime = xNext := by
  dsimp only
  have hp2w1 : 2 ^ (w - 1) ≥ 1 := pow2_pos_nat (w - 1)
  have h2w : 2 ^ w * u = 2 * (2 ^ (w - 1) * u) := by
    conv => lhs; rw [show w = (w - 1) + 1 by omega]
    rw [Nat.pow_succ, Nat.mul_comm (2 ^ (w - 1)) 2, Nat.mul_assoc]
  have hnp : (x - 1) / 2 = 2 ^ (w - 1) * u - 1 := by
    have : 2 ^ (w - 1) * u ≥ 1 := Nat.mul_pos hp2w1 hu
    omega
  let y := 3 ^ (w - 1) * u - 1
  have hy_pos : 3 ^ (w - 1) * u ≥ 1 := Nat.mul_pos (pow3_pos_nat (w - 1)) hu
  have h3w : 3 ^ w * u = 3 * (3 ^ (w - 1) * u) := by
    conv => lhs; rw [show w = (w - 1) + 1 by omega]
    rw [Nat.pow_succ, Nat.mul_comm (3 ^ (w - 1)) 3, Nat.mul_assoc]
  have hp2a2 : 2 ^ (a - 2) ≥ 1 := pow2_pos_nat (a - 2)
  have h2a : 2 ^ a * xNext = 4 * (2 ^ (a - 2) * xNext) := by
    conv => lhs; rw [show a = (a - 2) + 2 by omega]
    rw [Nat.pow_add, show 2 ^ 2 = 4 from rfl, Nat.mul_comm (2 ^ (a - 2)) 4, Nat.mul_assoc]
  have hy_mod4 : (3 * y + 2) % 4 = 0 := by dsimp [y]; omega
  have hy_even : (y % 2 == 0) = true := decide_eq_true (by omega)
  have hy2_odd : (((y / 2) % 2) == 0) = false := decide_eq_true (by omega) |> fun _ => by
    exact decide_eq_false (by omega)
  have hs1 : collatzStep y = y / 2 := by simp only [collatzStep, hy_even]; simp
  have hs2 : collatzStep (y / 2) = 2 ^ (a - 2) * xNext := by
    simp only [collatzStep, hy2_odd]; simp; dsimp [y]; omega
  have h2steps : collatzIter 2 y = 2 ^ (a - 2) * xNext := by
    simp only [collatzIter, hs1, hs2]
  rw [show (w - 1) + (a - 2) + 2 = (w - 1) + (2 + (a - 2)) by omega]
  rw [collatzIter_add (w - 1) (2 + (a - 2)), hnp, odd_run_iter (w - 1) u hu]
  change collatzIter (2 + (a - 2)) y = xNext
  rw [collatzIter_add 2 (a - 2) y, h2steps, even_run_iter (a - 2) xNext]

end CollatzFormal
