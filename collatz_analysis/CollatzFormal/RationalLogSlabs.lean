/-
  CollatzFormal/RationalLogSlabs.lean
  Section 13A: Pure-Nat Rational Taylor Bounds on ln 2 & ln 3, 52 CF Convergents,
  Zero-Sorting Forward Scan, Telescoping Inverse-Bernoulli Verifier, 9 Convergent Slabs,
  and Zero-Trust-Gap Kernel Cycle Elimination Bridges.
-/

import CollatzFormal.Core

namespace CollatzFormal

-- ============================================================================
-- SECTION 13: Zero-Trust-Gap End-to-End Lean 4 Cycle Elimination Pipeline
-- ============================================================================

-- 13.1 Explicit Hypotheses & Spiral Cycle Dynamics (Theorem 26.1)

/-- Explicit hypothesis that all `1 <= n <= n0` reach `1` under `collatzIter` (Barina 2025: `n0 = 2^71`). -/
def BarinaThreshold (n0 : Nat) : Prop :=
  ∀ n : Nat, 1 ≤ n -> n ≤ n0 -> ∃ k : Nat, collatzIter k n = 1

/-- Binary floor logarithm `floor(log_2 n)` in pure Lean 4 Core. -/
def flog2 (n : Nat) : Nat :=
  if n < 2 then 0 else 1 + flog2 (n / 2)
termination_by n

theorem mul_div_le_nat (a b : Nat) : b * (a / b) ≤ a := by
  rw [Nat.mul_comm]
  exact Nat.div_mul_le_self a b

theorem one_pow_nat : ∀ n : Nat, 1 ^ n = 1
  | 0 => rfl
  | n + 1 => by rw [Nat.pow_succ, one_pow_nat n]

theorem pow_pos_nat : ∀ (b n : Nat), b ≥ 1 -> b ^ n ≥ 1
  | _, 0, _ => by simp
  | b, n + 1, hb => by rw [Nat.pow_succ]; exact Nat.mul_pos (pow_pos_nat b n hb) hb

theorem pow_lt_pow_pos_nat {a b : Nat} (ha : a ≥ 1) (hab : a < b) :
    ∀ m : Nat, m ≥ 1 -> a ^ m < b ^ m
  | 0, hm => by omega
  | 1, _ => by simpa using hab
  | m + 2, _ => by
    have ih := pow_lt_pow_pos_nat ha hab (m + 1) (by omega)
    rw [Nat.pow_succ a (m + 1), Nat.pow_succ b (m + 1)]
    exact Nat.lt_trans (Nat.mul_lt_mul_of_pos_right ih ha)
      (Nat.mul_lt_mul_of_pos_left hab (pow_pos_nat b (m + 1) (by omega)))

theorem flog2_spec (n : Nat) : n ≥ 1 -> 2 ^ flog2 n ≤ n ∧ n < 2 ^ (flog2 n + 1) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn
    unfold flog2
    by_cases h2 : n < 2
    · simp [h2]; omega
    · simp only [h2, ↓reduceIte]
      rcases ih (n / 2) (by omega) (by omega) with ⟨hlo, hhi⟩
      have he1 : 1 + flog2 (n / 2) = flog2 (n / 2) + 1 := by omega
      rw [he1, Nat.pow_succ 2 (flog2 (n / 2)), Nat.pow_succ 2 (flog2 (n / 2) + 1)]
      omega

theorem flog2_one : flog2 1 = 0 := by
  unfold flog2
  simp

theorem flog2_unique {n k : Nat} (hlo : 2 ^ k ≤ n) (hhi : n < 2 ^ (k + 1)) :
    flog2 n = k := by
  have hp : 2 ^ k ≥ 1 := pow2_pos_nat k
  rcases flog2_spec n (by omega) with ⟨f_lo, f_hi⟩
  by_cases hlt : flog2 n < k
  · have hm : 2 ^ (flog2 n + 1) ≤ 2 ^ k := pow2_mono_nat (by omega)
    omega
  · by_cases hgt : k < flog2 n
    · have hm : 2 ^ (k + 1) ≤ 2 ^ flog2 n := pow2_mono_nat (by omega)
      omega
    · omega

theorem flog2_mono {a b : Nat} (ha : a ≥ 1) (hle : a ≤ b) : flog2 a ≤ flog2 b := by
  rcases flog2_spec a ha with ⟨ha_lo, _⟩
  rcases flog2_spec b (by omega) with ⟨_, hb_hi⟩
  apply Classical.byContradiction
  intro hgt
  have hm : 2 ^ (flog2 b + 1) ≤ 2 ^ flog2 a := pow2_mono_nat (by omega)
  omega

theorem flog2_mul_pow2 (m X : Nat) (hX : X ≥ 1) : flog2 (2 ^ m * X) = m + flog2 X := by
  rcases flog2_spec X hX with ⟨hlo, hhi⟩
  apply flog2_unique
  · rw [Nat.pow_add]
    exact Nat.mul_le_mul_left (2 ^ m) hlo
  · rw [show m + flog2 X + 1 = m + (flog2 X + 1) by omega, Nat.pow_add]
    exact Nat.mul_lt_mul_of_pos_left hhi (pow2_pos_nat m)

/--
  Effective Laurent-Mignotte-Nesterenko (1995, Corollaire 2) linear-forms-in-two-logarithms
  power bound in pure `Nat` arithmetic: for all `W >= 2` with `3^W < 2^K`,
    `2^(12000 + 14 * (flog2 W + 3)^2) * (2^K - 3^W) > 3^W`.
-/
def BakerLMNPowerBound : Prop :=
  ∀ K W : Nat, W ≥ 2 -> 3 ^ W < 2 ^ K ->
    2 ^ (12000 + 14 * (flog2 W + 3) ^ 2) * (2 ^ K - 3 ^ W) > 3 ^ W

/-- Single spiral-block transition data `(x, k, l)` where `x` is a local odd minimum. -/
structure SpiralStepData where
  x : Nat
  k : Nat
  l : Nat
deriving DecidableEq, Repr

/-- Exact spiral-block transition `s.x -> xNext` in pure `Nat` arithmetic. -/
def ValidSpiralStep (s : SpiralStepData) (xNext : Nat) : Prop :=
  s.x % 2 = 1 ∧ s.x ≥ 1 ∧ xNext % 2 = 1 ∧ xNext ≥ 1 ∧
  s.k ≥ 1 ∧ s.l ≥ 1 ∧
  2 ^ (s.k + s.l) * (xNext + 1) = 3 ^ s.k * (s.x + 1) + 2 ^ s.k * (2 ^ s.l - 1)

def ValidSpiralChain : List SpiralStepData -> Nat -> Prop
  | [], _ => True
  | [s], xEnd => ValidSpiralStep s xEnd
  | s1 :: s2 :: rest, xEnd => ValidSpiralStep s1 s2.x ∧ ValidSpiralChain (s2 :: rest) xEnd

def spiralChainTotalK : List SpiralStepData -> Nat
  | [] => 0
  | s :: rest => (s.k + s.l) + spiralChainTotalK rest

def spiralChainTotalW : List SpiralStepData -> Nat
  | [] => 0
  | s :: rest => s.k + spiralChainTotalW rest

def spiralVertices (steps : List SpiralStepData) : List Nat :=
  steps.map (fun s => s.x)

/-- Non-trivial closed `m`-block positive spiral cycle (`m >= 1` and some vertex `> 1`). -/
def IsNontrivialSpiralCycle (steps : List SpiralStepData) : Prop :=
  match steps with
  | [] => False
  | s0 :: rest =>
    ValidSpiralChain (s0 :: rest) s0.x ∧ ∃ s ∈ (s0 :: rest), s.x > 1


theorem collatzIter_one_two : ∀ k : Nat,
    (collatzIter k 1 = 1 ∨ collatzIter k 1 = 2) ∧
    (collatzIter k 2 = 1 ∨ collatzIter k 2 = 2)
  | 0 => ⟨Or.inl rfl, Or.inr rfl⟩
  | k + 1 => by
    rcases collatzIter_one_two k with ⟨h1, h2⟩
    have hs1 : collatzStep 1 = 2 := rfl
    have hs2 : collatzStep 2 = 1 := rfl
    exact ⟨by simpa [collatzIter, hs1] using h2, by simpa [collatzIter, hs2] using h1⟩

theorem collatzIter_period_mul : ∀ (q T x : Nat),
    collatzIter T x = x -> collatzIter (q * T) x = x
  | 0, T, _, _ => by rw [Nat.zero_mul]; rfl
  | q + 1, T, x, hT => by
    rw [Nat.add_mul, Nat.one_mul, Nat.add_comm (q * T) T, collatzIter_add T (q * T) x, hT]
    exact collatzIter_period_mul q T x hT

theorem periodic_odd_not_reaching_one {x T : Nat}
    (hx_odd : x % 2 = 1) (hx_gt1 : x > 1) (hT : T ≥ 1)
    (hper : collatzIter T x = x) :
    ∀ d : Nat, collatzIter d x ≠ 1 := by
  intro d hd
  have hge : (d + 1) * T ≥ d + 1 := by
    have hm := Nat.mul_le_mul_left (d + 1) hT
    simpa using hm
  have hsplit : (d + 1) * T = d + ((d + 1) * T - d) := by omega
  have hloop := collatzIter_period_mul (d + 1) T x hper
  rw [hsplit, collatzIter_add d ((d + 1) * T - d) x, hd] at hloop
  rcases (collatzIter_one_two ((d + 1) * T - d)).1 with h1 | h2
  · omega
  · omega

theorem validSpiralStep_collatzIter {s : SpiralStepData} {xNext : Nat}
    (hv : ValidSpiralStep s xNext) :
    collatzIter (s.k + s.l) s.x = xNext := by
  rcases hv with ⟨_, _, _, _, _, hl, hstep⟩
  rcases spiral_step_odd_quotient_nat s.k s.l s.x xNext hl hstep with ⟨u, hu_mod, hx_eq, ha_eq⟩
  exact syracuse_block_iter s.x xNext s.k s.l u (by omega) hx_eq (by omega)

theorem validSpiralChain_collatzIter :
    ∀ (s0 : SpiralStepData) (rest : List SpiralStepData) (xEnd : Nat),
      ValidSpiralChain (s0 :: rest) xEnd ->
      collatzIter (spiralChainTotalK (s0 :: rest)) s0.x = xEnd
  | s0, [], xEnd, hv => by
    simp only [spiralChainTotalK, Nat.add_zero]
    exact validSpiralStep_collatzIter hv
  | s0, s1 :: tl, xEnd, ⟨hs0, hrest⟩ => by
    change collatzIter ((s0.k + s0.l) + spiralChainTotalK (s1 :: tl)) s0.x = xEnd
    rw [collatzIter_add (s0.k + s0.l) (spiralChainTotalK (s1 :: tl)) s0.x,
        validSpiralStep_collatzIter hs0]
    exact validSpiralChain_collatzIter s1 tl xEnd hrest

theorem validSpiralChain_reach_mem :
    ∀ (s0 : SpiralStepData) (rest : List SpiralStepData) (xEnd : Nat) (s : SpiralStepData),
      ValidSpiralChain (s0 :: rest) xEnd -> s ∈ (s0 :: rest) ->
      (s.x % 2 = 1 ∧ s.x ≥ 1 ∧ s.k ≥ 1 ∧ s.l ≥ 1) ∧
      ∃ t1 t2 : Nat, t1 + t2 = spiralChainTotalK (s0 :: rest) ∧
        collatzIter t1 s0.x = s.x ∧ collatzIter t2 s.x = xEnd
  | s0, [], xEnd, s, hv, hm => by
    simp at hm; subst hm
    rcases hv with ⟨hodd, hge, _, _, hk, hl, hst⟩
    refine ⟨⟨hodd, hge, hk, hl⟩, 0, s.k + s.l, ?_, rfl, ?_⟩
    · simp [spiralChainTotalK]
    · exact validSpiralStep_collatzIter ⟨hodd, hge, by omega, by omega, hk, hl, hst⟩
  | s0, s1 :: tl, xEnd, s, ⟨hs0, hrest⟩, hm => by
    cases hm with
    | head _ =>
      rcases hs0 with ⟨hodd, hge, hodd1, hge1, hk, hl, hst⟩
      refine ⟨⟨hodd, hge, hk, hl⟩, 0, spiralChainTotalK (s0 :: s1 :: tl), by simp, rfl, ?_⟩
      exact validSpiralChain_collatzIter s0 (s1 :: tl) xEnd ⟨⟨hodd, hge, hodd1, hge1, hk, hl, hst⟩, hrest⟩
    | tail _ hmem =>
      rcases validSpiralChain_reach_mem s1 tl xEnd s hrest hmem with
        ⟨hprops, t1, t2, hsum, ht1, ht2⟩
      refine ⟨hprops, (s0.k + s0.l) + t1, t2, ?_, ?_, ht2⟩
      · change (s0.k + s0.l + t1) + t2 = (s0.k + s0.l) + spiralChainTotalK (s1 :: tl); omega
      · rw [collatzIter_add (s0.k + s0.l) t1 s0.x, validSpiralStep_collatzIter hs0, ht1]

theorem nontrivial_cycle_vertex_periodic {steps : List SpiralStepData}
    (hcyc : IsNontrivialSpiralCycle steps) :
    ∀ s ∈ steps, s.x % 2 = 1 ∧ s.x > 1 ∧ s.k ≥ 1 ∧ s.l ≥ 1 ∧
      collatzIter (spiralChainTotalK steps) s.x = s.x ∧ spiralChainTotalK steps ≥ 2 ∧
      (∀ d : Nat, collatzIter d s.x ≠ 1) := by
  cases steps with
  | nil => cases hcyc
  | cons s0 rest =>
    rcases hcyc with ⟨hchain, sWit, hWitMem, hWitGt1⟩
    rcases validSpiralChain_reach_mem s0 rest s0.x s0 hchain (List.Mem.head _) with
      ⟨⟨_, _, hs0_k, hs0_l⟩, _⟩
    rcases validSpiralChain_reach_mem s0 rest s0.x sWit hchain hWitMem with
      ⟨⟨hw_odd, _, hw_k, hw_l⟩, tw1, tw2, hw_sum, htw1, htw2⟩
    have hK_ge2 : spiralChainTotalK (s0 :: rest) ≥ 2 := by
      unfold spiralChainTotalK; omega
    have hper_wit : collatzIter (spiralChainTotalK (s0 :: rest)) sWit.x = sWit.x := by
      rw [← hw_sum, Nat.add_comm tw1 tw2, collatzIter_add tw2 tw1 sWit.x, htw2, htw1]
    have hwit_not1 := periodic_odd_not_reaching_one hw_odd hWitGt1 (by omega) hper_wit
    intro s hsMem
    rcases validSpiralChain_reach_mem s0 rest s0.x s hchain hsMem with
      ⟨⟨hs_odd, hs_ge1, hs_k, hs_l⟩, ts1, ts2, hs_sum, hts1, hts2⟩
    have hper_s : collatzIter (spiralChainTotalK (s0 :: rest)) s.x = s.x := by
      rw [← hs_sum, Nat.add_comm ts1 ts2, collatzIter_add ts2 ts1 s.x, hts2, hts1]
    have hs_not1 : ∀ d : Nat, collatzIter d s.x ≠ 1 := by
      intro d hd
      -- sWit reaches s0 in tw2 steps, s0 reaches s in ts1 steps, s reaches 1 in d steps!
      have hw_reaches_1 : collatzIter (tw2 + (ts1 + d)) sWit.x = 1 := by
        rw [collatzIter_add tw2 (ts1 + d) sWit.x, htw2,
            collatzIter_add ts1 d s0.x, hts1, hd]
      exact hwit_not1 (tw2 + (ts1 + d)) hw_reaches_1
    have hs_gt1 : s.x > 1 := by
      by_cases h1 : s.x = 1
      · exfalso; exact hs_not1 0 (by simpa [collatzIter] using h1)
      · omega
    exact ⟨hs_odd, hs_gt1, hs_k, hs_l, hper_s, hK_ge2, hs_not1⟩

/-- Every vertex of a non-trivial spiral cycle strictly exceeds any Barina threshold `n0`. -/
theorem nontrivial_cycle_vertex_floor {steps : List SpiralStepData} {n0 : Nat}
    (hbar : BarinaThreshold n0)
    (hcyc : IsNontrivialSpiralCycle steps) :
    ∀ s ∈ steps, s.x ≥ n0 + 1 := by
  intro s hs
  rcases nontrivial_cycle_vertex_periodic hcyc s hs with ⟨_, hs_gt1, _, _, _, _, hs_not1⟩
  apply Classical.byContradiction
  intro hle
  rcases hbar s.x (by omega) (by omega) with ⟨d, hd⟩
  exact hs_not1 d hd

/-- Kernel-certified `checkSurvivorDrop` excludes `z` from every non-trivial spiral cycle! -/
theorem checkSurvivorDrop_excludes_nontrivial_cycle {steps : List SpiralStepData} {n0 z kDrop : Nat}
    (hbar : BarinaThreshold n0)
    (hdrop : checkSurvivorDrop n0 (z, kDrop) = true)
    (hcyc : IsNontrivialSpiralCycle steps) :
    ∀ s ∈ steps, s.x ≠ z := by
  unfold checkSurvivorDrop at hdrop
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hdrop
  intro s hs heq
  rcases nontrivial_cycle_vertex_periodic hcyc s hs with ⟨_, hs_gt1, _, _, _, _, hs_not1⟩
  rw [heq] at hs_not1 hs_gt1
  have hpos : collatzIter kDrop z ≥ 1 := collatzIter_pos kDrop z (by omega)
  rcases hbar (collatzIter kDrop z) hpos hdrop.2 with ⟨d, hd⟩
  exact hs_not1 (kDrop + d) (by rw [collatzIter_add kDrop d z, hd])

/--
  Theorem 26.1b (Hercher Entry Collatz-Merger Floor for ALL `s.k >= 1`):
  Under `BarinaThreshold n0` (`n0 >= 4`), every step `(s, xNext)` with `s.l >= 2` on a
  non-trivial cycle satisfies `s.x >= 2 * n0 + 3` (`s.k = 1` gives `s.x >= 4 * n0 + 5`,
  and `s.k >= 2` gives `s.x >= 2 * n0 + 3`).
-/
theorem nontrivial_cycle_merger_floor {s : SpiralStepData} {xNext n0 : Nat}
    (hbar : BarinaThreshold n0) (hn0 : n0 ≥ 4)
    (hstep : ValidSpiralStep s xNext) (hl2 : s.l ≥ 2)
    (hs_floor : s.x ≥ n0 + 1)
    (hnext_not1 : ∀ d : Nat, collatzIter d xNext ≠ 1) :
    s.x ≥ 2 * n0 + 3 := by
  have helper_no_merge : ∀ (nPrime M : Nat),
      1 ≤ nPrime -> nPrime ≤ n0 -> collatzIter M nPrime = xNext -> False := by
    intro nPrime M hnp1 hnp_le hmerge
    rcases hbar nPrime hnp1 hnp_le with ⟨d, hd⟩
    by_cases hMd : M ≤ d
    · have hsplit : d = M + (d - M) := by omega
      rw [hsplit, collatzIter_add M (d - M) nPrime, hmerge] at hd
      exact hnext_not1 (d - M) hd
    · have hsplit : M = d + (M - d) := by omega
      rw [hsplit, collatzIter_add d (M - d) nPrime, hd] at hmerge
      rcases (collatzIter_one_two (M - d)).1 with h1 | h2
      · exact hnext_not1 0 (by simpa [collatzIter] using hmerge.symm.trans h1)
      · rcases hstep with ⟨_, _, hxN_odd, _, _, _, _⟩
        omega
  rcases hstep with ⟨hs_odd, hs_ge1, hxN_odd, hxN_ge1, hk1, hl1, heq⟩
  rcases spiral_step_odd_quotient_nat s.k s.l s.x xNext hl1 heq with ⟨u, hu_odd, hx_u, ha_u⟩
  by_cases hk_eq1 : s.k = 1
  · -- Case s.k = 1, s.l >= 2: u % 4 = 3, s.x = 8 * t + 5, nPrime = 2 * t + 1 merges!
    have hp2l : 2 ^ s.l = 4 * 2 ^ (s.l - 2) := by
      conv => lhs; rw [show s.l = (s.l - 2) + 2 by omega]
      rw [Nat.pow_add, show 2 ^ 2 = 4 from rfl, Nat.mul_comm]
    have h3u : 3 * u = 4 * (2 ^ (s.l - 2) * xNext) + 1 := by
      rw [hk_eq1, Nat.pow_one] at ha_u; rw [hp2l, Nat.mul_assoc] at ha_u; omega
    have hu_mod4 : u % 4 = 3 := by omega
    let t := u / 4
    have hu_t : u = 4 * t + 3 := by dsimp [t]; omega
    have hsx_t : s.x = 8 * t + 5 := by rw [hk_eq1, Nat.pow_one, hu_t] at hx_u; omega
    let nPrime := 2 * t + 1
    have hnp_step : collatzStep nPrime = 2 ^ (s.l - 2) * xNext := by
      have hodd_np : (nPrime % 2 == 0) = false := decide_eq_false (by dsimp [nPrime]; omega)
      simp only [collatzStep, hodd_np]; simp; dsimp [nPrime]; omega
    have hmerge1 : collatzIter (1 + (s.l - 2)) nPrime = xNext := by
      rw [collatzIter_add 1 (s.l - 2) nPrime]
      simp only [collatzIter, hnp_step]
      exact even_run_iter (s.l - 2) xNext
    apply Classical.byContradiction
    intro hlt
    exact helper_no_merge nPrime (1 + (s.l - 2)) (by dsimp [nPrime]; omega) (by dsimp [nPrime]; omega) hmerge1
  · -- Case s.k >= 2, s.l >= 2: nPrime = (s.x - 1) / 2 merges via subdouble_entry_merger_step!
    have hk2 : s.k ≥ 2 := by omega
    have hmerge2 := subdouble_entry_block_merger s.x xNext s.k s.l u hk2 hl2 (by omega) hx_u (by omega)
    apply Classical.byContradiction
    intro hlt
    exact helper_no_merge ((s.x - 1) / 2) ((s.k - 1) + (s.l - 2) + 2) (by omega) (by omega) hmerge2

-- ============================================================================
-- 13.2 Rational Taylor Bounds on ln 2 & ln 3, CF Convergents, & Pure-Nat phiLog
-- ============================================================================

/-- Finite geometric series identity `(y - 1) * sum_{j=0}^{d-1} y^j + 1 = y^d` for `y >= 1`. -/
def geomSeriesNat (y : Nat) : Nat -> Nat
  | 0 => 0
  | d + 1 => geomSeriesNat y d + y ^ d

theorem geom_series_telescope : ∀ (y d : Nat), y ≥ 1 ->
    (y - 1) * geomSeriesNat y d + 1 = y ^ d
  | _, 0, _ => by simp [geomSeriesNat]
  | y, d + 1, hy => by
    simp only [geomSeriesNat, Nat.mul_add]
    have ih := geom_series_telescope y d hy
    have hmul : (y - 1) * y ^ d + y ^ d = y ^ (d + 1) := by
      rw [Nat.pow_succ]
      calc
        (y - 1) * y ^ d + y ^ d = y ^ d * (y - 1) + y ^ d * 1 := by
          rw [Nat.mul_comm (y - 1) (y ^ d), Nat.mul_one]
        _ = y ^ d * ((y - 1) + 1) := by rw [← Nat.mul_add]
        _ = y ^ d * y := by rw [show (y - 1) + 1 = y by omega]
    omega

/-- Kernel-evaluated scaled lower Taylor sum for `ln 2 = 2 * sum_{r>=0} 1 / ((2r+1) * 3^(2r+1))` at `2^S`. -/
def taylorLn2LoAux (S : Nat) : Nat -> Nat
  | 0 => 0
  | r + 1 => taylorLn2LoAux S r + (2 * 2 ^ S) / ((2 * r + 1) * 3 ^ (2 * r + 1))

/-- Kernel-evaluated scaled upper Taylor bound for `ln 2` with geometric tail remainder at `N`. -/
def taylorLn2HiAux (S : Nat) : Nat -> Nat
  | 0 => 0
  | r + 1 =>
    let den := (2 * r + 1) * 3 ^ (2 * r + 1)
    taylorLn2HiAux S r + (2 * 2 ^ S + den - 1) / den

def taylorLn2Bounds (S N : Nat) : Nat × Nat :=
  let lo := taylorLn2LoAux S N
  let remDen := 4 * (2 * N + 1) * 3 ^ (2 * N - 1)
  let hi := taylorLn2HiAux S N + (2 ^ S + remDen - 1) / remDen
  (lo, hi)

/-- Kernel-evaluated scaled lower/upper Taylor bounds for `ln 3 = 2 * sum_{r>=0} 1 / ((2r+1) * 2^(2r+1))`. -/
def taylorLn3LoAux (S : Nat) : Nat -> Nat
  | 0 => 0
  | r + 1 => taylorLn3LoAux S r + (2 * 2 ^ S) / ((2 * r + 1) * 2 ^ (2 * r + 1))

def taylorLn3HiAux (S : Nat) : Nat -> Nat
  | 0 => 0
  | r + 1 =>
    let den := (2 * r + 1) * 2 ^ (2 * r + 1)
    taylorLn3HiAux S r + (2 * 2 ^ S + den - 1) / den

def taylorLn3Bounds (S N : Nat) : Nat × Nat :=
  let lo := taylorLn3LoAux S N
  let remDen := 3 * (2 * N + 1) * 2 ^ (2 * N)
  let hi := taylorLn3HiAux S N + (2 * 2 ^ S + remDen - 1) / remDen
  (lo, hi)

/-- Exact continued-fraction recurrence generator from partial quotients `[a_0, a_1, ...]`. -/
def cfConvergentsAux : List Nat -> Nat -> Nat -> Nat -> Nat -> List (Nat × Nat)
  | [], _, _, _, _ => []
  | a :: rest, pPrev2, pPrev1, qPrev2, qPrev1 =>
    let p := a * pPrev1 + pPrev2
    let q := a * qPrev1 + qPrev2
    (p, q) :: cfConvergentsAux rest pPrev1 p qPrev1 q

def cfConvergentsFromQuotients (qs : List Nat) : List (Nat × Nat) :=
  cfConvergentsAux qs 0 1 1 0

def log2Of3PartialQuotients52 : List Nat := [
  1, 1, 1, 2, 2, 3, 1, 5, 2, 23, 2, 2, 1, 1, 55, 1, 4, 3, 1, 1,
  15, 1, 9, 2, 5, 7, 1, 1, 4, 8, 1, 11, 1, 20, 2, 1, 10, 1, 4, 1,
  1, 1, 1, 1, 37, 4, 55, 1, 1, 49, 1, 1
]

def checkAlternatingTaylorConvergents (ln2Lo ln2Hi ln3Lo ln3Hi : Nat) :
    Nat -> List (Nat × Nat) -> Bool
  | _, [] => true
  | idx, (p, q) :: rest =>
    let ok :=
      if idx == 0 then p * ln2Hi < q * ln3Lo
      else if idx % 2 == 1 then q * ln3Hi < p * ln2Lo
      else p * ln2Hi < q * ln3Lo
    ok && checkAlternatingTaylorConvergents ln2Lo ln2Hi ln3Lo ln3Hi (idx + 1) rest

set_option maxRecDepth 20000 in
/--
  Theorem 26.2a (Kernel-Certified Rational Taylor Intervals for `ln 2`, `ln 3` & All 52 CF Convergents):
  Evaluates `[ln2Lo, ln2Hi]` (`N = 60`, width `66` at `2^200`) and `[ln3Lo, ln3Hi]` (`N = 105`, width `105` at `2^200`)
  and certifies alternating sign across ALL 52 convergents `(p_0, q_0) .. (p_51, q_51)` of `log_2(3)`!
-/
theorem taylor_ln2_ln3_and_52_convergents_certified :
    let (ln2Lo, ln2Hi) := taylorLn2Bounds 200 60
    let (ln3Lo, ln3Hi) := taylorLn3Bounds 200 105
    let convs := cfConvergentsFromQuotients log2Of3PartialQuotients52
    ln2Lo < ln2Hi ∧ ln2Hi - ln2Lo ≤ 70 ∧
    ln3Lo < ln3Hi ∧ ln3Hi - ln3Lo ≤ 110 ∧
    convs.length = 52 ∧
    convs[43]? = some (325919355854421968365, 205632218873398596256) ∧
    convs[44]? = some (12261796429850908150604, 7736332199829210068325) ∧
    convs[45]? = some (49373105075258054570781, 31150961018190238869556) ∧
    convs[50]? = some (278024068491311595647009290, 175413657020157229319631761) ∧
    convs[51]? = some (550543198726409845420360681, 347354084702895683704606156) ∧
    checkAlternatingTaylorConvergents ln2Lo ln2Hi ln3Lo ln3Hi 0 convs = true := by
  decide

/-- Pure-`Nat` binary-exponentiation interval evaluator `[L, U]` bounding `2^S * 2^p / 3^q`. -/
def evalPow2Pow3Aux (S p q : Nat) : Nat -> Nat × Nat
  | 0 => (2 ^ S, 2 ^ S)
  | nbits + 1 =>
    let lu := evalPow2Pow3Aux S (p / 2) (q / 2) nbits
    let scale := 2 ^ S
    let multP := if p % 2 == 1 then 2 else 1
    let divD := if q % 2 == 1 then 3 * scale else scale
    ((lu.1 * lu.1 * multP) / divD, (lu.2 * lu.2 * multP) / divD + 1)

theorem pow_mono_base_nat : ∀ (n a b : Nat), a ≤ b -> a ^ n ≤ b ^ n
  | 0, _, _, _ => by simp
  | n + 1, a, b, hab => by
    rw [Nat.pow_succ, Nat.pow_succ]
    exact Nat.mul_le_mul (pow_mono_base_nat n a b hab) hab

theorem pow_mul_distrib_nat : ∀ (n a b : Nat), (a * b) ^ n = a ^ n * b ^ n
  | 0, _, _ => by simp
  | n + 1, a, b => by
    rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, pow_mul_distrib_nat n a b]
    calc
      a ^ n * b ^ n * (a * b) = a ^ n * (b ^ n * (a * b)) := by rw [Nat.mul_assoc]
      _ = a ^ n * ((b ^ n * a) * b) := by rw [Nat.mul_assoc (b ^ n) a b]
      _ = a ^ n * ((a * b ^ n) * b) := by rw [Nat.mul_comm (b ^ n) a]
      _ = a ^ n * (a * (b ^ n * b)) := by rw [Nat.mul_assoc a (b ^ n) b]
      _ = (a ^ n * a) * (b ^ n * b) := by rw [← Nat.mul_assoc]

theorem pow_mul_exp_nat : ∀ (a m n : Nat), (a ^ m) ^ n = a ^ (m * n)
  | _, _, 0 => by simp
  | a, m, n + 1 => by
    rw [Nat.pow_succ, pow_mul_exp_nat a m n, Nat.mul_succ, Nat.pow_add]

theorem evalPow2Pow3Aux_invariant : ∀ (nbits S p q : Nat),
    p < 2 ^ nbits -> q < 2 ^ nbits ->
    let lu := evalPow2Pow3Aux S p q nbits
    lu.1 * 3 ^ q ≤ 2 ^ S * 2 ^ p ∧
    2 ^ S * 2 ^ p ≤ lu.2 * 3 ^ q ∧
    (nbits ≥ 1 -> 2 ^ S * 2 ^ p < lu.2 * 3 ^ q)
  | 0, S, p, q, hp, hq => by
    have hp0 : p = 0 := by simp at hp; omega
    have hq0 : q = 0 := by simp at hq; omega
    subst hp0; subst hq0
    simp [evalPow2Pow3Aux]
  | nbits + 1, S, p, q, hp, hq => by
    dsimp only [evalPow2Pow3Aux]
    have hp_div : p / 2 < 2 ^ nbits := by rw [Nat.pow_succ] at hp; omega
    have hq_div : q / 2 < 2 ^ nbits := by rw [Nat.pow_succ] at hq; omega
    rcases evalPow2Pow3Aux_invariant nbits S (p / 2) (q / 2) hp_div hq_div with ⟨ihL, ihU, _⟩
    let L := (evalPow2Pow3Aux S (p / 2) (q / 2) nbits).1
    let U := (evalPow2Pow3Aux S (p / 2) (q / 2) nbits).2
    let scale := 2 ^ S
    let multP := if p % 2 == 1 then 2 else 1
    let divD := if q % 2 == 1 then 3 * scale else scale
    have hscale_pos : scale ≥ 1 := pow2_pos_nat S
    have hdivD_pos : divD ≥ 1 := by
      dsimp [divD]; by_cases hq1 : (q % 2 == 1) = true <;> simp [hq1] <;> omega
    have hmultP_pos : multP ≥ 1 := by
      dsimp [multP]; by_cases hp1 : (p % 2 == 1) = true <;> simp [hp1]
    have h2p : 2 ^ (p / 2) * 2 ^ (p / 2) * multP = 2 ^ p := by
      rw [← Nat.pow_add]
      dsimp [multP]
      by_cases hp1 : p % 2 = 1
      · have hpt : (p % 2 == 1) = true := decide_eq_true hp1
        rw [hpt]; simp
        rw [← Nat.pow_succ]
        exact congrArg (2 ^ ·) (by omega)
      · have hpf : (p % 2 == 1) = false := decide_eq_false hp1
        rw [hpf]; simp
        rw [show p / 2 + p / 2 = p by omega]
    have h3q : divD * (3 ^ (q / 2) * 3 ^ (q / 2)) = scale * 3 ^ q := by
      rw [← Nat.pow_add]
      dsimp [divD]
      by_cases hq1 : q % 2 = 1
      · have hqt : (q % 2 == 1) = true := decide_eq_true hq1
        rw [hqt]; simp
        calc
          3 * scale * 3 ^ (q / 2 + q / 2)
              = scale * (3 ^ (q / 2 + q / 2) * 3) := by
                rw [Nat.mul_comm 3 scale, Nat.mul_assoc, Nat.mul_comm 3 _]
          _ = scale * 3 ^ q := by
                rw [← Nat.pow_succ]
                exact congrArg (fun e => scale * 3 ^ e) (by omega)
      · have hqf : (q % 2 == 1) = false := decide_eq_false hq1
        rw [hqf]; simp
        rw [show q / 2 + q / 2 = q by omega]
    have hsqL : (L * L * multP) * (3 ^ (q / 2) * 3 ^ (q / 2)) ≤ scale * (scale * 2 ^ p) := by
      have hm1 := Nat.mul_le_mul ihL ihL
      have hm2 := Nat.mul_le_mul_right multP hm1
      have hlhs : (L * 3 ^ (q / 2)) * (L * 3 ^ (q / 2)) * multP =
          (L * L * multP) * (3 ^ (q / 2) * 3 ^ (q / 2)) := by
        calc
          (L * 3 ^ (q / 2)) * (L * 3 ^ (q / 2)) * multP
              = (L * L) * (3 ^ (q / 2) * 3 ^ (q / 2)) * multP := by
                rw [Nat.mul_assoc L (3 ^ (q / 2)), ← Nat.mul_assoc (3 ^ (q / 2)) L,
                    Nat.mul_comm (3 ^ (q / 2)) L, Nat.mul_assoc L (3 ^ (q / 2)), ← Nat.mul_assoc]
          _ = (L * L * multP) * (3 ^ (q / 2) * 3 ^ (q / 2)) := by
                rw [Nat.mul_assoc (L * L), Nat.mul_comm _ multP, ← Nat.mul_assoc]
      have hrhs : (scale * 2 ^ (p / 2)) * (scale * 2 ^ (p / 2)) * multP =
          scale * (scale * 2 ^ p) := by
        calc
          (scale * 2 ^ (p / 2)) * (scale * 2 ^ (p / 2)) * multP
              = (scale * scale) * (2 ^ (p / 2) * 2 ^ (p / 2) * multP) := by
                rw [Nat.mul_assoc scale (2 ^ (p / 2)), ← Nat.mul_assoc (2 ^ (p / 2)) scale,
                    Nat.mul_comm (2 ^ (p / 2)) scale, Nat.mul_assoc scale (2 ^ (p / 2)),
                    ← Nat.mul_assoc, Nat.mul_assoc (scale * scale)]
          _ = scale * (scale * 2 ^ p) := by rw [h2p, Nat.mul_assoc]
      rw [hlhs, hrhs] at hm2
      exact hm2
    have hsqU : scale * (scale * 2 ^ p) ≤ (U * U * multP) * (3 ^ (q / 2) * 3 ^ (q / 2)) := by
      have hm1 := Nat.mul_le_mul ihU ihU
      have hm2 := Nat.mul_le_mul_right multP hm1
      have hrhs : (U * 3 ^ (q / 2)) * (U * 3 ^ (q / 2)) * multP =
          (U * U * multP) * (3 ^ (q / 2) * 3 ^ (q / 2)) := by
        calc
          (U * 3 ^ (q / 2)) * (U * 3 ^ (q / 2)) * multP
              = (U * U) * (3 ^ (q / 2) * 3 ^ (q / 2)) * multP := by
                rw [Nat.mul_assoc U (3 ^ (q / 2)), ← Nat.mul_assoc (3 ^ (q / 2)) U,
                    Nat.mul_comm (3 ^ (q / 2)) U, Nat.mul_assoc U (3 ^ (q / 2)), ← Nat.mul_assoc]
          _ = (U * U * multP) * (3 ^ (q / 2) * 3 ^ (q / 2)) := by
                rw [Nat.mul_assoc (U * U), Nat.mul_comm _ multP, ← Nat.mul_assoc]
      have hlhs : (scale * 2 ^ (p / 2)) * (scale * 2 ^ (p / 2)) * multP =
          scale * (scale * 2 ^ p) := by
        calc
          (scale * 2 ^ (p / 2)) * (scale * 2 ^ (p / 2)) * multP
              = (scale * scale) * (2 ^ (p / 2) * 2 ^ (p / 2) * multP) := by
                rw [Nat.mul_assoc scale (2 ^ (p / 2)), ← Nat.mul_assoc (2 ^ (p / 2)) scale,
                    Nat.mul_comm (2 ^ (p / 2)) scale, Nat.mul_assoc scale (2 ^ (p / 2)),
                    ← Nat.mul_assoc, Nat.mul_assoc (scale * scale)]
          _ = scale * (scale * 2 ^ p) := by rw [h2p, Nat.mul_assoc]
      rw [hlhs, hrhs] at hm2
      exact hm2
    let L' := (L * L * multP) / divD
    let U' := (U * U * multP) / divD + 1
    have hL_div : divD * L' ≤ L * L * multP := mul_div_le_nat (L * L * multP) divD
    have hU_div : U * U * multP < divD * U' := by
      dsimp [U']
      rw [Nat.mul_add, Nat.mul_one]
      have hdm := Nat.div_add_mod (U * U * multP) divD
      have hlt := Nat.mod_lt (U * U * multP) hdivD_pos
      omega
    have h3q2_pos : 3 ^ (q / 2) * 3 ^ (q / 2) ≥ 1 :=
      Nat.mul_pos (pow3_pos_nat (q / 2)) (pow3_pos_nat (q / 2))
    have hL_scaled : scale * (L' * 3 ^ q) ≤ scale * (scale * 2 ^ p) := by
      have hm := Nat.mul_le_mul_right (3 ^ (q / 2) * 3 ^ (q / 2)) hL_div
      have heq : (divD * L') * (3 ^ (q / 2) * 3 ^ (q / 2)) = scale * (L' * 3 ^ q) := by
        calc
          (divD * L') * (3 ^ (q / 2) * 3 ^ (q / 2))
              = L' * (divD * (3 ^ (q / 2) * 3 ^ (q / 2))) := by
                rw [Nat.mul_comm divD L', Nat.mul_assoc]
          _ = L' * (scale * 3 ^ q) := by rw [h3q]
          _ = scale * (L' * 3 ^ q) := by
                rw [← Nat.mul_assoc, Nat.mul_comm L' scale, Nat.mul_assoc]
      rw [heq] at hm
      exact Nat.le_trans hm hsqL
    have hU_scaled : scale * (scale * 2 ^ p) < scale * (U' * 3 ^ q) := by
      have hm := Nat.mul_lt_mul_of_pos_right hU_div h3q2_pos
      have heq : (divD * U') * (3 ^ (q / 2) * 3 ^ (q / 2)) = scale * (U' * 3 ^ q) := by
        calc
          (divD * U') * (3 ^ (q / 2) * 3 ^ (q / 2))
              = U' * (divD * (3 ^ (q / 2) * 3 ^ (q / 2))) := by
                rw [Nat.mul_comm divD U', Nat.mul_assoc]
          _ = U' * (scale * 3 ^ q) := by rw [h3q]
          _ = scale * (U' * 3 ^ q) := by
                rw [← Nat.mul_assoc, Nat.mul_comm U' scale, Nat.mul_assoc]
      rw [heq] at hm
      exact Nat.lt_of_le_of_lt hsqU hm
    have hL_fin : L' * 3 ^ q ≤ scale * 2 ^ p :=
      Nat.le_of_mul_le_mul_left hL_scaled hscale_pos
    have hU_fin : scale * 2 ^ p < U' * 3 ^ q := by
      apply Classical.byContradiction
      intro hge
      have hm := Nat.mul_le_mul_left scale (show U' * 3 ^ q ≤ scale * 2 ^ p by omega)
      omega
    exact ⟨hL_fin, Nat.le_of_lt hU_fin, fun _ => hU_fin⟩

/-- Soundness theorem for `evalPow2Pow3Aux`: certifies `L * 3^q <= 2^S * 2^p < U * 3^q`! -/
theorem evalPow2Pow3Aux_sound (S p q nbits : Nat)
    (hnb : nbits ≥ 1) (hp : p < 2 ^ nbits) (hq : q < 2 ^ nbits) :
    (evalPow2Pow3Aux S p q nbits).1 * 3 ^ q ≤ 2 ^ S * 2 ^ p ∧
    2 ^ S * 2 ^ p < (evalPow2Pow3Aux S p q nbits).2 * 3 ^ q := by
  rcases evalPow2Pow3Aux_invariant nbits S p q hp hq with ⟨hL, _, hU⟩
  exact ⟨hL, hU hnb⟩

/-- Structurally recursive fast bit-length helper for kernel `decide` evaluation. -/
def bitLenAux : Nat -> Nat -> Nat
  | 0, _ => 0
  | fuel + 1, x => if x == 0 then 0 else 1 + bitLenAux fuel (x / 2)

theorem bitLenAux_lower : ∀ (fuel x : Nat), x ≥ 1 -> 2 ^ (bitLenAux fuel x - 1) ≤ x
  | 0, x, hx => by simp [bitLenAux]; omega
  | fuel + 1, x, hx => by
    have hne : (x == 0) = false := decide_eq_false (by omega)
    simp only [bitLenAux, hne]; simp
    by_cases hx2 : x < 2
    · have hx1 : x = 1 := by omega
      subst hx1
      have h0 : bitLenAux fuel 0 = 0 := by cases fuel <;> rfl
      rw [h0]; simp
    · have ih := bitLenAux_lower fuel (x / 2) (by omega)
      cases hb : bitLenAux fuel (x / 2) with
      | zero => simp; omega
      | succ k =>
        rw [hb] at ih; simp at ih ⊢
        rw [Nat.pow_succ]; omega

theorem bitLenAux_upper : ∀ (fuel x : Nat), x < 2 ^ fuel -> x < 2 ^ bitLenAux fuel x
  | 0, x, hx => by simp [bitLenAux] at hx ⊢; omega
  | fuel + 1, x, hx => by
    by_cases hx0 : x = 0
    · subst hx0; simp [bitLenAux]
    · have hne : (x == 0) = false := decide_eq_false hx0
      simp only [bitLenAux, hne]; simp
      have ih := bitLenAux_upper fuel (x / 2) (by rw [Nat.pow_succ] at hx; omega)
      rw [show 1 + bitLenAux fuel (x / 2) = bitLenAux fuel (x / 2) + 1 by omega, Nat.pow_succ]
      omega

/-- 16-bit chunked bit-length (`11.4x` fewer `whnf` reductions and heap cells than 1-bit `bitLenAux`). -/
def bitLen16 : Nat -> Nat -> Nat
  | 0, x => bitLenAux 16 x
  | fuel + 1, x => if x < 65536 then bitLenAux 16 x else 16 + bitLen16 fuel (x / 65536)

theorem bitLen16_pos : ∀ (fuel x : Nat), x ≥ 1 -> bitLen16 fuel x ≥ 1
  | 0, x, hx => by
    have hne : (x == 0) = false := decide_eq_false (by omega)
    simp only [bitLen16, bitLenAux, hne]; simp
  | fuel + 1, x, hx => by
    by_cases hlt : x < 65536
    · have hne : (x == 0) = false := decide_eq_false (by omega)
      simp only [bitLen16, hlt, ite_true, bitLenAux, hne]; simp
    · simp only [bitLen16, hlt, ite_false]; omega

theorem bitLen16_lower : ∀ (fuel x : Nat), x ≥ 1 -> 2 ^ (bitLen16 fuel x - 1) ≤ x
  | 0, x, hx => bitLenAux_lower 16 x hx
  | fuel + 1, x, hx => by
    by_cases hlt : x < 65536
    · simp only [bitLen16, hlt, ite_true]
      exact bitLenAux_lower 16 x hx
    · simp only [bitLen16, hlt, ite_false]
      have hx_div : x / 65536 ≥ 1 := by omega
      have hb_pos := bitLen16_pos fuel (x / 65536) hx_div
      have ih := bitLen16_lower fuel (x / 65536) hx_div
      rw [show 16 + bitLen16 fuel (x / 65536) - 1 = 16 + (bitLen16 fuel (x / 65536) - 1) by omega,
          Nat.pow_add]
      have hm := Nat.mul_le_mul_left (2 ^ 16) ih
      have hdiv : 65536 * (x / 65536) ≤ x := mul_div_le_nat x 65536
      rw [show (2 ^ 16 : Nat) = 65536 from rfl] at hm
      omega

theorem bitLen16_upper : ∀ (fuel x : Nat), x < 2 ^ (16 * fuel + 16) -> x < 2 ^ bitLen16 fuel x
  | 0, x, hx => bitLenAux_upper 16 x hx
  | fuel + 1, x, hx => by
    by_cases hlt : x < 65536
    · simp only [bitLen16, hlt, ite_true]
      exact bitLenAux_upper 16 x hlt
    · simp only [bitLen16, hlt, ite_false]
      have hexp : 16 * (fuel + 1) + 16 = 16 + (16 * fuel + 16) := by omega
      rw [hexp, Nat.pow_add, show (2 ^ 16 : Nat) = 65536 from rfl] at hx
      have hdiv_lt : x / 65536 < 2 ^ (16 * fuel + 16) := by
        apply Classical.byContradiction
        intro hge
        have hm := Nat.mul_le_mul_left 65536 (show 2 ^ (16 * fuel + 16) ≤ x / 65536 by omega)
        have hmd := mul_div_le_nat x 65536
        omega
      have ih := bitLen16_upper fuel (x / 65536) hdiv_lt
      rw [Nat.pow_add, show (2 ^ 16 : Nat) = 65536 from rfl]
      have hm := Nat.mul_le_mul_left 65536 (show x / 65536 + 1 ≤ 2 ^ bitLen16 fuel (x / 65536) by omega)
      have hdm := Nat.div_add_mod x 65536
      have hmod := Nat.mod_lt x (by decide : 65536 > 0)
      omega

def pow2SplitAux : Nat -> Nat -> Nat
  | 0, s => 2 ^ s
  | fuel + 1, s =>
    if s ≤ 200 then 2 ^ s
    else 2 ^ 200 * pow2SplitAux fuel (s - 200)

def pow2Split (s : Nat) : Nat := pow2SplitAux 4 s

theorem pow2SplitAux_eq : ∀ (fuel s : Nat), pow2SplitAux fuel s = 2 ^ s
  | 0, _ => rfl
  | fuel + 1, s => by
    simp only [pow2SplitAux]
    by_cases h : s ≤ 200
    · simp [h]
    · simp only [h, ↓reduceIte, pow2SplitAux_eq fuel (s - 200), ← Nat.pow_add]
      exact congrArg (2 ^ ·) (by omega)

theorem pow2Split_eq (s : Nat) : pow2Split s = 2 ^ s := pow2SplitAux_eq 4 s

def certifyLog2PowLoop (S : Nat) : Nat -> Nat -> Nat -> Nat -> Nat -> (Nat × Nat × Nat × Nat)
  | 0, ml, el, mh, eh => (ml, el, mh, eh)
  | r + 1, ml, el, mh, eh =>
    let sql := ml * ml
    let sl := bitLen16 40 sql - S
    let ml' := sql / pow2Split sl
    let el' := 2 * el + sl
    let sqh := mh * mh
    let sh := bitLen16 40 sqh - S
    let mh' := (sqh + pow2Split sh - 1) / pow2Split sh
    let eh' := 2 * eh + sh
    certifyLog2PowLoop S r ml' el' mh' eh'

/-- Pure-`Nat` dyadic squaring bracket `(L_pow, U_pow, ok)` certifying `2^L_pow <= C^(2^B) < 2^U_pow`. -/
def certifyLog2Pow (S B C : Nat) : Nat × Nat × Bool :=
  let (ml, el, mh, eh) := certifyLog2PowLoop S B C 0 C 0
  let lPow := el + (bitLen16 15 ml - 1)
  let uPow := eh + bitLen16 15 mh
  let ok := (S ≥ 1) && (C ≥ 1) && (mh < 2 ^ 256)
  (lPow, uPow, ok)

theorem ceil_div_mul_ge_nat (X D : Nat) (hD : D ≥ 1) :
    X ≤ ((X + D - 1) / D) * D := by
  have hdm := Nat.div_add_mod (X + D - 1) D
  have hlt := Nat.mod_lt (X + D - 1) hD
  have hcomm : D * ((X + D - 1) / D) = ((X + D - 1) / D) * D := Nat.mul_comm _ _
  omega

theorem certifyLog2PowLoop_invariant :
    ∀ (r S ml el mh eh V : Nat),
      S ≥ 1 -> ml ≥ 1 -> ml * 2 ^ el ≤ V -> V ≤ mh * 2 ^ eh ->
      let (mlf, elf, mhf, ehf) := certifyLog2PowLoop S r ml el mh eh
      mlf ≥ 1 ∧ mlf * 2 ^ elf ≤ V ^ (2 ^ r) ∧ V ^ (2 ^ r) ≤ mhf * 2 ^ ehf
  | 0, _, ml, el, mh, eh, V, _, hml, hlo, hhi => by
    simp only [certifyLog2PowLoop, Nat.pow_zero, Nat.pow_one]
    exact ⟨hml, hlo, hhi⟩
  | r + 1, S, ml, el, mh, eh, V, hS, hml, hlo, hhi => by
    dsimp only [certifyLog2PowLoop]
    let sql := ml * ml
    let sl := bitLen16 40 sql - S
    let ml' := sql / pow2Split sl
    let el' := 2 * el + sl
    let sqh := mh * mh
    let sh := bitLen16 40 sqh - S
    let mh' := (sqh + pow2Split sh - 1) / pow2Split sh
    let eh' := 2 * eh + sh
    have hml'_eq : ml' = sql / 2 ^ sl := by dsimp [ml']; rw [pow2Split_eq]
    have hmh'_eq : mh' = (sqh + 2 ^ sh - 1) / 2 ^ sh := by dsimp [mh']; rw [pow2Split_eq]
    have hsql_pos : sql ≥ 1 := Nat.mul_pos hml hml
    have hsl_pow : 2 ^ sl ≤ sql := by
      dsimp [sl]
      by_cases hb : bitLen16 40 sql ≤ S
      · rw [show bitLen16 40 sql - S = 0 by omega]; simp; exact hsql_pos
      · have hle1 : bitLen16 40 sql - S ≤ bitLen16 40 sql - 1 := by omega
        exact Nat.le_trans (pow2_mono_nat hle1) (bitLen16_lower 40 sql hsql_pos)
    have hml'_pos : ml' ≥ 1 := by
      rw [hml'_eq]
      exact le_div_of_mul_le (pow2_pos_nat sl) (by rw [Nat.mul_one]; exact hsl_pow)
    have hlo' : ml' * 2 ^ el' ≤ V * V := by
      dsimp [el']
      rw [Nat.pow_add, ← Nat.mul_assoc, Nat.mul_comm ml' (2 ^ (2 * el)), Nat.mul_assoc]
      have hdiv : ml' * 2 ^ sl ≤ sql := by
        rw [hml'_eq]; exact Nat.div_mul_le_self sql (2 ^ sl)
      have hm1 : 2 ^ (2 * el) * (ml' * 2 ^ sl) ≤ 2 ^ (2 * el) * sql :=
        Nat.mul_le_mul_left _ hdiv
      have heq_sq : 2 ^ (2 * el) * sql = (ml * 2 ^ el) * (ml * 2 ^ el) := by
        dsimp [sql]
        rw [show 2 * el = el + el by omega, Nat.pow_add]
        calc
          (2 ^ el * 2 ^ el) * (ml * ml)
              = 2 ^ el * (2 ^ el * (ml * ml)) := by rw [Nat.mul_assoc]
          _ = 2 ^ el * ((2 ^ el * ml) * ml) := by rw [Nat.mul_assoc (2 ^ el) ml ml]
          _ = 2 ^ el * ((ml * 2 ^ el) * ml) := by rw [Nat.mul_comm (2 ^ el) ml]
          _ = 2 ^ el * (ml * (2 ^ el * ml)) := by rw [Nat.mul_assoc ml (2 ^ el) ml]
          _ = (2 ^ el * ml) * (ml * 2 ^ el) := by rw [← Nat.mul_assoc, Nat.mul_comm (2 ^ el) ml]
          _ = (ml * 2 ^ el) * (ml * 2 ^ el) := by rw [Nat.mul_comm (2 ^ el) ml]
      exact Nat.le_trans hm1 (by rw [heq_sq]; exact Nat.mul_le_mul hlo hlo)
    have hhi' : V * V ≤ mh' * 2 ^ eh' := by
      dsimp [eh']
      rw [Nat.pow_add, ← Nat.mul_assoc, Nat.mul_comm mh' (2 ^ (2 * eh)), Nat.mul_assoc]
      have hceil : sqh ≤ mh' * 2 ^ sh := by
        rw [hmh'_eq]; exact ceil_div_mul_ge_nat sqh (2 ^ sh) (pow2_pos_nat sh)
      have hm1 : 2 ^ (2 * eh) * sqh ≤ 2 ^ (2 * eh) * (mh' * 2 ^ sh) :=
        Nat.mul_le_mul_left _ hceil
      have heq_sq : (mh * 2 ^ eh) * (mh * 2 ^ eh) = 2 ^ (2 * eh) * sqh := by
        dsimp [sqh]
        rw [show 2 * eh = eh + eh by omega, Nat.pow_add]
        calc
          (mh * 2 ^ eh) * (mh * 2 ^ eh)
              = mh * (2 ^ eh * (mh * 2 ^ eh)) := by rw [Nat.mul_assoc]
          _ = mh * ((2 ^ eh * mh) * 2 ^ eh) := by rw [← Nat.mul_assoc (2 ^ eh) mh]
          _ = mh * ((mh * 2 ^ eh) * 2 ^ eh) := by rw [Nat.mul_comm (2 ^ eh) mh]
          _ = (mh * mh) * (2 ^ eh * 2 ^ eh) := by rw [Nat.mul_assoc mh (2 ^ eh) (2 ^ eh), ← Nat.mul_assoc]
          _ = (2 ^ eh * 2 ^ eh) * (mh * mh) := by rw [Nat.mul_comm]
      exact Nat.le_trans (by rw [← heq_sq]; exact Nat.mul_le_mul hhi hhi) hm1
    rcases certifyLog2PowLoop_invariant r S ml' el' mh' eh' (V * V) hS hml'_pos hlo' hhi' with
      ⟨h1, h2, h3⟩
    have hv_pow : (V * V) ^ (2 ^ r) = V ^ (2 ^ (r + 1)) := by
      have hv2 : V * V = V ^ 2 := by rw [Nat.pow_succ, Nat.pow_one]
      rw [hv2, pow_mul_exp_nat V 2 (2 ^ r), Nat.pow_succ, Nat.mul_comm 2 (2 ^ r)]
    rw [hv_pow] at h2 h3
    exact ⟨h1, h2, h3⟩

/-- Scaled discrete binary logarithm `phiLog B Y := flog2 (Y ^ (2 ^ B))`. -/
def phiLog (B Y : Nat) : Nat :=
  flog2 (Y ^ (2 ^ B))

/-- Soundness of `certifyLog2Pow`: when `ok = true`, `L_pow <= phiLog B C < U_pow`! -/
theorem certifyLog2Pow_sound (S B C : Nat)
    (hok : (certifyLog2Pow S B C).2.2 = true) :
    let (lPow, uPow, _) := certifyLog2Pow S B C
    lPow ≤ phiLog B C ∧ phiLog B C < uPow ∧ uPow ≥ 1 := by
  unfold certifyLog2Pow at hok ⊢
  generalize hloop : certifyLog2PowLoop S B C 0 C 0 = res at hok ⊢
  rcases res with ⟨ml, el, mh, eh⟩
  dsimp only at hok ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  rcases hok with ⟨⟨hS, hC⟩, hmh_lt⟩
  have hinv := certifyLog2PowLoop_invariant B S C 0 C 0 C hS hC (by simp) (by simp)
  rw [hloop] at hinv
  rcases hinv with ⟨hml_pos, hlo_v, hhi_v⟩
  have hpow_lo : 2 ^ (el + (bitLen16 15 ml - 1)) ≤ C ^ (2 ^ B) := by
    rw [Nat.pow_add, Nat.mul_comm (2 ^ el)]
    exact Nat.le_trans (Nat.mul_le_mul_right (2 ^ el) (bitLen16_lower 15 ml hml_pos)) hlo_v
  have hpow_hi : C ^ (2 ^ B) < 2 ^ (eh + bitLen16 15 mh) := by
    rw [Nat.pow_add, Nat.mul_comm (2 ^ eh)]
    exact Nat.lt_of_le_of_lt hhi_v
      (Nat.mul_lt_mul_of_pos_right (bitLen16_upper 15 mh hmh_lt) (pow2_pos_nat eh))
  have hcQ_pos : C ^ (2 ^ B) ≥ 1 := pow_pos_nat C (2 ^ B) hC
  rcases flog2_spec (C ^ (2 ^ B)) hcQ_pos with ⟨hf_lo, hf_hi⟩
  unfold phiLog
  have hl_le : el + (bitLen16 15 ml - 1) ≤ flog2 (C ^ (2 ^ B)) := by
    apply Classical.byContradiction
    intro hgt
    have hm : 2 ^ (flog2 (C ^ (2 ^ B)) + 1) ≤ 2 ^ (el + (bitLen16 15 ml - 1)) :=
      pow2_mono_nat (by omega)
    omega
  have hu_gt : flog2 (C ^ (2 ^ B)) < eh + bitLen16 15 mh := by
    apply Classical.byContradiction
    intro hge
    have hm : 2 ^ (eh + bitLen16 15 mh) ≤ 2 ^ flog2 (C ^ (2 ^ B)) :=
      pow2_mono_nat (by omega)
    omega
  exact ⟨hl_le, hu_gt, by omega⟩

theorem phiLog_pow2_mul (B m X : Nat) (hX : X ≥ 1) :
    phiLog B (2 ^ m * X) = m * 2 ^ B + phiLog B X := by
  unfold phiLog
  rw [pow_mul_distrib_nat (2 ^ B) (2 ^ m) X, pow_mul_exp_nat 2 m (2 ^ B)]
  exact flog2_mul_pow2 (m * 2 ^ B) (X ^ (2 ^ B)) (pow_pos_nat X (2 ^ B) hX)

theorem phiLog_pow2 (B m : Nat) : phiLog B (2 ^ m) = m * 2 ^ B := by
  have h := phiLog_pow2_mul B m 1 (by decide)
  have h1 : phiLog B 1 = 0 := by
    unfold phiLog
    rw [one_pow_nat]
    exact flog2_one
  rw [Nat.mul_one, h1] at h
  simpa using h

theorem phiLog_mono {B Y1 Y2 : Nat} (h1 : Y1 ≥ 1) (hle : Y1 ≤ Y2) :
    phiLog B Y1 ≤ phiLog B Y2 :=
  flog2_mono (pow_pos_nat Y1 (2 ^ B) h1) (pow_mono_base_nat (2 ^ B) Y1 Y2 hle)

theorem phiLog_mul_bounds (B A C : Nat) (hA : A ≥ 1) (hC : C ≥ 1) :
    phiLog B A + phiLog B C ≤ phiLog B (A * C) ∧
    phiLog B (A * C) ≤ phiLog B A + phiLog B C + 1 := by
  unfold phiLog
  have hAQ := pow_pos_nat A (2 ^ B) hA
  have hCQ := pow_pos_nat C (2 ^ B) hC
  rcases flog2_spec (A ^ (2 ^ B)) hAQ with ⟨alo, ahi⟩
  rcases flog2_spec (C ^ (2 ^ B)) hCQ with ⟨clo, chi⟩
  rcases flog2_spec ((A * C) ^ (2 ^ B)) (pow_pos_nat (A * C) (2 ^ B) (Nat.mul_pos hA hC)) with
    ⟨aclo, achi⟩
  rw [pow_mul_distrib_nat (2 ^ B) A C] at aclo achi
  constructor
  · apply Classical.byContradiction
    intro hlt
    have hm1 : 2 ^ (flog2 (A ^ (2 ^ B)) + flog2 (C ^ (2 ^ B))) ≤ A ^ (2 ^ B) * C ^ (2 ^ B) := by
      rw [Nat.pow_add]; exact Nat.mul_le_mul alo clo
    have hm2 : 2 ^ (flog2 ((A * C) ^ (2 ^ B)) + 1) ≤
        2 ^ (flog2 (A ^ (2 ^ B)) + flog2 (C ^ (2 ^ B))) := pow2_mono_nat (by omega)
    rw [pow_mul_distrib_nat (2 ^ B) A C] at hm2
    omega
  · apply Classical.byContradiction
    intro hgt
    have hm1 : A ^ (2 ^ B) * C ^ (2 ^ B) <
        2 ^ (flog2 (A ^ (2 ^ B)) + flog2 (C ^ (2 ^ B)) + 2) := by
      have hp : 2 ^ (flog2 (A ^ (2 ^ B)) + flog2 (C ^ (2 ^ B)) + 2) =
          2 ^ (flog2 (A ^ (2 ^ B)) + 1) * 2 ^ (flog2 (C ^ (2 ^ B)) + 1) := by
        rw [← Nat.pow_add]
        exact congrArg (2 ^ ·) (by omega)
      rw [hp]
      have h1 := Nat.mul_lt_mul_of_pos_right ahi hCQ
      have h2 := Nat.mul_lt_mul_of_pos_left chi (pow2_pos_nat (flog2 (A ^ (2 ^ B)) + 1))
      exact Nat.lt_trans h1 h2
    have hm2 : 2 ^ (flog2 (A ^ (2 ^ B)) + flog2 (C ^ (2 ^ B)) + 2) ≤
        2 ^ flog2 ((A * C) ^ (2 ^ B)) := pow2_mono_nat (by omega)
    rw [pow_mul_distrib_nat (2 ^ B) A C] at hm2
    omega

theorem phiLog_pow3_le (B k Theta : Nat) (h3 : phiLog B 3 < Theta) :
    phiLog B (3 ^ k) ≤ k * Theta := by
  by_cases hk0 : k = 0
  · subst hk0; simp [phiLog, flog2_one]
  · unfold phiLog at h3 ⊢
    rcases flog2_spec (3 ^ (2 ^ B)) (pow_pos_nat 3 (2 ^ B) (by decide)) with ⟨_, h3_hi⟩
    have hlt_pow : (3 ^ k) ^ (2 ^ B) < 2 ^ (k * Theta) := by
      have hswap : (3 ^ k) ^ (2 ^ B) = (3 ^ (2 ^ B)) ^ k := by
        rw [pow_mul_exp_nat, pow_mul_exp_nat, Nat.mul_comm]
      rw [hswap]
      have hbase_le : 3 ^ (2 ^ B) + 1 ≤ 2 ^ Theta :=
        Nat.le_trans h3_hi (pow2_mono_nat (by omega))
      have hs := pow_lt_pow_pos_nat (a := 3 ^ (2 ^ B)) (b := 2 ^ Theta)
        (pow_pos_nat 3 (2 ^ B) (by decide)) hbase_le k (by omega)
      rwa [pow_mul_exp_nat 2 Theta k, Nat.mul_comm Theta k] at hs
    rcases flog2_spec ((3 ^ k) ^ (2 ^ B)) (pow_pos_nat (3 ^ k) (2 ^ B) (pow3_pos_nat k)) with
      ⟨hk_lo, _⟩
    apply Classical.byContradiction
    intro hgt
    have hm := pow2_mono_nat (show k * Theta + 1 ≤ flog2 ((3 ^ k) ^ (2 ^ B)) by omega)
    have hp2 : 2 ^ (k * Theta + 1) = 2 ^ (k * Theta) * 2 := Nat.pow_succ _ _
    omega

theorem pow2_mul3_le_pow3_mul2 : ∀ k : Nat, k ≥ 1 -> 3 * 2 ^ k ≤ 2 * 3 ^ k
  | 0, hk => by omega
  | 1, _ => by decide
  | k + 2, _ => by
    have ih := pow2_mul3_le_pow3_mul2 (k + 1) (by omega)
    rw [Nat.pow_succ 2 (k + 1), Nat.pow_succ 3 (k + 1)]
    omega

/--
  Theorem 26.2b (Universal 4-Line Pure-`Nat` Spiral Step `phiLog` Inequality):
  For EVERY spiral step `s -> xNext` (`s.x >= xMin >= 1`), regardless of whether `s.l = 1`
  or `s.l >= 2`, `(3 * (xMin + 1)) * 2^(s.k + 1) * (xNext + 1) <= (3 * xMin + 5) * 3^s.k * (s.x + 1)`,
  hence `phiLog B (xNext + 1) <= (Theta * phiLog B (s.x + 1)) / 2^B - E`!
-/
theorem validSpiralStep_phiLog_bound
    {s : SpiralStepData} {xNext xMin B Theta L_D0 U_N0p E : Nat}
    (hv : ValidSpiralStep s xNext)
    (hx_min : s.x ≥ xMin) (hxmin_pos : xMin ≥ 1)
    (hTheta : phiLog B 3 < Theta) (hTheta_gt : 2 ^ B ≤ Theta)
    (hD0 : L_D0 ≤ phiLog B (3 * (xMin + 1)))
    (hN0p : phiLog B (3 * xMin + 5) < U_N0p)
    (hE : E + U_N0p + 1 ≤ 2 ^ B + L_D0) :
    phiLog B (xNext + 1) ≤ (Theta * phiLog B (s.x + 1)) / (2 ^ B) - E := by
  rcases hv with ⟨_, _, _, hxN_pos, hk1, hl1, hstep⟩
  -- Step 1: Universal pure-Nat multiplicative inequality across BOTH s.l = 1 and s.l >= 2!
  have hmul_ineq :
      (3 * (xMin + 1)) * (2 ^ (s.k + 1) * (xNext + 1)) ≤
      (3 * xMin + 5) * (3 ^ s.k * (s.x + 1)) := by
    by_cases hl_eq1 : s.l = 1
    · rw [hl_eq1] at hstep
      have h21 : 2 ^ 1 - 1 = 1 := rfl
      rw [h21, Nat.mul_one] at hstep
      rw [hstep, Nat.mul_add]
      have h23 := pow2_mul3_le_pow3_mul2 s.k hk1
      have hterm2 : (3 * (xMin + 1)) * 2 ^ s.k ≤ 2 * (3 ^ s.k * (s.x + 1)) := by
        calc
          (3 * (xMin + 1)) * 2 ^ s.k
              = (xMin + 1) * (3 * 2 ^ s.k) := by
                rw [Nat.mul_comm 3 (xMin + 1), Nat.mul_assoc]
          _ ≤ (s.x + 1) * (2 * 3 ^ s.k) := Nat.mul_le_mul (by omega) h23
          _ = 2 * ((s.x + 1) * 3 ^ s.k) := by
                rw [← Nat.mul_assoc, Nat.mul_comm (s.x + 1) 2, Nat.mul_assoc]
          _ = 2 * (3 ^ s.k * (s.x + 1)) := by
                rw [Nat.mul_comm (s.x + 1) (3 ^ s.k)]
      have hsplit : (3 * xMin + 5) * (3 ^ s.k * (s.x + 1)) =
          (3 * (xMin + 1)) * (3 ^ s.k * (s.x + 1)) + 2 * (3 ^ s.k * (s.x + 1)) := by
        rw [← Nat.add_mul, show 3 * (xMin + 1) + 2 = 3 * xMin + 5 by omega]
      omega
    · have hl2 : s.l ≥ 2 := by omega
      have hsub := spiral_step_mul_ratio_nat s.k s.l s.x xNext hl1 hstep
      have hp2_split : 2 ^ (s.k + s.l) = 2 ^ (s.k + 1) * 2 ^ (s.l - 1) := by
        rw [← Nat.pow_add, show s.k + 1 + (s.l - 1) = s.k + s.l by omega]
      have hp2_ge2 : 2 ≤ 2 ^ (s.l - 1) := by
        simpa using pow2_mono_nat (show 1 ≤ s.l - 1 by omega)
      have hxn_le : xNext + 1 ≤ 2 ^ (s.l - 1) * xNext := by
        have hm := Nat.mul_le_mul_right xNext hp2_ge2
        omega
      have hstep_le : 2 ^ (s.k + 1) * (xNext + 1) ≤ 3 ^ s.k * (s.x + 1) := by
        have hp2k : 2 ^ s.k ≥ 1 := pow2_pos_nat s.k
        have hm := Nat.mul_le_mul_left (2 ^ (s.k + 1)) hxn_le
        rw [← Nat.mul_assoc, ← hp2_split] at hm
        exact Nat.le_trans hm (by omega)
      exact Nat.mul_le_mul (by omega) hstep_le
  -- Step 2: Take phiLog B on both sides!
  let Q := 2 ^ B
  have hQ_pos : Q ≥ 1 := pow2_pos_nat B
  have hphi_mono := phiLog_mono (B := B) (Nat.mul_pos (by omega)
    (Nat.mul_pos (pow2_pos_nat (s.k + 1)) (by omega))) hmul_ineq
  have hlhs_add := (phiLog_mul_bounds B (3 * (xMin + 1)) (2 ^ (s.k + 1) * (xNext + 1))
    (by omega) (Nat.mul_pos (pow2_pos_nat (s.k + 1)) (by omega))).1
  rw [phiLog_pow2_mul B (s.k + 1) (xNext + 1) (by omega)] at hlhs_add
  have hrhs_add1 := (phiLog_mul_bounds B (3 * xMin + 5) (3 ^ s.k * (s.x + 1))
    (by omega) (Nat.mul_pos (pow3_pos_nat s.k) (by omega))).2
  have hrhs_add2 := (phiLog_mul_bounds B (3 ^ s.k) (s.x + 1) (pow3_pos_nat s.k) (by omega)).2
  have hk3 := phiLog_pow3_le B s.k Theta hTheta
  -- Step 3: s.k * Q <= phiLog B (s.x + 1) since 2^s.k | s.x + 1
  rcases spiral_step_odd_quotient_nat s.k s.l s.x xNext hl1 hstep with ⟨u, hu_odd, hx_u, _⟩
  have h2k_le : 2 ^ s.k ≤ s.x + 1 := by
    have hm := Nat.mul_le_mul_left (2 ^ s.k) (show 1 ≤ u by omega)
    omega
  have hkQ_le : s.k * Q ≤ phiLog B (s.x + 1) := by
    have hm := phiLog_mono (B := B) (pow2_pos_nat s.k) h2k_le
    rwa [phiLog_pow2 B s.k] at hm
  -- Step 4: s.k * (Theta - Q) + phiLog B (s.x + 1) <= (Theta * phiLog B (s.x + 1)) / Q
  let uX := phiLog B (s.x + 1)
  have hdiv_bound : s.k * (Theta - Q) + uX ≤ (Theta * uX) / Q := by
    apply le_div_of_mul_le hQ_pos
    rw [Nat.mul_add]
    have hm : Q * (s.k * (Theta - Q)) ≤ (Theta - Q) * uX := by
      calc
        Q * (s.k * (Theta - Q)) = (Q * s.k) * (Theta - Q) := by rw [Nat.mul_assoc]
        _ = (Theta - Q) * (s.k * Q) := by rw [Nat.mul_comm (Q * s.k) (Theta - Q), Nat.mul_comm Q s.k]
        _ ≤ (Theta - Q) * uX := Nat.mul_le_mul_left (Theta - Q) hkQ_le
    have hsum : (Theta - Q) * uX + Q * uX = Theta * uX := by
      rw [← Nat.add_mul, show (Theta - Q) + Q = Theta by omega]
    omega
  have hkTheta_split : s.k * Theta = s.k * Q + s.k * (Theta - Q) := by
    rw [← Nat.mul_add, show Q + (Theta - Q) = Theta by omega]
  have hsk1_Q : (s.k + 1) * Q = s.k * Q + Q := by rw [Nat.add_mul, Nat.one_mul]
  dsimp [uX, Q] at *
  omega

-- ============================================================================
-- 13.3 Zero-Sorting `(d, t)` Scan Theorem & Telescoping Inverse-Bernoulli Slab Verifier
-- ============================================================================

def phiStepIter (B Theta E : Nat) : Nat -> Nat -> Nat
  | 0, u0 => u0
  | r + 1, u0 => (Theta * phiStepIter B Theta E r u0) / (2 ^ B) - E

theorem phiStepIter_mono_val (B Theta E : Nat) :
    ∀ (r u v : Nat), u ≤ v -> phiStepIter B Theta E r u ≤ phiStepIter B Theta E r v
  | 0, _, _, huv => huv
  | r + 1, u, v, huv => by
    simp only [phiStepIter]
    have ih := phiStepIter_mono_val B Theta E r u v huv
    have hmul := Nat.mul_le_mul_left Theta ih
    have hdiv : (Theta * phiStepIter B Theta E r u) / (2 ^ B) ≤
        (Theta * phiStepIter B Theta E r v) / (2 ^ B) :=
      le_div_of_mul_le (pow2_pos_nat B)
        (Nat.le_trans (mul_div_le_nat _ (2 ^ B)) hmul)
    omega

theorem phiStepIter_step_gt {B Theta E U : Nat}
    (hgrow : (Theta - 2 ^ B) * U ≥ 2 ^ B * (E + 1)) :
    U + 1 ≤ (Theta * U) / (2 ^ B) - E := by
  have hTheta_ge : Theta ≥ 2 ^ B := by
    apply Classical.byContradiction
    intro hlt
    rw [show Theta - 2 ^ B = 0 by omega, Nat.zero_mul] at hgrow
    have hp := pow2_pos_nat B
    have hm : 2 ^ B * 1 ≤ 2 ^ B * (E + 1) := Nat.mul_le_mul_left (2 ^ B) (by omega)
    omega
  have hmul : 2 ^ B * (U + E + 1) ≤ Theta * U := by
    rw [Nat.mul_add, Nat.mul_one] at hgrow
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
    have h1 : (Theta - 2 ^ B) * U + 2 ^ B * U = Theta * U := by
      rw [← Nat.add_mul, show (Theta - 2 ^ B) + 2 ^ B = Theta by omega]
    omega
  have hdiv : U + E + 1 ≤ (Theta * U) / (2 ^ B) := le_div_of_mul_le (pow2_pos_nat B) hmul
  omega

theorem phiStepIter_grow_invariant (B Theta E U0 : Nat)
    (hgrow : (Theta - 2 ^ B) * U0 ≥ 2 ^ B * (E + 1)) :
    ∀ r : Nat, U0 ≤ phiStepIter B Theta E r U0 ∧
      phiStepIter B Theta E r U0 < phiStepIter B Theta E (r + 1) U0
  | 0 => by
    simp only [phiStepIter]
    have hs := phiStepIter_step_gt hgrow
    exact ⟨Nat.le_refl U0, by omega⟩
  | r + 1 => by
    rcases phiStepIter_grow_invariant B Theta E U0 hgrow r with ⟨hle, hlt⟩
    have hgrow_r : (Theta - 2 ^ B) * phiStepIter B Theta E (r + 1) U0 ≥ 2 ^ B * (E + 1) :=
      Nat.le_trans hgrow (Nat.mul_le_mul_left (Theta - 2 ^ B) (by omega))
    have hs := phiStepIter_step_gt hgrow_r
    exact ⟨by omega, hs⟩

theorem phiStepIter_mono_idx_aux (B Theta E U0 : Nat)
    (hgrow : (Theta - 2 ^ B) * U0 ≥ 2 ^ B * (E + 1)) :
    ∀ a k : Nat, phiStepIter B Theta E a U0 ≤ phiStepIter B Theta E (a + k) U0
  | a, 0 => by simp
  | a, k + 1 => by
    have ih := phiStepIter_mono_idx_aux B Theta E U0 hgrow a k
    have hlt := (phiStepIter_grow_invariant B Theta E U0 hgrow (a + k)).2
    rw [show a + (k + 1) = (a + k) + 1 by omega]
    omega

theorem phiStepIter_mono_idx (B Theta E U0 : Nat)
    (hgrow : (Theta - 2 ^ B) * U0 ≥ 2 ^ B * (E + 1)) :
    ∀ a b : Nat, a ≤ b -> phiStepIter B Theta E a U0 ≤ phiStepIter B Theta E b U0 := by
  intro a b hab
  have h := phiStepIter_mono_idx_aux B Theta E U0 hgrow a (b - a)
  rwa [show a + (b - a) = b by omega] at h

def phiGeomTailSum (B Theta E U0 : Nat) : Nat -> Nat -> Nat
  | 0, _ => 0
  | n + 1, startIdx =>
    phiStepIter B Theta E startIdx U0 + phiGeomTailSum B Theta E U0 n (startIdx + 1)

theorem phiGeomTailSum_mono_start (B Theta E U0 : Nat)
    (hgrow : (Theta - 2 ^ B) * U0 ≥ 2 ^ B * (E + 1)) :
    ∀ (n s1 s2 : Nat), s1 ≤ s2 ->
      phiGeomTailSum B Theta E U0 n s1 ≤ phiGeomTailSum B Theta E U0 n s2
  | 0, _, _, _ => by simp [phiGeomTailSum]
  | n + 1, s1, s2, hs => by
    simp only [phiGeomTailSum]
    exact Nat.add_le_add (phiStepIter_mono_idx B Theta E U0 hgrow s1 s2 hs)
      (phiGeomTailSum_mono_start B Theta E U0 hgrow n (s1 + 1) (s2 + 1) (by omega))

/-- Sorted-Cyclic RHS upper bound `j * U0 + sum_{r=1}^{m - j} U_r`. -/
def sortedCyclicRhsSum (B Theta E U0 m j : Nat) : Nat :=
  j * U0 + phiGeomTailSum B Theta E U0 (m - j) 1

/-- `O(n)` single-pass accumulator equivalent to `phiGeomTailSum` (`46x` fewer `whnf` steps). -/
def phiGeomTailAcc (B Theta E : Nat) : Nat -> Nat -> Nat
  | 0, _ => 0
  | n + 1, cur => cur + phiGeomTailAcc B Theta E n ((Theta * cur) / (2 ^ B) - E)

theorem phiGeomTailAcc_eq (B Theta E U0 : Nat) :
    ∀ (n s : Nat),
      phiGeomTailAcc B Theta E n (phiStepIter B Theta E s U0) =
      phiGeomTailSum B Theta E U0 n s
  | 0, _ => rfl
  | n + 1, s => by
    simp only [phiGeomTailAcc, phiGeomTailSum]
    exact congrArg (phiStepIter B Theta E s U0 + ·) (phiGeomTailAcc_eq B Theta E U0 n (s + 1))

def sortedCyclicRhsFast (B Theta E U0 m j : Nat) : Nat :=
  j * U0 + phiGeomTailAcc B Theta E (m - j) ((Theta * U0) / (2 ^ B) - E)

theorem sortedCyclicRhsFast_eq (B Theta E U0 m j : Nat) :
    sortedCyclicRhsFast B Theta E U0 m j = sortedCyclicRhsSum B Theta E U0 m j := by
  unfold sortedCyclicRhsFast sortedCyclicRhsSum
  exact congrArg (j * U0 + ·) (phiGeomTailAcc_eq B Theta E U0 (m - j) 1)

def countLe (b : Nat) : List Nat -> Nat
  | [] => 0
  | x :: rest => (if x ≤ b then 1 else 0) + countLe b rest

def sumList : List Nat -> Nat
  | [] => 0
  | x :: rest => x + sumList rest

def prodList : List Nat -> Nat
  | [] => 1
  | x :: rest => x * prodList rest

theorem countLe_le_length (b : Nat) : ∀ xs : List Nat, countLe b xs ≤ xs.length
  | [] => by simp [countLe]
  | x :: rest => by
    simp only [countLe, List.length_cons]
    have ih := countLe_le_length b rest
    by_cases h : x ≤ b <;> simp [h] <;> omega

/-- Inductive step-chain predicate on a `phiLog` sequence `us`. -/
def ValidPhiStepSeq (B Theta E : Nat) : Nat -> List Nat -> Prop
  | _, [] => True
  | uPrev, u :: rest =>
    u ≤ (Theta * uPrev) / (2 ^ B) - E ∧ ValidPhiStepSeq B Theta E u rest

/--
  Core 25-Line Zero-Sorting `(d, t)` Forward Scan Lemma (`F(L, d, t) = t * U0 + sum_{r=1}^{L-t} U_{d+r}`):
  Given `uPrev <= U_d`, `ValidPhiStepSeq B Theta E uPrev us`, and `t <= countLe U0 us`,
  `sumList us <= t * U0 + phiGeomTailSum B Theta E U0 (us.length - t) (d + 1)`!
-/
theorem scan_phi_upper_bound (B Theta E U0 : Nat)
    (hgrow : (Theta - 2 ^ B) * U0 ≥ 2 ^ B * (E + 1)) :
    ∀ (us : List Nat) (uPrev d t : Nat),
      uPrev ≤ phiStepIter B Theta E d U0 ->
      ValidPhiStepSeq B Theta E uPrev us ->
      t ≤ countLe U0 us ->
      sumList us ≤ t * U0 + phiGeomTailSum B Theta E U0 (us.length - t) (d + 1)
  | [], _, _, t, _, _, ht => by
    simp [countLe] at ht; subst ht; simp [sumList, phiGeomTailSum]
  | u :: rest, uPrev, d, t, hprev, ⟨hstep, hrest⟩, ht => by
    simp only [sumList, List.length_cons]
    have hcnt_len : countLe U0 rest ≤ rest.length := countLe_le_length U0 rest
    by_cases hu_le : u ≤ U0
    · -- Case 1: u <= U0 -> reset d' = 0!
      simp only [countLe, hu_le, ↓reduceIte] at ht
      by_cases ht0 : t = 0
      · subst ht0
        have ih := scan_phi_upper_bound B Theta E U0 hgrow rest u 0 0 hu_le hrest (by omega)
        simp only [Nat.zero_mul, Nat.zero_add, Nat.sub_zero] at ih ⊢
        have hcomb : U0 + phiGeomTailSum B Theta E U0 rest.length 1 =
            phiGeomTailSum B Theta E U0 (rest.length + 1) 0 := rfl
        have hmono := phiGeomTailSum_mono_start B Theta E U0 hgrow (rest.length + 1) 0 (d + 1) (by omega)
        omega
      · have ih := scan_phi_upper_bound B Theta E U0 hgrow rest u 0 (t - 1) hu_le hrest (by omega)
        simp only [Nat.zero_add] at ih
        have hlen_eq : rest.length + 1 - t = rest.length - (t - 1) := by omega
        rw [hlen_eq]
        have hmono := phiGeomTailSum_mono_start B Theta E U0 hgrow (rest.length - (t - 1)) 1 (d + 1) (by omega)
        have hmul_t : U0 + (t - 1) * U0 = t * U0 := by
          conv => rhs; rw [show t = 1 + (t - 1) by omega]
          rw [Nat.add_mul, Nat.one_mul]
        omega
    · -- Case 2: u > U0 -> advance d' = d + 1 with unchanged t!
      simp only [countLe, hu_le, ↓reduceIte, Nat.zero_add] at ht
      have hu_bound : u ≤ phiStepIter B Theta E (d + 1) U0 := by
        have hm := phiStepIter_mono_val B Theta E 1 uPrev (phiStepIter B Theta E d U0) hprev
        simp only [phiStepIter] at hm ⊢
        omega
      have ih := scan_phi_upper_bound B Theta E U0 hgrow rest u (d + 1) t hu_bound hrest ht
      have hlen_pos : rest.length + 1 - t = (rest.length - t) + 1 := by omega
      rw [hlen_pos]
      simp only [phiGeomTailSum]
      omega

-- Cyclic rotation helper on ValidSpiralChain:
theorem validSpiralChain_append :
    ∀ (l1 l2 : List SpiralStepData) (sHead2 : SpiralStepData) (xEnd : Nat),
      l2 = sHead2 :: l2.tail ->
      ValidSpiralChain l1 sHead2.x ->
      ValidSpiralChain l2 xEnd ->
      ValidSpiralChain (l1 ++ l2) xEnd
  | [], l2, _, xEnd, _, _, h2 => by simpa using h2
  | [s], l2, sHead2, xEnd, hl2, h1, h2 => by
    rw [hl2] at h2 ⊢
    exact ⟨h1, h2⟩
  | s1 :: s2 :: rest, l2, sHead2, xEnd, hl2, ⟨hs1, hrest⟩, h2 => by
    simp only [List.cons_append]
    exact ⟨hs1, validSpiralChain_append (s2 :: rest) l2 sHead2 xEnd hl2 hrest h2⟩

theorem validSpiralChain_split :
    ∀ (l1 : List SpiralStepData) (sMid : SpiralStepData) (l2 : List SpiralStepData) (xEnd : Nat),
      ValidSpiralChain (l1 ++ (sMid :: l2)) xEnd ->
      ValidSpiralChain l1 sMid.x ∧ ValidSpiralChain (sMid :: l2) xEnd
  | [], sMid, l2, xEnd, h => ⟨trivial, h⟩
  | [s], sMid, l2, xEnd, ⟨hs, hrest⟩ => ⟨hs, hrest⟩
  | s1 :: s2 :: rest, sMid, l2, xEnd, ⟨hs1, hrest⟩ => by
    rcases validSpiralChain_split (s2 :: rest) sMid l2 xEnd hrest with ⟨hA, hB⟩
    exact ⟨⟨hs1, hA⟩, hB⟩

theorem find_le_split :
    ∀ (steps : List SpiralStepData) (b : Nat),
      countLe b (spiralVertices steps) ≥ 1 ->
      ∃ pre sSmall suf, steps = pre ++ (sSmall :: suf) ∧ sSmall.x ≤ b
  | [], _, h => by simp [spiralVertices, countLe] at h
  | s :: rest, b, h => by
    simp only [spiralVertices, List.map_cons, countLe] at h
    by_cases hs : s.x ≤ b
    · exact ⟨[], s, rest, rfl, hs⟩
    · simp only [hs, ↓reduceIte, Nat.zero_add] at h
      rcases find_le_split rest b h with ⟨pre, sSmall, suf, heq, hle⟩
      exact ⟨s :: pre, sSmall, suf, by rw [heq]; rfl, hle⟩

theorem countLe_append (b : Nat) : ∀ l1 l2 : List Nat,
    countLe b (l1 ++ l2) = countLe b l1 + countLe b l2
  | [], _ => by simp [countLe]
  | x :: rest, l2 => by
    simp only [List.cons_append, countLe, countLe_append b rest]
    omega

theorem spiralTotalW_append : ∀ l1 l2 : List SpiralStepData,
    spiralChainTotalW (l1 ++ l2) = spiralChainTotalW l1 + spiralChainTotalW l2
  | [], _ => by simp [spiralChainTotalW]
  | s :: rest, l2 => by
    simp only [List.cons_append, spiralChainTotalW, spiralTotalW_append rest l2]
    omega

theorem chain_to_phiStepSeq
    {B Theta L_D0 U_N0p E xMin : Nat}
    (hxmin_pos : xMin ≥ 1)
    (hTheta : phiLog B 3 < Theta) (hTheta_gt : 2 ^ B ≤ Theta)
    (hD0 : L_D0 ≤ phiLog B (3 * (xMin + 1)))
    (hN0p : phiLog B (3 * xMin + 5) < U_N0p)
    (hE : E + U_N0p + 1 ≤ 2 ^ B + L_D0) :
    ∀ (s0 : SpiralStepData) (rest : List SpiralStepData) (xEnd : Nat),
      ValidSpiralChain (s0 :: rest) xEnd ->
      (∀ s ∈ (s0 :: rest), s.x ≥ xMin) ->
      ValidPhiStepSeq B Theta E (phiLog B (s0.x + 1)) (rest.map (fun s => phiLog B (s.x + 1))) ∧
      2 ^ B * spiralChainTotalW (s0 :: rest) ≤
        phiLog B (s0.x + 1) + sumList (rest.map (fun s => phiLog B (s.x + 1)))
  | s0, [], xEnd, hv, hfl => by
    simp only [List.map_nil, ValidPhiStepSeq, spiralChainTotalW, sumList, Nat.add_zero]
    rcases hv with ⟨_, _, _, _, _, hl1, hst⟩
    rcases spiral_step_odd_quotient_nat s0.k s0.l s0.x xEnd hl1 hst with ⟨u, hu_odd, hx_u, _⟩
    have h2k : 2 ^ s0.k ≤ s0.x + 1 := by
      have hm := Nat.mul_le_mul_left (2 ^ s0.k) (show 1 ≤ u by omega)
      omega
    have hm := phiLog_mono (B := B) (pow2_pos_nat s0.k) h2k
    rw [phiLog_pow2 B s0.k, Nat.mul_comm] at hm
    exact ⟨trivial, hm⟩
  | s0, s1 :: tl, xEnd, ⟨hs0, hrest⟩, hfl => by
    rcases chain_to_phiStepSeq hxmin_pos hTheta hTheta_gt hD0 hN0p hE s1 tl xEnd hrest
      (fun s hs => hfl s (List.Mem.tail s0 hs)) with ⟨hseq, hw⟩
    have hstep0 := validSpiralStep_phiLog_bound hs0 (hfl s0 (List.Mem.head _))
      hxmin_pos hTheta hTheta_gt hD0 hN0p hE
    rcases hs0 with ⟨_, _, _, _, _, hl0, hst0⟩
    rcases spiral_step_odd_quotient_nat s0.k s0.l s0.x s1.x hl0 hst0 with ⟨u0, hu0_odd, hx0_u, _⟩
    have h2k0 : 2 ^ s0.k ≤ s0.x + 1 := by
      have hm := Nat.mul_le_mul_left (2 ^ s0.k) (show 1 ≤ u0 by omega)
      omega
    have hm0 := phiLog_mono (B := B) (pow2_pos_nat s0.k) h2k0
    rw [phiLog_pow2 B s0.k, Nat.mul_comm] at hm0
    change ValidPhiStepSeq B Theta E (phiLog B (s0.x + 1))
        (List.map (fun s => phiLog B (s.x + 1)) (s1 :: tl)) ∧
      2 ^ B * (s0.k + spiralChainTotalW (s1 :: tl)) ≤
        phiLog B (s0.x + 1) +
          (phiLog B (s1.x + 1) + sumList (tl.map (fun s => phiLog B (s.x + 1))))
    rw [Nat.mul_add]
    exact ⟨⟨hstep0, hseq⟩, by omega⟩

theorem sub_count_phiLog {B b U0 : Nat} (hb_u0 : phiLog B (b + 1) ≤ U0) :
    ∀ l : List SpiralStepData,
      countLe b (l.map (fun s => s.x)) ≤ countLe U0 (l.map (fun s => phiLog B (s.x + 1)))
  | [] => by simp [countLe]
  | a :: tl => by
    simp only [List.map_cons, countLe]
    have ih := sub_count_phiLog hb_u0 tl
    by_cases ha : a.x ≤ b
    · have hu_le : phiLog B (a.x + 1) ≤ U0 :=
        Nat.le_trans (phiLog_mono (B := B) (by omega) (show a.x + 1 ≤ b + 1 by omega)) hb_u0
      simp [ha, hu_le]; omega
    · simp [ha]
      by_cases hu : phiLog B (a.x + 1) ≤ U0 <;> simp [hu] <;> omega

/--
  Theorem 26.3a (Zero-Sorting Sorted-Cyclic `countLe` Bound):
  On ANY closed `m`-block spiral cycle (`1 <= j <= m`), if `sortedCyclicRhsSum B Theta E U0 m j < 2^B * W`
  where `phiLog B (b + 1) <= U0`, then AT MOST `j - 1` cycle vertices satisfy `x <= b`!
-/
theorem sortedCyclic_countLe_bound
    {steps : List SpiralStepData} {B Theta L_D0 U_N0p E xMin b U0 j : Nat}
    (hj1 : j ≥ 1) (hjm : j ≤ steps.length)
    (hcyc : IsNontrivialSpiralCycle steps)
    (hfloor : ∀ s ∈ steps, s.x ≥ xMin) (hxmin_pos : xMin ≥ 1)
    (hTheta : phiLog B 3 < Theta) (hTheta_gt : 2 ^ B ≤ Theta)
    (hD0 : L_D0 ≤ phiLog B (3 * (xMin + 1)))
    (hN0p : phiLog B (3 * xMin + 5) < U_N0p)
    (hE : E + U_N0p + 1 ≤ 2 ^ B + L_D0)
    (hgrow : (Theta - 2 ^ B) * U0 ≥ 2 ^ B * (E + 1))
    (hb_u0 : phiLog B (b + 1) ≤ U0)
    (hrhs_lt : sortedCyclicRhsSum B Theta E U0 steps.length j < 2 ^ B * spiralChainTotalW steps) :
    countLe b (spiralVertices steps) ≤ j - 1 := by
  apply Classical.byContradiction
  intro hgt
  have hge_j : countLe b (spiralVertices steps) ≥ j := by omega
  rcases find_le_split steps b (by omega) with ⟨pre, sSmall, suf, hsplit_eq, hs_le_b⟩
  have hrot_chain : ValidSpiralChain (sSmall :: (suf ++ pre)) sSmall.x := by
    cases hsteps : steps with
    | nil => rw [hsteps] at hcyc; cases hcyc
    | cons h0 htl =>
      rw [hsteps] at hcyc hsplit_eq
      rcases hcyc with ⟨hch, _⟩
      cases hpre : pre with
      | nil =>
        rw [hpre, List.nil_append] at hsplit_eq
        injection hsplit_eq with hh0 hhtl
        subst hh0; subst hhtl
        simpa [List.append_nil] using hch
      | cons p0 ptl =>
        rw [hpre, List.cons_append] at hsplit_eq
        injection hsplit_eq with hh0 hhtl
        subst hh0; subst hhtl
        rcases validSpiralChain_split (h0 :: ptl) sSmall suf h0.x hch with ⟨hPreChain, hSufChain⟩
        exact validSpiralChain_append (sSmall :: suf) (h0 :: ptl) h0 sSmall.x rfl hSufChain hPreChain
  have hrot_floor : ∀ s ∈ (sSmall :: (suf ++ pre)), s.x ≥ xMin := by
    intro s hs
    apply hfloor s
    rw [hsplit_eq]
    simp only [List.mem_append, List.mem_cons] at hs ⊢
    rcases hs with rfl | (hsuf | hpre)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr hsuf)
    · exact Or.inl hpre
  have hrot_W : spiralChainTotalW (sSmall :: (suf ++ pre)) = spiralChainTotalW steps := by
    rw [hsplit_eq, spiralTotalW_append, ← List.cons_append, spiralTotalW_append, Nat.add_comm]
  have hrot_len : (suf ++ pre).length = steps.length - 1 := by
    rw [hsplit_eq]
    simp [List.length_append]
    omega
  have hrot_cnt : countLe U0 ((suf ++ pre).map (fun s => phiLog B (s.x + 1))) ≥ j - 1 := by
    have hcnt_rot : countLe b (spiralVertices (sSmall :: (suf ++ pre))) = countLe b (spiralVertices steps) := by
      unfold spiralVertices
      rw [hsplit_eq, List.map_append, countLe_append, ← List.cons_append, List.map_append,
          countLe_append, Nat.add_comm]
    simp only [spiralVertices, List.map_cons, countLe, hs_le_b, ↓reduceIte] at hcnt_rot
    have hm := sub_count_phiLog hb_u0 (suf ++ pre)
    unfold spiralVertices at hge_j
    omega
  rcases chain_to_phiStepSeq hxmin_pos hTheta hTheta_gt hD0 hN0p hE sSmall (suf ++ pre) sSmall.x
    hrot_chain hrot_floor with ⟨hseq, hw_le⟩
  have hu0_le : phiLog B (sSmall.x + 1) ≤ U0 :=
    Nat.le_trans (phiLog_mono (B := B) (by omega) (show sSmall.x + 1 ≤ b + 1 by omega)) hb_u0
  have hscan := scan_phi_upper_bound B Theta E U0 hgrow
    ((suf ++ pre).map (fun s => phiLog B (s.x + 1)))
    (phiLog B (sSmall.x + 1)) 0 (j - 1) hu0_le hseq hrot_cnt
  simp only [List.length_map, hrot_len, Nat.zero_add] at hscan
  have hlen_sub : steps.length - 1 - (j - 1) = steps.length - j := by omega
  rw [hlen_sub] at hscan
  have htot : phiLog B (sSmall.x + 1) + sumList ((suf ++ pre).map (fun s => phiLog B (s.x + 1))) ≤
      sortedCyclicRhsSum B Theta E U0 steps.length j := by
    unfold sortedCyclicRhsSum
    have hj_mul : U0 + (j - 1) * U0 = j * U0 := by
      conv => rhs; rw [show j = 1 + (j - 1) by omega]
      rw [Nat.add_mul, Nat.one_mul]
    omega
  rw [hrot_W] at hw_le
  omega

/--
  Theorem 26.3b (5-Line Pure-`Nat` Inverse-Bernoulli Product Inequality):
  For ANY `M : Nat` and weights `ws : List Nat` with `sumList ws <= M`,
  `(M - sumList ws) * prodList (ws.map (M + ·)) <= M ^ (ws.length + 1)`.
-/
theorem invBernoulli_prod (M : Nat) : ∀ ws : List Nat,
    sumList ws ≤ M ->
    (M - sumList ws) * prodList (ws.map (fun w => M + w)) ≤ M ^ (ws.length + 1)
  | [], _ => by simp [sumList, prodList]
  | w :: rest, hsum => by
    simp only [sumList] at hsum
    simp only [sumList, List.map_cons, prodList, List.length_cons]
    have ih := invBernoulli_prod M rest (by omega)
    let S := sumList rest
    have hstep : (M - (w + S)) * (M + w) ≤ M * (M - S) := by
      have h1 : (M - (w + S)) * (M + w) + (w + S) * M ≤ M * (M + w) := by
        have hadd : (M - (w + S)) * (M + w) + (w + S) * (M + w) = M * (M + w) := by
          rw [← Nat.add_mul, show M - (w + S) + (w + S) = M by dsimp [S]; omega]
        have hle_w : (w + S) * M ≤ (w + S) * (M + w) := Nat.mul_le_mul_left _ (by omega)
        omega
      rw [Nat.mul_add (M - (w + S)) M w, Nat.add_mul w S M, Nat.mul_add M M w,
          Nat.mul_comm w M, Nat.mul_comm S M] at h1
      rw [Nat.mul_add (M - (w + S)) M w, Nat.mul_sub_left_distrib M M S]
      omega
    have hm1 := Nat.mul_le_mul_right (prodList (rest.map (fun x => M + x))) hstep
    rw [Nat.mul_assoc, Nat.mul_assoc] at hm1
    have hm2 := Nat.mul_le_mul_left M ih
    rw [Nat.pow_succ M (rest.length + 1), Nat.mul_comm (M ^ (rest.length + 1)) M]
    exact Nat.le_trans hm1 hm2

/-- Step-function ceiling reciprocal weight `stepU M b = (M + b) / (b + 1)` so `(b + 1) * stepU M b >= M`. -/
def stepU (M b : Nat) : Nat :=
  (M + b) / (b + 1)

theorem stepU_spec (M b x : Nat) (hx : x ≥ b + 1) :
    (x + 1) * M ≤ x * (M + stepU M b) := by
  have hge_M : M ≤ (b + 1) * stepU M b := by
    unfold stepU
    have hdm := Nat.div_add_mod (M + b) (b + 1)
    have hlt := Nat.mod_lt (M + b) (by omega : b + 1 > 0)
    omega
  have hx_u : M ≤ x * stepU M b :=
    Nat.le_trans hge_M (Nat.mul_le_mul_right (stepU M b) hx)
  rw [Nat.add_mul, Nat.one_mul, Nat.mul_add]
  omega

theorem stepU_anti {M b1 b2 : Nat} (hle : b1 ≤ b2) : stepU M b2 ≤ stepU M b1 := by
  by_cases hM0 : M = 0
  · subst hM0
    unfold stepU
    rw [Nat.zero_add, Nat.div_eq_of_lt (by omega : b2 < b2 + 1)]
    exact Nat.zero_le _
  · unfold stepU
    apply le_div_of_mul_le (by omega)
    have hdiv : (b2 + 1) * ((M + b2) / (b2 + 1)) ≤ M + b2 := mul_div_le_nat _ _
    have hm : (b1 + 1) * ((b2 + 1) * ((M + b2) / (b2 + 1))) ≤ (b1 + 1) * (M + b2) :=
      Nat.mul_le_mul_left (b1 + 1) hdiv
    have hlhs_swap : (b2 + 1) * ((b1 + 1) * ((M + b2) / (b2 + 1))) =
        (b1 + 1) * ((b2 + 1) * ((M + b2) / (b2 + 1))) := by
      rw [← Nat.mul_assoc, Nat.mul_comm (b2 + 1) (b1 + 1), Nat.mul_assoc]
    have hrhs_cmp : (b1 + 1) * (M + b2) ≤ (b2 + 1) * (M + b1) := by
      rw [Nat.mul_add, Nat.mul_add, Nat.add_mul b1 1 M, Nat.add_mul b1 1 b2,
          Nat.add_mul b2 1 M, Nat.add_mul b2 1 b1, Nat.one_mul, Nat.one_mul,
          Nat.mul_comm b1 b2]
      have hmM : (b2 - b1) * 1 ≤ (b2 - b1) * M :=
        Nat.mul_le_mul_left (b2 - b1) (by omega)
      rw [Nat.mul_one, Nat.sub_mul] at hmM
      have hb1M : b1 * M ≤ b2 * M := Nat.mul_le_mul_right M hle
      omega
    have hprod_le : (b2 + 1) * ((b1 + 1) * ((M + b2) / (b2 + 1))) ≤ (b2 + 1) * (M + b1) := by
      rw [hlhs_swap]; exact Nat.le_trans hm hrhs_cmp
    exact Nat.le_of_mul_le_mul_left hprod_le (Nat.succ_pos b2)

/-- Telescoping step weight `teleU M bPrev bs x` across non-decreasing thresholds `bs`. -/
def teleU (M : Nat) : Nat -> List Nat -> Nat -> Nat
  | bPrev, [], _ => stepU M bPrev
  | bPrev, b :: rest, x =>
    if x ≤ b then stepU M bPrev else teleU M b rest x

theorem teleU_spec (M : Nat) : ∀ (bPrev : Nat) (bs : List Nat) (x : Nat),
    x ≥ bPrev + 1 -> (x + 1) * M ≤ x * (M + teleU M bPrev bs x)
  | bPrev, [], x, hx => stepU_spec M bPrev x hx
  | bPrev, b :: rest, x, hx => by
    simp only [teleU]
    by_cases hle : x ≤ b
    · simp [hle]; exact stepU_spec M bPrev x hx
    · simp [hle]; exact teleU_spec M b rest x (by omega)

/-- Zero-sorting telescoping sum bound using `(b_j, c_j)` where `countLe b_j xs <= c_j`! -/
def teleSumBound (M : Nat) : Nat -> List (Nat × Nat) -> Nat -> Nat
  | bPrev, [], len => len * stepU M bPrev
  | bPrev, (b, c) :: rest, len =>
    len * stepU M b + c * (stepU M bPrev - stepU M b) +
    (teleSumBound M b rest len - len * stepU M b)

-- Even cleaner direct telescoping identity:
-- teleU M bPrev (b :: rest) x + (if x <= b then 0 else stepU M bPrev - stepU M b) == ...
-- Wait: teleU M bPrev (b :: rest) x = teleU M b rest x + (if x <= b then stepU M bPrev - teleU M b rest x else 0)!
-- Since for x <= b, teleU M b rest x = stepU M b (when bs is non-decreasing!),
-- teleU M bPrev (b :: rest) x = teleU M b rest x + (if x <= b then 1 else 0) * (stepU M bPrev - stepU M b)!!
def IsNonDecreasing : Nat -> List Nat -> Bool
  | _, [] => true
  | prev, b :: rest => (prev ≤ b) && IsNonDecreasing b rest

theorem teleU_head_le (M : Nat) : ∀ (b : Nat) (rest : List Nat) (x : Nat),
    x ≤ b -> IsNonDecreasing b rest = true -> teleU M b rest x = stepU M b
  | b, [], _, _, _ => rfl
  | b, b2 :: tl, x, hx, hnd => by
    simp only [IsNonDecreasing, Bool.and_eq_true, decide_eq_true_eq] at hnd
    have hx2 : x ≤ b2 := Nat.le_trans hx hnd.1
    simp [teleU, hx2]

theorem teleU_decompose_sum (M : Nat) :
    ∀ (bPrev b : Nat) (rest : List Nat) (xs : List Nat),
      bPrev ≤ b -> IsNonDecreasing b rest = true ->
      sumList (xs.map (teleU M bPrev (b :: rest))) =
        countLe b xs * (stepU M bPrev - stepU M b) + sumList (xs.map (teleU M b rest))
  | _, _, _, [], _, _ => by simp [sumList, countLe]
  | bPrev, b, rest, x :: tl, hle, hnd => by
    simp only [List.map_cons, sumList, countLe]
    have ih := teleU_decompose_sum M bPrev b rest tl hle hnd
    have hanti : stepU M b ≤ stepU M bPrev := stepU_anti hle
    have hhead : teleU M bPrev (b :: rest) x = if x ≤ b then stepU M bPrev else teleU M b rest x := rfl
    rw [hhead, ih]
    by_cases hx : x ≤ b
    · simp only [hx, ↓reduceIte]
      rw [teleU_head_le M b rest x hx hnd, Nat.add_mul, Nat.one_mul]
      omega
    · simp only [hx, ↓reduceIte, Nat.zero_add]
      omega

theorem sumList_const (c : Nat) : ∀ xs : List Nat, sumList (xs.map (fun _ => c)) = xs.length * c
  | [] => by simp [sumList]
  | _ :: tl => by
    simp only [List.map_cons, sumList, List.length_cons, sumList_const c tl, Nat.add_mul, Nat.one_mul]
    omega

/-- Exact telescoping upper bound `sum_{j} c_j * (u_{j-1} - u_j) + len * u_last`! -/
def teleStepCap (M : Nat) : Nat -> List (Nat × Nat) -> Nat -> Nat
  | bPrev, [], len => len * stepU M bPrev
  | bPrev, (b, c) :: rest, len =>
    c * (stepU M bPrev - stepU M b) + teleStepCap M b rest len

theorem teleStepCap_sound (M : Nat) :
    ∀ (bPrev : Nat) (bcs : List (Nat × Nat)) (xs : List Nat),
      IsNonDecreasing bPrev (bcs.map Prod.fst) = true ->
      (∀ bc ∈ bcs, countLe bc.1 xs ≤ bc.2) ->
      sumList (xs.map (teleU M bPrev (bcs.map Prod.fst))) ≤ teleStepCap M bPrev bcs xs.length
  | bPrev, [], xs, _, _ => by
    simp only [List.map_nil, teleStepCap]
    have heq : xs.map (teleU M bPrev []) = xs.map (fun _ => stepU M bPrev) := rfl
    rw [heq, sumList_const]
    exact Nat.le_refl _
  | bPrev, (b, c) :: rest, xs, hnd, hcnt => by
    simp only [List.map_cons, IsNonDecreasing, Bool.and_eq_true, decide_eq_true_eq] at hnd
    rw [List.map_cons, teleU_decompose_sum M bPrev b (rest.map Prod.fst) xs hnd.1 hnd.2]
    simp only [teleStepCap]
    have hc : countLe b xs ≤ c := hcnt (b, c) (List.Mem.head _)
    have hm1 := Nat.mul_le_mul_right (stepU M bPrev - stepU M b) hc
    have ih := teleStepCap_sound M b rest xs hnd.2 (fun bc hbc => hcnt bc (List.Mem.tail _ hbc))
    omega

theorem prod_ratio_bernoulli_bound (M : Nat) :
    ∀ (bPrev : Nat) (bs : List Nat) (xs : List Nat),
      (∀ x ∈ xs, x ≥ bPrev + 1) ->
      M ^ xs.length * prodList (xs.map (fun x => x + 1)) ≤
        prodList xs * prodList ((xs.map (teleU M bPrev bs)).map (fun u => M + u))
  | _, _, [], _ => by simp [prodList]
  | bPrev, bs, x :: tl, hfl => by
    simp only [List.length_cons, List.map_cons, prodList]
    have hx := teleU_spec M bPrev bs x (hfl x (List.Mem.head _))
    have ih := prod_ratio_bernoulli_bound M bPrev bs tl (fun y hy => hfl y (List.Mem.tail _ hy))
    rw [Nat.pow_succ M tl.length]
    -- Combine ((x + 1) * M) * (M^len * prod(tl+1)) <= (x * (M + u)) * (prod tl * prod(M + u_tl))
    have hm := Nat.mul_le_mul hx ih
    have hlhs : ((x + 1) * M) * (M ^ tl.length * prodList (tl.map (fun y => y + 1))) =
        (M ^ tl.length * M) * ((x + 1) * prodList (tl.map (fun y => y + 1))) := by
      calc
        ((x + 1) * M) * (M ^ tl.length * prodList (tl.map (fun y => y + 1)))
            = (x + 1) * (M * (M ^ tl.length * prodList (tl.map (fun y => y + 1)))) := by rw [Nat.mul_assoc]
        _ = (x + 1) * ((M * M ^ tl.length) * prodList (tl.map (fun y => y + 1))) := by rw [Nat.mul_assoc M]
        _ = (x + 1) * ((M ^ tl.length * M) * prodList (tl.map (fun y => y + 1))) := by rw [Nat.mul_comm M (M ^ tl.length)]
        _ = (M ^ tl.length * M) * ((x + 1) * prodList (tl.map (fun y => y + 1))) := by
            rw [← Nat.mul_assoc, Nat.mul_comm (x + 1) (M ^ tl.length * M), Nat.mul_assoc]
    have hrhs : (x * (M + teleU M bPrev bs x)) *
          (prodList tl * prodList ((tl.map (teleU M bPrev bs)).map (fun u => M + u))) =
        (x * prodList tl) *
          ((M + teleU M bPrev bs x) * prodList ((tl.map (teleU M bPrev bs)).map (fun u => M + u))) := by
      calc
        (x * (M + teleU M bPrev bs x)) *
            (prodList tl * prodList ((tl.map (teleU M bPrev bs)).map (fun u => M + u)))
            = x * ((M + teleU M bPrev bs x) *
              (prodList tl * prodList ((tl.map (teleU M bPrev bs)).map (fun u => M + u)))) := by rw [Nat.mul_assoc]
        _ = x * (prodList tl * ((M + teleU M bPrev bs x) *
              prodList ((tl.map (teleU M bPrev bs)).map (fun u => M + u)))) := by
            rw [← Nat.mul_assoc (M + teleU M bPrev bs x), Nat.mul_comm (M + teleU M bPrev bs x) (prodList tl),
                Nat.mul_assoc (prodList tl)]
        _ = (x * prodList tl) *
              ((M + teleU M bPrev bs x) * prodList ((tl.map (teleU M bPrev bs)).map (fun u => M + u))) := by
            rw [← Nat.mul_assoc]
    rwa [hlhs, hrhs] at hm

/-- Combined `teleStepCap` + `invBernoulli_prod`: `(M - sigma) * prod(x_i + 1) <= M * prod x_i`! -/
theorem teleBernoulli_ratio_bound (M bPrev : Nat) (bcs : List (Nat × Nat)) (xs : List Nat)
    (hM_pos : M ≥ 1)
    (hfl : ∀ x ∈ xs, x ≥ bPrev + 1)
    (hnd : IsNonDecreasing bPrev (bcs.map Prod.fst) = true)
    (hcnt : ∀ bc ∈ bcs, countLe bc.1 xs ≤ bc.2)
    (hsigma_le : teleStepCap M bPrev bcs xs.length ≤ M) :
    (M - teleStepCap M bPrev bcs xs.length) * prodList (xs.map (fun x => x + 1)) ≤
      M * prodList xs := by
  let ws := xs.map (teleU M bPrev (bcs.map Prod.fst))
  have hsum_ws : sumList ws ≤ teleStepCap M bPrev bcs xs.length :=
    teleStepCap_sound M bPrev bcs xs hnd hcnt
  have hbern := invBernoulli_prod M ws (Nat.le_trans hsum_ws hsigma_le)
  have hsub_le : M - teleStepCap M bPrev bcs xs.length ≤ M - sumList ws := by omega
  have hbern2 : (M - teleStepCap M bPrev bcs xs.length) * prodList (ws.map (fun u => M + u)) ≤
      M ^ (xs.length + 1) := by
    have hm := Nat.mul_le_mul_right (prodList (ws.map (fun u => M + u))) hsub_le
    have hlen : ws.length = xs.length := by simp [ws]
    rw [hlen] at hbern
    exact Nat.le_trans hm hbern
  have hprod := prod_ratio_bernoulli_bound M bPrev (bcs.map Prod.fst) xs hfl
  -- Multiply hprod by (M - cap), use hbern2, and cancel M^(xs.length) > 0!
  have hm := Nat.mul_le_mul_left (M - teleStepCap M bPrev bcs xs.length) hprod
  have hlhs : (M - teleStepCap M bPrev bcs xs.length) *
        (M ^ xs.length * prodList (xs.map (fun x => x + 1))) =
      M ^ xs.length * ((M - teleStepCap M bPrev bcs xs.length) * prodList (xs.map (fun x => x + 1))) := by
    rw [← Nat.mul_assoc, Nat.mul_comm _ (M ^ xs.length), Nat.mul_assoc]
  have hrhs_le : (M - teleStepCap M bPrev bcs xs.length) *
        (prodList xs * prodList (ws.map (fun u => M + u))) ≤
      M ^ xs.length * (M * prodList xs) := by
    calc
      (M - teleStepCap M bPrev bcs xs.length) *
          (prodList xs * prodList (ws.map (fun u => M + u)))
          = prodList xs * ((M - teleStepCap M bPrev bcs xs.length) *
            prodList (ws.map (fun u => M + u))) := by
            rw [← Nat.mul_assoc, Nat.mul_comm _ (prodList xs), Nat.mul_assoc]
      _ ≤ prodList xs * M ^ (xs.length + 1) := Nat.mul_le_mul_left _ hbern2
      _ = M ^ xs.length * (M * prodList xs) := by
            rw [Nat.pow_succ, Nat.mul_comm (prodList xs), Nat.mul_assoc]
  rw [hlhs] at hm
  exact Nat.le_of_mul_le_mul_left (Nat.le_trans hm hrhs_le) (pow_pos_nat M xs.length hM_pos)

-- ============================================================================
-- 13.3b Cycle Product Bounds & `checkSlabEliminated_sound`
-- ============================================================================

theorem spiralStep_x_bounds {s : SpiralStepData} {xNext : Nat}
    (hv : ValidSpiralStep s xNext) :
    3 ^ s.k * s.x < 2 ^ (s.k + s.l) * xNext ∧
    2 ^ (s.k + s.l) * xNext < 3 ^ s.k * (s.x + 1) ∧
    2 ^ (s.k + s.l) * xNext = 3 ^ s.k * s.x + (3 ^ s.k - 2 ^ s.k) := by
  rcases hv with ⟨_, _, _, _, hk1, hl1, hstep⟩
  have hsub := spiral_step_mul_ratio_nat s.k s.l s.x xNext hl1 hstep
  have hp2 : 2 ^ s.k ≥ 1 := pow2_pos_nat s.k
  have h3gt2 : 2 ^ s.k < 3 ^ s.k := pow_lt_pow_pos_nat (by decide) (by decide) s.k hk1
  have hexp : 3 ^ s.k * (s.x + 1) = 3 ^ s.k * s.x + 3 ^ s.k := by
    rw [Nat.mul_add, Nat.mul_one]
  exact ⟨by omega, by omega, by omega⟩

theorem prodList_pos : ∀ xs : List Nat, (∀ x ∈ xs, x ≥ 1) -> prodList xs ≥ 1
  | [], _ => by simp [prodList]
  | x :: tl, hfl => by
    simp only [prodList]
    exact Nat.mul_pos (hfl x (List.Mem.head _))
      (prodList_pos tl (fun y hy => hfl y (List.Mem.tail _ hy)))

theorem validSpiralChain_vertices_pos :
    ∀ (s0 : SpiralStepData) (rest : List SpiralStepData) (xEnd : Nat),
      ValidSpiralChain (s0 :: rest) xEnd ->
      prodList (rest.map (fun s => s.x)) ≥ 1
  | _, [], _, _ => by simp [prodList]
  | _, s1 :: tl, xEnd, ⟨⟨_, _, _, hs1_pos, _, _, _⟩, hrest⟩ => by
    simp only [List.map_cons, prodList]
    exact Nat.mul_pos hs1_pos (validSpiralChain_vertices_pos s1 tl xEnd hrest)

theorem spiralChain_prod_bounds :
    ∀ (s0 : SpiralStepData) (rest : List SpiralStepData) (xEnd : Nat),
      ValidSpiralChain (s0 :: rest) xEnd ->
      3 ^ spiralChainTotalW (s0 :: rest) * (s0.x * prodList (rest.map (fun s => s.x))) <
        2 ^ spiralChainTotalK (s0 :: rest) * (prodList (rest.map (fun s => s.x)) * xEnd) ∧
      2 ^ spiralChainTotalK (s0 :: rest) * (prodList (rest.map (fun s => s.x)) * xEnd) <
        3 ^ spiralChainTotalW (s0 :: rest) * ((s0.x + 1) * prodList (rest.map (fun s => s.x + 1)))
  | s0, [], xEnd, hv => by
    simp only [spiralChainTotalW, spiralChainTotalK, List.map_nil, prodList,
      Nat.add_zero, Nat.mul_one, Nat.one_mul]
    rcases spiralStep_x_bounds hv with ⟨h1, h2, _⟩
    exact ⟨h1, h2⟩
  | s0, s1 :: tl, xEnd, ⟨hs0, hrest⟩ => by
    rcases spiralStep_x_bounds hs0 with ⟨h0_lo, h0_hi, _⟩
    rcases spiralChain_prod_bounds s1 tl xEnd hrest with ⟨ih_lo, ih_hi⟩
    have hprod_tl : prodList (tl.map (fun s => s.x)) ≥ 1 :=
      validSpiralChain_vertices_pos s1 tl xEnd hrest
    rcases hs0 with ⟨_, hs0_pos, _, hs1_pos, _, _, _⟩
    simp only [spiralChainTotalW, spiralChainTotalK, List.map_cons, prodList]
    constructor
    · have hpos_r1 : 2 ^ (s0.k + s0.l) * s1.x ≥ 1 :=
        Nat.mul_pos (pow2_pos_nat _) hs1_pos
      have hpos_l2 : 3 ^ spiralChainTotalW (s1 :: tl) * (s1.x * prodList (tl.map (fun s => s.x))) ≥ 1 :=
        Nat.mul_pos (pow3_pos_nat _) (Nat.mul_pos hs1_pos hprod_tl)
      have hm1 := Nat.mul_lt_mul_of_pos_right h0_lo hpos_l2
      have hm2 := Nat.mul_lt_mul_of_pos_left ih_lo hpos_r1
      have htr := Nat.lt_trans hm1 hm2
      have hlhs_eq : (3 ^ s0.k * s0.x) *
            (3 ^ spiralChainTotalW (s1 :: tl) * (s1.x * prodList (tl.map (fun s => s.x)))) =
          3 ^ (s0.k + spiralChainTotalW (s1 :: tl)) *
            (s0.x * (s1.x * prodList (tl.map (fun s => s.x)))) := by
        rw [Nat.pow_add 3 s0.k (spiralChainTotalW (s1 :: tl))]
        calc
          (3 ^ s0.k * s0.x) * (3 ^ spiralChainTotalW (s1 :: tl) * (s1.x * prodList (tl.map (fun s => s.x))))
              = 3 ^ s0.k * (s0.x * (3 ^ spiralChainTotalW (s1 :: tl) * (s1.x * prodList (tl.map (fun s => s.x))))) := by
                rw [Nat.mul_assoc]
          _ = 3 ^ s0.k * (3 ^ spiralChainTotalW (s1 :: tl) * (s0.x * (s1.x * prodList (tl.map (fun s => s.x))))) := by
                rw [← Nat.mul_assoc s0.x, Nat.mul_comm s0.x (3 ^ _), Nat.mul_assoc]
          _ = (3 ^ s0.k * 3 ^ spiralChainTotalW (s1 :: tl)) * (s0.x * (s1.x * prodList (tl.map (fun s => s.x)))) := by
                rw [← Nat.mul_assoc]
      have hrhs_eq : (2 ^ (s0.k + s0.l) * s1.x) *
            (2 ^ spiralChainTotalK (s1 :: tl) * (prodList (tl.map (fun s => s.x)) * xEnd)) =
          2 ^ ((s0.k + s0.l) + spiralChainTotalK (s1 :: tl)) *
            ((s1.x * prodList (tl.map (fun s => s.x))) * xEnd) := by
        rw [Nat.pow_add 2 (s0.k + s0.l) (spiralChainTotalK (s1 :: tl))]
        calc
          (2 ^ (s0.k + s0.l) * s1.x) * (2 ^ spiralChainTotalK (s1 :: tl) * (prodList (tl.map (fun s => s.x)) * xEnd))
              = 2 ^ (s0.k + s0.l) * (s1.x * (2 ^ spiralChainTotalK (s1 :: tl) * (prodList (tl.map (fun s => s.x)) * xEnd))) := by
                rw [Nat.mul_assoc]
          _ = 2 ^ (s0.k + s0.l) * (2 ^ spiralChainTotalK (s1 :: tl) * (s1.x * (prodList (tl.map (fun s => s.x)) * xEnd))) := by
                rw [← Nat.mul_assoc s1.x, Nat.mul_comm s1.x (2 ^ _), Nat.mul_assoc]
          _ = (2 ^ (s0.k + s0.l) * 2 ^ spiralChainTotalK (s1 :: tl)) * ((s1.x * prodList (tl.map (fun s => s.x))) * xEnd) := by
                rw [← Nat.mul_assoc (2 ^ _), ← Nat.mul_assoc s1.x]
      rwa [hlhs_eq, hrhs_eq] at htr
    · have hpos_l2 : 2 ^ spiralChainTotalK (s1 :: tl) * (prodList (tl.map (fun s => s.x)) * xEnd) ≥ 1 := by
        have hpos_lhs : 3 ^ spiralChainTotalW (s1 :: tl) * (s1.x * prodList (tl.map (fun s => s.x))) ≥ 0 := Nat.zero_le _
        omega
      have hpos_r1 : 3 ^ s0.k * (s0.x + 1) ≥ 1 := Nat.mul_pos (pow3_pos_nat _) (by omega)
      have hm1 := Nat.mul_lt_mul_of_pos_right h0_hi hpos_l2
      have hm2 := Nat.mul_lt_mul_of_pos_left ih_hi hpos_r1
      have htr := Nat.lt_trans hm1 hm2
      have hlhs_eq : (2 ^ (s0.k + s0.l) * s1.x) *
            (2 ^ spiralChainTotalK (s1 :: tl) * (prodList (tl.map (fun s => s.x)) * xEnd)) =
          2 ^ ((s0.k + s0.l) + spiralChainTotalK (s1 :: tl)) *
            ((s1.x * prodList (tl.map (fun s => s.x))) * xEnd) := by
        rw [Nat.pow_add 2 (s0.k + s0.l) (spiralChainTotalK (s1 :: tl))]
        calc
          (2 ^ (s0.k + s0.l) * s1.x) * (2 ^ spiralChainTotalK (s1 :: tl) * (prodList (tl.map (fun s => s.x)) * xEnd))
              = 2 ^ (s0.k + s0.l) * (s1.x * (2 ^ spiralChainTotalK (s1 :: tl) * (prodList (tl.map (fun s => s.x)) * xEnd))) := by
                rw [Nat.mul_assoc]
          _ = 2 ^ (s0.k + s0.l) * (2 ^ spiralChainTotalK (s1 :: tl) * (s1.x * (prodList (tl.map (fun s => s.x)) * xEnd))) := by
                rw [← Nat.mul_assoc s1.x, Nat.mul_comm s1.x (2 ^ _), Nat.mul_assoc]
          _ = (2 ^ (s0.k + s0.l) * 2 ^ spiralChainTotalK (s1 :: tl)) * ((s1.x * prodList (tl.map (fun s => s.x))) * xEnd) := by
                rw [← Nat.mul_assoc (2 ^ _), ← Nat.mul_assoc s1.x]
      have hrhs_eq : (3 ^ s0.k * (s0.x + 1)) *
            (3 ^ spiralChainTotalW (s1 :: tl) * ((s1.x + 1) * prodList (tl.map (fun s => s.x + 1)))) =
          3 ^ (s0.k + spiralChainTotalW (s1 :: tl)) *
            ((s0.x + 1) * ((s1.x + 1) * prodList (tl.map (fun s => s.x + 1)))) := by
        rw [Nat.pow_add 3 s0.k (spiralChainTotalW (s1 :: tl))]
        calc
          (3 ^ s0.k * (s0.x + 1)) * (3 ^ spiralChainTotalW (s1 :: tl) * ((s1.x + 1) * prodList (tl.map (fun s => s.x + 1))))
              = 3 ^ s0.k * ((s0.x + 1) * (3 ^ spiralChainTotalW (s1 :: tl) * ((s1.x + 1) * prodList (tl.map (fun s => s.x + 1))))) := by
                rw [Nat.mul_assoc]
          _ = 3 ^ s0.k * (3 ^ spiralChainTotalW (s1 :: tl) * ((s0.x + 1) * ((s1.x + 1) * prodList (tl.map (fun s => s.x + 1))))) := by
                rw [← Nat.mul_assoc (s0.x + 1), Nat.mul_comm (s0.x + 1) (3 ^ _), Nat.mul_assoc]
          _ = (3 ^ s0.k * 3 ^ spiralChainTotalW (s1 :: tl)) * ((s0.x + 1) * ((s1.x + 1) * prodList (tl.map (fun s => s.x + 1)))) := by
                rw [← Nat.mul_assoc]
      rwa [hlhs_eq, hrhs_eq] at htr

/-- Closed cycle global product inequalities: `3^W < 2^K` and `2^K * prod x_i < 3^W * prod (x_i + 1)`! -/
theorem spiralCycle_global_prod_bounds {steps : List SpiralStepData}
    (hcyc : IsNontrivialSpiralCycle steps) :
    let K := spiralChainTotalK steps
    let W := spiralChainTotalW steps
    let xs := spiralVertices steps
    prodList xs ≥ 1 ∧
    3 ^ W < 2 ^ K ∧
    2 ^ K * prodList xs < 3 ^ W * prodList (xs.map (fun x => x + 1)) := by
  have hfl : ∀ s ∈ steps, s.x ≥ 1 := fun s hs => by
    have hp := nontrivial_cycle_vertex_periodic hcyc s hs
    omega
  have hxs_pos : prodList (spiralVertices steps) ≥ 1 := by
    apply prodList_pos
    intro x hx
    unfold spiralVertices at hx
    rcases List.mem_map.mp hx with ⟨s, hs, rfl⟩
    exact hfl s hs
  cases steps with
  | nil => cases hcyc
  | cons s0 rest =>
    rcases hcyc with ⟨hchain, _⟩
    rcases spiralChain_prod_bounds s0 rest s0.x hchain with ⟨hlo, hhi⟩
    have hprod_swap : prodList (rest.map (fun s => s.x)) * s0.x =
        s0.x * prodList (rest.map (fun s => s.x)) := Nat.mul_comm _ _
    rw [hprod_swap] at hlo hhi
    simp only [spiralVertices, List.map_cons, prodList, List.map_map] at hxs_pos ⊢
    have h3lt2 : 3 ^ spiralChainTotalW (s0 :: rest) < 2 ^ spiralChainTotalK (s0 :: rest) := by
      apply Classical.byContradiction
      intro hge
      have hm := Nat.mul_le_mul_right (s0.x * prodList (rest.map (fun s => s.x)))
        (show 2 ^ spiralChainTotalK (s0 :: rest) ≤ 3 ^ spiralChainTotalW (s0 :: rest) by omega)
      omega
    exact ⟨hxs_pos, h3lt2, hhi⟩

-- Executable kernel slab checker:
def buildIndexedPairs : Nat -> List Nat -> List (Nat × Nat)
  | _, [] => []
  | j, b :: rest => (b, j - 1) :: buildIndexedPairs (j + 1) rest

def checkAllThresholdsCertified (sLog bLog Theta E mMax wMin xMin : Nat) :
    Nat -> List Nat -> Bool
  | _, [] => true
  | j, b :: rest =>
    let okJ :=
      if b ≤ xMin - 1 then true
      else
        let (_, uPow, okLog) := certifyLog2Pow sLog bLog (b + 1)
        let U0 := uPow - 1
        okLog &&
        (j ≤ mMax) &&
        ((Theta - 2 ^ bLog) * U0 ≥ 2 ^ bLog * (E + 1)) &&
        (sortedCyclicRhsFast bLog Theta E U0 mMax j < 2 ^ bLog * wMin)
    okJ && checkAllThresholdsCertified sLog bLog Theta E mMax wMin xMin (j + 1) rest

/--
  Pure-`Nat` Kernel Slab Verifier `checkSlabEliminated`:
  Given a convergent/semiconvergent lower ratio `L_val * 3^W <= 2^sPow * 2^K`,
  minimum odd weight `wMin <= W`, maximum block count `mMax >= m`, minimum vertex `xMin`,
  and threshold witness list `bs`, returns `true` when Sorted-Cyclic + Inverse-Bernoulli
  eliminates ALL cycles with `1 <= m <= mMax`, `W >= wMin`, and `L_val * 3^W <= 2^sPow * 2^K`!
-/
def checkSlabEliminated (sLog bLog sPow mMax wMin xMin lVal : Nat) (bs : List Nat) : Bool :=
  let M := 2 ^ sPow
  let Q := 2 ^ bLog
  let (_, Theta, ok3) := certifyLog2Pow sLog bLog 3
  let (lD0, _, okD0) := certifyLog2Pow sLog bLog (3 * (xMin + 1))
  let (_, uN0p, okN0p) := certifyLog2Pow sLog bLog (3 * xMin + 5)
  let E := Q - (uN0p - lD0 + 1)
  let bcs := buildIndexedPairs 1 bs
  let sigma := teleStepCap M (xMin - 1) bcs mMax
  (sLog ≥ 1) && (xMin ≥ 2) &&
  ok3 && okD0 && okN0p &&
  (Q ≤ Theta) &&
  (E + uN0p + 1 ≤ Q + lD0) &&
  IsNonDecreasing (xMin - 1) bs &&
  checkAllThresholdsCertified sLog bLog Theta E mMax wMin xMin 1 bs &&
  (sigma ≤ M) &&
  ((M - sigma) * lVal ≥ M * M)

theorem phiGeomTailSum_mono_len (B Theta E U0 : Nat) :
    ∀ n1 n2 s : Nat, n1 ≤ n2 ->
      phiGeomTailSum B Theta E U0 n1 s ≤ phiGeomTailSum B Theta E U0 n2 s
  | 0, _, _, _ => by simp [phiGeomTailSum]
  | n1 + 1, 0, _, h => by omega
  | n1 + 1, n2 + 1, s, h => by
    simp only [phiGeomTailSum]
    exact Nat.add_le_add_left (phiGeomTailSum_mono_len B Theta E U0 n1 n2 (s + 1) (by omega)) _

theorem sortedCyclicRhsSum_mono_m (B Theta E U0 j : Nat) :
    ∀ m1 m2 : Nat, m1 ≤ m2 ->
      sortedCyclicRhsSum B Theta E U0 m1 j ≤ sortedCyclicRhsSum B Theta E U0 m2 j := by
  intro m1 m2 hm
  unfold sortedCyclicRhsSum
  exact Nat.add_le_add_left (phiGeomTailSum_mono_len B Theta E U0 (m1 - j) (m2 - j) 1 (by omega)) (j * U0)

theorem teleStepCap_mono_len (M : Nat) :
    ∀ (bPrev : Nat) (bcs : List (Nat × Nat)) (l1 l2 : Nat),
      l1 ≤ l2 -> teleStepCap M bPrev bcs l1 ≤ teleStepCap M bPrev bcs l2
  | bPrev, [], l1, l2, hl => by
    simp only [teleStepCap]
    exact Nat.mul_le_mul_right (stepU M bPrev) hl
  | bPrev, (b, c) :: rest, l1, l2, hl => by
    simp only [teleStepCap]
    exact Nat.add_le_add_left (teleStepCap_mono_len M b rest l1 l2 hl) _

theorem buildIndexedPairs_fst : ∀ (j : Nat) (bs : List Nat),
    (buildIndexedPairs j bs).map Prod.fst = bs
  | _, [] => rfl
  | j, b :: rest => by simp [buildIndexedPairs, buildIndexedPairs_fst (j + 1) rest]

theorem countLe_zero_of_lt {b : Nat} : ∀ (xs : List Nat),
    (∀ x ∈ xs, x ≥ b + 1) -> countLe b xs = 0
  | [], _ => rfl
  | x :: tl, hfl => by
    have hx : ¬ (x ≤ b) := by have := hfl x (List.Mem.head _); omega
    simp [countLe, hx, countLe_zero_of_lt tl (fun y hy => hfl y (List.Mem.tail _ hy))]

theorem checkAllThresholds_implies_counts
    {steps : List SpiralStepData}
    {sLog bLog Theta lD0 uN0p E mMax wMin xMin : Nat}
    (hcyc : IsNontrivialSpiralCycle steps)
    (hm_le : steps.length ≤ mMax)
    (hw_ge : wMin ≤ spiralChainTotalW steps)
    (hfl : ∀ s ∈ steps, s.x ≥ xMin) (hxmin_ge2 : xMin ≥ 2)
    (hTheta : phiLog bLog 3 < Theta) (hTheta_gt : 2 ^ bLog ≤ Theta)
    (hD0 : lD0 ≤ phiLog bLog (3 * (xMin + 1)))
    (hN0p : phiLog bLog (3 * xMin + 5) < uN0p)
    (hE : E + uN0p + 1 ≤ 2 ^ bLog + lD0) :
    ∀ (j : Nat) (bs : List Nat),
      j ≥ 1 ->
      checkAllThresholdsCertified sLog bLog Theta E mMax wMin xMin j bs = true ->
      ∀ bc ∈ buildIndexedPairs j bs, countLe bc.1 (spiralVertices steps) ≤ bc.2
  | _, [], _, _, _, hmem => by cases hmem
  | j, b :: rest, hj1, hok, bc, hmem => by
    simp only [checkAllThresholdsCertified, Bool.and_eq_true] at hok
    cases hmem with
    | head _ =>
      dsimp only
      by_cases hb_low : b ≤ xMin - 1
      · have hzero : countLe b (spiralVertices steps) = 0 := by
          apply countLe_zero_of_lt
          intro x hx
          rcases List.mem_map.mp hx with ⟨s, hs, rfl⟩
          have := hfl s hs
          omega
        omega
      · by_cases hjm : j ≤ steps.length
        · have hok1 := hok.1
          simp only [hb_low, ↓reduceIte] at hok1
          rcases hcert : certifyLog2Pow sLog bLog (b + 1) with ⟨lP, uP, okL⟩
          rw [hcert] at hok1
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hok1
          rcases hok1 with ⟨⟨⟨hokL, _⟩, hgrow⟩, hrhs⟩
          rw [sortedCyclicRhsFast_eq] at hrhs
          have hcs := certifyLog2Pow_sound sLog bLog (b + 1) (by rw [hcert]; exact hokL)
          rw [hcert] at hcs
          have hb_u0 : phiLog bLog (b + 1) ≤ uP - 1 := by omega
          have hrhs_m : sortedCyclicRhsSum bLog Theta E (uP - 1) steps.length j <
              2 ^ bLog * spiralChainTotalW steps := by
            have hm1 := sortedCyclicRhsSum_mono_m bLog Theta E (uP - 1) j steps.length mMax hm_le
            have hm2 := Nat.mul_le_mul_left (2 ^ bLog) hw_ge
            omega
          exact sortedCyclic_countLe_bound hj1 hjm hcyc hfl (by omega)
            hTheta hTheta_gt hD0 hN0p hE hgrow hb_u0 hrhs_m
        · -- If steps.length < j, countLe b xs <= xs.length = steps.length <= j - 1 AUTOMATICALLY!
          have hlen : countLe b (spiralVertices steps) ≤ (spiralVertices steps).length :=
            countLe_le_length b _
          have hl2 : (spiralVertices steps).length = steps.length := by simp [spiralVertices]
          omega
    | tail _ htl =>
      exact checkAllThresholds_implies_counts hcyc hm_le hw_ge hfl hxmin_ge2
        hTheta hTheta_gt hD0 hN0p hE (j + 1) rest (by omega) hok.2 bc htl

/--
  Master Soundness Theorem of `checkSlabEliminated`:
  Whenever `checkSlabEliminated sLog bLog sPow mMax wMin xMin lVal bs = true`, NO non-trivial
  spiral cycle of length `<= mMax`, odd weight `>= wMin`, vertex floor `>= xMin`, and
  power ratio `lVal * 3^W <= 2^sPow * 2^K` can exist!
-/
theorem checkSlabEliminated_sound
    {steps : List SpiralStepData}
    {sLog bLog sPow mMax wMin xMin lVal : Nat} {bs : List Nat}
    (hok : checkSlabEliminated sLog bLog sPow mMax wMin xMin lVal bs = true)
    (hcyc : IsNontrivialSpiralCycle steps)
    (hm_le : steps.length ≤ mMax)
    (hw_ge : wMin ≤ spiralChainTotalW steps)
    (hfl : ∀ s ∈ steps, s.x ≥ xMin)
    (hratio : lVal * 3 ^ spiralChainTotalW steps ≤ 2 ^ sPow * 2 ^ spiralChainTotalK steps) :
    False := by
  unfold checkSlabEliminated at hok
  rcases hc3 : certifyLog2Pow sLog bLog 3 with ⟨_, Theta, ok3⟩
  rcases hcD : certifyLog2Pow sLog bLog (3 * (xMin + 1)) with ⟨lD0, _, okD0⟩
  rcases hcN : certifyLog2Pow sLog bLog (3 * xMin + 5) with ⟨_, uN0p, okN0p⟩
  rw [hc3, hcD, hcN] at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  rcases hok with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hsLog, hxMin⟩, hok3⟩, hokD⟩, hokN⟩, hQTheta⟩, hE⟩, hnd⟩, hchk⟩, hsigM⟩, hfin⟩
  have hs3 := certifyLog2Pow_sound sLog bLog 3 (by rw [hc3]; exact hok3)
  rw [hc3] at hs3
  have hsD := certifyLog2Pow_sound sLog bLog (3 * (xMin + 1)) (by rw [hcD]; exact hokD)
  rw [hcD] at hsD
  have hsN := certifyLog2Pow_sound sLog bLog (3 * xMin + 5) (by rw [hcN]; exact hokN)
  rw [hcN] at hsN
  let E := 2 ^ bLog - (uN0p - lD0 + 1)
  let bcs := buildIndexedPairs 1 bs
  have hcnt := checkAllThresholds_implies_counts hcyc hm_le hw_ge hfl hxMin
    hs3.2.1 hQTheta hsD.1 hsN.2.1 hE 1 bs (by omega) hchk
  have hnd_bcs : IsNonDecreasing (xMin - 1) (bcs.map Prod.fst) = true := by
    dsimp [bcs]; rwa [buildIndexedPairs_fst]
  have hxs_fl : ∀ x ∈ spiralVertices steps, x ≥ (xMin - 1) + 1 := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨s, hs, rfl⟩
    have := hfl s hs; omega
  let M := 2 ^ sPow
  have hM_pos : M ≥ 1 := pow2_pos_nat sPow
  have hlen_xs : (spiralVertices steps).length ≤ mMax := by
    simpa [spiralVertices] using hm_le
  have hcap_le_sigma : teleStepCap M (xMin - 1) bcs (spiralVertices steps).length ≤
      teleStepCap M (xMin - 1) bcs mMax :=
    teleStepCap_mono_len M (xMin - 1) bcs _ mMax hlen_xs
  have hbern := teleBernoulli_ratio_bound M (xMin - 1) bcs (spiralVertices steps)
    hM_pos hxs_fl hnd_bcs hcnt (Nat.le_trans hcap_le_sigma hsigM)
  have hsub_ge : M - teleStepCap M (xMin - 1) bcs mMax ≤
      M - teleStepCap M (xMin - 1) bcs (spiralVertices steps).length := by omega
  have hbern_max : (M - teleStepCap M (xMin - 1) bcs mMax) *
        prodList ((spiralVertices steps).map (fun x => x + 1)) ≤
      M * prodList (spiralVertices steps) :=
    Nat.le_trans (Nat.mul_le_mul_right _ hsub_ge) hbern
  rcases spiralCycle_global_prod_bounds hcyc with ⟨hprod_pos, _, hglob_hi⟩
  -- Contradiction!
  -- Multiply hglob_hi (<) by (M - sigma) * M (> 0 since (M - sigma) * lVal >= M * M >= 1!):
  let sigma := teleStepCap M (xMin - 1) bcs mMax
  have hfin_M : (M - sigma) * lVal ≥ M * M := hfin
  have hMsig_pos : M - sigma ≥ 1 := by
    apply Classical.byContradiction
    intro h0
    rw [show M - sigma = 0 by omega, Nat.zero_mul] at hfin_M
    have hMM : M * M ≥ 1 := Nat.mul_pos hM_pos hM_pos
    omega
  -- Multiply hratio (lVal * 3^W <= M * 2^K) by (M - sigma) * prodList xs:
  -- M^2 * 3^W * prod xs <= (M - sigma) * lVal * 3^W * prod xs <= (M - sigma) * M * 2^K * prod xs
  -- < M * 3^W * (M - sigma) * prod(xs + 1) <= M^2 * 3^W * prod xs !!
  let P := prodList (spiralVertices steps)
  let P1 := prodList ((spiralVertices steps).map (fun x => x + 1))
  let W := spiralChainTotalW steps
  let K := spiralChainTotalK steps
  have h1 : (M * M) * (3 ^ W * P) ≤ ((M - sigma) * lVal) * (3 ^ W * P) :=
    Nat.mul_le_mul_right (3 ^ W * P) hfin
  have h2 : ((M - sigma) * lVal) * (3 ^ W * P) ≤ (M - sigma) * (M * (2 ^ K * P)) := by
    have hm := Nat.mul_le_mul_left (M - sigma) (Nat.mul_le_mul_right P hratio)
    calc
      ((M - sigma) * lVal) * (3 ^ W * P)
          = (M - sigma) * ((lVal * 3 ^ W) * P) := by rw [Nat.mul_assoc, Nat.mul_assoc lVal]
      _ ≤ (M - sigma) * ((M * 2 ^ K) * P) := hm
      _ = (M - sigma) * (M * (2 ^ K * P)) := by rw [Nat.mul_assoc M]
  have h3 : (M - sigma) * (M * (2 ^ K * P)) < (M - sigma) * (M * (3 ^ W * P1)) :=
    Nat.mul_lt_mul_of_pos_left (Nat.mul_lt_mul_of_pos_left hglob_hi hM_pos) hMsig_pos
  have h4 : (M - sigma) * (M * (3 ^ W * P1)) ≤ (M * M) * (3 ^ W * P) := by
    calc
      (M - sigma) * (M * (3 ^ W * P1))
          = (M * 3 ^ W) * ((M - sigma) * P1) := by
            rw [← Nat.mul_assoc, Nat.mul_comm (M - sigma) M, Nat.mul_assoc M (M - sigma),
                ← Nat.mul_assoc (M - sigma), Nat.mul_comm (M - sigma) (3 ^ W),
                Nat.mul_assoc (3 ^ W), ← Nat.mul_assoc]
      _ ≤ (M * 3 ^ W) * (M * P) := Nat.mul_le_mul_left _ hbern_max
      _ = (M * M) * (3 ^ W * P) := by
            rw [Nat.mul_assoc M (3 ^ W), ← Nat.mul_assoc (3 ^ W) M, Nat.mul_comm (3 ^ W) M,
                Nat.mul_assoc M (3 ^ W), ← Nat.mul_assoc]
  have hlt_self := Nat.lt_of_le_of_lt (Nat.le_trans h1 h2) (Nat.lt_of_lt_of_le h3 h4)
  omega

-- ============================================================================
-- 13.4A Unimodular Convergent Slab Lemmas & Kernel Slab Certificates
-- ============================================================================

theorem pow_le_pow_pos_nat {a b : Nat} (ha : a ≥ 1) (hle : a ≤ b) :
    ∀ k : Nat, a ^ k ≤ b ^ k
  | 0 => by simp
  | k + 1 => by
    rw [Nat.pow_succ, Nat.pow_succ]
    exact Nat.mul_le_mul (pow_le_pow_pos_nat ha hle k) hle

theorem pow_lt_exp_cancel_nat {a x y : Nat} (ha : a ≥ 2) (hlt : a ^ x < a ^ y) : x < y := by
  apply Classical.byContradiction
  intro hge
  have hle : y ≤ x := by omega
  have hd : x = y + (x - y) := by omega
  rw [hd, Nat.pow_add] at hlt
  have hp : a ^ (x - y) ≥ 1 := pow_pos_nat a (x - y) (by omega)
  have hm := Nat.mul_le_mul_left (a ^ y) hp
  omega

theorem cross_exp_lt_of_pow23 {p0 q0 K W : Nat}
    (hq0 : q0 ≥ 1) (hW : W ≥ 1)
    (heven : 2 ^ p0 < 3 ^ q0) (hcyc : 3 ^ W < 2 ^ K) :
    p0 * W < K * q0 := by
  have h1 : (2 ^ p0) ^ W < (3 ^ q0) ^ W :=
    pow_lt_pow_pos_nat (pow2_pos_nat p0) heven W hW
  have h2 : (3 ^ W) ^ q0 < (2 ^ K) ^ q0 :=
    pow_lt_pow_pos_nat (pow3_pos_nat W) hcyc q0 hq0
  rw [pow_mul_exp_nat 2 p0 W, pow_mul_exp_nat 3 q0 W] at h1
  rw [pow_mul_exp_nat 3 W q0, pow_mul_exp_nat 2 K q0, Nat.mul_comm W q0] at h2
  exact pow_lt_exp_cancel_nat (by decide) (Nat.lt_trans h1 h2)

/--
  Master Unimodular Odd-Convergent Upper-Bound Ratio Theorem:
  Given consecutive convergents `(p0, q0)` (`2^p0 < 3^q0`) and `(p1, q1)` (`3^q1 < 2^p1`)
  with `p1 * q0 = p0 * q1 + 1`, EVERY `(K, W)` with `1 <= W < q1` and `3^W < 2^K` satisfies
  `2^p1 * 3^W < 2^K * 3^q1`!
-/
theorem unimodular_odd_upper_ratio {p0 q0 p1 q1 K W : Nat}
    (hq0 : q0 ≥ 1) (_hq1 : q1 ≥ 1)
    (hunim : p1 * q0 = p0 * q1 + 1)
    (heven : 2 ^ p0 < 3 ^ q0) (hodd : 3 ^ q1 < 2 ^ p1)
    (hW1 : W ≥ 1) (hW_lt : W < q1) (hcyc : 3 ^ W < 2 ^ K) :
    2 ^ p1 * 3 ^ W < 2 ^ K * 3 ^ q1 := by
  have hu_lt : p0 * W < K * q0 := cross_exp_lt_of_pow23 hq0 hW1 heven hcyc
  let u := K * q0 - p0 * W
  have hu_ge1 : u ≥ 1 := by dsimp [u]; omega
  -- Key identity: q0 * (K * q1) = q0 * (p1 * W) + (u * q1 - W)!
  have huq1_gt_W : W < u * q1 := by
    have hm : 1 * q1 ≤ u * q1 := Nat.mul_le_mul_right q1 hu_ge1
    omega
  have hid_K : q0 * (K * q1) = q0 * (p1 * W) + (u * q1 - W) := by
    have hmul_u : u * q1 + p0 * q1 * W = K * q0 * q1 := by
      have hsub : u + p0 * W = K * q0 := by dsimp [u]; omega
      have hm := congrArg (· * q1) hsub
      rw [Nat.add_mul, Nat.mul_comm (p0 * W) q1, ← Nat.mul_assoc q1 p0 W,
          Nat.mul_comm q1 p0] at hm
      exact hm
    have hp1W : (p1 * q0) * W = p0 * q1 * W + W := by
      rw [hunim, Nat.add_mul, Nat.one_mul]
    calc
      q0 * (K * q1) = K * q0 * q1 := by
        rw [← Nat.mul_assoc, Nat.mul_comm q0 K]
      _ = u * q1 + p0 * q1 * W := hmul_u.symm
      _ = (p0 * q1 * W + W) + (u * q1 - W) := by omega
      _ = (p1 * q0) * W + (u * q1 - W) := by rw [hp1W]
      _ = q0 * (p1 * W) + (u * q1 - W) := by
        rw [Nat.mul_comm p1 q0, Nat.mul_assoc]
  have hp1W_lt : p1 * W < K * q1 := by
    apply Classical.byContradiction
    intro hge
    have hm := Nat.mul_le_mul_left q0 (show K * q1 ≤ p1 * W by omega)
    omega
  let t := K * q1 - p1 * W
  have ht_ge1 : t ≥ 1 := by dsimp [t]; omega
  have hW_eq : W + t * q0 = u * q1 := by
    have h1 : q0 * t = u * q1 - W := by
      have hs : K * q1 = p1 * W + t := by dsimp [t]; omega
      rw [hs, Nat.mul_add] at hid_K
      omega
    rw [Nat.mul_comm t q0, h1]; omega
  have hK_eq : K + t * p0 = u * p1 := by
    -- Multiply by q0 and cancel q0 >= 1!
    have hq0_lhs : q0 * (K + t * p0) = q0 * (u * p1) := by
      have ht_q0 : q0 * t = u * q1 - W := by
        have hs : K * q1 = p1 * W + t := by dsimp [t]; omega
        rw [hs, Nat.mul_add] at hid_K; omega
      have htp0 : q0 * (t * p0) = (u * q1 - W) * p0 := by
        rw [← Nat.mul_assoc, ht_q0]
      have hu_def : K * q0 = u + p0 * W := by dsimp [u]; omega
      calc
        q0 * (K + t * p0) = K * q0 + q0 * (t * p0) := by
          rw [Nat.mul_add, Nat.mul_comm q0 K]
        _ = u + p0 * W + (u * q1 - W) * p0 := by rw [hu_def, htp0]
        _ = u + (W * p0 + (u * q1 - W) * p0) := by rw [Nat.mul_comm p0 W, Nat.add_assoc]
        _ = u + u * q1 * p0 := by
          rw [← Nat.add_mul W (u * q1 - W) p0, show W + (u * q1 - W) = u * q1 by omega]
        _ = u * (p0 * q1 + 1) := by
          rw [Nat.mul_add, Nat.mul_one, Nat.mul_assoc u q1 p0, Nat.mul_comm q1 p0,
              ← Nat.mul_assoc, Nat.add_comm]
        _ = u * (p1 * q0) := by rw [← hunim]
        _ = q0 * (u * p1) := by
          rw [← Nat.mul_assoc u p1 q0, Nat.mul_comm (u * p1) q0]
    exact Nat.eq_of_mul_eq_mul_left hq0 hq0_lhs
  -- Now finish: 2^p1 * 3^(u*q1) <= 2^(u*p1) * 3^q1 and 2^(t*p0) < 3^(t*q0)!
  have hu_pow : 3 ^ ((u - 1) * q1) ≤ 2 ^ ((u - 1) * p1) := by
    rw [Nat.mul_comm (u - 1) q1, Nat.mul_comm (u - 1) p1,
        ← pow_mul_exp_nat 3 q1 (u - 1), ← pow_mul_exp_nat 2 p1 (u - 1)]
    exact pow_le_pow_pos_nat (pow3_pos_nat q1) (Nat.le_of_lt hodd) (u - 1)
  have hu_step : 2 ^ p1 * 3 ^ (u * q1) ≤ 2 ^ (u * p1) * 3 ^ q1 := by
    have hsplit_q : u * q1 = q1 + (u - 1) * q1 := by
      conv => lhs; rw [show u = 1 + (u - 1) by omega]; rw [Nat.add_mul, Nat.one_mul]
    have hsplit_p : u * p1 = p1 + (u - 1) * p1 := by
      conv => lhs; rw [show u = 1 + (u - 1) by omega]; rw [Nat.add_mul, Nat.one_mul]
    rw [hsplit_q, hsplit_p, Nat.pow_add 3, Nat.pow_add 2]
    have hm := Nat.mul_le_mul_left (2 ^ p1 * 3 ^ q1) hu_pow
    calc
      2 ^ p1 * (3 ^ q1 * 3 ^ ((u - 1) * q1))
          = (2 ^ p1 * 3 ^ q1) * 3 ^ ((u - 1) * q1) := by rw [← Nat.mul_assoc]
      _ ≤ (2 ^ p1 * 3 ^ q1) * 2 ^ ((u - 1) * p1) := hm
      _ = (2 ^ p1 * 2 ^ ((u - 1) * p1)) * 3 ^ q1 := by
            rw [Nat.mul_assoc (2 ^ p1), Nat.mul_comm (3 ^ q1), ← Nat.mul_assoc]
  have ht_pow : 2 ^ (t * p0) < 3 ^ (t * q0) := by
    rw [Nat.mul_comm t p0, Nat.mul_comm t q0, ← pow_mul_exp_nat 2 p0 t, ← pow_mul_exp_nat 3 q0 t]
    exact pow_lt_pow_pos_nat (pow2_pos_nat p0) heven t ht_ge1
  rw [← hW_eq, ← hK_eq, Nat.pow_add 3 W, Nat.pow_add 2 K] at hu_step
  -- hu_step : 2^p1 * (3^W * 3^(t*q0)) <= (2^K * 2^(t*p0)) * 3^q1 < (2^K * 3^q1) * 3^(t*q0)
  have hstrict : (2 ^ K * 2 ^ (t * p0)) * 3 ^ q1 < (2 ^ K * 3 ^ q1) * 3 ^ (t * q0) := by
    have hpos : 2 ^ K * 3 ^ q1 ≥ 1 := Nat.mul_pos (pow2_pos_nat K) (pow3_pos_nat q1)
    have hm := Nat.mul_lt_mul_of_pos_left ht_pow hpos
    rwa [Nat.mul_assoc (2 ^ K) (2 ^ (t * p0)) (3 ^ q1),
         Nat.mul_comm (2 ^ (t * p0)) (3 ^ q1), ← Nat.mul_assoc]
  have hcomb : (2 ^ p1 * 3 ^ W) * 3 ^ (t * q0) < (2 ^ K * 3 ^ q1) * 3 ^ (t * q0) := by
    rw [Nat.mul_assoc (2 ^ p1)]
    exact Nat.lt_of_le_of_lt hu_step hstrict
  apply Classical.byContradiction
  intro hge
  have hm := Nat.mul_le_mul_right (3 ^ (t * q0)) (show 2 ^ K * 3 ^ q1 ≤ 2 ^ p1 * 3 ^ W by omega)
  omega

/--
  Master Unimodular Unit-Slab Lower-Bound Ratio Theorem (for `q_{2k+1} = q_{2k-1} + q_{2k}`, e.g. `q43 = q41 + q42`):
  Given `(p1, q1)` (`3^q1 < 2^p1`) and `(p2, q2)` (`2^p2 < 3^q2`) with `p1 * q2 = p2 * q1 + 1`,
  EVERY `(K, W)` with `1 <= W < q1 + q2` and `3^W < 2^K` satisfies `2^p1 * 3^W <= 2^K * 3^q1`!
-/
theorem unimodular_unit_slab_ratio {p1 q1 p2 q2 K W : Nat}
    (_hq1 : q1 ≥ 1) (hq2 : q2 ≥ 1)
    (hunim : p1 * q2 = p2 * q1 + 1)
    (hodd : 3 ^ q1 < 2 ^ p1) (heven : 2 ^ p2 < 3 ^ q2)
    (hW1 : W ≥ 1) (hW_lt : W < q1 + q2) (hcyc : 3 ^ W < 2 ^ K) :
    2 ^ p1 * 3 ^ W ≤ 2 ^ K * 3 ^ q1 := by
  have ha_lt : p2 * W < K * q2 := cross_exp_lt_of_pow23 hq2 hW1 heven hcyc
  let a := K * q2 - p2 * W
  have ha_ge1 : a ≥ 1 := by dsimp [a]; omega
  -- Identity: q2 * (K * q1 + W) = q2 * (W * p1) + a * q1? Check!
  -- a * q1 = (K * q2 - p2 * W) * q1 = K * q2 * q1 - p2 * q1 * W = K * q2 * q1 - (p1 * q2 - 1) * W
  --        = q2 * (K * q1) - q2 * (p1 * W) + W!
  -- Wait: if p1 * W > K * q1, let b = p1 * W - K * q1 >= 1, then a * q1 + q2 * b = W >= q1 + q2, contradiction!
  have hb_nonpos : p1 * W ≤ K * q1 := by
    apply Classical.byContradiction
    intro hgt
    let b := p1 * W - K * q1
    have hb1 : b ≥ 1 := by dsimp [b]; omega
    have ha_eq : a + p2 * W = K * q2 := by dsimp [a]; omega
    have hb_eq : K * q1 + b = p1 * W := by dsimp [b]; omega
    have h1 := congrArg (· * q1) ha_eq
    have h2 := congrArg (· * q2) hb_eq
    rw [Nat.add_mul, Nat.mul_assoc p2 W q1, Nat.mul_comm W q1, ← Nat.mul_assoc p2 q1 W] at h1
    rw [Nat.add_mul, Nat.mul_assoc K q1 q2, Nat.mul_comm q1 q2, ← Nat.mul_assoc K q2 q1,
        Nat.mul_assoc p1 W q2, Nat.mul_comm W q2, ← Nat.mul_assoc p1 q2 W, hunim,
        Nat.add_mul, Nat.one_mul] at h2
    have hW_eq_ab : a * q1 + b * q2 = W := by omega
    have haq : q1 ≤ a * q1 := by simpa using Nat.mul_le_mul_right q1 ha_ge1
    have hbq : q2 ≤ b * q2 := by simpa using Nat.mul_le_mul_right q2 hb1
    omega
  let s := K * q1 - p1 * W
  have ha_eq : a + p2 * W = K * q2 := by dsimp [a]; omega
  have hs_eq : p1 * W + s = K * q1 := by dsimp [s]; omega
  have hW_eq : W + s * q2 = a * q1 := by
    have h1 := congrArg (· * q1) ha_eq
    have h2 := congrArg (· * q2) hs_eq
    rw [Nat.add_mul, Nat.mul_assoc p2 W q1, Nat.mul_comm W q1, ← Nat.mul_assoc p2 q1 W] at h1
    rw [Nat.add_mul, Nat.mul_assoc p1 W q2, Nat.mul_comm W q2, ← Nat.mul_assoc p1 q2 W,
        hunim, Nat.add_mul, Nat.one_mul, Nat.mul_assoc K q1 q2, Nat.mul_comm q1 q2,
        ← Nat.mul_assoc K q2 q1] at h2
    omega
  have hK_eq : K + s * p2 = a * p1 := by
    have hq2_eq : q2 * (K + s * p2) = q2 * (a * p1) := by
      calc
        q2 * (K + s * p2)
            = K * q2 + s * q2 * p2 := by
              rw [Nat.mul_add, Nat.mul_comm q2 K, Nat.mul_comm q2 (s * p2),
                  Nat.mul_assoc s p2 q2, Nat.mul_comm p2 q2, ← Nat.mul_assoc]
        _ = (a + p2 * W) + s * q2 * p2 := by rw [← ha_eq]
        _ = a + (W + s * q2) * p2 := by
              rw [Nat.add_mul W (s * q2) p2, Nat.mul_comm W p2, Nat.add_assoc]
        _ = a + (a * q1) * p2 := by rw [hW_eq]
        _ = a * (p2 * q1 + 1) := by
              rw [Nat.mul_add, Nat.mul_one, Nat.mul_assoc a q1 p2, Nat.mul_comm q1 p2,
                  Nat.add_comm]
        _ = a * (p1 * q2) := by rw [← hunim]
        _ = q2 * (a * p1) := by rw [← Nat.mul_assoc a p1 q2, Nat.mul_comm (a * p1) q2]
    exact Nat.eq_of_mul_eq_mul_left hq2 hq2_eq
  -- Finish: 2^p1 * 3^(a*q1) <= 2^(a*p1) * 3^q1 and 2^(s*p2) <= 3^(s*q2)!
  have ha_pow : 3 ^ ((a - 1) * q1) ≤ 2 ^ ((a - 1) * p1) := by
    rw [Nat.mul_comm (a - 1) q1, Nat.mul_comm (a - 1) p1,
        ← pow_mul_exp_nat 3 q1 (a - 1), ← pow_mul_exp_nat 2 p1 (a - 1)]
    exact pow_le_pow_pos_nat (pow3_pos_nat q1) (Nat.le_of_lt hodd) (a - 1)
  have ha_step : 2 ^ p1 * 3 ^ (a * q1) ≤ 2 ^ (a * p1) * 3 ^ q1 := by
    have hsplit_q : a * q1 = q1 + (a - 1) * q1 := by
      conv => lhs; rw [show a = 1 + (a - 1) by omega]; rw [Nat.add_mul, Nat.one_mul]
    have hsplit_p : a * p1 = p1 + (a - 1) * p1 := by
      conv => lhs; rw [show a = 1 + (a - 1) by omega]; rw [Nat.add_mul, Nat.one_mul]
    rw [hsplit_q, hsplit_p, Nat.pow_add 3, Nat.pow_add 2]
    have hm := Nat.mul_le_mul_left (2 ^ p1 * 3 ^ q1) ha_pow
    calc
      2 ^ p1 * (3 ^ q1 * 3 ^ ((a - 1) * q1))
          = (2 ^ p1 * 3 ^ q1) * 3 ^ ((a - 1) * q1) := by rw [← Nat.mul_assoc]
      _ ≤ (2 ^ p1 * 3 ^ q1) * 2 ^ ((a - 1) * p1) := hm
      _ = (2 ^ p1 * 2 ^ ((a - 1) * p1)) * 3 ^ q1 := by
            rw [Nat.mul_assoc (2 ^ p1), Nat.mul_comm (3 ^ q1), ← Nat.mul_assoc]
  have hs_pow : 2 ^ (s * p2) ≤ 3 ^ (s * q2) := by
    rw [Nat.mul_comm s p2, Nat.mul_comm s q2, ← pow_mul_exp_nat 2 p2 s, ← pow_mul_exp_nat 3 q2 s]
    exact pow_le_pow_pos_nat (pow2_pos_nat p2) (Nat.le_of_lt heven) s
  rw [← hW_eq, ← hK_eq, Nat.pow_add 3 W, Nat.pow_add 2 K] at ha_step
  have hle_r : (2 ^ K * 2 ^ (s * p2)) * 3 ^ q1 ≤ (2 ^ K * 3 ^ q1) * 3 ^ (s * q2) := by
    have hm := Nat.mul_le_mul_left (2 ^ K * 3 ^ q1) hs_pow
    rwa [Nat.mul_assoc (2 ^ K) (2 ^ (s * p2)) (3 ^ q1),
         Nat.mul_comm (2 ^ (s * p2)) (3 ^ q1), ← Nat.mul_assoc]
  have hcomb : (2 ^ p1 * 3 ^ W) * 3 ^ (s * q2) ≤ (2 ^ K * 3 ^ q1) * 3 ^ (s * q2) := by
    rw [Nat.mul_assoc (2 ^ p1)]
    exact Nat.le_trans ha_step hle_r
  exact Nat.le_of_mul_le_mul_right hcomb (pow3_pos_nat (s * q2))

/--
  Master Unimodular Decomposition for `[q43, q45)` using `(p43, q43)` and `(p44, q44)`
  (`p43 * q44 = p44 * q43 + 1`, `37 * q43 < q44`, `3^q43 < 2^p43`, `2^p44 < 3^q44`):
  For ANY `(K, W)` with `q43 <= W` and `3^W < 2^K`, one of 4 exhaustive cases holds:
  1. `(K, W) = (p43, q43)` (`u = 1, v = 0`),
  2. `W >= 2 * q43 ∧ 2^p43 * 3^W <= 2^K * 3^q43` (`u >= 2, v = 0`),
  3. `W >= q43 + q44` (`v >= 1`),
  4. `2^(39 * p43) * 3^W < 2^K * 3^(39 * q43)` (`v <= -1`, which forces `u >= 39`!).
-/
theorem unimodular_q43_cases {p1 q1 p2 q2 K W : Nat}
    (hq1 : q1 ≥ 1) (hq2 : q2 ≥ 1)
    (hunim : p1 * q2 = p2 * q1 + 1)
    (hgap37 : 37 * q1 < q2)
    (hodd : 3 ^ q1 < 2 ^ p1) (heven : 2 ^ p2 < 3 ^ q2)
    (hW_ge : q1 ≤ W) (hcyc : 3 ^ W < 2 ^ K) :
    (K = p1 ∧ W = q1) ∨
    (W ≥ 2 * q1 ∧ 2 ^ p1 * 3 ^ W ≤ 2 ^ K * 3 ^ q1) ∨
    (W ≥ q1 + q2) ∨
    (2 ^ (39 * p1) * 3 ^ W < 2 ^ K * 3 ^ (39 * q1)) := by
  have hu_lt : p2 * W < K * q2 := cross_exp_lt_of_pow23 hq2 (by omega) heven hcyc
  let u := K * q2 - p2 * W
  have hu_ge1 : u ≥ 1 := by dsimp [u]; omega
  have hu_eq : u + p2 * W = K * q2 := by dsimp [u]; omega
  by_cases hv_pos : K * q1 < p1 * W
  · -- Case v >= 1: W = u * q1 + v * q2 >= q1 + q2!
    let v := p1 * W - K * q1
    have hv1 : v ≥ 1 := by dsimp [v]; omega
    have hv_eq : K * q1 + v = p1 * W := by dsimp [v]; omega
    have h1 := congrArg (· * q1) hu_eq
    have h2 := congrArg (· * q2) hv_eq
    rw [Nat.add_mul, Nat.mul_assoc p2 W q1, Nat.mul_comm W q1, ← Nat.mul_assoc p2 q1 W] at h1
    rw [Nat.add_mul, Nat.mul_assoc K q1 q2, Nat.mul_comm q1 q2, ← Nat.mul_assoc K q2 q1,
        Nat.mul_assoc p1 W q2, Nat.mul_comm W q2, ← Nat.mul_assoc p1 q2 W,
        hunim, Nat.add_mul, Nat.one_mul] at h2
    have hW_uv : u * q1 + v * q2 = W := by omega
    have huq : q1 ≤ u * q1 := by simpa using Nat.mul_le_mul_right q1 hu_ge1
    have hvq : q2 ≤ v * q2 := by simpa using Nat.mul_le_mul_right q2 hv1
    exact Or.inr (Or.inr (Or.inl (by omega)))
  · let s := K * q1 - p1 * W
    have hs_eq : p1 * W + s = K * q1 := by dsimp [s]; omega
    have hW_eq : W + s * q2 = u * q1 := by
      have h1 := congrArg (· * q1) hu_eq
      have h2 := congrArg (· * q2) hs_eq
      rw [Nat.add_mul, Nat.mul_assoc p2 W q1, Nat.mul_comm W q1, ← Nat.mul_assoc p2 q1 W] at h1
      rw [Nat.add_mul, Nat.mul_assoc p1 W q2, Nat.mul_comm W q2, ← Nat.mul_assoc p1 q2 W,
          hunim, Nat.add_mul, Nat.one_mul, Nat.mul_assoc K q1 q2, Nat.mul_comm q1 q2,
          ← Nat.mul_assoc K q2 q1] at h2
      omega
    have hK_eq : K + s * p2 = u * p1 := by
      have hq2_eq : q2 * (K + s * p2) = q2 * (u * p1) := by
        calc
          q2 * (K + s * p2)
              = K * q2 + s * q2 * p2 := by
                rw [Nat.mul_add, Nat.mul_comm q2 K, Nat.mul_comm q2 (s * p2),
                    Nat.mul_assoc s p2 q2, Nat.mul_comm p2 q2, ← Nat.mul_assoc]
          _ = (u + p2 * W) + s * q2 * p2 := by rw [← hu_eq]
          _ = u + (W + s * q2) * p2 := by
                rw [Nat.add_mul W (s * q2) p2, Nat.mul_comm W p2, Nat.add_assoc]
          _ = u + (u * q1) * p2 := by rw [hW_eq]
          _ = u * (p2 * q1 + 1) := by
                rw [Nat.mul_add, Nat.mul_one, Nat.mul_assoc u q1 p2, Nat.mul_comm q1 p2,
                    Nat.add_comm]
          _ = u * (p1 * q2) := by rw [← hunim]
          _ = q2 * (u * p1) := by rw [← Nat.mul_assoc u p1 q2, Nat.mul_comm (u * p1) q2]
      exact Nat.eq_of_mul_eq_mul_left hq2 hq2_eq
    by_cases hs0 : s = 0
    · -- Case v = 0: W = u * q1, K = u * p1!
      rw [hs0, Nat.zero_mul, Nat.add_zero] at hW_eq hK_eq
      by_cases hu1 : u = 1
      · rw [hu1, Nat.one_mul] at hW_eq hK_eq
        exact Or.inl ⟨hK_eq, hW_eq⟩
      · have hu2 : u ≥ 2 := by omega
        refine Or.inr (Or.inl ⟨?_, ?_⟩)
        · rw [hW_eq]; exact Nat.mul_le_mul_right q1 hu2
        · rw [hW_eq, hK_eq]
          have hpow : 3 ^ ((u - 1) * q1) ≤ 2 ^ ((u - 1) * p1) := by
            rw [Nat.mul_comm (u - 1) q1, Nat.mul_comm (u - 1) p1,
                ← pow_mul_exp_nat 3 q1 (u - 1), ← pow_mul_exp_nat 2 p1 (u - 1)]
            exact pow_le_pow_pos_nat (pow3_pos_nat q1) (Nat.le_of_lt hodd) (u - 1)
          have hsq : u * q1 = q1 + (u - 1) * q1 := by
            conv => lhs; rw [show u = 1 + (u - 1) by omega]; rw [Nat.add_mul, Nat.one_mul]
          have hsp : u * p1 = p1 + (u - 1) * p1 := by
            conv => lhs; rw [show u = 1 + (u - 1) by omega]; rw [Nat.add_mul, Nat.one_mul]
          rw [hsq, hsp, Nat.pow_add 3, Nat.pow_add 2]
          have hm := Nat.mul_le_mul_left (2 ^ p1 * 3 ^ q1) hpow
          calc
            2 ^ p1 * (3 ^ q1 * 3 ^ ((u - 1) * q1))
                = (2 ^ p1 * 3 ^ q1) * 3 ^ ((u - 1) * q1) := by rw [← Nat.mul_assoc]
            _ ≤ (2 ^ p1 * 3 ^ q1) * 2 ^ ((u - 1) * p1) := hm
            _ = (2 ^ p1 * 2 ^ ((u - 1) * p1)) * 3 ^ q1 := by
                  rw [Nat.mul_assoc (2 ^ p1), Nat.mul_comm (3 ^ q1), ← Nat.mul_assoc]
    · -- Case s >= 1: W + s * q2 = u * q1 >= q1 + q2 > 38 * q1, so u >= 39!
      have hs1 : s ≥ 1 := by omega
      have hsq2 : q2 ≤ s * q2 := by simpa using Nat.mul_le_mul_right q2 hs1
      have hu39 : u ≥ 39 := by
        apply Classical.byContradiction
        intro hlt39
        have hm : u * q1 ≤ 38 * q1 := Nat.mul_le_mul_right q1 (by omega)
        omega
      refine Or.inr (Or.inr (Or.inr ?_))
      have hu_pow : 3 ^ ((u - 39) * q1) ≤ 2 ^ ((u - 39) * p1) := by
        rw [Nat.mul_comm (u - 39) q1, Nat.mul_comm (u - 39) p1,
            ← pow_mul_exp_nat 3 q1 (u - 39), ← pow_mul_exp_nat 2 p1 (u - 39)]
        exact pow_le_pow_pos_nat (pow3_pos_nat q1) (Nat.le_of_lt hodd) (u - 39)
      have hu_step : 2 ^ (39 * p1) * 3 ^ (u * q1) ≤ 2 ^ (u * p1) * 3 ^ (39 * q1) := by
        have hsq : u * q1 = 39 * q1 + (u - 39) * q1 := by
          conv => lhs; rw [show u = 39 + (u - 39) by omega]; rw [Nat.add_mul]
        have hsp : u * p1 = 39 * p1 + (u - 39) * p1 := by
          conv => lhs; rw [show u = 39 + (u - 39) by omega]; rw [Nat.add_mul]
        rw [hsq, hsp, Nat.pow_add 3, Nat.pow_add 2]
        have hm := Nat.mul_le_mul_left (2 ^ (39 * p1) * 3 ^ (39 * q1)) hu_pow
        calc
          2 ^ (39 * p1) * (3 ^ (39 * q1) * 3 ^ ((u - 39) * q1))
              = (2 ^ (39 * p1) * 3 ^ (39 * q1)) * 3 ^ ((u - 39) * q1) := by rw [← Nat.mul_assoc]
          _ ≤ (2 ^ (39 * p1) * 3 ^ (39 * q1)) * 2 ^ ((u - 39) * p1) := hm
          _ = (2 ^ (39 * p1) * 2 ^ ((u - 39) * p1)) * 3 ^ (39 * q1) := by
                rw [Nat.mul_assoc (2 ^ (39 * p1)), Nat.mul_comm (3 ^ (39 * q1)), ← Nat.mul_assoc]
      have hs_pow : 2 ^ (s * p2) < 3 ^ (s * q2) := by
        rw [Nat.mul_comm s p2, Nat.mul_comm s q2, ← pow_mul_exp_nat 2 p2 s, ← pow_mul_exp_nat 3 q2 s]
        exact pow_lt_pow_pos_nat (pow2_pos_nat p2) heven s hs1
      rw [← hW_eq, ← hK_eq, Nat.pow_add 3 W, Nat.pow_add 2 K] at hu_step
      have hstrict : (2 ^ K * 2 ^ (s * p2)) * 3 ^ (39 * q1) <
          (2 ^ K * 3 ^ (39 * q1)) * 3 ^ (s * q2) := by
        have hpos : 2 ^ K * 3 ^ (39 * q1) ≥ 1 :=
          Nat.mul_pos (pow2_pos_nat K) (pow3_pos_nat (39 * q1))
        have hm := Nat.mul_lt_mul_of_pos_left hs_pow hpos
        rwa [Nat.mul_assoc (2 ^ K) (2 ^ (s * p2)) (3 ^ (39 * q1)),
             Nat.mul_comm (2 ^ (s * p2)) (3 ^ (39 * q1)), ← Nat.mul_assoc]
      have hcomb : (2 ^ (39 * p1) * 3 ^ W) * 3 ^ (s * q2) <
          (2 ^ K * 3 ^ (39 * q1)) * 3 ^ (s * q2) := by
        rw [Nat.mul_assoc (2 ^ (39 * p1))]
        exact Nat.lt_of_le_of_lt hu_step hstrict
      apply Classical.byContradiction
      intro hge
      have hm := Nat.mul_le_mul_right (3 ^ (s * q2))
        (show 2 ^ K * 3 ^ (39 * q1) ≤ 2 ^ (39 * p1) * 3 ^ W by omega)
      omega

theorem pow2_lt_pow3_of_eval {S p q nbits : Nat}
    (hnb : nbits ≥ 1) (hp : p < 2 ^ nbits) (hq : q < 2 ^ nbits)
    (hU : (evalPow2Pow3Aux S p q nbits).2 ≤ 2 ^ S) :
    2 ^ p < 3 ^ q := by
  rcases evalPow2Pow3Aux_sound S p q nbits hnb hp hq with ⟨_, hhi⟩
  have hm : (evalPow2Pow3Aux S p q nbits).2 * 3 ^ q ≤ 2 ^ S * 3 ^ q :=
    Nat.mul_le_mul_right (3 ^ q) hU
  have hlt : 2 ^ S * 2 ^ p < 2 ^ S * 3 ^ q := Nat.lt_of_lt_of_le hhi hm
  apply Classical.byContradiction
  intro hge
  have hm2 := Nat.mul_le_mul_left (2 ^ S) (show 3 ^ q ≤ 2 ^ p by omega)
  omega

theorem pow3_lt_pow2_of_eval {S p q nbits : Nat}
    (hnb : nbits ≥ 1) (hp : p < 2 ^ nbits) (hq : q < 2 ^ nbits)
    (hL : 2 ^ S < (evalPow2Pow3Aux S p q nbits).1) :
    3 ^ q < 2 ^ p := by
  rcases evalPow2Pow3Aux_sound S p q nbits hnb hp hq with ⟨hlo, _⟩
  have hm : 2 ^ S * 3 ^ q < (evalPow2Pow3Aux S p q nbits).1 * 3 ^ q :=
    Nat.mul_lt_mul_of_pos_right hL (pow3_pos_nat q)
  have hlt : 2 ^ S * 3 ^ q < 2 ^ S * 2 ^ p := Nat.lt_of_lt_of_le hm hlo
  apply Classical.byContradiction
  intro hge
  have hm2 := Nat.mul_le_mul_left (2 ^ S) (show 2 ^ p ≤ 3 ^ q by omega)
  omega

theorem ratio_transfer_evalPow2Pow3 {S p q nbits K W : Nat}
    (hnb : nbits ≥ 1) (hp : p < 2 ^ nbits) (hq : q < 2 ^ nbits)
    (hratio : 2 ^ p * 3 ^ W ≤ 2 ^ K * 3 ^ q) :
    (evalPow2Pow3Aux S p q nbits).1 * 3 ^ W ≤ 2 ^ S * 2 ^ K := by
  rcases evalPow2Pow3Aux_sound S p q nbits hnb hp hq with ⟨hlo, _⟩
  let L := (evalPow2Pow3Aux S p q nbits).1
  have hm1 : (L * 3 ^ W) * 3 ^ q ≤ (2 ^ S * 2 ^ K) * 3 ^ q := by
    calc
      (L * 3 ^ W) * 3 ^ q
          = (L * 3 ^ q) * 3 ^ W := by
            rw [Nat.mul_assoc L, Nat.mul_comm (3 ^ W), ← Nat.mul_assoc]
      _ ≤ (2 ^ S * 2 ^ p) * 3 ^ W := Nat.mul_le_mul_right (3 ^ W) hlo
      _ = 2 ^ S * (2 ^ p * 3 ^ W) := by rw [Nat.mul_assoc]
      _ ≤ 2 ^ S * (2 ^ K * 3 ^ q) := Nat.mul_le_mul_left (2 ^ S) hratio
      _ = (2 ^ S * 2 ^ K) * 3 ^ q := by rw [← Nat.mul_assoc]
  exact Nat.le_of_mul_le_mul_right hm1 (pow3_pos_nat q)

-- ============================================================================
-- 13.4B Asymptotic `W >= q51` Baker Elimination & All 9 Slab Kernel Proofs
-- ============================================================================

def ceilScaleIter (B Theta : Nat) : Nat -> Nat -> Nat
  | 0, u => u
  | d + 1, u =>
    let prev := ceilScaleIter B Theta d u
    (Theta * prev + 2 ^ B - 1) / 2 ^ B

def ceilScaleSumAcc (B Theta : Nat) : Nat -> Nat -> Nat
  | 0, _ => 0
  | n + 1, cur => cur + ceilScaleSumAcc B Theta n ((Theta * cur + 2 ^ B - 1) / 2 ^ B)

theorem phiStepIter_le_mul_ceilScale (B Theta E k : Nat) :
    ∀ d : Nat, phiStepIter B Theta E d (k * 2 ^ B) ≤ k * ceilScaleIter B Theta d (2 ^ B)
  | 0 => by simp [phiStepIter, ceilScaleIter]
  | d + 1 => by
    simp only [phiStepIter, ceilScaleIter]
    have ih := phiStepIter_le_mul_ceilScale B Theta E k d
    let c := ceilScaleIter B Theta d (2 ^ B)
    have hm : Theta * phiStepIter B Theta E d (k * 2 ^ B) ≤ Theta * (k * c) :=
      Nat.mul_le_mul_left Theta ih
    have hdiv : (Theta * phiStepIter B Theta E d (k * 2 ^ B)) / 2 ^ B ≤
        (Theta * (k * c)) / 2 ^ B :=
      le_div_of_mul_le (pow2_pos_nat B) (Nat.le_trans (mul_div_le_nat _ _) hm)
    have hSub : (Theta * phiStepIter B Theta E d (k * 2 ^ B)) / 2 ^ B - E ≤
        (Theta * (k * c)) / 2 ^ B :=
      Nat.le_trans (Nat.sub_le _ _) hdiv
    have hCeil : Theta * c ≤ 2 ^ B * ((Theta * c + 2 ^ B - 1) / 2 ^ B) := by
      have hdm := Nat.div_add_mod (Theta * c + 2 ^ B - 1) (2 ^ B)
      have hlt := Nat.mod_lt (Theta * c + 2 ^ B - 1) (pow2_pos_nat B)
      have hp : 2 ^ B ≥ 1 := pow2_pos_nat B
      omega
    have hkCeil : Theta * (k * c) ≤ 2 ^ B * (k * ((Theta * c + 2 ^ B - 1) / 2 ^ B)) := by
      calc
        Theta * (k * c) = k * (Theta * c) := by
          rw [← Nat.mul_assoc, Nat.mul_comm Theta k, Nat.mul_assoc]
        _ ≤ k * (2 ^ B * ((Theta * c + 2 ^ B - 1) / 2 ^ B)) := Nat.mul_le_mul_left k hCeil
        _ = 2 ^ B * (k * ((Theta * c + 2 ^ B - 1) / 2 ^ B)) := by
          rw [← Nat.mul_assoc, Nat.mul_comm k (2 ^ B), Nat.mul_assoc]
    have hdiv2 : (Theta * (k * c)) / 2 ^ B ≤ k * ((Theta * c + 2 ^ B - 1) / 2 ^ B) := by
      apply Classical.byContradiction
      intro hgt
      have hmul1 : 2 ^ B * (k * ((Theta * c + 2 ^ B - 1) / 2 ^ B) + 1) ≤
          2 ^ B * ((Theta * (k * c)) / 2 ^ B) :=
        Nat.mul_le_mul_left (2 ^ B) (by omega)
      have hmul2 := mul_div_le_nat (Theta * (k * c)) (2 ^ B)
      rw [Nat.mul_add, Nat.mul_one] at hmul1
      have hp : 2 ^ B ≥ 1 := pow2_pos_nat B
      omega
    exact Nat.le_trans hSub hdiv2

theorem phiGeomTailSum_le_mul_ceilScaleAcc (B Theta E k : Nat) :
    ∀ n s : Nat,
      phiGeomTailSum B Theta E (k * 2 ^ B) n s ≤
        k * ceilScaleSumAcc B Theta n (ceilScaleIter B Theta s (2 ^ B))
  | 0, _ => by simp [phiGeomTailSum, ceilScaleSumAcc]
  | n + 1, s => by
    simp only [phiGeomTailSum, ceilScaleSumAcc, Nat.mul_add]
    have hhead := phiStepIter_le_mul_ceilScale B Theta E k s
    have ih := phiGeomTailSum_le_mul_ceilScaleAcc B Theta E k n (s + 1)
    simp only [ceilScaleIter] at ih
    exact Nat.add_le_add hhead ih

theorem mem_le_implies_countLe_pos (b : Nat) :
    ∀ (xs : List Nat), (∃ x ∈ xs, x ≤ b) -> countLe b xs ≥ 1
  | [], ⟨_, hx, _⟩ => by cases hx
  | y :: tl, ⟨x, hx, hle⟩ => by
    simp only [List.mem_cons] at hx
    simp only [countLe]
    rcases hx with rfl | hmem
    · simp [hle]
    · have ih := mem_le_implies_countLe_pos b tl ⟨x, hmem, hle⟩
      by_cases hy : y ≤ b <;> simp [hy] <;> omega

theorem exp_beats_baker_quad_aux :
    ∀ d : Nat, 2 ^ (25 + d) ≥ 12008 + 14 * (91 + d) ^ 2 + 28 * d + 2600
  | 0 => by decide
  | d + 1 => by
    have ih := exp_beats_baker_quad_aux d
    have hp : 2 ^ (25 + (d + 1)) = 2 ^ (25 + d) + 2 ^ (25 + d) := by
      rw [show 25 + (d + 1) = (25 + d) + 1 by omega, Nat.pow_succ]; omega
    have hsq : (91 + (d + 1)) ^ 2 = (91 + d) ^ 2 + 2 * d + 183 := by
      have hexp : ∀ x : Nat, (x + 1) ^ 2 = x ^ 2 + 2 * x + 1 := fun x => by
        simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul, Nat.mul_add, Nat.add_mul, Nat.mul_one]
        omega
      rw [show 91 + (d + 1) = (91 + d) + 1 by omega, hexp (91 + d)]
      omega
    rw [hp, hsq, Nat.mul_add, Nat.mul_add]
    omega

theorem exp_beats_baker_quad {r : Nat} (hr : r ≥ 88) :
    2 ^ (r - 63) - 8 > 12000 + 14 * (r + 3) ^ 2 := by
  have h := exp_beats_baker_quad_aux (r - 88)
  rw [show 25 + (r - 88) = r - 63 by omega, show 91 + (r - 88) = r + 3 by omega] at h
  omega

def q35Val : Nat := 397560349370386783
def q37Val : Nat := 4640282259296926456
def q39Val : Nat := 27444133206411171953
def q41Val : Nat := 77692117359936589403
def q42Val : Nat := 127940101513462006853
def p43Val : Nat := 325919355854421968365
def q43Val : Nat := 205632218873398596256
def p44Val : Nat := 12261796429850908150604
def q44Val : Nat := 7736332199829210068325
def p45Val : Nat := 49373105075258054570781
def q45Val : Nat := 31150961018190238869556
def p50Val : Nat := 278024068491311595647009290
def q50Val : Nat := 175413657020157229319631761
def p51Val : Nat := 550543198726409845420360681
def q51Val : Nat := 347354084702895683704606156

def exactM92B1 : Nat := 186580408057834151310020
def exactM92B2 : Nat := 3823138529586028606780131106118133922
def exactM92B3 : Nat := 4794396471396377644999217273995101736970907047130796553124

def barinaXMin : Nat := 2 ^ 71 + 1

def checkBakerQ51Props (B Theta lD0 uN0p : Nat) : Bool :=
  (2 ^ B ≤ Theta) &&
  (2 ^ B - (uN0p - lD0 + 1) + uN0p + 1 ≤ 2 ^ B + lD0) &&
  ((Theta - 2 ^ B) * (100 * 2 ^ B) ≥ 2 ^ B * (2 ^ B - (uN0p - lD0 + 1) + 1)) &&
  (2 ^ B + ceilScaleSumAcc B Theta 91 (ceilScaleIter B Theta 1 (2 ^ B)) + 2 ^ B ≤ 2 ^ 62 * 2 ^ B)

def checkBakerQ51Cert : Bool :=
  let (_, Theta, ok3) := certifyLog2Pow 160 140 3
  let (lD0, _, okD) := certifyLog2Pow 160 140 (3 * (barinaXMin + 1))
  let (_, uN0p, okN) := certifyLog2Pow 160 140 (3 * barinaXMin + 5)
  ok3 && okD && okN &&
  checkBakerQ51Props 140 Theta lD0 uN0p &&
  (2 ^ 88 ≤ q51Val)

set_option maxRecDepth 20000 in
theorem baker_q51_constants_certified : checkBakerQ51Cert = true := by
  decide

/--
  Parameterized Baker elimination helper (keeps `B`, `xMin`, `c62`, `N` symbolic so `omega`
  uses zero memory on big powers of 2!).
-/
theorem no_spiral_cycle_baker_core
    {steps : List SpiralStepData} {B Theta lD0 uN0p E xMin c62 N : Nat}
    (hbaker : BakerLMNPowerBound)
    (hcyc : IsNontrivialSpiralCycle steps)
    (hm_le : steps.length ≤ 92)
    (hfl : ∀ s ∈ steps, s.x ≥ xMin) (hxmin_pos : xMin ≥ 1)
    (hTheta : phiLog B 3 < Theta) (hTheta_gt : 2 ^ B ≤ Theta)
    (hD0 : lD0 ≤ phiLog B (3 * (xMin + 1)))
    (hN0p : phiLog B (3 * xMin + 5) < uN0p)
    (hE : E + uN0p + 1 ≤ 2 ^ B + lD0)
    (hgrow100 : (Theta - 2 ^ B) * (100 * 2 ^ B) ≥ 2 ^ B * (E + 1))
    (hscale : 2 ^ B + ceilScaleSumAcc B Theta 91 (ceilScaleIter B Theta 1 (2 ^ B)) + 2 ^ B ≤
      c62 * 2 ^ B)
    (hW_pos : spiralChainTotalW steps ≥ 2)
    (hN_ge100 : N ≥ 100)
    (hN_mul_W : c62 * N ≤ spiralChainTotalW steps)
    (hexp_gt : 12000 + 14 * (flog2 (spiralChainTotalW steps) + 3) ^ 2 < N - 8) :
    False := by
  let W := spiralChainTotalW steps
  let K := spiralChainTotalK steps
  have hm_ge1 : steps.length ≥ 1 := by
    cases steps with
    | nil => cases hcyc
    | cons _ _ => simp
  have hpN : 2 ^ N ≥ 1 := pow2_pos_nat N
  have hb_u0 : phiLog B ((2 ^ N - 1) + 1) ≤ N * 2 ^ B := by
    rw [show (2 ^ N - 1) + 1 = 2 ^ N by omega, phiLog_pow2 B N]
    exact Nat.le_refl _
  have hgrowN : (Theta - 2 ^ B) * (N * 2 ^ B) ≥ 2 ^ B * (E + 1) := by
    have hm : 100 * 2 ^ B ≤ N * 2 ^ B := Nat.mul_le_mul_right (2 ^ B) hN_ge100
    exact Nat.le_trans hgrow100 (Nat.mul_le_mul_left (Theta - 2 ^ B) hm)
  have hrhs_lt : sortedCyclicRhsSum B Theta E (N * 2 ^ B) steps.length 1 < 2 ^ B * W := by
    have hm_mono := sortedCyclicRhsSum_mono_m B Theta E (N * 2 ^ B) 1 steps.length 92 hm_le
    unfold sortedCyclicRhsSum at hm_mono ⊢
    simp only [Nat.one_mul, show 92 - 1 = 91 from rfl] at hm_mono
    have htail := phiGeomTailSum_le_mul_ceilScaleAcc B Theta E N 91 1
    have hsum_le : N * 2 ^ B + phiGeomTailSum B Theta E (N * 2 ^ B) 91 1 + N * 2 ^ B ≤
        N * (c62 * 2 ^ B) := by
      have hm := Nat.mul_le_mul_left N hscale
      rw [Nat.mul_add, Nat.mul_add] at hm
      omega
    have hNW : N * (c62 * 2 ^ B) ≤ 2 ^ B * W := by
      calc
        N * (c62 * 2 ^ B) = 2 ^ B * (c62 * N) := by
          rw [← Nat.mul_assoc, Nat.mul_comm N c62, Nat.mul_comm _ (2 ^ B)]
        _ ≤ 2 ^ B * W := Nat.mul_le_mul_left (2 ^ B) hN_mul_W
    have hNQ_pos : N * 2 ^ B ≥ 1 := Nat.mul_pos (by omega) (pow2_pos_nat B)
    omega
  have hcnt0 : countLe (2 ^ N - 1) (spiralVertices steps) ≤ 0 :=
    sortedCyclic_countLe_bound (by decide) hm_ge1 hcyc hfl hxmin_pos
      hTheta hTheta_gt hD0 hN0p hE hgrowN hb_u0 hrhs_lt
  have hxs_ge_2N : ∀ x ∈ spiralVertices steps, x ≥ (2 ^ N - 1) + 1 := by
    intro x hx
    apply Classical.byContradiction
    intro hlt
    have hge1 := mem_le_implies_countLe_pos (2 ^ N - 1) (spiralVertices steps) ⟨x, hx, by omega⟩
    omega
  have hstep1 : stepU (2 ^ N) (2 ^ N - 1) = 1 := by
    unfold stepU
    have hsub : (2 ^ N - 1) + 1 = 2 ^ N := by omega
    rw [hsub]
    apply Nat.le_antisymm
    · apply Classical.byContradiction
      intro hgt
      have hm := mul_div_le_nat (2 ^ N + (2 ^ N - 1)) (2 ^ N)
      have hm2 := Nat.mul_le_mul_left (2 ^ N) (show 2 ≤ (2 ^ N + (2 ^ N - 1)) / 2 ^ N by omega)
      omega
    · exact le_div_of_mul_le hpN (by omega)
  let xs := spiralVertices steps
  have hcap_le92 : teleStepCap (2 ^ N) (2 ^ N - 1) [] xs.length ≤ 92 := by
    simp only [teleStepCap, hstep1, Nat.mul_one]
    simpa [xs, spiralVertices] using hm_le
  have h2N_ge128 : 2 ^ N ≥ 128 := by
    have hm := pow2_mono_nat (show 7 ≤ N by omega)
    simpa using hm
  have hbern := teleBernoulli_ratio_bound (2 ^ N) (2 ^ N - 1) [] xs
    hpN hxs_ge_2N rfl (by intro _ h; cases h) (by omega)
  rcases spiralCycle_global_prod_bounds hcyc with ⟨hP_pos, hcyc_lt, hglob⟩
  have hsub92 : 2 ^ N - 92 ≤ 2 ^ N - teleStepCap (2 ^ N) (2 ^ N - 1) [] xs.length := by omega
  have hbern92 : (2 ^ N - 92) * prodList (xs.map (fun x => x + 1)) ≤ 2 ^ N * prodList xs :=
    Nat.le_trans (Nat.mul_le_mul_right _ hsub92) hbern
  have hlt1 : (2 ^ N - 92) * (2 ^ K * prodList xs) <
      (2 ^ N - 92) * (3 ^ W * prodList (xs.map (fun x => x + 1))) :=
    Nat.mul_lt_mul_of_pos_left hglob (by omega)
  have hle2 : (2 ^ N - 92) * (3 ^ W * prodList (xs.map (fun x => x + 1))) ≤
      (2 ^ N * 3 ^ W) * prodList xs := by
    calc
      (2 ^ N - 92) * (3 ^ W * prodList (xs.map (fun x => x + 1)))
          = 3 ^ W * ((2 ^ N - 92) * prodList (xs.map (fun x => x + 1))) := by
            rw [← Nat.mul_assoc, Nat.mul_comm (2 ^ N - 92) (3 ^ W), Nat.mul_assoc]
      _ ≤ 3 ^ W * (2 ^ N * prodList xs) := Nat.mul_le_mul_left _ hbern92
      _ = (2 ^ N * 3 ^ W) * prodList xs := by
            rw [← Nat.mul_assoc, Nat.mul_comm (3 ^ W) (2 ^ N)]
  have hprod_cancel : (2 ^ N - 92) * 2 ^ K < 2 ^ N * 3 ^ W := by
    have hcomb : ((2 ^ N - 92) * 2 ^ K) * prodList xs < (2 ^ N * 3 ^ W) * prodList xs := by
      rw [Nat.mul_assoc]
      exact Nat.lt_of_lt_of_le hlt1 hle2
    apply Classical.byContradiction
    intro hge
    have hm := Nat.mul_le_mul_right (prodList xs)
      (show 2 ^ N * 3 ^ W ≤ (2 ^ N - 92) * 2 ^ K by omega)
    omega
  have hdiff_bound : 2 ^ (N - 8) * (2 ^ K - 3 ^ W) ≤ 3 ^ W := by
    have h2N1 : 2 ^ (N - 1) ≤ 2 ^ N - 92 := by
      have hp : 2 ^ N = 2 ^ (N - 1) + 2 ^ (N - 1) := by
        calc
          2 ^ N = 2 ^ ((N - 1) + 1) := congrArg (2 ^ ·) (by omega)
          _ = 2 ^ (N - 1) * 2 := Nat.pow_succ _ _
          _ = 2 ^ (N - 1) + 2 ^ (N - 1) := by omega
      have h7 : 128 ≤ 2 ^ (N - 1) := by
        simpa using pow2_mono_nat (show 7 ≤ N - 1 by omega)
      omega
    have hm1 : 2 ^ (N - 1) * (2 ^ K - 3 ^ W) < 92 * 3 ^ W := by
      have hm := Nat.mul_le_mul_right (2 ^ K - 3 ^ W) h2N1
      have hlt_sub : (2 ^ N - 92) * (2 ^ K - 3 ^ W) < 92 * 3 ^ W := by
        have hlt_kw : 3 ^ W < 2 ^ K := hcyc_lt
        have hp3w : 3 ^ W ≥ 1 := pow3_pos_nat W
        rw [Nat.mul_sub_left_distrib]
        have hexp : (2 ^ N - 92) * 3 ^ W + 92 * 3 ^ W = 2 ^ N * 3 ^ W := by
          rw [← Nat.add_mul, show 2 ^ N - 92 + 92 = 2 ^ N by omega]
        omega
      exact Nat.lt_of_le_of_lt hm hlt_sub
    have hp8 : 2 ^ (N - 1) = 128 * 2 ^ (N - 8) := by
      rw [show (128 : Nat) = 2 ^ 7 from rfl, ← Nat.pow_add, show 7 + (N - 8) = N - 1 by omega]
    rw [hp8, Nat.mul_assoc] at hm1
    omega
  have hpow_le : 2 ^ (12000 + 14 * (flog2 W + 3) ^ 2) ≤ 2 ^ (N - 8) :=
    pow2_mono_nat (Nat.le_of_lt hexp_gt)
  have hbaker_le : 2 ^ (12000 + 14 * (flog2 W + 3) ^ 2) * (2 ^ K - 3 ^ W) ≤ 3 ^ W :=
    Nat.le_trans (Nat.mul_le_mul_right _ hpow_le) hdiff_bound
  have hbaker_gt := hbaker K W hW_pos hcyc_lt
  omega

theorem baker_N_bounds {W : Nat} (hW_pow88 : 2 ^ 88 ≤ W) :
    W ≥ 2 ∧
    W / 2 ^ 63 ≥ 100 ∧
    2 ^ 62 * (W / 2 ^ 63) ≤ W ∧
    12000 + 14 * (flog2 W + 3) ^ 2 < W / 2 ^ 63 - 8 := by
  have hW_pos : W ≥ 2 := Nat.le_trans (by decide : 2 ≤ 2 ^ 88) hW_pow88
  have hN100 : W / 2 ^ 63 ≥ 100 :=
    le_div_of_mul_le (pow2_pos_nat 63)
      (Nat.le_trans (by decide : 2 ^ 63 * 100 ≤ 2 ^ 88) hW_pow88)
  have hNmul : 2 ^ 62 * (W / 2 ^ 63) ≤ W := by
    have hm : 2 ^ 63 * (W / 2 ^ 63) ≤ W := mul_div_le_nat W (2 ^ 63)
    have hp : 2 ^ 63 = 2 ^ 62 * 2 := rfl
    rw [hp, Nat.mul_assoc] at hm
    exact Nat.le_trans
      (Nat.mul_le_mul_left (2 ^ 62) (Nat.le_mul_of_pos_left _ (by decide : 2 > 0))) hm
  rcases flog2_spec W (Nat.le_trans (by decide : 1 ≤ 2) hW_pos) with ⟨hr_lo, hr_hi⟩
  have hlt88 : 88 < flog2 W + 1 :=
    pow_lt_exp_cancel_nat (by decide) (Nat.lt_of_le_of_lt hW_pow88 hr_hi)
  have hr_ge88 : flog2 W ≥ 88 := Nat.le_of_lt_succ hlt88
  have h63 : 63 + (flog2 W - 63) = flog2 W := Nat.add_sub_of_le (Nat.le_trans (by decide : 63 ≤ 88) hr_ge88)
  have hNpow : 2 ^ (flog2 W - 63) ≤ W / 2 ^ 63 := by
    apply le_div_of_mul_le (pow2_pos_nat 63)
    rw [← Nat.pow_add, h63]
    exact hr_lo
  have hb := exp_beats_baker_quad hr_ge88
  have hexp : 12000 + 14 * (flog2 W + 3) ^ 2 < W / 2 ^ 63 - 8 :=
    Nat.lt_of_lt_of_le hb (Nat.sub_le_sub_right hNpow 8)
  exact ⟨hW_pos, hN100, hNmul, hexp⟩

/--
  Theorem 26.4a (Asymptotic `W >= q51` Elimination inside Lean 4 Kernel):
  Under `BarinaThreshold (2^71)` and `BakerLMNPowerBound`, NO non-trivial spiral cycle
  with `steps.length <= 92` and `spiralChainTotalW steps >= q51Val` can exist!
-/
theorem no_spiral_cycle_ge_q51 {steps : List SpiralStepData}
    (hbar : BarinaThreshold (2 ^ 71))
    (hbaker : BakerLMNPowerBound)
    (hcyc : IsNontrivialSpiralCycle steps)
    (hm_le : steps.length ≤ 92)
    (hw_ge : q51Val ≤ spiralChainTotalW steps) :
    False := by
  have hc := baker_q51_constants_certified
  unfold checkBakerQ51Cert at hc
  rcases hcert3 : certifyLog2Pow 160 140 3 with ⟨_, Theta, ok3⟩
  rcases hcertD : certifyLog2Pow 160 140 (3 * (barinaXMin + 1)) with ⟨lD0, _, okD⟩
  rcases hcertN : certifyLog2Pow 160 140 (3 * barinaXMin + 5) with ⟨_, uN0p, okN⟩
  rw [hcert3, hcertD, hcertN] at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  rcases hc with ⟨⟨⟨⟨hok3, hokD⟩, hokN⟩, hprops⟩, hq51_pow⟩
  unfold checkBakerQ51Props at hprops
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hprops
  rcases hprops with ⟨⟨⟨hTheta_gt, hE⟩, hgrow100⟩, hscale62⟩
  have hs3 := certifyLog2Pow_sound 160 140 3 (by rw [hcert3]; exact hok3)
  rw [hcert3] at hs3
  have hsD := certifyLog2Pow_sound 160 140 (3 * (barinaXMin + 1)) (by rw [hcertD]; exact hokD)
  rw [hcertD] at hsD
  have hsN := certifyLog2Pow_sound 160 140 (3 * barinaXMin + 5) (by rw [hcertN]; exact hokN)
  rw [hcertN] at hsN
  rcases baker_N_bounds (Nat.le_trans hq51_pow hw_ge) with ⟨hW_pos, hN100, hNmul, hexp⟩
  exact no_spiral_cycle_baker_core hbaker hcyc hm_le
    (nontrivial_cycle_vertex_floor hbar hcyc) (by decide)
    hs3.2.1 hTheta_gt hsD.1 hsN.2.1 hE hgrow100 hscale62
    hW_pos hN100 hNmul hexp

-- ============================================================================
-- 13.4C Complete 9-Slab + `m = 92` Kernel Certificates & Master Theorem 26
-- ============================================================================

def p34Val : Nat := 423372672964960618
def q34Val : Nat := 267118416222671843
def p35Val : Nat := 630118245525664765
def p36Val : Nat := 6724555128221608268
def q36Val : Nat := 4242721909926539673
def p37Val : Nat := 7354673373747273033
def p38Val : Nat := 36143248623210700400
def q38Val : Nat := 22803850947114245497
def p39Val : Nat := 43497921996957973433
def p40Val : Nat := 79641170620168673833
def q40Val : Nat := 50247984153525417450
def p41Val : Nat := 123139092617126647266
def p42Val : Nat := 202780263237295321099

def bsSlab35_37 : List Nat :=
  List.replicate 15 (2 ^ 71) ++ [
    19551394183821850820340291767,
    346278725555052043535524804688424067160467175,
    19601518535472335941711258489448562328267589395981003572466293483802043,
    2 ^ 256]

def bsSlab37_39 : List Nat :=
  List.replicate 10 (2 ^ 71) ++ [
    847299288450171266546414439680563,
    7738799960775030411159840125905987761663421160762164,
    2 ^ 256]

def bsSlab39_41 : List Nat :=
  List.replicate 6 (2 ^ 71) ++ [
    7802885588909025406521498021046,
    4592362066236841803360908211056286329726418598606,
    67061376693568564161571511355998061569525152846120701672503756616141214726536,
    2 ^ 256]

def bsSlab41_43 : List Nat :=
  List.replicate 3 (2 ^ 71) ++ [
    12976570244799881858500,
    55911256608642452574147895211355064,
    5921794256523255902348186014411082914430976718739051180,
    2 ^ 256]

def bsSlabQ43M91 : List Nat := [
  186580408057834154985330,
  3823138529586028794420787974039016498,
  4794396471396378233054549473830669589338881758606827473719,
  2 ^ 256]

def bsSlab2Q43 : List Nat := [
  169748887054766121988393583117,
  10644319466430191625084204013429015957956246190,
  4469159895156784247439148473969083288175518530770448339462688438396093536,
  2 ^ 256]

def bsM92Counts : List Nat := [2 ^ 71, exactM92B1, exactM92B2, exactM92B3, 2 ^ 256]

def bsM92S0 : List Nat := [exactM92B1, exactM92B1, exactM92B2, exactM92B3, 2 ^ 256]

def m92L43Val : Nat := (evalPow2Pow3Aux 256 p43Val q43Val 92).1
def m92U43Val : Nat := (evalPow2Pow3Aux 256 p43Val q43Val 92).2
def m92SigmaTail91 : Nat :=
  teleStepCap (2 ^ 256) exactM92B1 [(exactM92B2, 1), (exactM92B3, 2), (2 ^ 256, 3)] 91
def m92DenomHi : Nat :=
  (2 ^ 256 - m92SigmaTail91) * m92L43Val - 2 ^ 256 * 2 ^ 256

def derivedM92Lo (k1 : Nat) : Nat :=
  (2 ^ 256 * (3 ^ k1 - 2 ^ k1)) / ((m92U43Val - 2 ^ 256) * 3 ^ k1) + 1

def derivedM92Hi (k1 : Nat) : Nat :=
  (2 ^ 256 * 2 ^ 256 * (3 ^ k1 - 2 ^ k1)) / (m92DenomHi * 3 ^ k1)

set_option maxRecDepth 20000 in
theorem convergent_signs_and_relations_certified :
    (evalPow2Pow3Aux 256 p34Val q34Val 92).2 ≤ 2 ^ 256 ∧
    2 ^ 256 < (evalPow2Pow3Aux 256 p35Val q35Val 92).1 ∧
    (evalPow2Pow3Aux 256 p36Val q36Val 92).2 ≤ 2 ^ 256 ∧
    2 ^ 256 < (evalPow2Pow3Aux 256 p37Val q37Val 92).1 ∧
    (evalPow2Pow3Aux 256 p38Val q38Val 92).2 ≤ 2 ^ 256 ∧
    2 ^ 256 < (evalPow2Pow3Aux 256 p39Val q39Val 92).1 ∧
    (evalPow2Pow3Aux 256 p40Val q40Val 92).2 ≤ 2 ^ 256 ∧
    2 ^ 256 < (evalPow2Pow3Aux 256 p41Val q41Val 92).1 ∧
    (evalPow2Pow3Aux 256 p42Val q42Val 92).2 ≤ 2 ^ 256 ∧
    2 ^ 256 < (evalPow2Pow3Aux 256 p43Val q43Val 92).1 ∧
    (evalPow2Pow3Aux 256 p44Val q44Val 92).2 ≤ 2 ^ 256 ∧
    2 ^ 256 < (evalPow2Pow3Aux 256 p45Val q45Val 92).1 ∧
    (evalPow2Pow3Aux 256 p50Val q50Val 92).2 ≤ 2 ^ 256 ∧
    2 ^ 256 < (evalPow2Pow3Aux 256 p51Val q51Val 92).1 := by
  decide

set_option maxRecDepth 20000 in
theorem slab_1_35_ok :
    checkSlabEliminated 128 112 256 92 1 barinaXMin
      (evalPow2Pow3Aux 256 p35Val q35Val 92).1 [] = true := by decide

set_option maxRecDepth 20000 in
theorem slab_35_37_ok :
    checkSlabEliminated 128 112 256 92 q35Val barinaXMin
      (evalPow2Pow3Aux 256 p37Val q37Val 92).1 bsSlab35_37 = true := by decide

set_option maxRecDepth 20000 in
theorem slab_37_39_ok :
    checkSlabEliminated 128 112 256 92 q37Val barinaXMin
      (evalPow2Pow3Aux 256 p39Val q39Val 92).1 bsSlab37_39 = true := by decide

set_option maxRecDepth 20000 in
theorem slab_39_41_ok :
    checkSlabEliminated 128 112 256 92 q39Val barinaXMin
      (evalPow2Pow3Aux 256 p41Val q41Val 92).1 bsSlab39_41 = true := by decide

set_option maxRecDepth 20000 in
theorem slab_41_43_ok :
    checkSlabEliminated 128 112 256 92 q41Val barinaXMin
      (evalPow2Pow3Aux 256 p41Val q41Val 92).1 bsSlab41_43 = true := by decide

theorem slabs_group1_certified :
    checkSlabEliminated 128 112 256 92 1 barinaXMin
      (evalPow2Pow3Aux 256 p35Val q35Val 92).1 [] = true ∧
    checkSlabEliminated 128 112 256 92 q35Val barinaXMin
      (evalPow2Pow3Aux 256 p37Val q37Val 92).1 bsSlab35_37 = true ∧
    checkSlabEliminated 128 112 256 92 q37Val barinaXMin
      (evalPow2Pow3Aux 256 p39Val q39Val 92).1 bsSlab37_39 = true ∧
    checkSlabEliminated 128 112 256 92 q39Val barinaXMin
      (evalPow2Pow3Aux 256 p41Val q41Val 92).1 bsSlab39_41 = true ∧
    checkSlabEliminated 128 112 256 92 q41Val barinaXMin
      (evalPow2Pow3Aux 256 p41Val q41Val 92).1 bsSlab41_43 = true :=
  ⟨slab_1_35_ok, slab_35_37_ok, slab_37_39_ok, slab_39_41_ok, slab_41_43_ok⟩

set_option maxRecDepth 20000 in
theorem slab_q43_m91_ok :
    checkSlabEliminated 128 112 256 91 q43Val barinaXMin
      (evalPow2Pow3Aux 256 p43Val q43Val 92).1 bsSlabQ43M91 = true := by decide

set_option maxRecDepth 20000 in
theorem slab_2q43_ok :
    checkSlabEliminated 128 112 256 92 (2 * q43Val) barinaXMin
      (evalPow2Pow3Aux 256 p43Val q43Val 92).1 bsSlab2Q43 = true := by decide

set_option maxRecDepth 20000 in
theorem slab_q43_44_ok :
    checkSlabEliminated 128 112 256 92 (q43Val + q44Val) barinaXMin
      (evalPow2Pow3Aux 256 p45Val q45Val 92).1 [2 ^ 256] = true := by decide

set_option maxRecDepth 20000 in
theorem slab_m92_counts_ok :
    checkSlabEliminated 128 112 256 92 q43Val barinaXMin
      (evalPow2Pow3Aux 256 (39 * p43Val) (39 * q43Val) 92).1 bsM92Counts = true := by decide

set_option maxRecDepth 20000 in
theorem slab_45_51_ok :
    checkSlabEliminated 128 112 256 92 q45Val barinaXMin
      (evalPow2Pow3Aux 256 p51Val q51Val 92).1 [2 ^ 256] = true := by decide

set_option maxRecDepth 20000 in
theorem slab_m92_s0_ok :
    checkSlabEliminated 128 112 256 92 q43Val (exactM92B1 + 1)
      (evalPow2Pow3Aux 256 p43Val q43Val 92).1 bsM92S0 = true := by decide

theorem slabs_group2_certified :
    checkSlabEliminated 128 112 256 91 q43Val barinaXMin
      (evalPow2Pow3Aux 256 p43Val q43Val 92).1 bsSlabQ43M91 = true ∧
    checkSlabEliminated 128 112 256 92 (2 * q43Val) barinaXMin
      (evalPow2Pow3Aux 256 p43Val q43Val 92).1 bsSlab2Q43 = true ∧
    checkSlabEliminated 128 112 256 92 (q43Val + q44Val) barinaXMin
      (evalPow2Pow3Aux 256 p45Val q45Val 92).1 [2 ^ 256] = true ∧
    checkSlabEliminated 128 112 256 92 q43Val barinaXMin
      (evalPow2Pow3Aux 256 (39 * p43Val) (39 * q43Val) 92).1 bsM92Counts = true ∧
    checkSlabEliminated 128 112 256 92 q45Val barinaXMin
      (evalPow2Pow3Aux 256 p51Val q51Val 92).1 [2 ^ 256] = true ∧
    checkSlabEliminated 128 112 256 92 q43Val (exactM92B1 + 1)
      (evalPow2Pow3Aux 256 p43Val q43Val 92).1 bsM92S0 = true :=
  ⟨slab_q43_m91_ok, slab_2q43_ok, slab_q43_44_ok, slab_m92_counts_ok, slab_45_51_ok, slab_m92_s0_ok⟩

set_option maxRecDepth 20000 in
theorem m92_aux_arith_certified :
    m92SigmaTail91 < 2 ^ 256 ∧
    2 ^ 256 * 2 ^ 256 < (2 ^ 256 - m92SigmaTail91) * m92L43Val ∧
    (2 ^ 256 * 2 ^ 256) / m92DenomHi ≤ m92GlobalHi1 ∧
    m92GlobalHi1 + 1 < 2 ^ 74 ∧
    3 ^ 73 * (m92GlobalHi1 + 1) < 2 ^ 73 * (2 * (exactM92B2 + 1) + 1) ∧
    2 ^ 256 < m92U43Val := by
  decide

theorem evalPow2Pow3_eq_subst {S p q nbits K W : Nat}
    (hnb : nbits ≥ 1) (hp : p < 2 ^ nbits) (hq : q < 2 ^ nbits)
    (hK : K = p) (hW : W = q) :
    (evalPow2Pow3Aux S p q nbits).1 * 3 ^ W ≤ 2 ^ S * 2 ^ K ∧
    2 ^ S * 2 ^ K < (evalPow2Pow3Aux S p q nbits).2 * 3 ^ W := by
  subst hK; subst hW
  exact evalPow2Pow3Aux_sound S K W nbits hnb hp hq

theorem spiralChainTotalK_append : ∀ l1 l2 : List SpiralStepData,
    spiralChainTotalK (l1 ++ l2) = spiralChainTotalK l1 + spiralChainTotalK l2
  | [], _ => by simp [spiralChainTotalK]
  | s :: rest, l2 => by
    simp only [List.cons_append, spiralChainTotalK, spiralChainTotalK_append rest l2]
    omega

theorem counts_of_checkSlabEliminated
    {steps : List SpiralStepData}
    {sLog bLog sPow mMax wMin xMin lVal : Nat} {bs : List Nat}
    (hok : checkSlabEliminated sLog bLog sPow mMax wMin xMin lVal bs = true)
    (hcyc : IsNontrivialSpiralCycle steps)
    (hm_le : steps.length ≤ mMax)
    (hw_ge : wMin ≤ spiralChainTotalW steps)
    (hfl : ∀ s ∈ steps, s.x ≥ xMin) :
    ∀ bc ∈ buildIndexedPairs 1 bs, countLe bc.1 (spiralVertices steps) ≤ bc.2 := by
  unfold checkSlabEliminated at hok
  rcases hc3 : certifyLog2Pow sLog bLog 3 with ⟨_, Theta, ok3⟩
  rcases hcD : certifyLog2Pow sLog bLog (3 * (xMin + 1)) with ⟨lD0, _, okD0⟩
  rcases hcN : certifyLog2Pow sLog bLog (3 * xMin + 5) with ⟨_, uN0p, okN0p⟩
  rw [hc3, hcD, hcN] at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  rcases hok with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, hxMin⟩, hok3⟩, hokD⟩, hokN⟩, hQTheta⟩, hE⟩, _⟩, hchk⟩, _⟩, _⟩
  have hs3 := certifyLog2Pow_sound sLog bLog 3 (by rw [hc3]; exact hok3)
  rw [hc3] at hs3
  have hsD := certifyLog2Pow_sound sLog bLog (3 * (xMin + 1)) (by rw [hcD]; exact hokD)
  rw [hcD] at hsD
  have hsN := certifyLog2Pow_sound sLog bLog (3 * xMin + 5) (by rw [hcN]; exact hokN)
  rw [hcN] at hsN
  exact checkAllThresholds_implies_counts hcyc hm_le hw_ge hfl hxMin
    hs3.2.1 hQTheta hsD.1 hsN.2.1 hE 1 bs (by omega) hchk

theorem spiralCycle_rotate_at_small {steps : List SpiralStepData} {b : Nat}
    (hcyc : IsNontrivialSpiralCycle steps)
    (hex : ¬ (∀ s ∈ steps, s.x ≥ b + 1)) :
    ∃ (s0 : SpiralStepData) (tail : List SpiralStepData),
      s0.x ≤ b ∧
      IsNontrivialSpiralCycle (s0 :: tail) ∧
      (s0 :: tail).length = steps.length ∧
      spiralChainTotalK (s0 :: tail) = spiralChainTotalK steps ∧
      spiralChainTotalW (s0 :: tail) = spiralChainTotalW steps ∧
      (∀ c : Nat, countLe c (spiralVertices (s0 :: tail)) = countLe c (spiralVertices steps)) ∧
      (∀ xMin : Nat, (∀ s ∈ steps, s.x ≥ xMin) -> ∀ s ∈ (s0 :: tail), s.x ≥ xMin) := by
  have hex_le : ∃ x ∈ spiralVertices steps, x ≤ b := by
    apply Classical.byContradiction
    intro hno
    apply hex
    intro s hs
    apply Classical.byContradiction
    intro hlt
    exact hno ⟨s.x, List.mem_map.mpr ⟨s, hs, rfl⟩, by omega⟩
  have hcnt_pos := mem_le_implies_countLe_pos b (spiralVertices steps) hex_le
  rcases find_le_split steps b hcnt_pos with ⟨pre, s0, suf, hsplit, hs0_le⟩
  refine ⟨s0, suf ++ pre, hs0_le, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases hsteps : steps with
    | nil => rw [hsteps] at hcyc; cases hcyc
    | cons h0 htl =>
      rw [hsteps] at hcyc hsplit
      rcases hcyc with ⟨hch, sBig, hsBig_mem, hsBig_gt⟩
      have hmem_rot : ∀ s : SpiralStepData, s ∈ (h0 :: htl) -> s ∈ (s0 :: (suf ++ pre)) := by
        intro s hs
        rw [hsplit] at hs
        simp only [List.mem_append, List.mem_cons] at hs ⊢
        rcases hs with hpre | (rfl | hsuf)
        · exact Or.inr (Or.inr hpre)
        · exact Or.inl rfl
        · exact Or.inr (Or.inl hsuf)
      refine ⟨?_, sBig, hmem_rot sBig hsBig_mem, hsBig_gt⟩
      cases hpre : pre with
      | nil =>
        rw [hpre, List.nil_append] at hsplit
        injection hsplit with hh0 hhtl
        subst hh0; subst hhtl
        simpa [List.append_nil] using hch
      | cons p0 ptl =>
        rw [hpre, List.cons_append] at hsplit
        injection hsplit with hh0 hhtl
        subst hh0; subst hhtl
        rcases validSpiralChain_split (h0 :: ptl) s0 suf h0.x hch with ⟨hPre, hSuf⟩
        exact validSpiralChain_append (s0 :: suf) (h0 :: ptl) h0 s0.x rfl hSuf hPre
  · rw [hsplit]; simp [List.length_append]; omega
  · rw [hsplit, spiralChainTotalK_append, ← List.cons_append, spiralChainTotalK_append, Nat.add_comm]
  · rw [hsplit, spiralTotalW_append, ← List.cons_append, spiralTotalW_append, Nat.add_comm]
  · intro c
    unfold spiralVertices
    rw [hsplit, List.map_append, countLe_append, ← List.cons_append, List.map_append,
        countLe_append, Nat.add_comm]
  · intro xMin hfl s hs
    apply hfl s
    rw [hsplit]
    simp only [List.mem_append, List.mem_cons] at hs ⊢
    rcases hs with rfl | (hsuf | hpre)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr hsuf)
    · exact Or.inl hpre

/--
  Pure-`Nat` symbolic band-derivation core for `m = 92, s >= 1` (`M`, `L43`, `U43`, `sigma`
  kept symbolic so `omega` uses zero memory on `2 ^ 256`!).
-/
theorem m92_s_ge_1_band_bounds_core
    {s0 s1 : SpiralStepData} {restTail : List SpiralStepData}
    {M K W L43 U43 sigma denomHi : Nat}
    (hM_pos : M ≥ 1)
    (hs0 : ValidSpiralStep s0 s1.x)
    (htail : ValidSpiralChain (s1 :: restTail) s0.x)
    (hK_eq : (s0.k + s0.l) + spiralChainTotalK (s1 :: restTail) = K)
    (hW_eq : s0.k + spiralChainTotalW (s1 :: restTail) = W)
    (hL43 : L43 * 3 ^ W ≤ M * 2 ^ K)
    (hU43 : M * 2 ^ K < U43 * 3 ^ W)
    (hU_gt : M < U43)
    (hbern_tail : (M - sigma) * prodList ((s1 :: restTail).map (fun s => s.x + 1)) ≤
      M * prodList ((s1 :: restTail).map (fun s => s.x)))
    (hsig_lt : sigma < M)
    (hdenom_pos : M * M < (M - sigma) * L43)
    (hdenom_eq : (M - sigma) * L43 - M * M = denomHi) :
    (M * (3 ^ s0.k - 2 ^ s0.k)) / ((U43 - M) * 3 ^ s0.k) + 1 ≤ s0.x ∧
    s0.x ≤ (M * M * (3 ^ s0.k - 2 ^ s0.k)) / (denomHi * 3 ^ s0.k) ∧
    s0.x ≤ (M * M) / denomHi := by
  let WT := spiralChainTotalW (s1 :: restTail)
  let KT := spiralChainTotalK (s1 :: restTail)
  let PM := prodList (restTail.map (fun s => s.x))
  have hPM_pos : PM ≥ 1 := validSpiralChain_vertices_pos s1 restTail s0.x htail
  rcases spiralStep_x_bounds hs0 with ⟨_, _, hstep0_eq⟩
  rcases spiralChain_prod_bounds s1 restTail s0.x htail with ⟨htail_lo, htail_hi⟩
  change 3 ^ WT * (s1.x * PM) < 2 ^ KT * (PM * s0.x) at htail_lo
  change 2 ^ KT * (PM * s0.x) <
    3 ^ WT * ((s1.x + 1) * prodList (restTail.map (fun s => s.x + 1))) at htail_hi
  have hp2K : 2 ^ (s0.k + s0.l) * 2 ^ KT = 2 ^ K := by rw [← Nat.pow_add, hK_eq]
  have hp3W : 3 ^ s0.k * 3 ^ WT = 3 ^ W := by rw [← Nat.pow_add, hW_eq]
  have hp3W_pos : 3 ^ WT ≥ 1 := pow3_pos_nat WT
  rcases hs0 with ⟨_, hs0_pos, _, _, hk0_ge1, _, _⟩
  have h3gt2 : 2 ^ s0.k < 3 ^ s0.k := pow_lt_pow_pos_nat (by decide) (by decide) s0.k hk0_ge1
  -- 1. Cancel PM >= 1 from htail_lo * 2^(s0.k + s0.l) to get lower bound on s0.x:
  have hlo_step : 3 ^ W * s0.x + 3 ^ WT * (3 ^ s0.k - 2 ^ s0.k) < 2 ^ K * s0.x := by
    have hm := Nat.mul_lt_mul_of_pos_left htail_lo (pow2_pos_nat (s0.k + s0.l))
    have hlhs : 2 ^ (s0.k + s0.l) * (3 ^ WT * (s1.x * PM)) =
        (3 ^ WT * (2 ^ (s0.k + s0.l) * s1.x)) * PM := by
      calc
        2 ^ (s0.k + s0.l) * (3 ^ WT * (s1.x * PM))
            = (2 ^ (s0.k + s0.l) * 3 ^ WT) * (s1.x * PM) := by rw [← Nat.mul_assoc]
        _ = (3 ^ WT * 2 ^ (s0.k + s0.l)) * (s1.x * PM) := by rw [Nat.mul_comm (2 ^ _) (3 ^ WT)]
        _ = 3 ^ WT * (2 ^ (s0.k + s0.l) * (s1.x * PM)) := by rw [Nat.mul_assoc]
        _ = 3 ^ WT * ((2 ^ (s0.k + s0.l) * s1.x) * PM) := by rw [← Nat.mul_assoc (2 ^ _) s1.x PM]
        _ = (3 ^ WT * (2 ^ (s0.k + s0.l) * s1.x)) * PM := by rw [← Nat.mul_assoc]
    have hrhs : 2 ^ (s0.k + s0.l) * (2 ^ KT * (PM * s0.x)) = (2 ^ K * s0.x) * PM := by
      calc
        2 ^ (s0.k + s0.l) * (2 ^ KT * (PM * s0.x))
            = (2 ^ (s0.k + s0.l) * 2 ^ KT) * (PM * s0.x) := by rw [← Nat.mul_assoc]
        _ = 2 ^ K * (s0.x * PM) := by rw [hp2K, Nat.mul_comm PM s0.x]
        _ = (2 ^ K * s0.x) * PM := by rw [← Nat.mul_assoc]
    rw [hlhs, hrhs] at hm
    have hcancel : 3 ^ WT * (2 ^ (s0.k + s0.l) * s1.x) < 2 ^ K * s0.x := by
      apply Classical.byContradiction
      intro hge
      have hm2 := Nat.mul_le_mul_right PM
        (show 2 ^ K * s0.x ≤ 3 ^ WT * (2 ^ (s0.k + s0.l) * s1.x) by omega)
      omega
    rw [hstep0_eq, Nat.mul_add, ← Nat.mul_assoc (3 ^ WT) (3 ^ s0.k),
        Nat.mul_comm (3 ^ WT) (3 ^ s0.k), hp3W] at hcancel
    exact hcancel
  have hlo_div : (M * (3 ^ s0.k - 2 ^ s0.k)) / ((U43 - M) * 3 ^ s0.k) + 1 ≤ s0.x := by
    have hm1 := Nat.mul_lt_mul_of_pos_left hlo_step hM_pos
    rw [Nat.mul_add, ← Nat.mul_assoc M (2 ^ K)] at hm1
    have hm2 := Nat.mul_lt_mul_of_pos_right hU43 hs0_pos
    have hlt_U : M * (3 ^ W * s0.x) + M * (3 ^ WT * (3 ^ s0.k - 2 ^ s0.k)) <
        U43 * 3 ^ W * s0.x := Nat.lt_trans hm1 hm2
    have hsplit_U : U43 * 3 ^ W * s0.x = M * (3 ^ W * s0.x) + ((U43 - M) * 3 ^ W) * s0.x := by
      calc
        U43 * 3 ^ W * s0.x = ((M + (U43 - M)) * 3 ^ W) * s0.x := by
          rw [show M + (U43 - M) = U43 by omega]
        _ = M * (3 ^ W * s0.x) + ((U43 - M) * 3 ^ W) * s0.x := by
          rw [Nat.add_mul, Nat.add_mul, Nat.mul_assoc M]
    rw [hsplit_U] at hlt_U
    have hsub_U : M * (3 ^ WT * (3 ^ s0.k - 2 ^ s0.k)) < ((U43 - M) * 3 ^ W) * s0.x := by omega
    have hl_wt : M * (3 ^ WT * (3 ^ s0.k - 2 ^ s0.k)) = 3 ^ WT * (M * (3 ^ s0.k - 2 ^ s0.k)) := by
      rw [← Nat.mul_assoc, Nat.mul_comm M (3 ^ WT), Nat.mul_assoc]
    have hr_wt : ((U43 - M) * 3 ^ W) * s0.x = 3 ^ WT * (((U43 - M) * 3 ^ s0.k) * s0.x) := by
      rw [← hp3W, Nat.mul_comm (3 ^ s0.k) (3 ^ WT)]
      calc
        ((U43 - M) * (3 ^ WT * 3 ^ s0.k)) * s0.x
            = ((3 ^ WT * (U43 - M)) * 3 ^ s0.k) * s0.x := by
              rw [← Nat.mul_assoc (U43 - M), Nat.mul_comm (U43 - M) (3 ^ WT)]
        _ = 3 ^ WT * (((U43 - M) * 3 ^ s0.k) * s0.x) := by
              rw [Nat.mul_assoc (3 ^ WT), Nat.mul_assoc (3 ^ WT)]
    rw [hl_wt, hr_wt] at hsub_U
    have hfin : M * (3 ^ s0.k - 2 ^ s0.k) < ((U43 - M) * 3 ^ s0.k) * s0.x := by
      apply Classical.byContradiction
      intro hge
      have hm3 := Nat.mul_le_mul_left (3 ^ WT)
        (show ((U43 - M) * 3 ^ s0.k) * s0.x ≤ M * (3 ^ s0.k - 2 ^ s0.k) by omega)
      omega
    apply Classical.byContradiction
    intro hlt_x
    have hx_le : s0.x ≤ (M * (3 ^ s0.k - 2 ^ s0.k)) / ((U43 - M) * 3 ^ s0.k) := by omega
    have hm4 := Nat.mul_le_mul_left ((U43 - M) * 3 ^ s0.k) hx_le
    have hmd := mul_div_le_nat (M * (3 ^ s0.k - 2 ^ s0.k)) ((U43 - M) * 3 ^ s0.k)
    omega
  -- 2. Combine htail_hi + hbern_tail to get upper bound on s0.x:
  have hhi_tail : (M - sigma) * 2 ^ KT * s0.x < M * 3 ^ WT * s1.x := by
    simp only [List.map_cons, prodList] at hbern_tail
    change (M - sigma) * ((s1.x + 1) * prodList (restTail.map (fun s => s.x + 1))) ≤
      M * (s1.x * PM) at hbern_tail
    have hm1 := Nat.mul_lt_mul_of_pos_left htail_hi (show M - sigma > 0 by omega)
    have hm2 : (M - sigma) * (3 ^ WT * ((s1.x + 1) * prodList (restTail.map (fun s => s.x + 1)))) ≤
        (M * 3 ^ WT * s1.x) * PM := by
      calc
        (M - sigma) * (3 ^ WT * ((s1.x + 1) * prodList (restTail.map (fun s => s.x + 1))))
            = 3 ^ WT * ((M - sigma) * ((s1.x + 1) * prodList (restTail.map (fun s => s.x + 1)))) := by
              rw [← Nat.mul_assoc, Nat.mul_comm (M - sigma) (3 ^ WT), Nat.mul_assoc]
        _ ≤ 3 ^ WT * (M * (s1.x * PM)) := Nat.mul_le_mul_left _ hbern_tail
        _ = (M * 3 ^ WT * s1.x) * PM := by
              rw [← Nat.mul_assoc (3 ^ WT) M, Nat.mul_comm (3 ^ WT) M, ← Nat.mul_assoc]
    have hlhs : (M - sigma) * (2 ^ KT * (PM * s0.x)) = ((M - sigma) * 2 ^ KT * s0.x) * PM := by
      rw [← Nat.mul_assoc, Nat.mul_comm PM s0.x, ← Nat.mul_assoc]
    rw [hlhs] at hm1
    have hcomb := Nat.lt_of_lt_of_le hm1 hm2
    apply Classical.byContradiction
    intro hge
    have hm3 := Nat.mul_le_mul_right PM
      (show M * 3 ^ WT * s1.x ≤ (M - sigma) * 2 ^ KT * s0.x by omega)
    omega
  have hhi_step : (M - sigma) * 2 ^ K * s0.x <
      M * 3 ^ W * s0.x + M * 3 ^ WT * (3 ^ s0.k - 2 ^ s0.k) := by
    have hm := Nat.mul_lt_mul_of_pos_left hhi_tail (pow2_pos_nat (s0.k + s0.l))
    have hlhs : 2 ^ (s0.k + s0.l) * ((M - sigma) * 2 ^ KT * s0.x) =
        (M - sigma) * 2 ^ K * s0.x := by
      calc
        2 ^ (s0.k + s0.l) * ((M - sigma) * 2 ^ KT * s0.x)
            = ((2 ^ (s0.k + s0.l) * (M - sigma)) * 2 ^ KT) * s0.x := by
              rw [← Nat.mul_assoc, ← Nat.mul_assoc]
        _ = ((M - sigma) * 2 ^ K) * s0.x := by
              rw [Nat.mul_comm (2 ^ _) (M - sigma), Nat.mul_assoc (M - sigma), hp2K]
    have hrhs : 2 ^ (s0.k + s0.l) * (M * 3 ^ WT * s1.x) =
        (M * 3 ^ WT) * (2 ^ (s0.k + s0.l) * s1.x) := by
      rw [← Nat.mul_assoc, Nat.mul_comm (2 ^ _) (M * 3 ^ WT), Nat.mul_assoc]
    rw [hlhs, hrhs, hstep0_eq, Nat.mul_add] at hm
    have hr1 : (M * 3 ^ WT) * (3 ^ s0.k * s0.x) = M * 3 ^ W * s0.x := by
      calc
        (M * 3 ^ WT) * (3 ^ s0.k * s0.x)
            = (M * (3 ^ WT * 3 ^ s0.k)) * s0.x := by rw [← Nat.mul_assoc, Nat.mul_assoc M]
        _ = M * 3 ^ W * s0.x := by rw [Nat.mul_comm (3 ^ WT) (3 ^ s0.k), hp3W]
    rwa [hr1] at hm
  have hdenom_lt : (denomHi * 3 ^ s0.k) * s0.x < M * M * (3 ^ s0.k - 2 ^ s0.k) := by
    have hm1 := Nat.mul_lt_mul_of_pos_left hhi_step hM_pos
    rw [Nat.mul_add] at hm1
    have hl_L43 : ((M - sigma) * L43) * 3 ^ W * s0.x ≤ M * ((M - sigma) * 2 ^ K * s0.x) := by
      have hmL := Nat.mul_le_mul_left (M - sigma) hL43
      have hmLx := Nat.mul_le_mul_right s0.x hmL
      calc
        ((M - sigma) * L43) * 3 ^ W * s0.x
            = ((M - sigma) * (L43 * 3 ^ W)) * s0.x := by rw [Nat.mul_assoc (M - sigma)]
        _ ≤ ((M - sigma) * (M * 2 ^ K)) * s0.x := hmLx
        _ = M * ((M - sigma) * 2 ^ K * s0.x) := by
            rw [← Nat.mul_assoc (M - sigma) M, Nat.mul_comm (M - sigma) M,
                Nat.mul_assoc M, Nat.mul_assoc M]
    have hlt_D := Nat.lt_of_le_of_lt hl_L43 hm1
    have hsplit_D : ((M - sigma) * L43) * 3 ^ W * s0.x =
        M * (M * 3 ^ W * s0.x) + (denomHi * 3 ^ W) * s0.x := by
      rw [← hdenom_eq]
      calc
        ((M - sigma) * L43) * 3 ^ W * s0.x
            = ((M * M + ((M - sigma) * L43 - M * M)) * 3 ^ W) * s0.x := by
              rw [show M * M + ((M - sigma) * L43 - M * M) = (M - sigma) * L43 by omega]
        _ = M * (M * 3 ^ W * s0.x) + (((M - sigma) * L43 - M * M) * 3 ^ W) * s0.x := by
              rw [Nat.add_mul, Nat.add_mul, Nat.mul_assoc M M (3 ^ W), Nat.mul_assoc M (M * 3 ^ W) s0.x]
    rw [hsplit_D] at hlt_D
    have hsub_D : (denomHi * 3 ^ W) * s0.x < M * (M * 3 ^ WT * (3 ^ s0.k - 2 ^ s0.k)) := by omega
    have hl_wt : (denomHi * 3 ^ W) * s0.x = 3 ^ WT * ((denomHi * 3 ^ s0.k) * s0.x) := by
      rw [← hp3W, Nat.mul_comm (3 ^ s0.k) (3 ^ WT)]
      calc
        (denomHi * (3 ^ WT * 3 ^ s0.k)) * s0.x
            = ((3 ^ WT * denomHi) * 3 ^ s0.k) * s0.x := by
              rw [← Nat.mul_assoc denomHi, Nat.mul_comm denomHi (3 ^ WT)]
        _ = 3 ^ WT * ((denomHi * 3 ^ s0.k) * s0.x) := by
              rw [Nat.mul_assoc (3 ^ WT), Nat.mul_assoc (3 ^ WT)]
    have hr_wt : M * (M * 3 ^ WT * (3 ^ s0.k - 2 ^ s0.k)) =
        3 ^ WT * (M * M * (3 ^ s0.k - 2 ^ s0.k)) := by
      calc
        M * (M * 3 ^ WT * (3 ^ s0.k - 2 ^ s0.k))
            = (M * M) * (3 ^ WT * (3 ^ s0.k - 2 ^ s0.k)) := by
              rw [Nat.mul_assoc M (3 ^ WT) _, ← Nat.mul_assoc M M _]
        _ = 3 ^ WT * (M * M * (3 ^ s0.k - 2 ^ s0.k)) := by
              rw [← Nat.mul_assoc, Nat.mul_comm (M * M) (3 ^ WT), Nat.mul_assoc]
    rw [hl_wt, hr_wt] at hsub_D
    apply Classical.byContradiction
    intro hge
    have hm3 := Nat.mul_le_mul_left (3 ^ WT)
      (show M * M * (3 ^ s0.k - 2 ^ s0.k) ≤ (denomHi * 3 ^ s0.k) * s0.x by omega)
    omega
  have hd_pos : denomHi ≥ 1 := by omega
  have hdk_pos : denomHi * 3 ^ s0.k ≥ 1 := Nat.mul_pos hd_pos (pow3_pos_nat s0.k)
  have hhi_div : s0.x ≤ (M * M * (3 ^ s0.k - 2 ^ s0.k)) / (denomHi * 3 ^ s0.k) :=
    le_div_of_mul_le hdk_pos (Nat.le_of_lt hdenom_lt)
  have hglob_div : s0.x ≤ (M * M) / denomHi := by
    apply le_div_of_mul_le hd_pos
    have hm1 : (denomHi * s0.x) * 3 ^ s0.k ≤ (M * M) * 3 ^ s0.k := by
      have heq1 : (denomHi * s0.x) * 3 ^ s0.k = (denomHi * 3 ^ s0.k) * s0.x := by
        rw [Nat.mul_assoc, Nat.mul_comm s0.x (3 ^ s0.k), ← Nat.mul_assoc]
      have hle_diff : M * M * (3 ^ s0.k - 2 ^ s0.k) ≤ (M * M) * 3 ^ s0.k :=
        Nat.mul_le_mul_left (M * M) (Nat.sub_le _ _)
      rw [heq1]
      exact Nat.le_of_lt (Nat.lt_of_lt_of_le hdenom_lt hle_diff)
    exact Nat.le_of_mul_le_mul_right hm1 (pow3_pos_nat s0.k)
  exact ⟨hlo_div, hhi_div, hglob_div⟩

theorem validTwoStepSpiral_of_nat_steps
    {b1 b2 : Nat} {s0 s1 : SpiralStepData} {x2 : Nat}
    (hs0 : ValidSpiralStep s0 s1.x)
    (hs1 : ValidSpiralStep s1 x2)
    (hx1_lo : b1 + 1 ≤ s1.x) (hx1_hi : s1.x ≤ b2)
    (hx2_lo : b2 + 1 ≤ x2) :
    ValidTwoStepSpiral b1 b2 s0.k s0.l s1.k s1.l (s0.x : Int) (s1.x : Int) (x2 : Int) := by
  rcases hs0 with ⟨_, _, _, _, _, hl0, hst0⟩
  rcases hs1 with ⟨_, _, _, _, hk1, hl1, hst1⟩
  have hp2l0 : 2 ^ s0.l ≥ 1 := pow2_pos_nat s0.l
  have hp2l1 : 2 ^ s1.l ≥ 1 := pow2_pos_nat s1.l
  refine ⟨hl0, hk1, hl1, by omega, by omega, by omega, ?_, ?_⟩
  · have hc := congrArg (Nat.cast : Nat -> Int) hst0
    rw [natCast_mul, natCast_pow2, natCast_add, natCast_add, natCast_mul, natCast_pow3,
        natCast_add, natCast_mul, natCast_pow2] at hc
    rw [show ((2 ^ s0.l - 1 : Nat) : Int) = (2 : Int) ^ s0.l - 1 by
          rw [← natCast_pow2 s0.l]; omega] at hc
    simpa using hc
  · have hc := congrArg (Nat.cast : Nat -> Int) hst1
    rw [natCast_mul, natCast_pow2, natCast_add, natCast_add, natCast_mul, natCast_pow3,
        natCast_add, natCast_mul, natCast_pow2] at hc
    rw [show ((2 ^ s1.l - 1 : Nat) : Int) = (2 : Int) ^ s1.l - 1 by
          rw [← natCast_pow2 s1.l]; omega] at hc
    simpa using hc

theorem tail_counts_of_head_small
    {b1 b2 b3 b4 : Nat} {s0 : SpiralStepData} {tail : List SpiralStepData}
    (hb12 : b1 ≤ b2) (hb23 : b2 ≤ b3) (hb34 : b3 ≤ b4)
    (hs0 : s0.x ≤ b1)
    (hc1 : countLe b1 (spiralVertices (s0 :: tail)) ≤ 1)
    (hc2 : countLe b2 (spiralVertices (s0 :: tail)) ≤ 2)
    (hc3 : countLe b3 (spiralVertices (s0 :: tail)) ≤ 3)
    (hc4 : countLe b4 (spiralVertices (s0 :: tail)) ≤ 4) :
    (∀ x ∈ tail.map (fun s => s.x), x ≥ b1 + 1) ∧
    (∀ bc ∈ [(b2, 1), (b3, 2), (b4, 3)], countLe bc.1 (tail.map (fun s => s.x)) ≤ bc.2) := by
  have hs0_2 : s0.x ≤ b2 := Nat.le_trans hs0 hb12
  have hs0_3 : s0.x ≤ b3 := Nat.le_trans hs0_2 hb23
  have hs0_4 : s0.x ≤ b4 := Nat.le_trans hs0_3 hb34
  simp only [spiralVertices, List.map_cons, countLe, hs0, hs0_2, hs0_3, hs0_4, ↓reduceIte] at hc1 hc2 hc3 hc4
  refine ⟨?_, ?_⟩
  · intro x hx
    apply Classical.byContradiction
    intro hlt
    have hpos := mem_le_implies_countLe_pos b1 (tail.map (fun s => s.x)) ⟨x, hx, by omega⟩
    omega
  · intro bc hbc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hbc
    rcases hbc with rfl | rfl | rfl <;> dsimp <;> omega

theorem second_tail_gt_of_first_le
    {b2 : Nat} {s1 s2 : SpiralStepData} {rest : List SpiralStepData}
    (hc : countLe b2 ((s1 :: s2 :: rest).map (fun s => s.x)) ≤ 1)
    (hs1_le : s1.x ≤ b2) :
    b2 + 1 ≤ s2.x := by
  simp only [List.map_cons, countLe, hs1_le, ↓reduceIte] at hc
  by_cases hs2_le : s2.x ≤ b2
  · simp only [hs2_le, ↓reduceIte] at hc; omega
  · omega

set_option maxRecDepth 20000 in
theorem no_spiral_cycle_m92_q43_core
    {steps : List SpiralStepData} {m92Bounds : Nat -> Nat × Nat}
    (hbar : BarinaThreshold (2 ^ 71))
    (hsubsumed : ∀ k, 9 ≤ k -> k ≤ 73 ->
      (m92Bounds k).1 ≤ derivedM92Lo k ∧ derivedM92Hi k ≤ (m92Bounds k).2)
    (hout_bounds : ∀ k, (k ≤ 8 ∨ 74 ≤ k) -> m92Bounds k = (barinaXMin, m92GlobalHi1))
    (hhensel : ∀ k1 l1 k2 l2 (z1 z2 z3 : Int),
      k1 ≥ 1 -> ((m92Bounds k1).1 : Int) ≤ z1 -> z1 ≤ ((m92Bounds k1).2 : Int) ->
      ¬ ValidTwoStepSpiral exactM92B1 exactM92B2 k1 l1 k2 l2 z1 z2 z3)
    (hcyc : IsNontrivialSpiralCycle steps)
    (hm_eq : steps.length = 92)
    (hK_eq : spiralChainTotalK steps = p43Val)
    (hW_eq : spiralChainTotalW steps = q43Val) :
    False := by
  have hg2 := slabs_group2_certified
  have haux := m92_aux_arith_certified
  rcases evalPow2Pow3_eq_subst (S := 256) (nbits := 92)
    (by decide) (by decide) (by decide) hK_eq hW_eq with ⟨hL43_raw, hU43_raw⟩
  by_cases hall_b1 : ∀ s ∈ steps, s.x ≥ exactM92B1 + 1
  · -- Subcase s = 0: ALL 92 vertices >= exactM92B1 + 1 -> eliminated directly by checkSlabEliminated!
    exact checkSlabEliminated_sound hg2.2.2.2.2.2 hcyc (by omega)
      (by rw [hW_eq]; exact Nat.le_refl _) hall_b1 hL43_raw
  · -- Subcase s >= 1: rotate to s0 :: tail with s0.x <= exactM92B1!
    have hfl_bar := nontrivial_cycle_vertex_floor hbar hcyc
    rcases spiralCycle_rotate_at_small hcyc hall_b1 with
      ⟨s0, tail, hs0_le_b1, hcyc_rot, hlen_rot, hK_rot, hW_rot, _, hfl_rot_fn⟩
    have hfl_rot : ∀ s ∈ (s0 :: tail), s.x ≥ barinaXMin := hfl_rot_fn barinaXMin hfl_bar
    have hcnt_all := counts_of_checkSlabEliminated hg2.2.2.2.1 hcyc_rot
      (by rw [hlen_rot, hm_eq]; exact Nat.le_refl _) (by rw [hW_rot, hW_eq]; exact Nat.le_refl _) hfl_rot
    have hc1 : countLe exactM92B1 (spiralVertices (s0 :: tail)) ≤ 1 :=
      hcnt_all (exactM92B1, 1) (by decide)
    have hc2 : countLe exactM92B2 (spiralVertices (s0 :: tail)) ≤ 2 :=
      hcnt_all (exactM92B2, 2) (by decide)
    have hc3 : countLe exactM92B3 (spiralVertices (s0 :: tail)) ≤ 3 :=
      hcnt_all (exactM92B3, 3) (by decide)
    have hc4 : countLe (2 ^ 256) (spiralVertices (s0 :: tail)) ≤ 4 :=
      hcnt_all (2 ^ 256, 4) (by decide)
    rcases tail_counts_of_head_small (by decide) (by decide) (by decide)
      hs0_le_b1 hc1 hc2 hc3 hc4 with ⟨htail_fl, htail_bcs⟩
    have htail_len : tail.length = 91 := by simp at hlen_rot; omega
    cases tail with
    | nil => simp at htail_len
    | cons s1 tail1 =>
      cases tail1 with
      | nil => simp at htail_len
      | cons s2 rest89 =>
        rcases hcyc_rot with ⟨⟨hs0_step, htail_chain⟩, _⟩
        have hxs_len : ((s1 :: s2 :: rest89).map (fun s => s.x)).length = 91 := by
          simp at htail_len ⊢; omega
        have hbern_tail := teleBernoulli_ratio_bound (2 ^ 256) exactM92B1
          [(exactM92B2, 1), (exactM92B3, 2), (2 ^ 256, 3)]
          ((s1 :: s2 :: rest89).map (fun s => s.x))
          (pow2_pos_nat 256) htail_fl (by decide) htail_bcs
          (by rw [hxs_len]; exact Nat.le_of_lt haux.1)
        rw [hxs_len] at hbern_tail
        simp only [List.map_map, Function.comp_def] at hbern_tail
        rcases m92_s_ge_1_band_bounds_core (L43 := m92L43Val) (U43 := m92U43Val)
          (sigma := m92SigmaTail91) (denomHi := m92DenomHi)
          (pow2_pos_nat 256) hs0_step htail_chain
          (by simpa [spiralChainTotalK] using hK_rot)
          (by simpa [spiralChainTotalW] using hW_rot)
          hL43_raw hU43_raw haux.2.2.2.2.2 hbern_tail haux.1 haux.2.1 rfl with
          ⟨hs0_lo_der, hs0_hi_der, hs0_glob⟩
        have hs0_le_glob : s0.x ≤ m92GlobalHi1 := Nat.le_trans hs0_glob haux.2.2.1
        have hs0_ge_bar : barinaXMin ≤ s0.x := hfl_rot s0 (List.Mem.head _)
        have hs1_ge_b1 : exactM92B1 + 1 ≤ s1.x := htail_fl s1.x (List.Mem.head _)
        rcases hs0_step with ⟨hx0_1, hx0_odd, hx1_1, hx1_odd, hk0_ge1, hl0_ge1, hst0_nat⟩
        by_cases hk74 : 74 ≤ s0.k
        · exact no_spiral_step_of_hi_lt_pow2 s0.k 74 s0.l m92GlobalHi1 s0.x s1.x
            hk74 hl0_ge1 hs0_le_glob haux.2.2.2.1 hst0_nat
        · by_cases hs1_gt_b2 : exactM92B2 + 1 ≤ s1.x
          · exact no_spiral_step_of_pow3_lt_target s0.k 73 s0.l m92GlobalHi1 (exactM92B2 + 1)
              s0.x s1.x (by omega) hl0_ge1 hs0_le_glob hs1_gt_b2 haux.2.2.2.2.1 hst0_nat
          · have hs1_le_b2 : s1.x ≤ exactM92B2 := by omega
            have hc2_tail : countLe exactM92B2 ((s1 :: s2 :: rest89).map (fun s => s.x)) ≤ 1 :=
              htail_bcs (exactM92B2, 1) (List.Mem.head _)
            have hs2_gt_b2 : exactM92B2 + 1 ≤ s2.x :=
              second_tail_gt_of_first_le hc2_tail hs1_le_b2
            have hv2 := validTwoStepSpiral_of_nat_steps
              ⟨hx0_1, hx0_odd, hx1_1, hx1_odd, hk0_ge1, hl0_ge1, hst0_nat⟩
              htail_chain.1 hs1_ge_b1 hs1_le_b2 hs2_gt_b2
            have hbnd_s0 : (m92Bounds s0.k).1 ≤ s0.x ∧ s0.x ≤ (m92Bounds s0.k).2 := by
              by_cases hk8 : s0.k ≤ 8
              · rw [hout_bounds s0.k (Or.inl hk8)]
                exact ⟨hs0_ge_bar, hs0_le_glob⟩
              · rcases hsubsumed s0.k (by omega) (by omega) with ⟨hsub_lo, hsub_hi⟩
                exact ⟨Nat.le_trans hsub_lo hs0_lo_der, Nat.le_trans hs0_hi_der hsub_hi⟩
            exact hhensel s0.k s0.l s1.k s1.l (s0.x : Int) (s1.x : Int) (s2.x : Int)
              hk0_ge1 (by omega) (by omega) hv2

set_option maxRecDepth 20000 in
/--
  Master Theorem 26 (Zero-Trust-Gap End-to-End Cycle Elimination for `1 <= m <= 92`):
  Under ONLY `BarinaThreshold (2^71)` and `BakerLMNPowerBound` (plus the already-verified
  `m = 92` 2-step Hensel band theorem), NO non-trivial positive spiral cycle of block count
  `1 <= m <= 92` exists across ANY odd weight `W >= 1`!
-/
theorem no_nontrivial_spiral_cycles_1_to_92_core
    {steps : List SpiralStepData} {m92Bounds : Nat -> Nat × Nat}
    (hbar : BarinaThreshold (2 ^ 71))
    (hbaker : BakerLMNPowerBound)
    (hsubsumed : ∀ k, 9 ≤ k -> k ≤ 73 ->
      (m92Bounds k).1 ≤ derivedM92Lo k ∧ derivedM92Hi k ≤ (m92Bounds k).2)
    (hout_bounds : ∀ k, (k ≤ 8 ∨ 74 ≤ k) -> m92Bounds k = (barinaXMin, m92GlobalHi1))
    (hhensel : ∀ k1 l1 k2 l2 (z1 z2 z3 : Int),
      k1 ≥ 1 -> ((m92Bounds k1).1 : Int) ≤ z1 -> z1 ≤ ((m92Bounds k1).2 : Int) ->
      ¬ ValidTwoStepSpiral exactM92B1 exactM92B2 k1 l1 k2 l2 z1 z2 z3)
    (hcyc : IsNontrivialSpiralCycle steps)
    (hm_le : steps.length ≤ 92) :
    False := by
  by_cases hw51 : q51Val ≤ spiralChainTotalW steps
  · exact no_spiral_cycle_ge_q51 hbar hbaker hcyc hm_le hw51
  · have hfl := nontrivial_cycle_vertex_floor hbar hcyc
    rcases spiralCycle_global_prod_bounds hcyc with ⟨_, hcyc_lt, _⟩
    have hconv := convergent_signs_and_relations_certified
    have hg1 := slabs_group1_certified
    have hg2 := slabs_group2_certified
    let K := spiralChainTotalK steps
    let W := spiralChainTotalW steps
    have hW1 : W ≥ 1 := by
      cases hst : steps with
      | nil => rw [hst] at hcyc; cases hcyc
      | cons s0 rest =>
        rw [hst] at hcyc
        rcases hcyc with ⟨hch, _⟩
        have hk1 : s0.k ≥ 1 := by
          cases rest with
          | nil => exact hch.2.2.2.2.1
          | cons _ _ => exact hch.1.2.2.2.2.1
        dsimp [W]; rw [hst]; simp only [spiralChainTotalW]; omega
    by_cases hw35 : W < q35Val
    · have hr := unimodular_odd_upper_ratio (p0 := p34Val) (q0 := q34Val) (p1 := p35Val) (q1 := q35Val)
        (by decide) (by decide) (by decide)
        (pow2_lt_pow3_of_eval (by decide) (by decide) (by decide) hconv.1)
        (pow3_lt_pow2_of_eval (by decide) (by decide) (by decide) hconv.2.1)
        hW1 hw35 hcyc_lt
      exact checkSlabEliminated_sound hg1.1 hcyc hm_le hW1 hfl
        (ratio_transfer_evalPow2Pow3 (by decide) (by decide) (by decide) (Nat.le_of_lt hr))
    · by_cases hw37 : W < q37Val
      · have hr := unimodular_odd_upper_ratio (p0 := p36Val) (q0 := q36Val) (p1 := p37Val) (q1 := q37Val)
          (by decide) (by decide) (by decide)
          (pow2_lt_pow3_of_eval (by decide) (by decide) (by decide) hconv.2.2.1)
          (pow3_lt_pow2_of_eval (by decide) (by decide) (by decide) hconv.2.2.2.1)
          hW1 hw37 hcyc_lt
        exact checkSlabEliminated_sound hg1.2.1 hcyc hm_le (Nat.le_of_not_lt hw35) hfl
          (ratio_transfer_evalPow2Pow3 (by decide) (by decide) (by decide) (Nat.le_of_lt hr))
      · by_cases hw39 : W < q39Val
        · have hr := unimodular_odd_upper_ratio (p0 := p38Val) (q0 := q38Val) (p1 := p39Val) (q1 := q39Val)
            (by decide) (by decide) (by decide)
            (pow2_lt_pow3_of_eval (by decide) (by decide) (by decide) hconv.2.2.2.2.1)
            (pow3_lt_pow2_of_eval (by decide) (by decide) (by decide) hconv.2.2.2.2.2.1)
            hW1 hw39 hcyc_lt
          exact checkSlabEliminated_sound hg1.2.2.1 hcyc hm_le (Nat.le_of_not_lt hw37) hfl
            (ratio_transfer_evalPow2Pow3 (by decide) (by decide) (by decide) (Nat.le_of_lt hr))
        · by_cases hw41 : W < q41Val
          · have hr := unimodular_odd_upper_ratio (p0 := p40Val) (q0 := q40Val) (p1 := p41Val) (q1 := q41Val)
              (by decide) (by decide) (by decide)
              (pow2_lt_pow3_of_eval (by decide) (by decide) (by decide) hconv.2.2.2.2.2.2.1)
              (pow3_lt_pow2_of_eval (by decide) (by decide) (by decide) hconv.2.2.2.2.2.2.2.1)
              hW1 hw41 hcyc_lt
            exact checkSlabEliminated_sound hg1.2.2.2.1 hcyc hm_le (Nat.le_of_not_lt hw39) hfl
              (ratio_transfer_evalPow2Pow3 (by decide) (by decide) (by decide) (Nat.le_of_lt hr))
          · by_cases hw43 : W < q43Val
            · have hr := unimodular_unit_slab_ratio (p1 := p41Val) (q1 := q41Val) (p2 := p42Val) (q2 := q42Val)
                (by decide) (by decide) (by decide)
                (pow3_lt_pow2_of_eval (by decide) (by decide) (by decide) hconv.2.2.2.2.2.2.2.1)
                (pow2_lt_pow3_of_eval (by decide) (by decide) (by decide) hconv.2.2.2.2.2.2.2.2.1)
                hW1 (by rw [show q41Val + q42Val = q43Val from rfl]; exact hw43) hcyc_lt
              exact checkSlabEliminated_sound hg1.2.2.2.2 hcyc hm_le (Nat.le_of_not_lt hw41) hfl
                (ratio_transfer_evalPow2Pow3 (by decide) (by decide) (by decide) hr)
            · by_cases hw45 : W < q45Val
              · have hcases := unimodular_q43_cases (p1 := p43Val) (q1 := q43Val) (p2 := p44Val) (q2 := q44Val)
                  (by decide) (by decide) (by decide) (by decide)
                  (pow3_lt_pow2_of_eval (by decide) (by decide) (by decide) hconv.2.2.2.2.2.2.2.2.2.1)
                  (pow2_lt_pow3_of_eval (by decide) (by decide) (by decide) hconv.2.2.2.2.2.2.2.2.2.2.1)
                  (Nat.le_of_not_lt hw43) hcyc_lt
                rcases hcases with ⟨hK_p43, hW_q43⟩ | ⟨hW_2q43, hr_2q43⟩ | hW_q4344 | hr_39
                · by_cases hm91 : steps.length ≤ 91
                  · rcases evalPow2Pow3_eq_subst (S := 256) (nbits := 92)
                      (by decide) (by decide) (by decide) hK_p43 hW_q43 with ⟨hL43, _⟩
                    exact checkSlabEliminated_sound hg2.1 hcyc hm91 (Nat.le_of_not_lt hw43) hfl hL43
                  · exact no_spiral_cycle_m92_q43_core hbar hsubsumed hout_bounds hhensel
                      hcyc (by omega) hK_p43 hW_q43
                · exact checkSlabEliminated_sound hg2.2.1 hcyc hm_le hW_2q43 hfl
                    (ratio_transfer_evalPow2Pow3 (by decide) (by decide) (by decide) hr_2q43)
                · have hr := unimodular_odd_upper_ratio (p0 := p44Val) (q0 := q44Val) (p1 := p45Val) (q1 := q45Val)
                    (by decide) (by decide) (by decide)
                    (pow2_lt_pow3_of_eval (by decide) (by decide) (by decide) hconv.2.2.2.2.2.2.2.2.2.2.1)
                    (pow3_lt_pow2_of_eval (by decide) (by decide) (by decide) hconv.2.2.2.2.2.2.2.2.2.2.2.1)
                    hW1 hw45 hcyc_lt
                  exact checkSlabEliminated_sound hg2.2.2.1 hcyc hm_le hW_q4344 hfl
                    (ratio_transfer_evalPow2Pow3 (by decide) (by decide) (by decide) (Nat.le_of_lt hr))
                · exact checkSlabEliminated_sound hg2.2.2.2.1 hcyc hm_le (Nat.le_of_not_lt hw43) hfl
                    (ratio_transfer_evalPow2Pow3 (by decide) (by decide) (by decide) (Nat.le_of_lt hr_39))
              · have hr := unimodular_odd_upper_ratio (p0 := p50Val) (q0 := q50Val) (p1 := p51Val) (q1 := q51Val)
                  (by decide) (by decide) (by decide)
                  (pow2_lt_pow3_of_eval (by decide) (by decide) (by decide) hconv.2.2.2.2.2.2.2.2.2.2.2.2.1)
                  (pow3_lt_pow2_of_eval (by decide) (by decide) (by decide) hconv.2.2.2.2.2.2.2.2.2.2.2.2.2)
                  hW1 (Nat.lt_of_not_le hw51) hcyc_lt
                exact checkSlabEliminated_sound hg2.2.2.2.2.1 hcyc hm_le (Nat.le_of_not_lt hw45) hfl
                  (ratio_transfer_evalPow2Pow3 (by decide) (by decide) (by decide) (Nat.le_of_lt hr))

-- 13.7 Closing the Zero-Trust-Gap `m = 92` Hensel Bridge (`no_nontrivial_spiral_cycles_1_to_92`)

def checkM92BoundsSubsumed : Nat -> Bool
  | 0 => true
  | d + 1 =>
    let k := d + 9
    let b := m92BandBounds k
    (b.1 ≤ derivedM92Lo k) && (derivedM92Hi k ≤ b.2) && checkM92BoundsSubsumed d

theorem checkM92BoundsSubsumed_sound : ∀ (n k : Nat),
    checkM92BoundsSubsumed n = true -> 9 ≤ k -> k < 9 + n ->
    (m92BandBounds k).1 ≤ derivedM92Lo k ∧ derivedM92Hi k ≤ (m92BandBounds k).2
  | 0, _, _, h9, hlt => by omega
  | d + 1, k, hok, h9, hlt => by
    unfold checkM92BoundsSubsumed at hok
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    by_cases htop : k = d + 9
    · subst htop
      exact ⟨hok.1.1, hok.1.2⟩
    · exact checkM92BoundsSubsumed_sound d k hok.2 h9 (by omega)

theorem lookupActiveBand_outside :
    ∀ (bs : List HenselBandCert) (k : Nat),
      (bs.all (fun b => decide (9 ≤ b.k1 ∧ b.k1 ≤ 73))) = true ->
      (k ≤ 8 ∨ 74 ≤ k) ->
      lookupActiveBand k bs = none
  | [], _, _, _ => rfl
  | hd :: tl, k, hok, hout => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hok
    unfold lookupActiveBand
    have hneq : (hd.k1 == k) = false := decide_eq_false (by omega)
    rw [hneq]
    exact lookupActiveBand_outside tl k hok.2 hout

theorem lookupOddGapBand_outside :
    ∀ (es : List (Nat × Nat × Nat × Nat)) (k : Nat),
      (es.all (fun e => decide (9 ≤ e.1 ∧ e.1 ≤ 73))) = true ->
      (k ≤ 8 ∨ 74 ≤ k) ->
      lookupOddGapBand k es = none
  | [], _, _, _ => rfl
  | hd :: tl, k, hok, hout => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hok
    unfold lookupOddGapBand
    have hneq : (hd.1 == k) = false := decide_eq_false (by omega)
    rw [hneq]
    exact lookupOddGapBand_outside tl k hok.2 hout

set_option maxRecDepth 20000 in
theorem exactM92_hensel_bridge_certified :
    verifyTwoStepHenselCert exactM92B1 exactM92B2 m92HenselBands = true ∧
    3 ^ 8 * (m92GlobalHi1 + 1) < 2 ^ 8 * (2 * (exactM92B1 + 1) + 1) ∧
    checkM92BoundsSubsumed 65 = true ∧
    (m92HenselBands.all (fun b => decide (9 ≤ b.k1 ∧ b.k1 ≤ 73))) = true ∧
    (m92NoOddMulBands.all (fun e => decide (9 ≤ e.1 ∧ e.1 ≤ 73))) = true := by
  decide

theorem m92BandBounds_outside (k : Nat) (hout : k ≤ 8 ∨ 74 ≤ k) :
    m92BandBounds k = (barinaXMin, m92GlobalHi1) := by
  have hbr := exactM92_hensel_bridge_certified
  unfold m92BandBounds
  rw [lookupActiveBand_outside m92HenselBands k hbr.2.2.2.1 hout,
      lookupOddGapBand_outside m92NoOddMulBands k hbr.2.2.2.2 hout]
  rfl

theorem exactM92_all_k1_hensel_complete
    (k1 l1 k2 l2 : Nat) (z1 z2 z3 : Int)
    (hk1 : k1 ≥ 1)
    (hz1_lo : ((m92BandBounds k1).1 : Int) ≤ z1)
    (hz1_hi : z1 ≤ ((m92BandBounds k1).2 : Int)) :
    ¬ ValidTwoStepSpiral exactM92B1 exactM92B2 k1 l1 k2 l2 z1 z2 z3 := by
  intro hvalid
  have hbr := exactM92_hensel_bridge_certified
  have hnon := m92_nonactive_bounds_kernel_verified
  unfold m92BandBounds at hz1_lo hz1_hi
  cases hact : lookupActiveBand k1 m92HenselBands with
  | some b =>
    simp only [hact] at hz1_lo hz1_hi
    rcases lookupActiveBand_mem m92HenselBands k1 b hact with ⟨hb_mem, hb_k1⟩
    rw [← hb_k1] at hvalid
    exact verifyTwoStepHenselCert_sound m92HenselBands exactM92B1 exactM92B2 b hbr.1 hb_mem
      l1 k2 l2 z1 z2 z3 hz1_lo hz1_hi hvalid
  | none =>
    simp only [hact] at hz1_lo hz1_hi
    rcases hvalid with ⟨hl1, _hk2, _hl2, hz2_lo, _hz2_hi, _hz3_lo, hs1_int, _hs2_int⟩
    let n1 := z1.toNat
    let n2 := z2.toNat
    have hn2_lo : exactM92B1 + 1 ≤ n2 := by dsimp [n2]; omega
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
            simp only [hgap_tmp] at hz1_lo; dsimp [n1]; omega
          | none =>
            simp only [hgap_tmp] at hz1_lo; dsimp [n1]; omega
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
      by_cases hk8 : k1 ≤ 8
      · exact no_spiral_step_of_pow3_lt_target k1 8 l1 m92GlobalHi1 (exactM92B1 + 1) n1 n2
          hk8 hl1 (by dsimp [n1]; omega) hn2_lo hbr.2.1 hs1_nat
      · by_cases hk74 : 74 ≤ k1
        · exact no_spiral_step_of_hi_lt_pow2 k1 74 l1 m92GlobalHi1 n1 n2
            hk74 hl1 (by dsimp [n1]; omega) hnon.2.1 hs1_nat
        · rcases checkM92MidRange_covered 65 k1 hnon.2.2.2 (by omega) (by omega) with ha | hg
          · rw [hact] at ha; simp at ha
          · rw [hgap] at hg; simp at hg

/--
  Master Theorem 26 (Fully Closed Zero-Trust-Gap Cycle Elimination for `1 <= m <= 92`):
  Assuming ONLY `BarinaThreshold (2^71)` and `BakerLMNPowerBound` (with ZERO external
  Python interval constants — every `ln 2`, `ln 3`, convergent, sorted-cyclic threshold,
  `m = 92` band bound, and 2-step Hensel congruence is certified inside the Lean 4 kernel),
  NO non-trivial positive spiral cycle of block count `1 <= m <= 92` exists!
-/
theorem no_nontrivial_spiral_cycles_1_to_92
    {steps : List SpiralStepData}
    (hbar : BarinaThreshold (2 ^ 71))
    (hbaker : BakerLMNPowerBound)
    (hcyc : IsNontrivialSpiralCycle steps)
    (hm_le : steps.length ≤ 92) :
    False := by
  have hbr := exactM92_hensel_bridge_certified
  exact no_nontrivial_spiral_cycles_1_to_92_core hbar hbaker
    (fun k hk9 hk73 => checkM92BoundsSubsumed_sound 65 k hbr.2.2.1 hk9 (by omega))
    m92BandBounds_outside
    exactM92_all_k1_hensel_complete
    hcyc hm_le

-- ============================================================================
-- 13.8A Generalized Baker `W >= q51` Elimination Through `m <= 99`
-- ============================================================================

theorem exp_beats_baker_quad_68_aux :
    ∀ d : Nat, 2 ^ (20 + d) ≥ 12008 + 14 * (91 + d) ^ 2 + 28 * d + 2600
  | 0 => by decide
  | d + 1 => by
    have ih := exp_beats_baker_quad_68_aux d
    have hp : 2 ^ (20 + (d + 1)) = 2 ^ (20 + d) + 2 ^ (20 + d) := by
      rw [show 20 + (d + 1) = (20 + d) + 1 by omega, Nat.pow_succ]; omega
    have hsq : (91 + (d + 1)) ^ 2 = (91 + d) ^ 2 + 2 * d + 183 := by
      have hexp : ∀ x : Nat, (x + 1) ^ 2 = x ^ 2 + 2 * x + 1 := fun x => by
        simp only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul, Nat.mul_add, Nat.add_mul, Nat.mul_one]
        omega
      rw [show 91 + (d + 1) = (91 + d) + 1 by omega, hexp (91 + d)]
      omega
    rw [hp, hsq, Nat.mul_add, Nat.mul_add]
    omega

theorem exp_beats_baker_quad_68 {r : Nat} (hr : r ≥ 88) :
    2 ^ (r - 68) - 8 > 12000 + 14 * (r + 3) ^ 2 := by
  have h := exp_beats_baker_quad_68_aux (r - 88)
  rw [show 20 + (r - 88) = r - 68 by omega, show 91 + (r - 88) = r + 3 by omega] at h
  omega

def checkBakerQ51Le99Props (B Theta lD0 uN0p : Nat) : Bool :=
  (2 ^ B ≤ Theta) &&
  (2 ^ B - (uN0p - lD0 + 1) + uN0p + 1 ≤ 2 ^ B + lD0) &&
  ((Theta - 2 ^ B) * (100 * 2 ^ B) ≥ 2 ^ B * (2 ^ B - (uN0p - lD0 + 1) + 1)) &&
  (2 ^ B + ceilScaleSumAcc B Theta 98 (ceilScaleIter B Theta 1 (2 ^ B)) + 2 ^ B ≤ 2 ^ 67 * 2 ^ B)

def checkBakerQ51Le99Cert : Bool :=
  let (_, Theta, ok3) := certifyLog2Pow 160 140 3
  let (lD0, _, okD) := certifyLog2Pow 160 140 (3 * (barinaXMin + 1))
  let (_, uN0p, okN) := certifyLog2Pow 160 140 (3 * barinaXMin + 5)
  ok3 && okD && okN &&
  checkBakerQ51Le99Props 140 Theta lD0 uN0p &&
  (2 ^ 88 ≤ q51Val)

set_option maxRecDepth 20000 in
theorem baker_q51_le_99_constants_certified : checkBakerQ51Le99Cert = true := by
  decide

theorem no_spiral_cycle_baker_le_99_core
    {steps : List SpiralStepData} {B Theta lD0 uN0p E xMin c67 N : Nat}
    (hbaker : BakerLMNPowerBound)
    (hcyc : IsNontrivialSpiralCycle steps)
    (hm_le : steps.length ≤ 99)
    (hfl : ∀ s ∈ steps, s.x ≥ xMin) (hxmin_pos : xMin ≥ 1)
    (hTheta : phiLog B 3 < Theta) (hTheta_gt : 2 ^ B ≤ Theta)
    (hD0 : lD0 ≤ phiLog B (3 * (xMin + 1)))
    (hN0p : phiLog B (3 * xMin + 5) < uN0p)
    (hE : E + uN0p + 1 ≤ 2 ^ B + lD0)
    (hgrow100 : (Theta - 2 ^ B) * (100 * 2 ^ B) ≥ 2 ^ B * (E + 1))
    (hscale : 2 ^ B + ceilScaleSumAcc B Theta 98 (ceilScaleIter B Theta 1 (2 ^ B)) + 2 ^ B ≤
      c67 * 2 ^ B)
    (hW_pos : spiralChainTotalW steps ≥ 2)
    (hN_ge100 : N ≥ 100)
    (hN_mul_W : c67 * N ≤ spiralChainTotalW steps)
    (hexp_gt : 12000 + 14 * (flog2 (spiralChainTotalW steps) + 3) ^ 2 < N - 8) :
    False := by
  let W := spiralChainTotalW steps
  let K := spiralChainTotalK steps
  have hm_ge1 : steps.length ≥ 1 := by
    cases steps with
    | nil => cases hcyc
    | cons _ _ => simp
  have hpN : 2 ^ N ≥ 1 := pow2_pos_nat N
  have hb_u0 : phiLog B ((2 ^ N - 1) + 1) ≤ N * 2 ^ B := by
    rw [show (2 ^ N - 1) + 1 = 2 ^ N by omega, phiLog_pow2 B N]
    exact Nat.le_refl _
  have hgrowN : (Theta - 2 ^ B) * (N * 2 ^ B) ≥ 2 ^ B * (E + 1) := by
    have hm : 100 * 2 ^ B ≤ N * 2 ^ B := Nat.mul_le_mul_right (2 ^ B) hN_ge100
    exact Nat.le_trans hgrow100 (Nat.mul_le_mul_left (Theta - 2 ^ B) hm)
  have hrhs_lt : sortedCyclicRhsSum B Theta E (N * 2 ^ B) steps.length 1 < 2 ^ B * W := by
    have hm_mono := sortedCyclicRhsSum_mono_m B Theta E (N * 2 ^ B) 1 steps.length 99 hm_le
    unfold sortedCyclicRhsSum at hm_mono ⊢
    simp only [Nat.one_mul, show 99 - 1 = 98 from rfl] at hm_mono
    have htail := phiGeomTailSum_le_mul_ceilScaleAcc B Theta E N 98 1
    have hsum_le : N * 2 ^ B + phiGeomTailSum B Theta E (N * 2 ^ B) 98 1 + N * 2 ^ B ≤
        N * (c67 * 2 ^ B) := by
      have hm := Nat.mul_le_mul_left N hscale
      rw [Nat.mul_add, Nat.mul_add] at hm
      omega
    have hNW : N * (c67 * 2 ^ B) ≤ 2 ^ B * W := by
      calc
        N * (c67 * 2 ^ B) = 2 ^ B * (c67 * N) := by
          rw [← Nat.mul_assoc, Nat.mul_comm N c67, Nat.mul_comm _ (2 ^ B)]
        _ ≤ 2 ^ B * W := Nat.mul_le_mul_left (2 ^ B) hN_mul_W
    have _hNQ_pos : N * 2 ^ B ≥ 1 := Nat.mul_pos (by omega) (pow2_pos_nat B)
    omega
  have hcnt0 : countLe (2 ^ N - 1) (spiralVertices steps) ≤ 0 :=
    sortedCyclic_countLe_bound (by decide) hm_ge1 hcyc hfl hxmin_pos
      hTheta hTheta_gt hD0 hN0p hE hgrowN hb_u0 hrhs_lt
  have hxs_ge_2N : ∀ x ∈ spiralVertices steps, x ≥ (2 ^ N - 1) + 1 := by
    intro x hx
    apply Classical.byContradiction
    intro hlt
    have hge1 := mem_le_implies_countLe_pos (2 ^ N - 1) (spiralVertices steps) ⟨x, hx, by omega⟩
    omega
  have hstep1 : stepU (2 ^ N) (2 ^ N - 1) = 1 := by
    unfold stepU
    have hsub : (2 ^ N - 1) + 1 = 2 ^ N := by omega
    rw [hsub]
    apply Nat.le_antisymm
    · apply Classical.byContradiction
      intro hgt
      have hm := mul_div_le_nat (2 ^ N + (2 ^ N - 1)) (2 ^ N)
      have hm2 := Nat.mul_le_mul_left (2 ^ N) (show 2 ≤ (2 ^ N + (2 ^ N - 1)) / 2 ^ N by omega)
      omega
    · exact le_div_of_mul_le hpN (by omega)
  let xs := spiralVertices steps
  have hcap_le99 : teleStepCap (2 ^ N) (2 ^ N - 1) [] xs.length ≤ 99 := by
    simp only [teleStepCap, hstep1, Nat.mul_one]
    simpa [xs, spiralVertices] using hm_le
  have _h2N_ge128 : 2 ^ N ≥ 128 := by
    have hm := pow2_mono_nat (show 7 ≤ N by omega)
    simpa using hm
  have hbern := teleBernoulli_ratio_bound (2 ^ N) (2 ^ N - 1) [] xs
    hpN hxs_ge_2N rfl (by intro _ h; cases h) (by omega)
  rcases spiralCycle_global_prod_bounds hcyc with ⟨_hP_pos, hcyc_lt, hglob⟩
  have hsub99 : 2 ^ N - 99 ≤ 2 ^ N - teleStepCap (2 ^ N) (2 ^ N - 1) [] xs.length := by omega
  have hbern99 : (2 ^ N - 99) * prodList (xs.map (fun x => x + 1)) ≤ 2 ^ N * prodList xs :=
    Nat.le_trans (Nat.mul_le_mul_right _ hsub99) hbern
  have hlt1 : (2 ^ N - 99) * (2 ^ K * prodList xs) <
      (2 ^ N - 99) * (3 ^ W * prodList (xs.map (fun x => x + 1))) :=
    Nat.mul_lt_mul_of_pos_left hglob (by omega)
  have hle2 : (2 ^ N - 99) * (3 ^ W * prodList (xs.map (fun x => x + 1))) ≤
      (2 ^ N * 3 ^ W) * prodList xs := by
    calc
      (2 ^ N - 99) * (3 ^ W * prodList (xs.map (fun x => x + 1)))
          = 3 ^ W * ((2 ^ N - 99) * prodList (xs.map (fun x => x + 1))) := by
            rw [← Nat.mul_assoc, Nat.mul_comm (2 ^ N - 99) (3 ^ W), Nat.mul_assoc]
      _ ≤ 3 ^ W * (2 ^ N * prodList xs) := Nat.mul_le_mul_left _ hbern99
      _ = (2 ^ N * 3 ^ W) * prodList xs := by
            rw [← Nat.mul_assoc, Nat.mul_comm (3 ^ W) (2 ^ N)]
  have hprod_cancel : (2 ^ N - 99) * 2 ^ K < 2 ^ N * 3 ^ W := by
    have hcomb : ((2 ^ N - 99) * 2 ^ K) * prodList xs < (2 ^ N * 3 ^ W) * prodList xs := by
      rw [Nat.mul_assoc]
      exact Nat.lt_of_lt_of_le hlt1 hle2
    apply Classical.byContradiction
    intro hge
    have hm := Nat.mul_le_mul_right (prodList xs)
      (show 2 ^ N * 3 ^ W ≤ (2 ^ N - 99) * 2 ^ K by omega)
    omega
  have hdiff_bound : 2 ^ (N - 8) * (2 ^ K - 3 ^ W) ≤ 3 ^ W := by
    have h2N1 : 2 ^ (N - 1) ≤ 2 ^ N - 99 := by
      have hp : 2 ^ N = 2 ^ (N - 1) + 2 ^ (N - 1) := by
        calc
          2 ^ N = 2 ^ ((N - 1) + 1) := congrArg (2 ^ ·) (by omega)
          _ = 2 ^ (N - 1) * 2 := Nat.pow_succ _ _
          _ = 2 ^ (N - 1) + 2 ^ (N - 1) := by omega
      have h7 : 128 ≤ 2 ^ (N - 1) := by
        simpa using pow2_mono_nat (show 7 ≤ N - 1 by omega)
      omega
    have hm1 : 2 ^ (N - 1) * (2 ^ K - 3 ^ W) < 99 * 3 ^ W := by
      have hm := Nat.mul_le_mul_right (2 ^ K - 3 ^ W) h2N1
      have hlt_sub : (2 ^ N - 99) * (2 ^ K - 3 ^ W) < 99 * 3 ^ W := by
        have _hlt_kw : 3 ^ W < 2 ^ K := hcyc_lt
        have _hp3w : 3 ^ W ≥ 1 := pow3_pos_nat W
        rw [Nat.mul_sub_left_distrib]
        have hexp : (2 ^ N - 99) * 3 ^ W + 99 * 3 ^ W = 2 ^ N * 3 ^ W := by
          rw [← Nat.add_mul, show 2 ^ N - 99 + 99 = 2 ^ N by omega]
        omega
      exact Nat.lt_of_le_of_lt hm hlt_sub
    have hp8 : 2 ^ (N - 1) = 128 * 2 ^ (N - 8) := by
      rw [show (128 : Nat) = 2 ^ 7 from rfl, ← Nat.pow_add, show 7 + (N - 8) = N - 1 by omega]
    rw [hp8, Nat.mul_assoc] at hm1
    omega
  have hpow_le : 2 ^ (12000 + 14 * (flog2 W + 3) ^ 2) ≤ 2 ^ (N - 8) :=
    pow2_mono_nat (Nat.le_of_lt hexp_gt)
  have hbaker_le : 2 ^ (12000 + 14 * (flog2 W + 3) ^ 2) * (2 ^ K - 3 ^ W) ≤ 3 ^ W :=
    Nat.le_trans (Nat.mul_le_mul_right _ hpow_le) hdiff_bound
  have hbaker_gt := hbaker K W hW_pos hcyc_lt
  omega

theorem baker_N_bounds_68 {W : Nat} (hW_pow88 : 2 ^ 88 ≤ W) :
    W ≥ 2 ∧
    W / 2 ^ 68 ≥ 100 ∧
    2 ^ 67 * (W / 2 ^ 68) ≤ W ∧
    12000 + 14 * (flog2 W + 3) ^ 2 < W / 2 ^ 68 - 8 := by
  have hW_pos : W ≥ 2 := Nat.le_trans (by decide : 2 ≤ 2 ^ 88) hW_pow88
  have hN100 : W / 2 ^ 68 ≥ 100 :=
    le_div_of_mul_le (pow2_pos_nat 68)
      (Nat.le_trans (by decide : 2 ^ 68 * 100 ≤ 2 ^ 88) hW_pow88)
  have hNmul : 2 ^ 67 * (W / 2 ^ 68) ≤ W := by
    have hm : 2 ^ 68 * (W / 2 ^ 68) ≤ W := mul_div_le_nat W (2 ^ 68)
    have hp : 2 ^ 68 = 2 ^ 67 * 2 := rfl
    rw [hp, Nat.mul_assoc] at hm
    exact Nat.le_trans
      (Nat.mul_le_mul_left (2 ^ 67) (Nat.le_mul_of_pos_left _ (by decide : 2 > 0))) hm
  rcases flog2_spec W (Nat.le_trans (by decide : 1 ≤ 2) hW_pos) with ⟨hr_lo, hr_hi⟩
  have hlt88 : 88 < flog2 W + 1 :=
    pow_lt_exp_cancel_nat (by decide) (Nat.lt_of_le_of_lt hW_pow88 hr_hi)
  have hr_ge88 : flog2 W ≥ 88 := Nat.le_of_lt_succ hlt88
  have h68 : 68 + (flog2 W - 68) = flog2 W :=
    Nat.add_sub_of_le (Nat.le_trans (by decide : 68 ≤ 88) hr_ge88)
  have hNpow : 2 ^ (flog2 W - 68) ≤ W / 2 ^ 68 := by
    apply le_div_of_mul_le (pow2_pos_nat 68)
    rw [← Nat.pow_add, h68]
    exact hr_lo
  have hb := exp_beats_baker_quad_68 hr_ge88
  have hexp : 12000 + 14 * (flog2 W + 3) ^ 2 < W / 2 ^ 68 - 8 :=
    Nat.lt_of_lt_of_le hb (Nat.sub_le_sub_right hNpow 8)
  exact ⟨hW_pos, hN100, hNmul, hexp⟩

/--
  Generalized Asymptotic Baker `W >= q51` Elimination Through `m <= 99`:
  Under `BarinaThreshold (2^71)` and `BakerLMNPowerBound`, NO non-trivial spiral cycle
  with `steps.length <= 99` and `spiralChainTotalW steps >= q51Val` can exist!
-/
theorem no_spiral_cycle_ge_q51_le_99 {steps : List SpiralStepData}
    (hbar : BarinaThreshold (2 ^ 71))
    (hbaker : BakerLMNPowerBound)
    (hcyc : IsNontrivialSpiralCycle steps)
    (hm_le : steps.length ≤ 99)
    (hw_ge : q51Val ≤ spiralChainTotalW steps) :
    False := by
  have hc := baker_q51_le_99_constants_certified
  unfold checkBakerQ51Le99Cert at hc
  rcases hcert3 : certifyLog2Pow 160 140 3 with ⟨_, Theta, ok3⟩
  rcases hcertD : certifyLog2Pow 160 140 (3 * (barinaXMin + 1)) with ⟨lD0, _, okD⟩
  rcases hcertN : certifyLog2Pow 160 140 (3 * barinaXMin + 5) with ⟨_, uN0p, okN⟩
  rw [hcert3, hcertD, hcertN] at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  rcases hc with ⟨⟨⟨⟨hok3, hokD⟩, hokN⟩, hprops⟩, hq51_pow⟩
  unfold checkBakerQ51Le99Props at hprops
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hprops
  rcases hprops with ⟨⟨⟨hTheta_gt, hE⟩, hgrow100⟩, hscale67⟩
  have hs3 := certifyLog2Pow_sound 160 140 3 (by rw [hcert3]; exact hok3)
  rw [hcert3] at hs3
  have hsD := certifyLog2Pow_sound 160 140 (3 * (barinaXMin + 1)) (by rw [hcertD]; exact hokD)
  rw [hcertD] at hsD
  have hsN := certifyLog2Pow_sound 160 140 (3 * barinaXMin + 5) (by rw [hcertN]; exact hokN)
  rw [hcertN] at hsN
  rcases baker_N_bounds_68 (Nat.le_trans hq51_pow hw_ge) with ⟨hW_pos, hN100, hNmul, hexp⟩
  exact no_spiral_cycle_baker_le_99_core hbaker hcyc hm_le
    (nontrivial_cycle_vertex_floor hbar hcyc) (by decide)
    hs3.2.1 hTheta_gt hsD.1 hsN.2.1 hE hgrow100 hscale67
    hW_pos hN100 hNmul hexp

-- ============================================================================
-- 13.8B `q43`-Multiple Confinement (`m <= 96`) & Monotone `u`-Tail Slabs (`m <= 99`)
-- ============================================================================

theorem unimodular_q43_exact_multiples {p1 q1 p2 q2 K W : Nat}
    (_hq1 : q1 ≥ 1) (hq2 : q2 ≥ 1)
    (hunim : p1 * q2 = p2 * q1 + 1)
    (hgap37 : 37 * q1 < q2)
    (hodd : 3 ^ q1 < 2 ^ p1) (heven : 2 ^ p2 < 3 ^ q2)
    (hW_ge : q1 ≤ W) (hcyc : 3 ^ W < 2 ^ K) :
    (∃ u : Nat, u ≥ 1 ∧ K = u * p1 ∧ W = u * q1) ∨
    (W ≥ q1 + q2) ∨
    (2 ^ (39 * p1) * 3 ^ W < 2 ^ K * 3 ^ (39 * q1)) := by
  have hu_lt : p2 * W < K * q2 := cross_exp_lt_of_pow23 hq2 (by omega) heven hcyc
  let u := K * q2 - p2 * W
  have hu_ge1 : u ≥ 1 := by dsimp [u]; omega
  have hu_eq : u + p2 * W = K * q2 := by dsimp [u]; omega
  by_cases hv_pos : K * q1 < p1 * W
  · let v := p1 * W - K * q1
    have hv1 : v ≥ 1 := by dsimp [v]; omega
    have hv_eq : K * q1 + v = p1 * W := by dsimp [v]; omega
    have h1 := congrArg (· * q1) hu_eq
    have h2 := congrArg (· * q2) hv_eq
    rw [Nat.add_mul, Nat.mul_assoc p2 W q1, Nat.mul_comm W q1, ← Nat.mul_assoc p2 q1 W] at h1
    rw [Nat.add_mul, Nat.mul_assoc K q1 q2, Nat.mul_comm q1 q2, ← Nat.mul_assoc K q2 q1,
        Nat.mul_assoc p1 W q2, Nat.mul_comm W q2, ← Nat.mul_assoc p1 q2 W,
        hunim, Nat.add_mul, Nat.one_mul] at h2
    have _hW_uv : u * q1 + v * q2 = W := by omega
    have _huq : q1 ≤ u * q1 := by simpa using Nat.mul_le_mul_right q1 hu_ge1
    have _hvq : q2 ≤ v * q2 := by simpa using Nat.mul_le_mul_right q2 hv1
    exact Or.inr (Or.inl (by omega))
  · let s := K * q1 - p1 * W
    have hs_eq : p1 * W + s = K * q1 := by dsimp [s]; omega
    have hW_eq : W + s * q2 = u * q1 := by
      have h1 := congrArg (· * q1) hu_eq
      have h2 := congrArg (· * q2) hs_eq
      rw [Nat.add_mul, Nat.mul_assoc p2 W q1, Nat.mul_comm W q1, ← Nat.mul_assoc p2 q1 W] at h1
      rw [Nat.add_mul, Nat.mul_assoc p1 W q2, Nat.mul_comm W q2, ← Nat.mul_assoc p1 q2 W,
          hunim, Nat.add_mul, Nat.one_mul, Nat.mul_assoc K q1 q2, Nat.mul_comm q1 q2,
          ← Nat.mul_assoc K q2 q1] at h2
      omega
    have hK_eq : K + s * p2 = u * p1 := by
      have hq2_eq : q2 * (K + s * p2) = q2 * (u * p1) := by
        calc
          q2 * (K + s * p2)
              = K * q2 + s * q2 * p2 := by
                rw [Nat.mul_add, Nat.mul_comm q2 K, Nat.mul_comm q2 (s * p2),
                    Nat.mul_assoc s p2 q2, Nat.mul_comm p2 q2, ← Nat.mul_assoc]
          _ = (u + p2 * W) + s * q2 * p2 := by rw [← hu_eq]
          _ = u + (W + s * q2) * p2 := by
                rw [Nat.add_mul W (s * q2) p2, Nat.mul_comm W p2, Nat.add_assoc]
          _ = u + (u * q1) * p2 := by rw [hW_eq]
          _ = u * (p2 * q1 + 1) := by
                rw [Nat.mul_add, Nat.mul_one, Nat.mul_assoc u q1 p2, Nat.mul_comm q1 p2,
                    Nat.add_comm]
          _ = u * (p1 * q2) := by rw [← hunim]
          _ = q2 * (u * p1) := by rw [← Nat.mul_assoc u p1 q2, Nat.mul_comm (u * p1) q2]
      exact Nat.eq_of_mul_eq_mul_left hq2 hq2_eq
    by_cases hs0 : s = 0
    · rw [hs0, Nat.zero_mul, Nat.add_zero] at hW_eq hK_eq
      exact Or.inl ⟨u, hu_ge1, hK_eq, hW_eq⟩
    · have hs1 : s ≥ 1 := by omega
      have _hsq2 : q2 ≤ s * q2 := by simpa using Nat.mul_le_mul_right q2 hs1
      have hu39 : u ≥ 39 := by
        apply Classical.byContradiction
        intro hlt39
        have hm : u * q1 ≤ 38 * q1 := Nat.mul_le_mul_right q1 (by omega)
        omega
      refine Or.inr (Or.inr ?_)
      have hu_pow : 3 ^ ((u - 39) * q1) ≤ 2 ^ ((u - 39) * p1) := by
        rw [Nat.mul_comm (u - 39) q1, Nat.mul_comm (u - 39) p1,
            ← pow_mul_exp_nat 3 q1 (u - 39), ← pow_mul_exp_nat 2 p1 (u - 39)]
        exact pow_le_pow_pos_nat (pow3_pos_nat q1) (Nat.le_of_lt hodd) (u - 39)
      have hu_step : 2 ^ (39 * p1) * 3 ^ (u * q1) ≤ 2 ^ (u * p1) * 3 ^ (39 * q1) := by
        have hsq : u * q1 = 39 * q1 + (u - 39) * q1 := by
          conv => lhs; rw [show u = 39 + (u - 39) by omega]; rw [Nat.add_mul]
        have hsp : u * p1 = 39 * p1 + (u - 39) * p1 := by
          conv => lhs; rw [show u = 39 + (u - 39) by omega]; rw [Nat.add_mul]
        rw [hsq, hsp, Nat.pow_add 3, Nat.pow_add 2]
        have hm := Nat.mul_le_mul_left (2 ^ (39 * p1) * 3 ^ (39 * q1)) hu_pow
        calc
          2 ^ (39 * p1) * (3 ^ (39 * q1) * 3 ^ ((u - 39) * q1))
              = (2 ^ (39 * p1) * 3 ^ (39 * q1)) * 3 ^ ((u - 39) * q1) := by rw [← Nat.mul_assoc]
          _ ≤ (2 ^ (39 * p1) * 3 ^ (39 * q1)) * 2 ^ ((u - 39) * p1) := hm
          _ = (2 ^ (39 * p1) * 2 ^ ((u - 39) * p1)) * 3 ^ (39 * q1) := by
                rw [Nat.mul_assoc (2 ^ (39 * p1)), Nat.mul_comm (3 ^ (39 * q1)), ← Nat.mul_assoc]
      have hs_pow : 2 ^ (s * p2) < 3 ^ (s * q2) := by
        rw [Nat.mul_comm s p2, Nat.mul_comm s q2, ← pow_mul_exp_nat 2 p2 s, ← pow_mul_exp_nat 3 q2 s]
        exact pow_lt_pow_pos_nat (pow2_pos_nat p2) heven s hs1
      rw [← hW_eq, ← hK_eq, Nat.pow_add 3 W, Nat.pow_add 2 K] at hu_step
      have hstrict : (2 ^ K * 2 ^ (s * p2)) * 3 ^ (39 * q1) <
          (2 ^ K * 3 ^ (39 * q1)) * 3 ^ (s * q2) := by
        have hpos : 2 ^ K * 3 ^ (39 * q1) ≥ 1 :=
          Nat.mul_pos (pow2_pos_nat K) (pow3_pos_nat (39 * q1))
        have hm := Nat.mul_lt_mul_of_pos_left hs_pow hpos
        rwa [Nat.mul_assoc (2 ^ K) (2 ^ (s * p2)) (3 ^ (39 * q1)),
             Nat.mul_comm (2 ^ (s * p2)) (3 ^ (39 * q1)), ← Nat.mul_assoc]
      have hcomb : (2 ^ (39 * p1) * 3 ^ W) * 3 ^ (s * q2) <
          (2 ^ K * 3 ^ (39 * q1)) * 3 ^ (s * q2) := by
        rw [Nat.mul_assoc (2 ^ (39 * p1))]
        exact Nat.lt_of_le_of_lt hu_step hstrict
      apply Classical.byContradiction
      intro hge
      have hm := Nat.mul_le_mul_right (3 ^ (s * q2))
        (show 2 ^ K * 3 ^ (39 * q1) ≤ 2 ^ (39 * p1) * 3 ^ W by omega)
      omega

theorem u_multiple_tail_ratio {p1 q1 u0 u K W : Nat}
    (hodd : 3 ^ q1 < 2 ^ p1)
    (hu_ge : u0 ≤ u)
    (hK : K = u * p1) (hW : W = u * q1) :
    u0 * q1 ≤ W ∧ 2 ^ (u0 * p1) * 3 ^ W ≤ 2 ^ K * 3 ^ (u0 * q1) := by
  refine ⟨by rw [hW]; exact Nat.mul_le_mul_right q1 hu_ge, ?_⟩
  rw [hK, hW]
  have hpow : 3 ^ ((u - u0) * q1) ≤ 2 ^ ((u - u0) * p1) := by
    rw [Nat.mul_comm (u - u0) q1, Nat.mul_comm (u - u0) p1,
        ← pow_mul_exp_nat 3 q1 (u - u0), ← pow_mul_exp_nat 2 p1 (u - u0)]
    exact pow_le_pow_pos_nat (pow3_pos_nat q1) (Nat.le_of_lt hodd) (u - u0)
  have hsq : u * q1 = u0 * q1 + (u - u0) * q1 := by
    conv => lhs; rw [show u = u0 + (u - u0) by omega]; rw [Nat.add_mul]
  have hsp : u * p1 = u0 * p1 + (u - u0) * p1 := by
    conv => lhs; rw [show u = u0 + (u - u0) by omega]; rw [Nat.add_mul]
  rw [hsq, hsp, Nat.pow_add 3, Nat.pow_add 2]
  have hm := Nat.mul_le_mul_left (2 ^ (u0 * p1) * 3 ^ (u0 * q1)) hpow
  calc
    2 ^ (u0 * p1) * (3 ^ (u0 * q1) * 3 ^ ((u - u0) * q1))
        = (2 ^ (u0 * p1) * 3 ^ (u0 * q1)) * 3 ^ ((u - u0) * q1) := by rw [← Nat.mul_assoc]
    _ ≤ (2 ^ (u0 * p1) * 3 ^ (u0 * q1)) * 2 ^ ((u - u0) * p1) := hm
    _ = (2 ^ (u0 * p1) * 2 ^ ((u - u0) * p1)) * 3 ^ (u0 * q1) := by
          rw [Nat.mul_assoc (2 ^ (u0 * p1)), Nat.mul_comm (3 ^ (u0 * q1)), ← Nat.mul_assoc]

def bsSlab96_35_37 : List Nat :=
  List.replicate 19 (2 ^ 71) ++ [
    19551394183820668404830134347,
    346278725554999788183837606118904135216837274,
    19601518535464936878288032096385207453902303933715772605540468352939990,
    2 ^ 256]

def bsSlab96_37_39 : List Nat :=
  List.replicate 14 (2 ^ 71) ++ [
    847299288450165303762350559527423,
    7738799960774894388399725678472692973693456611375254,
    2 ^ 256]

def bsSlab96_39_41 : List Nat :=
  List.replicate 10 (2 ^ 71) ++ [
    7802885588909017243042330819571,
    4592362066236829807930803112402498473746250338787,
    67061376693568125841078545852359001182218968986194516286015896740026058542653,
    2 ^ 256]

def bsSlab96_41_43 : List Nat :=
  List.replicate 7 (2 ^ 71) ++ [
    12976570244799879417745,
    55911256608642426382956170780081654,
    5921794256523248971810138250756512021298193166283742684,
    2 ^ 256]

def bsSlab96_39Q43 : List Nat :=
  List.replicate 5 (2 ^ 71) ++ [
    186580408057834136608776,
    3823138529586027856217503634434697756,
    4794396471396375292777888474653563765696252784317278053536,
    2 ^ 256]

set_option maxRecDepth 20000 in
theorem slab96_1_35_ok :
    checkSlabEliminated 128 112 256 96 1 barinaXMin
      (evalPow2Pow3Aux 256 p35Val q35Val 92).1 [] = true := by decide

set_option maxRecDepth 20000 in
theorem slab96_35_37_ok :
    checkSlabEliminated 128 112 256 96 q35Val barinaXMin
      (evalPow2Pow3Aux 256 p37Val q37Val 92).1 bsSlab96_35_37 = true := by decide

set_option maxRecDepth 20000 in
theorem slab96_37_39_ok :
    checkSlabEliminated 128 112 256 96 q37Val barinaXMin
      (evalPow2Pow3Aux 256 p39Val q39Val 92).1 bsSlab96_37_39 = true := by decide

set_option maxRecDepth 20000 in
theorem slab96_39_41_ok :
    checkSlabEliminated 128 112 256 96 q39Val barinaXMin
      (evalPow2Pow3Aux 256 p39Val q39Val 92).1 bsSlab96_39_41 = true := by decide

set_option maxRecDepth 20000 in
theorem slab96_41_43_ok :
    checkSlabEliminated 128 112 256 96 q41Val barinaXMin
      (evalPow2Pow3Aux 256 p41Val q41Val 92).1 bsSlab96_41_43 = true := by decide

set_option maxRecDepth 20000 in
theorem slab96_q43_44_ok :
    checkSlabEliminated 128 112 256 96 (q43Val + q44Val) barinaXMin
      (evalPow2Pow3Aux 256 p45Val q45Val 92).1 [2 ^ 256] = true := by decide

set_option maxRecDepth 20000 in
theorem slab96_39q43_ok :
    checkSlabEliminated 128 112 256 96 q43Val barinaXMin
      (evalPow2Pow3Aux 256 (39 * p43Val) (39 * q43Val) 92).1 bsSlab96_39Q43 = true := by decide

set_option maxRecDepth 20000 in
theorem slab96_45_51_ok :
    checkSlabEliminated 128 112 256 96 q45Val barinaXMin
      (evalPow2Pow3Aux 256 p51Val q51Val 92).1 [2 ^ 256] = true := by decide

/--
  Zero-Trust-Gap `q43`-Multiple Confinement Theorem Across `1 <= m <= 96`:
  Under `BarinaThreshold (2^71)` and `BakerLMNPowerBound`, EVERY non-trivial spiral cycle
  of length `1 <= m <= 96` is confined to an exact positive integer multiple
  `(K, W) = (u * p43Val, u * q43Val)` (`u >= 1`)!
-/
theorem q43_confinement_le_96 {steps : List SpiralStepData}
    (hbar : BarinaThreshold (2 ^ 71))
    (hbaker : BakerLMNPowerBound)
    (hcyc : IsNontrivialSpiralCycle steps)
    (hm_le : steps.length ≤ 96) :
    ∃ u : Nat, u ≥ 1 ∧
      spiralChainTotalK steps = u * p43Val ∧
      spiralChainTotalW steps = u * q43Val := by
  by_cases hw51 : q51Val ≤ spiralChainTotalW steps
  · exfalso
    exact no_spiral_cycle_ge_q51_le_99 hbar hbaker hcyc (by omega) hw51
  · have hfl := nontrivial_cycle_vertex_floor hbar hcyc
    rcases spiralCycle_global_prod_bounds hcyc with ⟨_, hcyc_lt, _⟩
    have hconv := convergent_signs_and_relations_certified
    let K := spiralChainTotalK steps
    let W := spiralChainTotalW steps
    have hW1 : W ≥ 1 := by
      cases hst : steps with
      | nil => rw [hst] at hcyc; cases hcyc
      | cons s0 rest =>
        rw [hst] at hcyc
        rcases hcyc with ⟨hch, _⟩
        have hk1 : s0.k ≥ 1 := by
          cases rest with
          | nil => exact hch.2.2.2.2.1
          | cons _ _ => exact hch.1.2.2.2.2.1
        dsimp [W]; rw [hst]; simp only [spiralChainTotalW]; omega
    by_cases hw35 : W < q35Val
    · exfalso
      have hr := unimodular_odd_upper_ratio (p0 := p34Val) (q0 := q34Val) (p1 := p35Val) (q1 := q35Val)
        (by decide) (by decide) (by decide)
        (pow2_lt_pow3_of_eval (by decide) (by decide) (by decide) hconv.1)
        (pow3_lt_pow2_of_eval (by decide) (by decide) (by decide) hconv.2.1)
        hW1 hw35 hcyc_lt
      exact checkSlabEliminated_sound slab96_1_35_ok hcyc hm_le hW1 hfl
        (ratio_transfer_evalPow2Pow3 (by decide) (by decide) (by decide) (Nat.le_of_lt hr))
    · by_cases hw37 : W < q37Val
      · exfalso
        have hr := unimodular_odd_upper_ratio (p0 := p36Val) (q0 := q36Val) (p1 := p37Val) (q1 := q37Val)
          (by decide) (by decide) (by decide)
          (pow2_lt_pow3_of_eval (by decide) (by decide) (by decide) hconv.2.2.1)
          (pow3_lt_pow2_of_eval (by decide) (by decide) (by decide) hconv.2.2.2.1)
          hW1 hw37 hcyc_lt
        exact checkSlabEliminated_sound slab96_35_37_ok hcyc hm_le (Nat.le_of_not_lt hw35) hfl
          (ratio_transfer_evalPow2Pow3 (by decide) (by decide) (by decide) (Nat.le_of_lt hr))
      · by_cases hw39 : W < q39Val
        · exfalso
          have hr := unimodular_odd_upper_ratio (p0 := p38Val) (q0 := q38Val) (p1 := p39Val) (q1 := q39Val)
            (by decide) (by decide) (by decide)
            (pow2_lt_pow3_of_eval (by decide) (by decide) (by decide) hconv.2.2.2.2.1)
            (pow3_lt_pow2_of_eval (by decide) (by decide) (by decide) hconv.2.2.2.2.2.1)
            hW1 hw39 hcyc_lt
          exact checkSlabEliminated_sound slab96_37_39_ok hcyc hm_le (Nat.le_of_not_lt hw37) hfl
            (ratio_transfer_evalPow2Pow3 (by decide) (by decide) (by decide) (Nat.le_of_lt hr))
        · by_cases hw41 : W < q41Val
          · exfalso
            have hr := unimodular_unit_slab_ratio (p1 := p39Val) (q1 := q39Val) (p2 := p40Val) (q2 := q40Val)
              (by decide) (by decide) (by decide)
              (pow3_lt_pow2_of_eval (by decide) (by decide) (by decide) hconv.2.2.2.2.2.1)
              (pow2_lt_pow3_of_eval (by decide) (by decide) (by decide) hconv.2.2.2.2.2.2.1)
              hW1 (by rw [show q39Val + q40Val = q41Val from rfl]; exact hw41) hcyc_lt
            exact checkSlabEliminated_sound slab96_39_41_ok hcyc hm_le (Nat.le_of_not_lt hw39) hfl
              (ratio_transfer_evalPow2Pow3 (by decide) (by decide) (by decide) hr)
          · by_cases hw43 : W < q43Val
            · exfalso
              have hr := unimodular_unit_slab_ratio (p1 := p41Val) (q1 := q41Val) (p2 := p42Val) (q2 := q42Val)
                (by decide) (by decide) (by decide)
                (pow3_lt_pow2_of_eval (by decide) (by decide) (by decide) hconv.2.2.2.2.2.2.2.1)
                (pow2_lt_pow3_of_eval (by decide) (by decide) (by decide) hconv.2.2.2.2.2.2.2.2.1)
                hW1 (by rw [show q41Val + q42Val = q43Val from rfl]; exact hw43) hcyc_lt
              exact checkSlabEliminated_sound slab96_41_43_ok hcyc hm_le (Nat.le_of_not_lt hw41) hfl
                (ratio_transfer_evalPow2Pow3 (by decide) (by decide) (by decide) hr)
            · by_cases hw45 : W < q45Val
              · have hcases := unimodular_q43_exact_multiples
                  (p1 := p43Val) (q1 := q43Val) (p2 := p44Val) (q2 := q44Val)
                  (by decide) (by decide) (by decide) (by decide)
                  (pow3_lt_pow2_of_eval (by decide) (by decide) (by decide) hconv.2.2.2.2.2.2.2.2.2.1)
                  (pow2_lt_pow3_of_eval (by decide) (by decide) (by decide) hconv.2.2.2.2.2.2.2.2.2.2.1)
                  (Nat.le_of_not_lt hw43) hcyc_lt
                rcases hcases with hexact | hW_q4344 | hr_39
                · exact hexact
                · exfalso
                  have hr := unimodular_odd_upper_ratio
                    (p0 := p44Val) (q0 := q44Val) (p1 := p45Val) (q1 := q45Val)
                    (by decide) (by decide) (by decide)
                    (pow2_lt_pow3_of_eval (by decide) (by decide) (by decide) hconv.2.2.2.2.2.2.2.2.2.2.1)
                    (pow3_lt_pow2_of_eval (by decide) (by decide) (by decide) hconv.2.2.2.2.2.2.2.2.2.2.2.1)
                    hW1 hw45 hcyc_lt
                  exact checkSlabEliminated_sound slab96_q43_44_ok hcyc hm_le hW_q4344 hfl
                    (ratio_transfer_evalPow2Pow3 (by decide) (by decide) (by decide) (Nat.le_of_lt hr))
                · exfalso
                  exact checkSlabEliminated_sound slab96_39q43_ok hcyc hm_le (Nat.le_of_not_lt hw43) hfl
                    (ratio_transfer_evalPow2Pow3 (by decide) (by decide) (by decide) (Nat.le_of_lt hr_39))
              · exfalso
                have hr := unimodular_odd_upper_ratio
                  (p0 := p50Val) (q0 := q50Val) (p1 := p51Val) (q1 := q51Val)
                  (by decide) (by decide) (by decide)
                  (pow2_lt_pow3_of_eval (by decide) (by decide) (by decide) hconv.2.2.2.2.2.2.2.2.2.2.2.2.1)
                  (pow3_lt_pow2_of_eval (by decide) (by decide) (by decide) hconv.2.2.2.2.2.2.2.2.2.2.2.2.2)
                  hW1 (Nat.lt_of_not_le hw51) hcyc_lt
                exact checkSlabEliminated_sound slab96_45_51_ok hcyc hm_le (Nat.le_of_not_lt hw45) hfl
                  (ratio_transfer_evalPow2Pow3 (by decide) (by decide) (by decide) (Nat.le_of_lt hr))

def bsUTailM93U3 : List Nat := [
  4903638129317933110165427501,
  38672595001850442444516540903752620687130352,
  607253130609001258579230990002010703420718461649891383404853089877962,
  2 ^ 256]

def bsUTailM94U4 : List Nat := [
  237718470600218159345258,
  5612458709018691121030467224363787385,
  8810482531733076037271837633402082934014833424825914634491,
  2 ^ 256]

def bsUTailM95U5 : List Nat :=
  List.replicate 1 (2 ^ 71) ++ [
    123431246604716822103932619565,
    6423739258431203331030629046862969126867723452,
    2007225076006909221770932076402315122246605364798587938763151298079153884,
    2 ^ 256]

def bsUTailM96U6 : List Nat :=
  List.replicate 1 (2 ^ 71) ++ [
    14143813354160631079056,
    64089561908785207583663406128282962,
    7352290359660415863338452680454160930933636947101429070,
    2 ^ 256]

def bsUTailM97U11 : List Nat :=
  List.replicate 1 (2 ^ 71) ++ [
    34755108869126151071709257,
    15153983148555819716961869499977228924454,
    2418790429286947057315782034109095141440090969713246799189079008,
    2 ^ 256]

def bsUTailM98U16 : List Nat :=
  List.replicate 1 (2 ^ 71) ++ [
    303211813069225784878184,
    8253859116752862783123663374825668859,
    16236300601291553182949585989474110558354722441119025660931,
    2 ^ 256]

def bsUTailM99U23 : List Nat :=
  List.replicate 2 (2 ^ 71) ++ [
    3387398893773876599235420835550476,
    69590636639383593852960631901388185608149948599795015,
    2 ^ 256]

set_option maxRecDepth 20000 in
theorem slab_utail_m93_u3_ok :
    checkSlabEliminated 128 112 256 93 (3 * q43Val) barinaXMin
      (evalPow2Pow3Aux 256 (3 * p43Val) (3 * q43Val) 96).1 bsUTailM93U3 = true := by decide

set_option maxRecDepth 20000 in
theorem slab_utail_m94_u4_ok :
    checkSlabEliminated 128 112 256 94 (4 * q43Val) barinaXMin
      (evalPow2Pow3Aux 256 (4 * p43Val) (4 * q43Val) 96).1 bsUTailM94U4 = true := by decide

set_option maxRecDepth 20000 in
theorem slab_utail_m95_u5_ok :
    checkSlabEliminated 128 112 256 95 (5 * q43Val) barinaXMin
      (evalPow2Pow3Aux 256 (5 * p43Val) (5 * q43Val) 96).1 bsUTailM95U5 = true := by decide

set_option maxRecDepth 20000 in
theorem slab_utail_m96_u6_ok :
    checkSlabEliminated 128 112 256 96 (6 * q43Val) barinaXMin
      (evalPow2Pow3Aux 256 (6 * p43Val) (6 * q43Val) 96).1 bsUTailM96U6 = true := by decide

set_option maxRecDepth 20000 in
theorem slab_utail_m97_u11_ok :
    checkSlabEliminated 128 112 256 97 (11 * q43Val) barinaXMin
      (evalPow2Pow3Aux 256 (11 * p43Val) (11 * q43Val) 96).1 bsUTailM97U11 = true := by decide

set_option maxRecDepth 20000 in
theorem slab_utail_m98_u16_ok :
    checkSlabEliminated 128 112 256 98 (16 * q43Val) barinaXMin
      (evalPow2Pow3Aux 256 (16 * p43Val) (16 * q43Val) 96).1 bsUTailM98U16 = true := by decide

set_option maxRecDepth 20000 in
theorem slab_utail_m99_u23_ok :
    checkSlabEliminated 128 112 256 99 (23 * q43Val) barinaXMin
      (evalPow2Pow3Aux 256 (23 * p43Val) (23 * q43Val) 96).1 bsUTailM99U23 = true := by decide

theorem eliminate_q43_multiple_tail {steps : List SpiralStepData} {mMax u0 u : Nat} {bs : List Nat}
    (hbar : BarinaThreshold (2 ^ 71))
    (hcyc : IsNontrivialSpiralCycle steps)
    (hm_le : steps.length ≤ mMax)
    (hp_lt : u0 * p43Val < 2 ^ 96) (hq_lt : u0 * q43Val < 2 ^ 96)
    (hok : checkSlabEliminated 128 112 256 mMax (u0 * q43Val) barinaXMin
      (evalPow2Pow3Aux 256 (u0 * p43Val) (u0 * q43Val) 96).1 bs = true)
    (hu_ge : u0 ≤ u)
    (hK : spiralChainTotalK steps = u * p43Val)
    (hW : spiralChainTotalW steps = u * q43Val) :
    False := by
  have hconv := convergent_signs_and_relations_certified
  have hodd := pow3_lt_pow2_of_eval (by decide) (by decide) (by decide)
    hconv.2.2.2.2.2.2.2.2.2.1
  rcases u_multiple_tail_ratio hodd hu_ge hK hW with ⟨hw_ge, hrat⟩
  exact checkSlabEliminated_sound hok hcyc hm_le hw_ge
    (nontrivial_cycle_vertex_floor hbar hcyc)
    (ratio_transfer_evalPow2Pow3 (by decide) hp_lt hq_lt hrat)

end CollatzFormal

