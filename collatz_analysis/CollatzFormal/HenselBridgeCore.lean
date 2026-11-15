/-
  CollatzFormal/HenselBridgeCore.lean
  Section 13.8C: Self-Guided `r = 1` & Ultra-Lean `r = 2` Kernel Hensel Verifiers,
  Incremental Congruence Collapse, and Cycle Elimination Cores for `m = 93..96`.
-/

import CollatzFormal.RationalLogSlabs

namespace CollatzFormal

-- ============================================================================
-- 13.8C Self-Guided `r = 1` & `r = 2` Kernel Hensel Verifiers & Cycle Cores
-- ============================================================================

set_option exponentiation.threshold 2048

theorem list_all_mem_pred {α : Type} {p : α -> Bool} :
    ∀ {xs : List α} {x : α}, xs.all p = true -> x ∈ xs -> p x = true
  | [], _, _, hm => by cases hm
  | _ :: _, _, hok, .head _ => by
    simp only [List.all_cons, Bool.and_eq_true] at hok; exact hok.1
  | _ :: _, _, hok, .tail _ hm => by
    simp only [List.all_cons, Bool.and_eq_true] at hok
    exact list_all_mem_pred hok.2 hm

theorem list_any_exists_pred {α : Type} {p : α -> Bool} :
    ∀ {xs : List α}, xs.any p = true -> ∃ y ∈ xs, p y = true
  | [], h => by simp at h
  | y :: tl, h => by
    simp only [List.any_cons, Bool.or_eq_true] at h
    rcases h with hy | htl
    · exact ⟨y, List.Mem.head _, hy⟩
    · rcases list_any_exists_pred htl with ⟨z, hz, hpz⟩
      exact ⟨z, List.Mem.tail y hz, hpz⟩

theorem exempt_in_survivors32_excludes_cycle
    {steps : List SpiralStepData} {s : SpiralStepData} {exemptIds : List Nat}
    (hbar : BarinaThreshold (2 ^ 71))
    (hcyc : IsNontrivialSpiralCycle steps)
    (hs_mem : s ∈ steps)
    (hex_ok : exemptIds.all (fun x => henselSurvivors92To95.any (fun zk => x == zk.1)) = true)
    (hmem : s.x ∈ exemptIds) :
    False := by
  have hsurv := all_32_hensel_survivors_drop_below_2_pow_71.2
  have hany := list_all_mem_pred hex_ok hmem
  rcases list_any_exists_pred hany with ⟨zk, hzk_mem, heq⟩
  simp only [beq_iff_eq] at heq
  have hdrop := list_all_mem_pred hsurv hzk_mem
  rcases zk with ⟨z, d⟩
  dsimp at heq
  exact checkSurvivorDrop_excludes_nontrivial_cycle hbar hdrop hcyc s hs_mem heq

theorem universal_vertex_lower_bound_of_U
    {s0 s1 : SpiralStepData} {restTail : List SpiralStepData}
    {M K W U : Nat}
    (hM_pos : M ≥ 1)
    (hs0 : ValidSpiralStep s0 s1.x)
    (htail : ValidSpiralChain (s1 :: restTail) s0.x)
    (hK_eq : (s0.k + s0.l) + spiralChainTotalK (s1 :: restTail) = K)
    (hW_eq : s0.k + spiralChainTotalW (s1 :: restTail) = W)
    (hU : M * 2 ^ K < U * 3 ^ W)
    (hU_gt : M < U) :
    (M * (3 ^ s0.k - 2 ^ s0.k)) / ((U - M) * 3 ^ s0.k) + 1 ≤ s0.x := by
  let WT := spiralChainTotalW (s1 :: restTail)
  let KT := spiralChainTotalK (s1 :: restTail)
  let PM := prodList (restTail.map (fun s => s.x))
  have hPM_pos : PM ≥ 1 := validSpiralChain_vertices_pos s1 restTail s0.x htail
  rcases spiralStep_x_bounds hs0 with ⟨_, _, hstep0_eq⟩
  rcases spiralChain_prod_bounds s1 restTail s0.x htail with ⟨htail_lo, _⟩
  change 3 ^ WT * (s1.x * PM) < 2 ^ KT * (PM * s0.x) at htail_lo
  have hp2K : 2 ^ (s0.k + s0.l) * 2 ^ KT = 2 ^ K := by rw [← Nat.pow_add, hK_eq]
  have hp3W : 3 ^ s0.k * 3 ^ WT = 3 ^ W := by rw [← Nat.pow_add, hW_eq]
  have hp3WT_pos : 3 ^ WT ≥ 1 := pow3_pos_nat WT
  rcases hs0 with ⟨_, hs0_pos, _, _, _, _, _⟩
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
  have hm1 := Nat.mul_lt_mul_of_pos_left hlo_step hM_pos
  rw [Nat.mul_add, ← Nat.mul_assoc M (2 ^ K)] at hm1
  have hm2 := Nat.mul_lt_mul_of_pos_right hU hs0_pos
  have hlt_U : M * (3 ^ W * s0.x) + M * (3 ^ WT * (3 ^ s0.k - 2 ^ s0.k)) <
      U * 3 ^ W * s0.x := Nat.lt_trans hm1 hm2
  have hsplit_U : U * 3 ^ W * s0.x = M * (3 ^ W * s0.x) + ((U - M) * 3 ^ W) * s0.x := by
    calc
      U * 3 ^ W * s0.x = ((M + (U - M)) * 3 ^ W) * s0.x := by
        rw [show M + (U - M) = U by omega]
      _ = M * (3 ^ W * s0.x) + ((U - M) * 3 ^ W) * s0.x := by
        rw [Nat.add_mul, Nat.add_mul, Nat.mul_assoc M]
  rw [hsplit_U] at hlt_U
  have hsub_U : M * (3 ^ WT * (3 ^ s0.k - 2 ^ s0.k)) < ((U - M) * 3 ^ W) * s0.x := by omega
  have hl_wt : M * (3 ^ WT * (3 ^ s0.k - 2 ^ s0.k)) = 3 ^ WT * (M * (3 ^ s0.k - 2 ^ s0.k)) := by
    rw [← Nat.mul_assoc, Nat.mul_comm M (3 ^ WT), Nat.mul_assoc]
  have hr_wt : ((U - M) * 3 ^ W) * s0.x = 3 ^ WT * (((U - M) * 3 ^ s0.k) * s0.x) := by
    rw [← hp3W, Nat.mul_comm (3 ^ s0.k) (3 ^ WT)]
    calc
      ((U - M) * (3 ^ WT * 3 ^ s0.k)) * s0.x
          = ((3 ^ WT * (U - M)) * 3 ^ s0.k) * s0.x := by
            rw [← Nat.mul_assoc (U - M), Nat.mul_comm (U - M) (3 ^ WT)]
      _ = 3 ^ WT * (((U - M) * 3 ^ s0.k) * s0.x) := by
            rw [Nat.mul_assoc (3 ^ WT), Nat.mul_assoc (3 ^ WT)]
  rw [hl_wt, hr_wt] at hsub_U
  have hfin : M * (3 ^ s0.k - 2 ^ s0.k) < ((U - M) * 3 ^ s0.k) * s0.x := by
    apply Classical.byContradiction
    intro hge
    have hm3 := Nat.mul_le_mul_left (3 ^ WT)
      (show ((U - M) * 3 ^ s0.k) * s0.x ≤ M * (3 ^ s0.k - 2 ^ s0.k) by omega)
    omega
  apply Classical.byContradiction
  intro hlt_x
  have hx_le : s0.x ≤ (M * (3 ^ s0.k - 2 ^ s0.k)) / ((U - M) * 3 ^ s0.k) := by omega
  have hm4 := Nat.mul_le_mul_left ((U - M) * 3 ^ s0.k) hx_le
  have hmd := mul_div_le_nat (M * (3 ^ s0.k - 2 ^ s0.k)) ((U - M) * 3 ^ s0.k)
  omega

theorem spiralCycle_rotate_one {s0 s1 : SpiralStepData} {rest : List SpiralStepData}
    (hcyc : IsNontrivialSpiralCycle (s0 :: s1 :: rest)) :
    IsNontrivialSpiralCycle (s1 :: (rest ++ [s0])) ∧
    (s1 :: (rest ++ [s0])).length = (s0 :: s1 :: rest).length ∧
    spiralChainTotalK (s1 :: (rest ++ [s0])) = spiralChainTotalK (s0 :: s1 :: rest) ∧
    spiralChainTotalW (s1 :: (rest ++ [s0])) = spiralChainTotalW (s0 :: s1 :: rest) ∧
    (∀ c : Nat, countLe c (spiralVertices (s1 :: (rest ++ [s0]))) =
      countLe c (spiralVertices (s0 :: s1 :: rest))) ∧
    (∀ xMin : Nat, (∀ s ∈ (s0 :: s1 :: rest), s.x ≥ xMin) ->
      ∀ s ∈ (s1 :: (rest ++ [s0])), s.x ≥ xMin) := by
  rcases hcyc with ⟨⟨hs0, hrest⟩, sBig, hsBig_mem, hsBig_gt⟩
  refine ⟨⟨?_, sBig, ?_, hsBig_gt⟩, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [List.cons_append] using validSpiralChain_append (s1 :: rest) [s0] s0 s1.x rfl hrest hs0
  · simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hsBig_mem ⊢
    rcases hsBig_mem with rfl | rfl | hr
    · exact Or.inr (Or.inr rfl)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl hr)
  · simp [List.length_append]
  · change spiralChainTotalK ((s1 :: rest) ++ [s0]) = (s0.k + s0.l) + spiralChainTotalK (s1 :: rest)
    rw [spiralChainTotalK_append]
    simp [spiralChainTotalK]; omega
  · change spiralChainTotalW ((s1 :: rest) ++ [s0]) = s0.k + spiralChainTotalW (s1 :: rest)
    rw [spiralTotalW_append]
    simp [spiralChainTotalW]; omega
  · intro c
    change countLe c (((s1 :: rest) ++ [s0]).map (fun s => s.x)) =
      countLe c (([s0] ++ (s1 :: rest)).map (fun s => s.x))
    rw [List.map_append, countLe_append, List.map_append, countLe_append, Nat.add_comm]
  · intro xMin hfl s hs
    apply hfl s
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hs ⊢
    rcases hs with rfl | hr | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr hr)
    · exact Or.inl rfl

theorem spiralCycle_rotate_small_to_large {steps : List SpiralStepData} {b : Nat}
    (hcyc : IsNontrivialSpiralCycle steps)
    (hlen3 : steps.length ≥ 3)
    (hex : ¬ (∀ s ∈ steps, s.x ≥ b + 1))
    (hc2 : countLe b (spiralVertices steps) ≤ 2) :
    ∃ (s0 s1 : SpiralStepData) (tailRest : List SpiralStepData),
      s0.x ≤ b ∧
      b + 1 ≤ s1.x ∧
      IsNontrivialSpiralCycle (s0 :: s1 :: tailRest) ∧
      (s0 :: s1 :: tailRest).length = steps.length ∧
      spiralChainTotalK (s0 :: s1 :: tailRest) = spiralChainTotalK steps ∧
      spiralChainTotalW (s0 :: s1 :: tailRest) = spiralChainTotalW steps ∧
      (∀ c : Nat, countLe c (spiralVertices (s0 :: s1 :: tailRest)) =
        countLe c (spiralVertices steps)) ∧
      (∀ xMin : Nat, (∀ s ∈ steps, s.x ≥ xMin) ->
        ∀ s ∈ (s0 :: s1 :: tailRest), s.x ≥ xMin) := by
  rcases spiralCycle_rotate_at_small hcyc hex with
    ⟨a0, tl, ha0_le, hcyc_a, hlen_a, hK_a, hW_a, hcnt_a, hfl_a⟩
  have htl_len : tl.length ≥ 2 := by simp at hlen_a; omega
  cases tl with
  | nil => simp at htl_len
  | cons a1 tl1 =>
    cases tl1 with
    | nil => simp at htl_len
    | cons a2 rest =>
      by_cases ha1_gt : b + 1 ≤ a1.x
      · exact ⟨a0, a1, a2 :: rest, ha0_le, ha1_gt, hcyc_a, hlen_a, hK_a, hW_a, hcnt_a, hfl_a⟩
      · have ha1_le : a1.x ≤ b := by omega
        have hc_rot : countLe b (spiralVertices (a0 :: a1 :: a2 :: rest)) ≤ 2 := by
          rw [hcnt_a b]; exact hc2
        have ha2_gt : b + 1 ≤ a2.x := by
          simp only [spiralVertices, List.map_cons, countLe, ha0_le, ha1_le, ↓reduceIte] at hc_rot
          by_cases ha2_le : a2.x ≤ b
          · simp only [ha2_le, ↓reduceIte] at hc_rot; omega
          · omega
        rcases spiralCycle_rotate_one hcyc_a with
          ⟨hcyc_b, hlen_b, hK_b, hW_b, hcnt_b, hfl_b⟩
        simp only [List.cons_append] at hcyc_b hlen_b hK_b hW_b hcnt_b hfl_b
        exact ⟨a1, a2, rest ++ [a0], ha1_le, ha2_gt, hcyc_b,
          hlen_b.trans hlen_a, hK_b.trans hK_a, hW_b.trans hW_a,
          fun c => (hcnt_b c).trans (hcnt_a c),
          fun xMin hf => hfl_b xMin (hfl_a xMin hf)⟩

theorem tail_counts_c2_s1
    {b1 b2 b3 b4 : Nat} {s0 : SpiralStepData} {tail : List SpiralStepData}
    (hb12 : b1 ≤ b2) (hb23 : b2 ≤ b3) (hb34 : b3 ≤ b4)
    (hs0 : s0.x ≤ b1)
    (hc1 : countLe b1 (spiralVertices (s0 :: tail)) ≤ 1)
    (hc2 : countLe b2 (spiralVertices (s0 :: tail)) ≤ 3)
    (hc3 : countLe b3 (spiralVertices (s0 :: tail)) ≤ 4)
    (hc4 : countLe b4 (spiralVertices (s0 :: tail)) ≤ 5) :
    (∀ x ∈ tail.map (fun s => s.x), x ≥ b1 + 1) ∧
    (∀ bc ∈ [(b2, 2), (b3, 3), (b4, 4)], countLe bc.1 (tail.map (fun s => s.x)) ≤ bc.2) := by
  have hs0_2 : s0.x ≤ b2 := Nat.le_trans hs0 hb12
  have hs0_3 : s0.x ≤ b3 := Nat.le_trans hs0_2 hb23
  have hs0_4 : s0.x ≤ b4 := Nat.le_trans hs0_3 hb34
  simp only [spiralVertices, List.map_cons, countLe, hs0, hs0_2, hs0_3, hs0_4, ↓reduceIte]
    at hc1 hc2 hc3 hc4
  refine ⟨?_, ?_⟩
  · intro x hx
    apply Classical.byContradiction
    intro hlt
    have hpos := mem_le_implies_countLe_pos b1 (tail.map (fun s => s.x)) ⟨x, hx, by omega⟩
    omega
  · intro bc hbc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hbc
    rcases hbc with rfl | rfl | rfl <;> dsimp <;> omega

theorem third_tail_gt_of_two_le
    {b2 : Nat} {s1 s2 s3 : SpiralStepData} {rest : List SpiralStepData}
    (hc : countLe b2 ((s1 :: s2 :: s3 :: rest).map (fun s => s.x)) ≤ 2)
    (hs1_le : s1.x ≤ b2) (hs2_le : s2.x ≤ b2) :
    b2 + 1 ≤ s3.x := by
  simp only [List.map_cons, countLe, hs1_le, hs2_le, ↓reduceIte] at hc
  by_cases hs3_le : s3.x ≤ b2
  · simp only [hs3_le, ↓reduceIte] at hc; omega
  · omega

theorem c2_s2_forces_s2_gt_b2
    {b1 b2 kCap : Nat} {s0 s1 s2 s3 : SpiralStepData} {rest : List SpiralStepData}
    (hb12 : b1 ≤ b2)
    (hkCap2 : kCap ≥ 2)
    (hb1_pow : b1 + 1 < 2 ^ kCap)
    (hb1_tgt : 3 ^ (kCap - 1) * (b1 + 1) < 2 ^ (kCap - 1) * (2 * (b2 + 1) + 1))
    (hs0_le : s0.x ≤ b1)
    (hs1_lo : b1 + 1 ≤ s1.x) (hs1_hi : s1.x ≤ b2)
    (hs2_step : ValidSpiralStep s2 s3.x)
    (hc1_ge2 : 2 ≤ countLe b1 (spiralVertices (s0 :: s1 :: s2 :: s3 :: rest)))
    (hc2_le3 : countLe b2 (spiralVertices (s0 :: s1 :: s2 :: s3 :: rest)) ≤ 3) :
    b2 + 1 ≤ s2.x := by
  apply Classical.byContradiction
  intro hnot
  have hs2_le_b2 : s2.x ≤ b2 := by omega
  have hs0_b2 : s0.x ≤ b2 := Nat.le_trans hs0_le hb12
  have hs1_not_b1 : ¬ (s1.x ≤ b1) := by omega
  by_cases hs2_le_b1 : s2.x ≤ b1
  · -- s0, s1, s2 all <= b2, so countLe b2 <= 3 forces s3.x >= b2 + 1!
    have hs3_gt_b2 : b2 + 1 ≤ s3.x := by
      simp only [spiralVertices, List.map_cons, countLe, hs0_b2, hs1_hi, hs2_le_b2, ↓reduceIte]
        at hc2_le3
      by_cases hs3_le : s3.x ≤ b2
      · simp only [hs3_le, ↓reduceIte] at hc2_le3; omega
      · omega
    rcases hs2_step with ⟨_, _, _, _, _, hl2_ge1, hst2⟩
    by_cases hk_hi : kCap ≤ s2.k
    · exact no_spiral_step_of_hi_lt_pow2 s2.k kCap s2.l b1 s2.x s3.x
        hk_hi hl2_ge1 hs2_le_b1 hb1_pow hst2
    · exact no_spiral_step_of_pow3_lt_target s2.k (kCap - 1) s2.l b1 (b2 + 1) s2.x s3.x
        (by omega) hl2_ge1 hs2_le_b1 hs3_gt_b2 hb1_tgt hst2
  · -- s2.x > b1 and s2.x <= b2, while countLe b1 >= 2 forces some w in (s3 :: rest) with w.x <= b1 <= b2!
    simp only [spiralVertices, List.map_cons, countLe, hs0_le, hs1_not_b1, hs2_le_b1, ↓reduceIte]
      at hc1_ge2
    have hcnt_b1_pos : countLe b1 ((s3 :: rest).map (fun s => s.x)) ≥ 1 := by
      simp only [List.map_cons, countLe]; omega
    have hle_b1_b2 : ∀ xs : List Nat, countLe b1 xs ≤ countLe b2 xs := by
      intro xs
      induction xs with
      | nil => exact Nat.le_refl _
      | cons x tl ih =>
        simp only [countLe]
        by_cases hx1 : x ≤ b1
        · have hx2 : x ≤ b2 := Nat.le_trans hx1 hb12
          simp only [hx1, hx2, ↓reduceIte]; omega
        · by_cases hx2 : x ≤ b2 <;> simp only [hx1, hx2, ↓reduceIte] <;> omega
    have hcnt_b2_pos : countLe b2 ((s3 :: rest).map (fun s => s.x)) ≥ 1 :=
      Nat.le_trans hcnt_b1_pos (hle_b1_b2 _)
    simp only [List.map_cons, countLe] at hcnt_b2_pos
    simp only [spiralVertices, List.map_cons, countLe, hs0_b2, hs1_hi, hs2_le_b2, ↓reduceIte]
      at hc2_le3
    omega

-- Exact 2-adic valuation & spiral-step simulator for candidate filtering:
def strip2Aux : Nat -> Nat -> Nat -> Nat × Nat
  | 0, e, n => (e, n)
  | fuel + 1, e, n =>
    if n % 2 == 0 then strip2Aux fuel (e + 1) (n / 2) else (e, n)

theorem strip2Aux_unique :
    ∀ (fuel e n eTrue qTrue : Nat),
      qTrue % 2 = 1 ->
      2 ^ e * n = 2 ^ eTrue * qTrue ->
      e ≤ eTrue ->
      eTrue ≤ e + fuel ->
      strip2Aux fuel e n = (eTrue, qTrue)
  | 0, e, n, eTrue, qTrue, hq_odd, heq, hle, hfuel => by
    have he_eq : e = eTrue := by omega
    subst he_eq
    have hn_eq : n = qTrue := mul_left_cancel_pow2_nat e n qTrue heq
    subst hn_eq
    rfl
  | fuel + 1, e, n, eTrue, qTrue, hq_odd, heq, hle, hfuel => by
    by_cases he_eq : e = eTrue
    · subst he_eq
      have hn_eq : n = qTrue := mul_left_cancel_pow2_nat e n qTrue heq
      subst hn_eq
      have hodd_b : (n % 2 == 0) = false := decide_eq_false (by omega)
      simp only [strip2Aux, hodd_b, Bool.false_eq_true, ↓reduceIte]
    · have hlt : e < eTrue := by omega
      let d := eTrue - (e + 1)
      have heTrue_sp : eTrue = e + (1 + d) := by dsimp [d]; omega
      have hrhs : 2 ^ eTrue * qTrue = 2 ^ e * (2 * (2 ^ d * qTrue)) := by
        rw [heTrue_sp, Nat.pow_add 2 e (1 + d), Nat.pow_add 2 1 d, Nat.pow_one,
            Nat.mul_assoc, Nat.mul_assoc]
      have hn_even_val : n = 2 * (2 ^ d * qTrue) :=
        mul_left_cancel_pow2_nat e n (2 * (2 ^ d * qTrue)) (heq.trans hrhs)
      have hev_b : (n % 2 == 0) = true := decide_eq_true (by rw [hn_even_val]; omega)
      have hdiv : n / 2 = 2 ^ d * qTrue := by rw [hn_even_val]; omega
      simp only [strip2Aux, hev_b, ↓reduceIte]
      apply strip2Aux_unique fuel (e + 1) (n / 2) eTrue qTrue hq_odd _ (by omega) (by omega)
      rw [hdiv, heTrue_sp, show e + (1 + d) = (e + 1) + d by omega, Nat.pow_add 2 (e + 1) d,
          Nat.mul_assoc]

def simSpiralStep (x : Nat) : Nat :=
  let ku := strip2Aux 1024 0 (x + 1)
  (strip2Aux 1024 0 (3 ^ ku.1 * ku.2 - 1)).2

set_option maxRecDepth 20000 in
theorem pow3_256_mul_pow2_256_lt : 3 ^ 256 * 2 ^ 256 < 2 ^ 1025 := by decide

theorem pow3_mono_nat {a b : Nat} (hab : a ≤ b) : 3 ^ a ≤ 3 ^ b := by
  have h := pow3_mono_nat_aux a (b - a)
  rwa [show a + (b - a) = b by omega] at h

theorem simSpiralStep_unique {s : SpiralStepData} {xNext : Nat}
    (hx_lt : s.x < 2 ^ 256)
    (hv : ValidSpiralStep s xNext) :
    simSpiralStep s.x = xNext := by
  rcases hv with ⟨_, _, hxN_odd, hxN_pos, _, hl1, hstep⟩
  rcases spiral_step_odd_quotient_nat s.k s.l s.x xNext hl1 hstep with ⟨u, hu_odd, hx_eq, ha_eq⟩
  have hu_pos : u ≥ 1 := by omega
  have hk_le_256 : s.k ≤ 256 := by
    have hp : 2 ^ s.k ≤ 2 ^ 256 := by
      have hm : 2 ^ s.k * 1 ≤ 2 ^ s.k * u := Nat.mul_le_mul_left (2 ^ s.k) hu_pos
      omega
    apply Classical.byContradiction
    intro hgt
    have hm2 : 2 ^ 257 ≤ 2 ^ s.k := pow2_mono_nat (by omega)
    have h257 : 2 ^ 256 < 2 ^ 257 := by rw [Nat.pow_succ]; have := pow2_pos_nat 256; omega
    omega
  have hl_le_1024 : s.l ≤ 1024 := by
    have hp3 : 3 ^ s.k ≤ 3 ^ 256 := pow3_mono_nat hk_le_256
    have h3u_le : 3 ^ s.k * u ≤ 3 ^ 256 * 2 ^ 256 := by
      calc
        3 ^ s.k * u ≤ 3 ^ s.k * (2 ^ s.k * u) :=
          Nat.mul_le_mul_left (3 ^ s.k)
            (by simpa using Nat.mul_le_mul_right u (pow2_pos_nat s.k))
        _ = 3 ^ s.k * (s.x + 1) := by rw [← hx_eq]
        _ ≤ 3 ^ 256 * 2 ^ 256 := Nat.mul_le_mul hp3 (by omega)
    have h2l_lt : 2 ^ s.l < 2 ^ 1025 := by
      have hm : 2 ^ s.l * 1 ≤ 2 ^ s.l * xNext := Nat.mul_le_mul_left (2 ^ s.l) hxN_pos
      exact Nat.lt_of_le_of_lt (by omega) pow3_256_mul_pow2_256_lt
    have hlt := pow_lt_exp_cancel_nat (by decide) h2l_lt
    omega
  unfold simSpiralStep
  have h1 := strip2Aux_unique 1024 0 (s.x + 1) s.k u hu_odd
    (by simpa using hx_eq) (Nat.zero_le _) (by omega)
  have h2 := strip2Aux_unique 1024 0 (3 ^ s.k * u - 1) s.l xNext hxN_odd
    (by simp only [Nat.pow_zero, Nat.one_mul]; omega) (Nat.zero_le _) (by omega)
  dsimp only
  rw [h1]
  dsimp only
  rw [h2]

def checkCandR1 (b1 b2 : Nat) (exemptIds : List Nat) (cand : Nat) : Bool :=
  let z2 := simSpiralStep cand
  if (b1 + 1 ≤ z2) && (z2 ≤ b2) then
    let z3 := simSpiralStep z2
    if b2 + 1 ≤ z3 then memNatList cand exemptIds else true
  else true

theorem checkCandR1_sound {b1 b2 : Nat} {exemptIds : List Nat}
    {s0 s1 : SpiralStepData} {x2 : Nat}
    (hb2_lt : b2 < 2 ^ 256)
    (hs0_le : s0.x ≤ b1) (_hb12 : b1 ≤ b2)
    (hs1_lo : b1 + 1 ≤ s1.x) (hs1_hi : s1.x ≤ b2)
    (hx2_lo : b2 + 1 ≤ x2)
    (hst0 : ValidSpiralStep s0 s1.x)
    (hst1 : ValidSpiralStep s1 x2)
    (hok : checkCandR1 b1 b2 exemptIds s0.x = true) :
    s0.x ∈ exemptIds := by
  unfold checkCandR1 at hok
  have hz2 : simSpiralStep s0.x = s1.x := simSpiralStep_unique (by omega) hst0
  have hz3 : simSpiralStep s1.x = x2 := simSpiralStep_unique (by omega) hst1
  rw [hz2] at hok
  have hc1 : ((decide (b1 + 1 ≤ s1.x) && decide (s1.x ≤ b2)) = true) := by
    simp [hs1_lo, hs1_hi]
  simp only [hc1, ↓reduceIte, hz3, hx2_lo] at hok
  rcases memNatList_sound exemptIds s0.x hok with ⟨s, hs, rfl⟩
  exact hs

def checkCandR2 (b1 b2 : Nat) (exemptIds : List Nat) (cand : Nat) : Bool :=
  let z2 := simSpiralStep cand
  if (b1 + 1 ≤ z2) && (z2 ≤ b2) then
    let z3 := simSpiralStep z2
    if (b1 + 1 ≤ z3) && (z3 ≤ b2) then
      let z4 := simSpiralStep z3
      if b2 + 1 ≤ z4 then memNatList cand exemptIds else true
    else true
  else true

theorem checkCandR2_sound {b1 b2 : Nat} {exemptIds : List Nat}
    {s0 s1 s2 : SpiralStepData} {x3 : Nat}
    (hb2_lt : b2 < 2 ^ 256)
    (hs0_le : s0.x ≤ b1) (_hb12 : b1 ≤ b2)
    (hs1_lo : b1 + 1 ≤ s1.x) (hs1_hi : s1.x ≤ b2)
    (hs2_lo : b1 + 1 ≤ s2.x) (hs2_hi : s2.x ≤ b2)
    (hx3_lo : b2 + 1 ≤ x3)
    (hst0 : ValidSpiralStep s0 s1.x)
    (hst1 : ValidSpiralStep s1 s2.x)
    (hst2 : ValidSpiralStep s2 x3)
    (hok : checkCandR2 b1 b2 exemptIds s0.x = true) :
    s0.x ∈ exemptIds := by
  unfold checkCandR2 at hok
  have hz2 : simSpiralStep s0.x = s1.x := simSpiralStep_unique (by omega) hst0
  have hz3 : simSpiralStep s1.x = s2.x := simSpiralStep_unique (by omega) hst1
  have hz4 : simSpiralStep s2.x = x3 := simSpiralStep_unique (by omega) hst2
  rw [hz2] at hok
  have hc1 : ((decide (b1 + 1 ≤ s1.x) && decide (s1.x ≤ b2)) = true) := by
    simp [hs1_lo, hs1_hi]
  have hc2 : ((decide (b1 + 1 ≤ s2.x) && decide (s2.x ≤ b2)) = true) := by
    simp [hs2_lo, hs2_hi]
  simp only [hc1, ↓reduceIte, hz3, hc2, hz4, hx3_lo] at hok
  rcases memNatList_sound exemptIds s0.x hok with ⟨s, hs, rfl⟩
  exact hs

-- Universal 384-bit modular inverse of 3 and single-span congruence checker:
def inv3Pow384 : Nat :=
  4060763850009800490309179532645980031526221820083763918809927971222209156419166063993330086774797869564373858816513

set_option maxRecDepth 20000 in
theorem inv3Pow384_certified : (3 ^ 384 * inv3Pow384) % 2 ^ 384 = 1 := by decide

def pow3Split (s : Nat) : Nat :=
  if s ≤ 200 then 3 ^ s else 3 ^ 200 * 3 ^ (s - 200)

theorem pow3Split_eq (s : Nat) : pow3Split s = 3 ^ s := by
  unfold pow3Split
  by_cases h : s ≤ 200
  · simp [h]
  · simp only [h, ↓reduceIte, ← Nat.pow_add]
    exact congrArg (3 ^ ·) (by omega)

def inv3At384 (w : Nat) : Nat :=
  (pow3Split (384 - w) * inv3Pow384) % (2 ^ 192 * 2 ^ 192)

theorem inv3At384_spec {w : Nat} (hw : w ≤ 384) :
    (3 ^ w * inv3At384 w) % 2 ^ 384 = 1 := by
  unfold inv3At384
  rw [pow3Split_eq, show (2 ^ 192 * 2 ^ 192 : Nat) = 2 ^ 384 by rw [← Nat.pow_add]]
  rw [Nat.mul_mod, Nat.mod_mod_of_dvd _ (Nat.dvd_refl _), ← Nat.mul_mod,
      ← Nat.mul_assoc, ← Nat.pow_add, show w + (384 - w) = 384 by omega]
  exact inv3Pow384_certified

def checkCongPred (lo hi exp invAt g : Nat) (okCand : Nat -> Bool) : Bool :=
  let M := pow2Split exp
  let span := hi - lo
  let rem := (invAt * g + (lo + 1)) % M
  let off := (M - rem) % M
  (exp ≤ 384) && (span < M) && ((off > span) || okCand (lo + off))

theorem checkCongPred_sound
    {lo hi exp w invAt g n1 : Nat} {okCand : Nat -> Bool}
    (hlo : lo ≤ n1) (hhi : n1 ≤ hi)
    (hinv : (3 ^ w * invAt) % 2 ^ 384 = 1)
    (hdvd : 2 ^ exp ∣ 3 ^ w * (n1 + 1) + g)
    (hok : checkCongPred lo hi exp invAt g okCand = true) :
    okCand n1 = true := by
  unfold checkCongPred at hok
  rw [pow2Split_eq] at hok
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hok
  rcases hok with ⟨⟨hexp_le, hspan_lt⟩, hoff_or⟩
  let M := 2 ^ exp
  have hM_pos : M ≥ 1 := pow2_pos_nat exp
  have hinv_eq : 3 ^ w * invAt =
      M * (2 ^ (384 - exp) * ((3 ^ w * invAt) / 2 ^ 384)) + 1 := by
    have hdm := (Nat.div_add_mod (3 ^ w * invAt) (2 ^ 384)).symm
    have hp : 2 ^ 384 = M * 2 ^ (384 - exp) := by
      dsimp [M]; rw [← Nat.pow_add, show exp + (384 - exp) = 384 by omega]
    calc
      3 ^ w * invAt
          = 2 ^ 384 * ((3 ^ w * invAt) / 2 ^ 384) + (3 ^ w * invAt) % 2 ^ 384 := hdm
      _ = 2 ^ 384 * ((3 ^ w * invAt) / 2 ^ 384) + 1 := by rw [hinv]
      _ = (M * 2 ^ (384 - exp)) * ((3 ^ w * invAt) / 2 ^ 384) + 1 :=
            congrArg (fun t => t * ((3 ^ w * invAt) / 2 ^ 384) + 1) hp
      _ = M * (2 ^ (384 - exp) * ((3 ^ w * invAt) / 2 ^ 384)) + 1 := by rw [Nat.mul_assoc]
  rcases hdvd with ⟨Q, hQ⟩
  let qInv := 2 ^ (384 - exp) * ((3 ^ w * invAt) / 2 ^ 384)
  let S := invAt * g + (lo + 1)
  let qRem := S / M
  let rem := S % M
  have hS_dm : M * qRem + rem = S := Nat.div_add_mod S M
  have hrem_lt_M : rem < M := Nat.mod_lt S (by omega)
  let delta := n1 - lo
  have hn1_split : n1 + 1 = delta + (lo + 1) := by dsimp [delta]; omega
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
    dsimp [A, B] at hm; omega
  have hAB : M * A = M * B + M * (A - B) := by
    conv => lhs; rw [show A = B + (A - B) by omega]
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
          rw [hdiff, show q'' + 1 + 1 = (q'' + 1) + 1 from rfl, Nat.mul_add, Nat.mul_add,
              Nat.mul_one] at hdvd_dr
          dsimp [delta, M] at *; omega
  rcases hoff_or with hoff_gt | hok_cand
  · dsimp [delta, M, rem, S] at hdelta_eq_off
    dsimp [off, M, rem, S] at hoff_gt hdelta_eq_off
    omega
  · have heq_n1 : lo + off = n1 := by dsimp [delta, off, M, rem, S] at *; omega
    rwa [heq_n1] at hok_cand

-- Fast +16/+4/+1 exponent floor finders and pullback/quotient lemmas:
def stepAdvanceK (step hi target : Nat) : Nat -> Nat -> Nat
  | 0, k => k
  | fuel + 1, k =>
    if 3 ^ (k + step - 1) * (hi + 1) < 2 ^ (k + step - 1) * (2 * target + 1) then
      stepAdvanceK step hi target fuel (k + step)
    else k

theorem stepAdvanceK_inv (step hi target : Nat) (hstep : step ≥ 1) :
    ∀ (fuel k : Nat),
      (k ≥ 1 ∧ (k = 1 ∨ 3 ^ (k - 1) * (hi + 1) < 2 ^ (k - 1) * (2 * target + 1))) ->
      let kOut := stepAdvanceK step hi target fuel k
      kOut ≥ 1 ∧ (kOut = 1 ∨ 3 ^ (kOut - 1) * (hi + 1) < 2 ^ (kOut - 1) * (2 * target + 1))
  | 0, k, hinv => hinv
  | fuel + 1, k, hinv => by
    simp only [stepAdvanceK]
    by_cases hc : 3 ^ (k + step - 1) * (hi + 1) < 2 ^ (k + step - 1) * (2 * target + 1)
    · simp only [hc, ↓reduceIte]
      exact stepAdvanceK_inv step hi target hstep fuel (k + step) ⟨by omega, Or.inr hc⟩
    · simp only [hc, ↓reduceIte]; exact hinv

def advanceKMin (hi target : Nat) : Nat :=
  let k1 := stepAdvanceK 16 hi target 16 1
  let k2 := stepAdvanceK 4 hi target 4 k1
  stepAdvanceK 1 hi target 4 k2

theorem advanceKMin_sound {hi target k l n1 n2 : Nat}
    (hk1 : k ≥ 1) (hl1 : l ≥ 1)
    (hn1_hi : n1 ≤ hi) (hn2_lo : target ≤ n2)
    (hstep : 2 ^ (k + l) * (n2 + 1) = 3 ^ k * (n1 + 1) + 2 ^ k * (2 ^ l - 1)) :
    advanceKMin hi target ≤ k := by
  change stepAdvanceK 1 hi target 4 (stepAdvanceK 4 hi target 4 (stepAdvanceK 16 hi target 16 1)) ≤ k
  have hi1 := stepAdvanceK_inv 16 hi target (by decide) 16 1 ⟨by omega, Or.inl rfl⟩
  generalize stepAdvanceK 16 hi target 16 1 = k1 at hi1 ⊢
  have hi2 := stepAdvanceK_inv 4 hi target (by decide) 4 k1 hi1
  generalize stepAdvanceK 4 hi target 4 k1 = k2 at hi2 ⊢
  have hinv3 := stepAdvanceK_inv 1 hi target (by decide) 4 k2 hi2
  generalize stepAdvanceK 1 hi target 4 k2 = kOut at hinv3 ⊢
  rcases hinv3 with ⟨hk_pos, h_one | hlt⟩
  · omega
  · apply Classical.byContradiction
    intro hnot
    exact no_spiral_step_of_pow3_lt_target k (kOut - 1) l hi target n1 n2
      (by omega) hl1 hn1_hi hn2_lo hlt hstep

def stepAdvanceL (step evMin wHi : Nat) : Nat -> Nat -> Nat
  | 0, l => l
  | fuel + 1, l =>
    if evMin > 2 ^ (l + step - 1) * wHi then
      stepAdvanceL step evMin wHi fuel (l + step)
    else l

theorem stepAdvanceL_inv (step evMin wHi : Nat) (hstep : step ≥ 1) :
    ∀ (fuel l : Nat),
      (l ≥ 1 ∧ (l = 1 ∨ evMin > 2 ^ (l - 1) * wHi)) ->
      let lOut := stepAdvanceL step evMin wHi fuel l
      lOut ≥ 1 ∧ (lOut = 1 ∨ evMin > 2 ^ (lOut - 1) * wHi)
  | 0, l, hinv => hinv
  | fuel + 1, l, hinv => by
    simp only [stepAdvanceL]
    by_cases hc : evMin > 2 ^ (l + step - 1) * wHi
    · simp only [hc, ↓reduceIte]
      exact stepAdvanceL_inv step evMin wHi hstep fuel (l + step) ⟨by omega, Or.inr hc⟩
    · simp only [hc, ↓reduceIte]; exact hinv

def advanceLMin (evMin wHi : Nat) : Nat :=
  let l1 := stepAdvanceL 16 evMin wHi 16 1
  let l2 := stepAdvanceL 4 evMin wHi 4 l1
  stepAdvanceL 1 evMin wHi 4 l2

theorem advanceLMin_sound {evMin wHi l nNext : Nat}
    (hl1 : l ≥ 1) (hnNext_hi : nNext ≤ wHi) (hev_lo : evMin ≤ 2 ^ l * nNext) :
    advanceLMin evMin wHi ≤ l := by
  change stepAdvanceL 1 evMin wHi 4 (stepAdvanceL 4 evMin wHi 4 (stepAdvanceL 16 evMin wHi 16 1)) ≤ l
  have hi1 := stepAdvanceL_inv 16 evMin wHi (by decide) 16 1 ⟨by omega, Or.inl rfl⟩
  generalize stepAdvanceL 16 evMin wHi 16 1 = l1 at hi1 ⊢
  have hi2 := stepAdvanceL_inv 4 evMin wHi (by decide) 4 l1 hi1
  generalize stepAdvanceL 4 evMin wHi 4 l1 = l2 at hi2 ⊢
  have hinv3 := stepAdvanceL_inv 1 evMin wHi (by decide) 4 l2 hi2
  generalize stepAdvanceL 1 evMin wHi 4 l2 = lOut at hinv3 ⊢
  rcases hinv3 with ⟨hl_pos, h_one | hgt⟩
  · omega
  · apply Classical.byContradiction
    intro hnot
    have hp : 2 ^ l ≤ 2 ^ (lOut - 1) := pow2_mono_nat (by omega)
    have hm : 2 ^ l * nNext ≤ 2 ^ (lOut - 1) * wHi :=
      Nat.mul_le_mul hp hnNext_hi
    omega

def oddQuotMin (k lo : Nat) : Nat :=
  let u0 := ceilDiv (lo + 1) (2 ^ k)
  if u0 % 2 == 1 then u0 else u0 + 1

def oddQuotMax (k hi : Nat) : Nat :=
  let u1 := (hi + 1) / (2 ^ k)
  if u1 % 2 == 1 then u1 else u1 - 1

theorem oddQuotBounds_sound {k l lo hi n1 n2 : Nat}
    (hl : l ≥ 1) (hlo : lo ≤ n1) (hhi : n1 ≤ hi)
    (hpow_le : 2 ^ k ≤ hi + 1)
    (hstep : 2 ^ (k + l) * (n2 + 1) = 3 ^ k * (n1 + 1) + 2 ^ k * (2 ^ l - 1)) :
    oddQuotMin k lo ≤ oddQuotMax k hi ∧
    2 ^ k * oddQuotMin k lo - 1 ≤ n1 ∧
    n1 ≤ 2 ^ k * oddQuotMax k hi - 1 ∧
    3 ^ k * oddQuotMin k lo - 1 ≤ 2 ^ l * n2 ∧
    2 ^ l * n2 ≤ 3 ^ k * oddQuotMax k hi - 1 := by
  rcases spiral_step_odd_quotient_nat k l n1 n2 hl hstep with ⟨u, hu_odd, hn1_u, hn2_u⟩
  have hp2k : 2 ^ k ≥ 1 := pow2_pos_nat k
  have hu0_le : ceilDiv (lo + 1) (2 ^ k) ≤ u :=
    ceilDiv_le_of_le_mul hp2k (by omega)
  have hu1_ge : u ≤ (hi + 1) / (2 ^ k) :=
    le_div_of_mul_le hp2k (by omega)
  have hu1_pos : (hi + 1) / (2 ^ k) ≥ 1 := le_div_of_mul_le hp2k (by omega)
  have huMin_le : oddQuotMin k lo ≤ u := by
    unfold oddQuotMin
    by_cases ho : ceilDiv (lo + 1) (2 ^ k) % 2 = 1
    · have hb : (ceilDiv (lo + 1) (2 ^ k) % 2 == 1) = true := decide_eq_true ho
      simp only [hb, ↓reduceIte]; exact hu0_le
    · have hb : (ceilDiv (lo + 1) (2 ^ k) % 2 == 1) = false := decide_eq_false ho
      simp only [hb, Bool.false_eq_true, ↓reduceIte]; omega
  have hu_le_Max : u ≤ oddQuotMax k hi := by
    unfold oddQuotMax
    by_cases ho : ((hi + 1) / 2 ^ k) % 2 = 1
    · have hb : (((hi + 1) / 2 ^ k) % 2 == 1) = true := decide_eq_true ho
      simp only [hb, ↓reduceIte]; exact hu1_ge
    · have hb : (((hi + 1) / 2 ^ k) % 2 == 1) = false := decide_eq_false ho
      simp only [hb, Bool.false_eq_true, ↓reduceIte]; omega
  have hm2_lo := Nat.mul_le_mul_left (2 ^ k) huMin_le
  have hm2_hi := Nat.mul_le_mul_left (2 ^ k) hu_le_Max
  have hm3_lo := Nat.mul_le_mul_left (3 ^ k) huMin_le
  have hm3_hi := Nat.mul_le_mul_left (3 ^ k) hu_le_Max
  exact ⟨Nat.le_trans huMin_le hu_le_Max, by omega, by omega, by omega, by omega⟩

def pullbackLo1 (k1 l1 p3k1 lo1 lo2 : Nat) : Nat :=
  maxNat lo1 (ceilDiv (2 ^ (k1 + l1) * lo2 + 2 ^ k1) p3k1 - 1)

def pullbackHi1 (k1 l1 p3k1 hi1 hi2 : Nat) : Nat :=
  minNat hi1 ((2 ^ (k1 + l1) * hi2 + 2 ^ k1) / p3k1 - 1)

theorem pullback_n1_bounds {k1 l1 lo1 hi1 lo2 hi2 n1 n2 : Nat}
    (hl1 : l1 ≥ 1)
    (hn1_lo : lo1 ≤ n1) (hn1_hi : n1 ≤ hi1)
    (hn2_lo : lo2 ≤ n2) (hn2_hi : n2 ≤ hi2)
    (hstep1 : 2 ^ (k1 + l1) * (n2 + 1) = 3 ^ k1 * (n1 + 1) + 2 ^ k1 * (2 ^ l1 - 1)) :
    pullbackLo1 k1 l1 (3 ^ k1) lo1 lo2 ≤ n1 ∧
    n1 ≤ pullbackHi1 k1 l1 (3 ^ k1) hi1 hi2 := by
  have hsub := spiral_step_mul_ratio_nat k1 l1 n1 n2 hl1 hstep1
  have hp3 : 3 ^ k1 ≥ 1 := pow3_pos_nat k1
  have hlo_mul : 2 ^ (k1 + l1) * lo2 + 2 ^ k1 ≤ 3 ^ k1 * (n1 + 1) := by
    have hm := Nat.mul_le_mul_left (2 ^ (k1 + l1)) hn2_lo; omega
  have hhi_mul : 3 ^ k1 * (n1 + 1) ≤ 2 ^ (k1 + l1) * hi2 + 2 ^ k1 := by
    have hm := Nat.mul_le_mul_left (2 ^ (k1 + l1)) hn2_hi; omega
  have hcl := ceilDiv_le_of_le_mul hp3 hlo_mul
  have hfl := le_div_of_mul_le hp3 hhi_mul
  refine ⟨?_, ?_⟩
  · unfold pullbackLo1 maxNat
    by_cases hc : lo1 ≤ ceilDiv (2 ^ (k1 + l1) * lo2 + 2 ^ k1) (3 ^ k1) - 1 <;> simp [hc] <;> omega
  · unfold pullbackHi1 minNat
    by_cases hc : hi1 ≤ (2 ^ (k1 + l1) * hi2 + 2 ^ k1) / 3 ^ k1 - 1 <;> simp [hc] <;> omega

-- Core congruence divisibility lemmas for R1 and R2:
theorem dvd_two_step_collapse {kAcc wAcc kNext kMin lNext n1 nCur nNext gAcc : Nat}
    (hk_ge : kMin ≤ kNext) (_hlNext : lNext ≥ 1)
    (hacc : 2 ^ kAcc * (nCur + 1) = 3 ^ wAcc * (n1 + 1) + gAcc)
    (hnext : 2 ^ (kNext + lNext) * (nNext + 1) =
      3 ^ kNext * (nCur + 1) + 2 ^ kNext * (2 ^ lNext - 1)) :
    2 ^ (kAcc + kMin) ∣ 3 ^ wAcc * (n1 + 1) + gAcc := by
  have hp2l : 2 ^ lNext ≥ 1 := pow2_pos_nat lNext
  have hl_le : 2 ^ lNext - 1 ≤ 2 ^ lNext * (nNext + 1) := by
    have hm : 2 ^ lNext * 1 ≤ 2 ^ lNext * (nNext + 1) :=
      Nat.mul_le_mul_left (2 ^ lNext) (by omega)
    omega
  let Q := 2 ^ lNext * (nNext + 1) - (2 ^ lNext - 1)
  have hdiv_next : 3 ^ kNext * (nCur + 1) = 2 ^ kNext * Q := by
    have hlhs : 2 ^ (kNext + lNext) * (nNext + 1) = 2 ^ kNext * (2 ^ lNext * (nNext + 1)) := by
      rw [Nat.pow_add, Nat.mul_assoc]
    have hsp : 2 ^ lNext * (nNext + 1) = Q + (2 ^ lNext - 1) := by dsimp [Q]; omega
    rw [hlhs, hsp, Nat.mul_add] at hnext; omega
  have hcomb : 2 ^ (kAcc + kMin) ∣ 3 ^ kNext * (3 ^ wAcc * (n1 + 1) + gAcc) := by
    refine ⟨2 ^ (kNext - kMin) * Q, ?_⟩
    rw [← hacc]
    calc
      3 ^ kNext * (2 ^ kAcc * (nCur + 1))
          = 2 ^ kAcc * (3 ^ kNext * (nCur + 1)) := by
            rw [← Nat.mul_assoc, Nat.mul_comm (3 ^ kNext) (2 ^ kAcc), Nat.mul_assoc]
      _ = 2 ^ kAcc * (2 ^ kNext * Q) := by rw [hdiv_next]
      _ = 2 ^ (kAcc + kNext) * Q := by rw [← Nat.mul_assoc, ← Nat.pow_add]
      _ = 2 ^ ((kAcc + kMin) + (kNext - kMin)) * Q := by
            rw [show kAcc + kNext = (kAcc + kMin) + (kNext - kMin) by omega]
      _ = 2 ^ (kAcc + kMin) * (2 ^ (kNext - kMin) * Q) := by rw [Nat.pow_add, Nat.mul_assoc]
  exact pow2_dvd_of_pow2_dvd_pow3_mul_nat (kAcc + kMin) kNext _ hcomb

theorem step_hensel_extend {kAcc wAcc k l n1 nCur nNext gAcc : Nat}
    (hacc : 2 ^ kAcc * (nCur + 1) = 3 ^ wAcc * (n1 + 1) + gAcc)
    (hstep : 2 ^ (k + l) * (nNext + 1) = 3 ^ k * (nCur + 1) + 2 ^ k * (2 ^ l - 1)) :
    2 ^ (kAcc + k + l) * (nNext + 1) =
      3 ^ (wAcc + k) * (n1 + 1) + (3 ^ k * gAcc + 2 ^ (kAcc + k) * (2 ^ l - 1)) := by
  calc
    2 ^ (kAcc + k + l) * (nNext + 1)
        = 2 ^ kAcc * (2 ^ (k + l) * (nNext + 1)) := by
          rw [show kAcc + k + l = kAcc + (k + l) by omega, Nat.pow_add, Nat.mul_assoc]
    _ = 2 ^ kAcc * (3 ^ k * (nCur + 1) + 2 ^ k * (2 ^ l - 1)) := by rw [hstep]
    _ = 3 ^ k * (2 ^ kAcc * (nCur + 1)) + 2 ^ (kAcc + k) * (2 ^ l - 1) := by
          rw [Nat.mul_add, ← Nat.mul_assoc (2 ^ kAcc) (3 ^ k),
              Nat.mul_comm (2 ^ kAcc) (3 ^ k), Nat.mul_assoc,
              ← Nat.mul_assoc (2 ^ kAcc) (2 ^ k), ← Nat.pow_add]
    _ = 3 ^ k * (3 ^ wAcc * (n1 + 1) + gAcc) + 2 ^ (kAcc + k) * (2 ^ l - 1) := by rw [hacc]
    _ = 3 ^ (wAcc + k) * (n1 + 1) + (3 ^ k * gAcc + 2 ^ (kAcc + k) * (2 ^ l - 1)) := by
          rw [Nat.mul_add, ← Nat.mul_assoc (3 ^ k) (3 ^ wAcc),
              Nat.mul_comm (3 ^ k) (3 ^ wAcc), ← Nat.pow_add, Nat.add_assoc]

theorem dvd_l_collapse {kAcc wAcc k l lCur n1 nCur nNext gAcc : Nat}
    (hl_ge : lCur ≤ l)
    (hacc : 2 ^ kAcc * (nCur + 1) = 3 ^ wAcc * (n1 + 1) + gAcc)
    (hstep : 2 ^ (k + l) * (nNext + 1) = 3 ^ k * (nCur + 1) + 2 ^ k * (2 ^ l - 1)) :
    2 ^ (kAcc + k + lCur) ∣
      3 ^ (wAcc + k) * (n1 + 1) + (3 ^ k * gAcc + 2 ^ (kAcc + k) * (2 ^ lCur - 1)) := by
  have hext := step_hensel_extend hacc hstep
  let d := l - lCur
  have hp2c : 2 ^ lCur ≥ 1 := pow2_pos_nat lCur
  have hp2d : 2 ^ d ≥ 1 := pow2_pos_nat d
  have hl_sp : 2 ^ l - 1 = 2 ^ lCur * (2 ^ d - 1) + (2 ^ lCur - 1) := by
    have hpow : 2 ^ l = 2 ^ lCur * 2 ^ d := by
      rw [show l = lCur + d by dsimp [d]; omega, Nat.pow_add]
    have hmul : 2 ^ lCur * (2 ^ d - 1) + 2 ^ lCur = 2 ^ lCur * 2 ^ d := by
      calc
        2 ^ lCur * (2 ^ d - 1) + 2 ^ lCur
            = 2 ^ lCur * (2 ^ d - 1) + 2 ^ lCur * 1 := by rw [Nat.mul_one]
        _ = 2 ^ lCur * ((2 ^ d - 1) + 1) := by rw [← Nat.mul_add]
        _ = 2 ^ lCur * 2 ^ d := by rw [show (2 ^ d - 1) + 1 = 2 ^ d by omega]
    omega
  have hlhs : 2 ^ (kAcc + k + l) * (nNext + 1) =
      2 ^ (kAcc + k + lCur) * (2 ^ d * (nNext + 1)) := by
    rw [show kAcc + k + l = (kAcc + k + lCur) + d by dsimp [d]; omega, Nat.pow_add, Nat.mul_assoc]
  have hrhs_g : 2 ^ (kAcc + k) * (2 ^ l - 1) =
      2 ^ (kAcc + k + lCur) * (2 ^ d - 1) + 2 ^ (kAcc + k) * (2 ^ lCur - 1) := by
    rw [hl_sp, Nat.mul_add, ← Nat.mul_assoc, ← Nat.pow_add]
  let A := 2 ^ d * (nNext + 1)
  let B := 2 ^ d - 1
  have hBA : B ≤ A := by
    have hm : 2 ^ d * 1 ≤ 2 ^ d * (nNext + 1) := Nat.mul_le_mul_left (2 ^ d) (by omega)
    dsimp [A, B]; omega
  refine ⟨A - B, ?_⟩
  have hAB : 2 ^ (kAcc + k + lCur) * A =
      2 ^ (kAcc + k + lCur) * (A - B) + 2 ^ (kAcc + k + lCur) * B := by
    rw [← Nat.mul_add, show (A - B) + B = A by omega]
  rw [hlhs, hrhs_g] at hext
  change 2 ^ (kAcc + k + lCur) * A =
    3 ^ (wAcc + k) * (n1 + 1) +
    (3 ^ k * gAcc + (2 ^ (kAcc + k + lCur) * B + 2 ^ (kAcc + k) * (2 ^ lCur - 1))) at hext
  omega

-- Self-guided R1 verifier (`z1 -> z2 -> z3`):
def loopL1R1 (b1 b2 k1 p3k1 inv1 lo1 hi1 evMin evMax : Nat) (exemptIds : List Nat) :
    Nat -> Nat -> Bool
  | 0, _ => false
  | fuel + 1, l1 =>
    if evMax < 2 ^ l1 * (b1 + 1) then true
    else
      let P1 := 2 ^ l1
      let lo2 := maxNat (b1 + 1) (ceilDiv evMin P1)
      let hi2 := minNat b2 (evMax / P1)
      let okHere :=
        if lo2 > hi2 then true
        else
          let nlo1 := pullbackLo1 k1 l1 p3k1 lo1 lo2
          let nhi1 := pullbackHi1 k1 l1 p3k1 hi1 hi2
          if nlo1 > nhi1 then true
          else
            let k2Min := advanceKMin hi2 (b2 + 1)
            if hi2 + 1 < 2 ^ k2Min then true
            else
              let g1 := 2 ^ k1 * (P1 - 1)
              checkCongPred nlo1 nhi1 (k1 + l1 + k2Min) inv1 g1 (checkCandR1 b1 b2 exemptIds)
      okHere && loopL1R1 b1 b2 k1 p3k1 inv1 lo1 hi1 evMin evMax exemptIds fuel (l1 + 1)

theorem loopL1R1_sound
    {b1 b2 k1 inv1 lo1 hi1 evMin evMax : Nat} {exemptIds : List Nat}
    {s0 s1 : SpiralStepData} {x2 : Nat}
    (hb2_lt : b2 < 2 ^ 256) (hb12 : b1 ≤ b2)
    (hk0_eq : s0.k = k1)
    (hs0_lo : lo1 ≤ s0.x) (hs0_hi : s0.x ≤ hi1) (hs0_b1 : s0.x ≤ b1)
    (hs1_lo : b1 + 1 ≤ s1.x) (hs1_hi : s1.x ≤ b2)
    (hx2_lo : b2 + 1 ≤ x2)
    (hev_lo : evMin ≤ 2 ^ s0.l * s1.x) (hev_hi : 2 ^ s0.l * s1.x ≤ evMax)
    (hinv1 : (3 ^ k1 * inv1) % 2 ^ 384 = 1)
    (hst0 : ValidSpiralStep s0 s1.x)
    (hst1 : ValidSpiralStep s1 x2) :
    ∀ (fuel lCur : Nat),
      lCur ≤ s0.l ->
      loopL1R1 b1 b2 k1 (3 ^ k1) inv1 lo1 hi1 evMin evMax exemptIds fuel lCur = true ->
      s0.x ∈ exemptIds
  | 0, _, _, hok => by simp [loopL1R1] at hok
  | fuel + 1, lCur, hl_ge, hok => by
    unfold loopL1R1 at hok
    by_cases hexit : evMax < 2 ^ lCur * (b1 + 1)
    · exfalso
      have hp : 2 ^ lCur ≤ 2 ^ s0.l := pow2_mono_nat hl_ge
      have hm : 2 ^ lCur * (b1 + 1) ≤ 2 ^ s0.l * s1.x := Nat.mul_le_mul hp hs1_lo
      omega
    · simp only [hexit, ↓reduceIte, Bool.and_eq_true] at hok
      rcases hok with ⟨hokHere, hmore⟩
      by_cases heq_l : s0.l = lCur
      · subst heq_l; subst hk0_eq
        let P1 := 2 ^ s0.l
        have hP1 : P1 ≥ 1 := pow2_pos_nat s0.l
        have hlo2 : maxNat (b1 + 1) (ceilDiv evMin P1) ≤ s1.x := by
          unfold maxNat
          have hc := ceilDiv_le_of_le_mul hP1 hev_lo
          by_cases h : b1 + 1 ≤ ceilDiv evMin P1 <;> simp [h] <;> omega
        have hhi2 : s1.x ≤ minNat b2 (evMax / P1) := by
          unfold minNat
          have hf := le_div_of_mul_le hP1 hev_hi
          by_cases h : b2 ≤ evMax / P1 <;> simp [h] <;> omega
        have hnot_gt2 : ¬ (maxNat (b1 + 1) (ceilDiv evMin P1) > minNat b2 (evMax / P1)) := by omega
        rw [ite_eq_right hnot_gt2] at hokHere
        rcases hst0 with ⟨hx0_o, hx0_p, hx1_o, hx1_p, hk0_1, hl0_1, hstep0⟩
        rcases pullback_n1_bounds hl0_1 hs0_lo hs0_hi hlo2 hhi2 hstep0 with ⟨hnlo1, hnhi1⟩
        let lo2 := maxNat (b1 + 1) (ceilDiv evMin P1)
        let hi2 := minNat b2 (evMax / P1)
        have hnot_gt1 : ¬ (pullbackLo1 s0.k s0.l (3 ^ s0.k) lo1 lo2 >
            pullbackHi1 s0.k s0.l (3 ^ s0.k) hi1 hi2) := by dsimp [lo2, hi2]; omega
        rw [ite_eq_right hnot_gt1] at hokHere
        rcases hst1 with ⟨hx1_o2, hx1_p2, hx2_o, hx2_p, hk1_1, hl1_1, hstep1⟩
        have hk2_ge : advanceKMin hi2 (b2 + 1) ≤ s1.k :=
          advanceKMin_sound hk1_1 hl1_1 hhi2 hx2_lo hstep1
        generalize advanceKMin hi2 (b2 + 1) = k2Min at hk2_ge hokHere
        by_cases hhi_lt : hi2 + 1 < 2 ^ k2Min
        · exfalso
          exact no_spiral_step_of_hi_lt_pow2 s1.k k2Min s1.l hi2 s1.x x2
            hk2_ge hl1_1 hhi2 hhi_lt hstep1
        · rw [ite_eq_right hhi_lt] at hokHere
          have hacc0 : 2 ^ 0 * (s0.x + 1) = 3 ^ 0 * (s0.x + 1) + 0 := by simp
          have hacc1 := step_hensel_extend hacc0 hstep0
          simp only [Nat.zero_add, Nat.mul_zero] at hacc1
          have hdvd := dvd_two_step_collapse hk2_ge hl1_1 hacc1 hstep1
          have hcand := checkCongPred_sound hnlo1 hnhi1 hinv1 hdvd hokHere
          exact checkCandR1_sound hb2_lt hs0_b1 hb12 hs1_lo hs1_hi hx2_lo
            ⟨hx0_o, hx0_p, hx1_o, hx1_p, hk0_1, hl0_1, hstep0⟩
            ⟨hx1_o2, hx1_p2, hx2_o, hx2_p, hk1_1, hl1_1, hstep1⟩ hcand
      · exact loopL1R1_sound hb2_lt hb12 hk0_eq hs0_lo hs0_hi hs0_b1 hs1_lo hs1_hi hx2_lo
          hev_lo hev_hi hinv1 hst0 hst1 fuel (lCur + 1) (by omega) hmore

def verifyBandR1 (b1 b2 : Nat) (exemptIds : List Nat) (k1 lo1 hi1 : Nat) : Bool :=
  if lo1 > hi1 then true
  else if k1 > 384 then false
  else if hi1 + 1 < 2 ^ k1 then true
  else if 3 ^ k1 * (hi1 + 1) < 2 ^ k1 * (2 * (b1 + 1) + 1) then true
  else
    let uMin := oddQuotMin k1 lo1
    let uMax := oddQuotMax k1 hi1
    if uMin > uMax then true
    else
      let p3k1 := 3 ^ k1
      let evMin := p3k1 * uMin - 1
      let evMax := p3k1 * uMax - 1
      let l1Min := advanceLMin evMin b2
      let inv1 := inv3At384 k1
      let lo1u := maxNat lo1 (2 ^ k1 * uMin - 1)
      let hi1u := minNat hi1 (2 ^ k1 * uMax - 1)
      loopL1R1 b1 b2 k1 p3k1 inv1 lo1u hi1u evMin evMax exemptIds 256 l1Min

theorem verifyBandR1_sound
    {b1 b2 k1 lo1 hi1 : Nat} {exemptIds : List Nat}
    {s0 s1 : SpiralStepData} {x2 : Nat}
    (hb2_lt : b2 < 2 ^ 256) (hb12 : b1 ≤ b2)
    (hk0_eq : s0.k = k1)
    (hs0_lo : lo1 ≤ s0.x) (hs0_hi : s0.x ≤ hi1) (hs0_b1 : s0.x ≤ b1)
    (hs1_lo : b1 + 1 ≤ s1.x) (hs1_hi : s1.x ≤ b2)
    (hx2_lo : b2 + 1 ≤ x2)
    (hst0 : ValidSpiralStep s0 s1.x)
    (hst1 : ValidSpiralStep s1 x2)
    (hok : verifyBandR1 b1 b2 exemptIds k1 lo1 hi1 = true) :
    s0.x ∈ exemptIds := by
  unfold verifyBandR1 at hok
  by_cases hgt : lo1 > hi1
  · omega
  · simp only [hgt, ↓reduceIte] at hok
    by_cases hk384 : k1 > 384
    · simp [hk384] at hok
    · simp only [hk384, ↓reduceIte] at hok
      rcases hst0 with ⟨hx0_o, hx0_p, hx1_o, hx1_p, hk0_1, hl0_1, hstep0⟩
      by_cases hpow : hi1 + 1 < 2 ^ k1
      · exfalso
        exact no_spiral_step_of_hi_lt_pow2 s0.k k1 s0.l hi1 s0.x s1.x
          (by omega) hl0_1 hs0_hi hpow hstep0
      · simp only [hpow, ↓reduceIte] at hok
        by_cases htgt : 3 ^ k1 * (hi1 + 1) < 2 ^ k1 * (2 * (b1 + 1) + 1)
        · exfalso
          exact no_spiral_step_of_pow3_lt_target s0.k k1 s0.l hi1 (b1 + 1) s0.x s1.x
            (by omega) hl0_1 hs0_hi hs1_lo htgt hstep0
        · simp only [htgt, ↓reduceIte] at hok
          subst hk0_eq
          rcases oddQuotBounds_sound hl0_1 hs0_lo hs0_hi (by omega) hstep0 with
            ⟨hu_le, hlo_u, hhi_u, hev_lo, hev_hi⟩
          have hnot_u : ¬ (oddQuotMin s0.k lo1 > oddQuotMax s0.k hi1) := by omega
          simp only [hnot_u, ↓reduceIte] at hok
          have hlo1u : maxNat lo1 (2 ^ s0.k * oddQuotMin s0.k lo1 - 1) ≤ s0.x := by
            unfold maxNat
            by_cases hc : lo1 ≤ 2 ^ s0.k * oddQuotMin s0.k lo1 - 1 <;> simp [hc] <;> omega
          have hhi1u : s0.x ≤ minNat hi1 (2 ^ s0.k * oddQuotMax s0.k hi1 - 1) := by
            unfold minNat
            by_cases hc : hi1 ≤ 2 ^ s0.k * oddQuotMax s0.k hi1 - 1 <;> simp [hc] <;> omega
          have hl1_ge := advanceLMin_sound hl0_1 hs1_hi hev_lo
          generalize advanceLMin (3 ^ s0.k * oddQuotMin s0.k lo1 - 1) b2 = l1Min at hl1_ge hok
          exact loopL1R1_sound hb2_lt hb12 rfl hlo1u hhi1u hs0_b1 hs1_lo hs1_hi hx2_lo
            hev_lo hev_hi (inv3At384_spec (by omega))
            ⟨hx0_o, hx0_p, hx1_o, hx1_p, hk0_1, hl0_1, hstep0⟩ hst1 256 l1Min hl1_ge hok

-- Power-hoisted fast helpers for R2 (`loopL2R2` & `loopK2R2`, zero inner `2^k`/`3^k`):
def inv3One384 : Nat :=
  26268004130929652808186026733429075870053159513643631111965528936163814514331473740942844169923277093871085326871211

set_option maxRecDepth 20000 in
theorem inv3One384_spec : (3 * inv3One384) % 2 ^ 384 = 1 := by decide

theorem inv3_step_spec {w invW : Nat} (h : (3 ^ w * invW) % 2 ^ 384 = 1) :
    (3 ^ (w + 1) * ((invW * inv3One384) % 2 ^ 384)) % 2 ^ 384 = 1 := by
  rw [Nat.mul_mod, Nat.mod_mod_of_dvd _ (Nat.dvd_refl _), ← Nat.mul_mod, Nat.pow_succ]
  have heq : (3 ^ w * 3) * (invW * inv3One384) = (3 ^ w * invW) * (3 * inv3One384) := by
    calc
      (3 ^ w * 3) * (invW * inv3One384)
          = 3 ^ w * (3 * (invW * inv3One384)) := by rw [Nat.mul_assoc]
      _ = 3 ^ w * (invW * (3 * inv3One384)) := by
            rw [← Nat.mul_assoc 3, Nat.mul_comm 3 invW, Nat.mul_assoc]
      _ = (3 ^ w * invW) * (3 * inv3One384) := by rw [← Nat.mul_assoc]
  rw [heq, Nat.mul_mod, h, inv3One384_spec]

def checkCongPredM (lo span M exp invAt g : Nat) (okCand : Nat -> Bool) : Bool :=
  let rem := (invAt * g + (lo + 1)) % M
  let off := (M - rem) % M
  (exp ≤ 384) && (span < M) && ((off > span) || okCand (lo + off))

theorem checkCongPredM_sound
    {lo hi M exp w invAt g n1 : Nat} {okCand : Nat -> Bool}
    (hM : M = 2 ^ exp)
    (hlo : lo ≤ n1) (hhi : n1 ≤ hi)
    (hinv : (3 ^ w * invAt) % 2 ^ 384 = 1)
    (hdvd : 2 ^ exp ∣ 3 ^ w * (n1 + 1) + g)
    (hok : checkCongPredM lo (hi - lo) M exp invAt g okCand = true) :
    okCand n1 = true := by
  subst hM
  apply checkCongPred_sound hlo hhi hinv hdvd
  unfold checkCongPred; rw [pow2Split_eq]; exact hok

def stepAdvanceKFast (step mul3 mul2 hi tgt : Nat) :
    Nat -> (Nat × Nat × Nat) -> Nat × Nat × Nat
  | 0, st => st
  | fuel + 1, (k, p3, p2) =>
    let np3 := p3 * mul3
    let np2 := p2 * mul2
    if np3 * (hi + 1) < np2 * tgt then
      stepAdvanceKFast step mul3 mul2 hi tgt fuel (k + step, np3, np2)
    else (k, p3, p2)

theorem stepAdvanceKFast_inv (step mul3 mul2 : Nat) {hi tgt x : Nat}
    (hstep : step ≥ 1) (hm3 : mul3 = 3 ^ step) (hm2 : mul2 = 2 ^ step) (hx_le : x ≤ hi) :
    ∀ (fuel : Nat) (st : Nat × Nat × Nat),
      (st.1 ≥ 1 ∧ st.2.1 = 3 ^ (st.1 - 1) ∧ st.2.2 = 2 ^ (st.1 - 1) ∧
        (st.1 = 1 ∨ 3 ^ (st.1 - 1) * (x + 1) < 2 ^ (st.1 - 1) * tgt)) ->
      (stepAdvanceKFast step mul3 mul2 hi tgt fuel st).1 ≥ 1 ∧
      (stepAdvanceKFast step mul3 mul2 hi tgt fuel st).2.1 =
        3 ^ ((stepAdvanceKFast step mul3 mul2 hi tgt fuel st).1 - 1) ∧
      (stepAdvanceKFast step mul3 mul2 hi tgt fuel st).2.2 =
        2 ^ ((stepAdvanceKFast step mul3 mul2 hi tgt fuel st).1 - 1) ∧
      ((stepAdvanceKFast step mul3 mul2 hi tgt fuel st).1 = 1 ∨
        3 ^ ((stepAdvanceKFast step mul3 mul2 hi tgt fuel st).1 - 1) * (x + 1) <
          2 ^ ((stepAdvanceKFast step mul3 mul2 hi tgt fuel st).1 - 1) * tgt)
  | 0, _, hinv => hinv
  | fuel + 1, (k, p3, p2), ⟨hk1, hp3, hp2, hlt_prev⟩ => by
    dsimp only at hk1 hp3 hp2 hlt_prev
    simp only [stepAdvanceKFast]
    by_cases hc : (p3 * mul3) * (hi + 1) < (p2 * mul2) * tgt
    · simp only [hc, ↓reduceIte]
      have hexp : k + step - 1 = (k - 1) + step := by omega
      have hnp3 : p3 * mul3 = 3 ^ (k + step - 1) := by rw [hp3, hm3, hexp, Nat.pow_add]
      have hnp2 : p2 * mul2 = 2 ^ (k + step - 1) := by rw [hp2, hm2, hexp, Nat.pow_add]
      have hx_lt : 3 ^ (k + step - 1) * (x + 1) < 2 ^ (k + step - 1) * tgt := by
        rw [← hnp3, ← hnp2]
        exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ (by omega)) hc
      exact stepAdvanceKFast_inv step mul3 mul2 hstep hm3 hm2 hx_le fuel (k + step, p3 * mul3, p2 * mul2)
        ⟨by omega, hnp3, hnp2, Or.inr hx_lt⟩
    · simp only [hc, ↓reduceIte]
      exact ⟨hk1, hp3, hp2, hlt_prev⟩

def advanceKFrom (hi target k0 p3_0 p2_0 : Nat) : Nat × Nat × Nat :=
  stepAdvanceKFast 1 3 2 hi (2 * target + 1) 4
    (stepAdvanceKFast 4 81 16 hi (2 * target + 1) 4
      (stepAdvanceKFast 16 43046721 65536 hi (2 * target + 1) 16 (k0, p3_0, p2_0)))

theorem advanceKFrom_inv {hi target x k0 p3_0 p2_0 : Nat}
    (hx_le : x ≤ hi)
    (hinv0 : k0 ≥ 1 ∧ p3_0 = 3 ^ (k0 - 1) ∧ p2_0 = 2 ^ (k0 - 1) ∧
      (k0 = 1 ∨ 3 ^ (k0 - 1) * (x + 1) < 2 ^ (k0 - 1) * (2 * target + 1))) :
    (advanceKFrom hi target k0 p3_0 p2_0).1 ≥ 1 ∧
    (advanceKFrom hi target k0 p3_0 p2_0).2.1 =
      3 ^ ((advanceKFrom hi target k0 p3_0 p2_0).1 - 1) ∧
    (advanceKFrom hi target k0 p3_0 p2_0).2.2 =
      2 ^ ((advanceKFrom hi target k0 p3_0 p2_0).1 - 1) ∧
    ((advanceKFrom hi target k0 p3_0 p2_0).1 = 1 ∨
      3 ^ ((advanceKFrom hi target k0 p3_0 p2_0).1 - 1) * (x + 1) <
        2 ^ ((advanceKFrom hi target k0 p3_0 p2_0).1 - 1) * (2 * target + 1)) := by
  unfold advanceKFrom
  have h1 := stepAdvanceKFast_inv 16 43046721 65536 (by decide) (by decide) (by decide) hx_le
    16 (k0, p3_0, p2_0) hinv0
  generalize stepAdvanceKFast 16 43046721 65536 hi (2 * target + 1) 16 (k0, p3_0, p2_0) = r1 at h1 ⊢
  have h2 := stepAdvanceKFast_inv 4 81 16 (by decide) (by decide) (by decide) hx_le 4 r1 h1
  generalize stepAdvanceKFast 4 81 16 hi (2 * target + 1) 4 r1 = r2 at h2 ⊢
  exact stepAdvanceKFast_inv 1 3 2 (by decide) (by decide) (by decide) hx_le 4 r2 h2

theorem advanceK_inv_implies_le {target k l x nNext kOut p2m1 : Nat}
    (hk1 : k ≥ 1) (hl1 : l ≥ 1) (hnNext : target ≤ nNext)
    (hkOut1 : kOut ≥ 1) (hp2 : p2m1 = 2 ^ (kOut - 1))
    (hor : kOut = 1 ∨ 3 ^ (kOut - 1) * (x + 1) < 2 ^ (kOut - 1) * (2 * target + 1))
    (hstep : 2 ^ (k + l) * (nNext + 1) = 3 ^ k * (x + 1) + 2 ^ k * (2 ^ l - 1)) :
    kOut ≤ k ∧ 2 * p2m1 = 2 ^ kOut := by
  have hp2_out : 2 * p2m1 = 2 ^ kOut := by
    rw [hp2, Nat.mul_comm 2, ← Nat.pow_succ, show (kOut - 1).succ = kOut by omega]
  refine ⟨?_, hp2_out⟩
  rcases hor with rfl | hlt
  · exact hk1
  · apply Classical.byContradiction
    intro hnot
    exact no_spiral_step_of_pow3_lt_target k (kOut - 1) l x target x nNext
      (by omega) hl1 (Nat.le_refl x) hnNext hlt hstep

def stepAdvanceLFast (step mul2 evMin wHi : Nat) : Nat -> (Nat × Nat) -> Nat × Nat
  | 0, st => st
  | fuel + 1, (l, p2) =>
    let np2 := p2 * mul2
    if evMin > np2 * wHi then
      stepAdvanceLFast step mul2 evMin wHi fuel (l + step, np2)
    else (l, p2)

theorem stepAdvanceLFast_inv (step mul2 : Nat) {evMin wHi : Nat}
    (hstep : step ≥ 1) (hm2 : mul2 = 2 ^ step) :
    ∀ (fuel : Nat) (st : Nat × Nat),
      (st.1 ≥ 1 ∧ st.2 = 2 ^ (st.1 - 1) ∧ (st.1 = 1 ∨ evMin > 2 ^ (st.1 - 1) * wHi)) ->
      (stepAdvanceLFast step mul2 evMin wHi fuel st).1 ≥ 1 ∧
      (stepAdvanceLFast step mul2 evMin wHi fuel st).2 =
        2 ^ ((stepAdvanceLFast step mul2 evMin wHi fuel st).1 - 1) ∧
      ((stepAdvanceLFast step mul2 evMin wHi fuel st).1 = 1 ∨
        evMin > 2 ^ ((stepAdvanceLFast step mul2 evMin wHi fuel st).1 - 1) * wHi)
  | 0, _, hinv => hinv
  | fuel + 1, (l, p2), ⟨hl1, hp2, hor⟩ => by
    dsimp only at hl1 hp2 hor
    simp only [stepAdvanceLFast]
    by_cases hc : evMin > (p2 * mul2) * wHi
    · simp only [hc, ↓reduceIte]
      have hexp : l + step - 1 = (l - 1) + step := by omega
      have hnp2 : p2 * mul2 = 2 ^ (l + step - 1) := by rw [hp2, hm2, hexp, Nat.pow_add]
      have hgt : evMin > 2 ^ (l + step - 1) * wHi := by rwa [← hnp2]
      exact stepAdvanceLFast_inv step mul2 hstep hm2 fuel (l + step, p2 * mul2) ⟨by omega, hnp2, Or.inr hgt⟩
    · simp only [hc, ↓reduceIte]
      exact ⟨hl1, hp2, hor⟩

def advanceLMinFast (evMin wHi : Nat) : Nat × Nat :=
  let r3 := stepAdvanceLFast 1 2 evMin wHi 4
    (stepAdvanceLFast 4 16 evMin wHi 4
      (stepAdvanceLFast 16 65536 evMin wHi 16 (1, 1)))
  (r3.1, 2 * r3.2)

theorem advanceLMinFast_sound {evMin wHi l nNext : Nat}
    (hl1 : l ≥ 1) (hnNext_hi : nNext ≤ wHi) (hev_lo : evMin ≤ 2 ^ l * nNext) :
    (advanceLMinFast evMin wHi).1 ≤ l ∧ (advanceLMinFast evMin wHi).2 = 2 ^ (advanceLMinFast evMin wHi).1 := by
  change (stepAdvanceLFast 1 2 evMin wHi 4
    (stepAdvanceLFast 4 16 evMin wHi 4
      (stepAdvanceLFast 16 65536 evMin wHi 16 (1, 1)))).1 ≤ l ∧
    2 * (stepAdvanceLFast 1 2 evMin wHi 4
      (stepAdvanceLFast 4 16 evMin wHi 4
        (stepAdvanceLFast 16 65536 evMin wHi 16 (1, 1)))).2 =
    2 ^ (stepAdvanceLFast 1 2 evMin wHi 4
      (stepAdvanceLFast 4 16 evMin wHi 4
        (stepAdvanceLFast 16 65536 evMin wHi 16 (1, 1)))).1
  have h1 := stepAdvanceLFast_inv 16 65536 (by decide) (by decide) (evMin := evMin) (wHi := wHi)
    16 (1, 1) ⟨by omega, rfl, Or.inl rfl⟩
  generalize stepAdvanceLFast 16 65536 evMin wHi 16 (1, 1) = r1 at h1 ⊢
  have h2 := stepAdvanceLFast_inv 4 16 (by decide) (by decide) (evMin := evMin) (wHi := wHi)
    4 r1 h1
  generalize stepAdvanceLFast 4 16 evMin wHi 4 r1 = r2 at h2 ⊢
  have h3 := stepAdvanceLFast_inv 1 2 (by decide) (by decide) (evMin := evMin) (wHi := wHi)
    4 r2 h2
  generalize stepAdvanceLFast 1 2 evMin wHi 4 r2 = r3 at h3 ⊢
  rcases r3 with ⟨lOut, p2Out⟩
  dsimp only at h3 ⊢
  rcases h3 with ⟨hl_pos, hp2, hor⟩
  have hp2_out : 2 * p2Out = 2 ^ lOut := by
    rw [hp2, Nat.mul_comm 2, ← Nat.pow_succ, show (lOut - 1).succ = lOut by omega]
  refine ⟨?_, hp2_out⟩
  rcases hor with h_one | hgt
  · omega
  · apply Classical.byContradiction
    intro hnot
    have hp : 2 ^ l ≤ 2 ^ (lOut - 1) := pow2_mono_nat (by omega)
    have hm : 2 ^ l * nNext ≤ 2 ^ (lOut - 1) * wHi := Nat.mul_le_mul hp hnNext_hi
    omega

def oddQuotMinP (p2k lo : Nat) : Nat :=
  let u0 := ceilDiv (lo + 1) p2k
  if u0 % 2 == 1 then u0 else u0 + 1

def oddQuotMaxP (p2k hi : Nat) : Nat :=
  let u1 := (hi + 1) / p2k
  if u1 % 2 == 1 then u1 else u1 - 1

def pullbackLo1P (p2kl p2k1 p3k1 lo1 lo2 : Nat) : Nat :=
  maxNat lo1 (ceilDiv (p2kl * lo2 + p2k1) p3k1 - 1)

def pullbackHi1P (p2kl p2k1 p3k1 hi1 hi2 : Nat) : Nat :=
  minNat hi1 ((p2kl * hi2 + p2k1) / p3k1 - 1)

-- Self-guided power-carrying R2 verifier (`z1 -> z2 -> z3 -> z4`):
def loopL2R2 (b1 b2 inv12 blo1 span1 baseG2 p2K12 ev2Min ev2Max : Nat)
    (okCand : Nat -> Bool) :
    Nat -> Nat -> Nat -> Nat -> Nat -> Nat -> Nat -> Nat -> Bool
  | 0, _, _, _, _, _, _, _ => false
  | fuel + 1, l2, P2, p2Exp, expBase, k3, p3k3m1, p2k3m1 =>
    if ev2Max < P2 * (b1 + 1) then true
    else if span1 < p2Exp then
      let g2c := baseG2 + p2K12 * (P2 - 1)
      checkCongPredM blo1 span1 p2Exp expBase inv12 g2c okCand
    else
      let lo3 := maxNat (b1 + 1) (ceilDiv ev2Min P2)
      let hi3 := minNat b2 (ev2Max / P2)
      if lo3 > hi3 then
        loopL2R2 b1 b2 inv12 blo1 span1 baseG2 p2K12 ev2Min ev2Max okCand
          fuel (l2 + 1) (2 * P2) (2 * p2Exp) (expBase + 1) k3 p3k3m1 p2k3m1
      else
        let rk3 := advanceKFrom hi3 (b2 + 1) k3 p3k3m1 p2k3m1
        let k3Min := rk3.1
        let p3Next := rk3.2.1
        let p2Next := rk3.2.2
        let p2k3 := 2 * p2Next
        if hi3 + 1 < p2k3 then true
        else
          let g2 := baseG2 + p2K12 * (P2 - 1)
          checkCongPredM blo1 span1 (p2Exp * p2k3) (expBase + k3Min) inv12 g2 okCand &&
          loopL2R2 b1 b2 inv12 blo1 span1 baseG2 p2K12 ev2Min ev2Max okCand
            fuel (l2 + 1) (2 * P2) (2 * p2Exp) (expBase + 1) k3Min p3Next p2Next

theorem loopL2R2_sound
    {b1 b2 k1 l1 k2 inv12 blo1 bhi1 g1 ev2Min ev2Max : Nat} {exemptIds : List Nat}
    {s0 s1 s2 : SpiralStepData} {x3 : Nat}
    (hb2_lt : b2 < 2 ^ 256) (hb12 : b1 ≤ b2)
    (hk0_eq : s0.k = k1) (hl0_eq : s0.l = l1) (hk1_eq : s1.k = k2)
    (hs0_lo : blo1 ≤ s0.x) (hs0_hi : s0.x ≤ bhi1) (hs0_b1 : s0.x ≤ b1)
    (hs1_lo : b1 + 1 ≤ s1.x) (hs1_hi : s1.x ≤ b2)
    (hs2_lo : b1 + 1 ≤ s2.x) (hs2_hi : s2.x ≤ b2)
    (hx3_lo : b2 + 1 ≤ x3)
    (hev2_lo : ev2Min ≤ 2 ^ s1.l * s2.x) (hev2_hi : 2 ^ s1.l * s2.x ≤ ev2Max)
    (hacc1 : 2 ^ (k1 + l1) * (s1.x + 1) = 3 ^ k1 * (s0.x + 1) + g1)
    (hinv12 : (3 ^ (k1 + k2) * inv12) % 2 ^ 384 = 1)
    (hst0 : ValidSpiralStep s0 s1.x)
    (hst1 : ValidSpiralStep s1 s2.x)
    (hst2 : ValidSpiralStep s2 x3) :
    ∀ (fuel l2Cur P2 p2Exp expBase k3 p3k3m1 p2k3m1 : Nat),
      l2Cur ≤ s1.l ->
      P2 = 2 ^ l2Cur ->
      expBase = k1 + l1 + k2 + l2Cur ->
      p2Exp = 2 ^ expBase ->
      (k3 ≥ 1 ∧ p3k3m1 = 3 ^ (k3 - 1) ∧ p2k3m1 = 2 ^ (k3 - 1) ∧
        (k3 = 1 ∨ 3 ^ (k3 - 1) * (s2.x + 1) < 2 ^ (k3 - 1) * (2 * (b2 + 1) + 1))) ->
      loopL2R2 b1 b2 inv12 blo1 (bhi1 - blo1) (3 ^ k2 * g1) (2 ^ (k1 + l1 + k2)) ev2Min ev2Max
        (checkCandR2 b1 b2 exemptIds) fuel l2Cur P2 p2Exp expBase k3 p3k3m1 p2k3m1 = true ->
      s0.x ∈ exemptIds
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, hok => by simp [loopL2R2] at hok
  | fuel + 1, l2Cur, P2, p2Exp, expBase, k3, p3k3m1, p2k3m1,
    hl2_ge, hP2, hexpB, hp2E, hk3_inv, hok => by
    unfold loopL2R2 at hok
    by_cases hexit : ev2Max < P2 * (b1 + 1)
    · exfalso
      rw [hP2] at hexit
      have hp : 2 ^ l2Cur ≤ 2 ^ s1.l := pow2_mono_nat hl2_ge
      have hm : 2 ^ l2Cur * (b1 + 1) ≤ 2 ^ s1.l * s2.x := Nat.mul_le_mul hp hs2_lo
      omega
    · simp only [hexit, ↓reduceIte] at hok
      rcases hst1 with ⟨hx1_o, hx1_p, hx2_o, hx2_p, hk1_1, hl1_1, hstep1⟩
      rcases hst2 with ⟨hx2_o2, hx2_p2, hx3_o, hx3_p, hk2_1, hl2_1, hstep2⟩
      by_cases hcol : bhi1 - blo1 < p2Exp
      · simp only [hcol, ↓reduceIte] at hok
        subst hk1_eq
        rw [hP2] at hok
        have hdvd := dvd_l_collapse hl2_ge hacc1 hstep1
        rw [← hexpB] at hdvd
        have hcand := checkCongPredM_sound hp2E hs0_lo hs0_hi hinv12 hdvd hok
        exact checkCandR2_sound hb2_lt hs0_b1 hb12 hs1_lo hs1_hi hs2_lo hs2_hi hx3_lo
          hst0 ⟨hx1_o, hx1_p, hx2_o, hx2_p, hk1_1, hl1_1, hstep1⟩
          ⟨hx2_o2, hx2_p2, hx3_o, hx3_p, hk2_1, hl2_1, hstep2⟩ hcand
      · simp only [hcol, ↓reduceIte] at hok
        let lo3 := maxNat (b1 + 1) (ceilDiv ev2Min P2)
        let hi3 := minNat b2 (ev2Max / P2)
        have hP2_pos : P2 > 0 := by rw [hP2]; exact pow2_pos_nat l2Cur
        have hs2_le_hi3 : s2.x ≤ hi3 := by
          have hp : P2 ≤ 2 ^ s1.l := by rw [hP2]; exact pow2_mono_nat hl2_ge
          have hm : P2 * s2.x ≤ ev2Max :=
            Nat.le_trans (Nat.mul_le_mul_right s2.x hp) hev2_hi
          have hf := le_div_of_mul_le hP2_pos hm
          dsimp [hi3, minNat]
          by_cases hc : b2 ≤ ev2Max / P2 <;> simp [hc] <;> omega
        have hP2_nx : 2 * P2 = 2 ^ (l2Cur + 1) := by rw [hP2, Nat.pow_succ, Nat.mul_comm]
        have hexp_nx : expBase + 1 = k1 + l1 + k2 + (l2Cur + 1) := by omega
        have hp2E_nx : 2 * p2Exp = 2 ^ (expBase + 1) := by rw [hp2E, Nat.pow_succ, Nat.mul_comm]
        by_cases hgt3 : lo3 > hi3
        · rw [ite_eq_left hgt3] at hok
          by_cases heq_l2 : s1.l = l2Cur
          · exfalso
            subst heq_l2
            have hev2_le : ev2Min ≤ P2 * s2.x := by rwa [← hP2] at hev2_lo
            have hc := ceilDiv_le_of_le_mul hP2_pos hev2_le
            have hlo3 : lo3 ≤ s2.x := by
              dsimp [lo3, maxNat]
              by_cases h : b1 + 1 ≤ ceilDiv ev2Min P2 <;> simp [h] <;> omega
            omega
          · exact loopL2R2_sound hb2_lt hb12 hk0_eq hl0_eq hk1_eq hs0_lo hs0_hi hs0_b1
              hs1_lo hs1_hi hs2_lo hs2_hi hx3_lo hev2_lo hev2_hi hacc1 hinv12 hst0
              ⟨hx1_o, hx1_p, hx2_o, hx2_p, hk1_1, hl1_1, hstep1⟩
              ⟨hx2_o2, hx2_p2, hx3_o, hx3_p, hk2_1, hl2_1, hstep2⟩ fuel (l2Cur + 1)
              (2 * P2) (2 * p2Exp) (expBase + 1) k3 p3k3m1 p2k3m1
              (by omega) hP2_nx hexp_nx hp2E_nx hk3_inv hok
        · rw [ite_eq_right hgt3] at hok
          have hk3_nx := advanceKFrom_inv hs2_le_hi3 hk3_inv
          generalize advanceKFrom hi3 (b2 + 1) k3 p3k3m1 p2k3m1 = rk3 at hk3_nx hok
          rcases advanceK_inv_implies_le hk2_1 hl2_1 hx3_lo hk3_nx.1 hk3_nx.2.2.1 hk3_nx.2.2.2 hstep2
            with ⟨hk3_ge, hp2k3_eq⟩
          by_cases hhi3_lt : hi3 + 1 < 2 * rk3.2.2
          · exfalso
            rw [hp2k3_eq] at hhi3_lt
            exact no_spiral_step_of_hi_lt_pow2 s2.k rk3.1 s2.l hi3 s2.x x3
              hk3_ge hl2_1 hs2_le_hi3 hhi3_lt hstep2
          · rw [ite_eq_right hhi3_lt] at hok
            simp only [Bool.and_eq_true] at hok
            rcases hok with ⟨hokLeaf, hmore⟩
            by_cases heq_l2 : s1.l = l2Cur
            · subst heq_l2; subst hk1_eq
              rw [hP2] at hokLeaf
              have hacc2 := step_hensel_extend hacc1 hstep1
              have hdvd := dvd_two_step_collapse hk3_ge hl2_1 hacc2 hstep2
              rw [← hexpB] at hdvd
              have hM_leaf : p2Exp * (2 * rk3.2.2) = 2 ^ (expBase + rk3.1) := by
                rw [hp2E, hp2k3_eq, ← Nat.pow_add]
              have hcand := checkCongPredM_sound hM_leaf hs0_lo hs0_hi hinv12 hdvd hokLeaf
              exact checkCandR2_sound hb2_lt hs0_b1 hb12 hs1_lo hs1_hi hs2_lo hs2_hi hx3_lo
                hst0 ⟨hx1_o, hx1_p, hx2_o, hx2_p, hk1_1, hl1_1, hstep1⟩
                ⟨hx2_o2, hx2_p2, hx3_o, hx3_p, hk2_1, hl2_1, hstep2⟩ hcand
            · exact loopL2R2_sound hb2_lt hb12 hk0_eq hl0_eq hk1_eq hs0_lo hs0_hi hs0_b1
                hs1_lo hs1_hi hs2_lo hs2_hi hx3_lo hev2_lo hev2_hi hacc1 hinv12 hst0
                ⟨hx1_o, hx1_p, hx2_o, hx2_p, hk1_1, hl1_1, hstep1⟩
                ⟨hx2_o2, hx2_p2, hx3_o, hx3_p, hk2_1, hl2_1, hstep2⟩ fuel (l2Cur + 1)
                (2 * P2) (2 * p2Exp) (expBase + 1) rk3.1 rk3.2.1 rk3.2.2
                (by omega) hP2_nx hexp_nx hp2E_nx hk3_nx hmore

-- Ultra-lean incremental congruence checker & constant-k3 inner L2 loop:
def checkRemMod (lo spanp1 M S : Nat) (okCand : Nat -> Bool) : Bool :=
  let rem := Nat.mod S M
  let off :=
    match Nat.beq rem 0 with
    | true => 0
    | false => Nat.sub M rem
  match Nat.ble spanp1 off with
  | true => true
  | false => okCand (Nat.add lo off)

theorem checkRemMod_sound
    {lo hi M exp w invAt g S n1 : Nat} {okCand : Nat -> Bool}
    (hM : M = 2 ^ exp)
    (hexp : exp ≤ 384)
    (hspan : hi - lo + 1 ≤ M)
    (hS : S = invAt * g + (lo + 1))
    (hlo : lo ≤ n1) (hhi : n1 ≤ hi)
    (hinv : (3 ^ w * invAt) % 2 ^ 384 = 1)
    (hdvd : 2 ^ exp ∣ 3 ^ w * (n1 + 1) + g)
    (hok : checkRemMod lo (hi - lo + 1) M S okCand = true) :
    okCand n1 = true := by
  subst hM; subst hS
  apply checkCongPred_sound hlo hhi hinv hdvd
  unfold checkCongPred
  rw [pow2Split_eq]
  unfold checkRemMod at hok
  have hM_pos : 2 ^ exp > 0 := pow2_pos_nat exp
  let rem := (invAt * g + (lo + 1)) % 2 ^ exp
  have hrem_lt : rem < 2 ^ exp := Nat.mod_lt _ hM_pos
  change (match Nat.ble (hi - lo + 1)
      (match Nat.beq rem 0 with | true => 0 | false => 2 ^ exp - rem) with
    | true => true
    | false => okCand (lo + (match Nat.beq rem 0 with | true => 0 | false => 2 ^ exp - rem))) = true at hok
  have hoff_eq : (match Nat.beq rem 0 with | true => 0 | false => 2 ^ exp - rem) =
      (2 ^ exp - rem) % 2 ^ exp := by
    cases hrz : Nat.beq rem 0 with
    | true =>
      dsimp only
      have hz : rem = 0 := of_decide_eq_true hrz
      rw [hz, Nat.sub_zero, Nat.mod_self]
    | false =>
      dsimp only
      have hnz : rem ≠ 0 := of_decide_eq_false hrz
      have hsub_lt : 2 ^ exp - rem < 2 ^ exp := by dsimp [rem] at hnz hrem_lt; omega
      exact (Nat.mod_eq_of_lt hsub_lt).symm
  rw [hoff_eq] at hok
  let off := (2 ^ exp - rem) % 2 ^ exp
  change (match Nat.ble (hi - lo + 1) off with | true => true | false => okCand (lo + off)) = true at hok
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
  refine ⟨⟨hexp, by omega⟩, ?_⟩
  cases hb3 : Nat.ble (hi - lo + 1) off with
  | true =>
    have hgt := Nat.le_of_ble_eq_true hb3
    exact Or.inl (by dsimp [off, rem] at hgt; omega)
  | false =>
    rw [hb3] at hok
    exact Or.inr hok

def loopL2ConstK3 (lo spanp1 p2Stop : Nat) (okCand : Nat -> Bool) :
    Nat -> Nat -> Nat -> Nat -> Nat -> Nat -> Nat -> Bool
  | 0, _, _, _, _, _, _ => false
  | fuel + 1, P2, p2Exp, M, expTot, S, dS =>
    match Nat.ble p2Stop P2 with
    | true => true
    | false =>
      match Nat.ble expTot 384 with
      | false => false
      | true =>
        match Nat.ble spanp1 p2Exp with
        | true => checkRemMod lo spanp1 p2Exp S okCand
        | false =>
          match checkRemMod lo spanp1 M S okCand with
          | false => false
          | true =>
            loopL2ConstK3 lo spanp1 p2Stop okCand fuel
              (Nat.mul 2 P2) (Nat.mul 2 p2Exp) (Nat.mul 2 M) (Nat.add expTot 1)
              (Nat.add S dS) (Nat.mul 2 dS)

theorem loopL2ConstK3_sound
    {b1 b2 k1 l1 k2 k3Fix inv12 lo hi g1 ev2Max : Nat} {exemptIds : List Nat}
    {s0 s1 s2 : SpiralStepData} {x3 : Nat}
    (hb2_lt : b2 < 2 ^ 256) (hb12 : b1 ≤ b2)
    (hk1_eq : s1.k = k2)
    (hs0_lo : lo ≤ s0.x) (hs0_hi : s0.x ≤ hi) (hs0_b1 : s0.x ≤ b1)
    (hs1_lo : b1 + 1 ≤ s1.x) (hs1_hi : s1.x ≤ b2)
    (hs2_lo : b1 + 1 ≤ s2.x) (hs2_hi : s2.x ≤ b2)
    (hx3_lo : b2 + 1 ≤ x3)
    (hev2_hi : 2 ^ s1.l * s2.x ≤ ev2Max)
    (hk3_ge : k3Fix ≤ s2.k)
    (hacc1 : 2 ^ (k1 + l1) * (s1.x + 1) = 3 ^ k1 * (s0.x + 1) + g1)
    (hinv12 : (3 ^ (k1 + k2) * inv12) % 2 ^ 384 = 1)
    (hst0 : ValidSpiralStep s0 s1.x)
    (hst1 : ValidSpiralStep s1 s2.x)
    (hst2 : ValidSpiralStep s2 x3) :
    ∀ (fuel l2Cur P2 p2Exp M expTot S dS : Nat),
      l2Cur ≤ s1.l ->
      P2 = 2 ^ l2Cur ->
      p2Exp = 2 ^ (k1 + l1 + k2 + l2Cur) ->
      expTot = k1 + l1 + k2 + l2Cur + k3Fix ->
      M = 2 ^ expTot ->
      hi - lo + 1 ≤ M ->
      S = inv12 * (3 ^ k2 * g1 + 2 ^ (k1 + l1 + k2) * (P2 - 1)) + (lo + 1) ->
      dS = inv12 * p2Exp ->
      loopL2ConstK3 lo (hi - lo + 1) (ev2Max / (b1 + 1) + 1) (checkCandR2 b1 b2 exemptIds)
        fuel P2 p2Exp M expTot S dS = true ->
      s0.x ∈ exemptIds
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hok => by cases hok
  | fuel + 1, l2Cur, P2, p2Exp, M, expTot, S, dS,
    hl2_ge, hP2, hp2E, hexpT, hM, hspanM, hS, hdS, hok => by
    unfold loopL2ConstK3 at hok
    cases hb_stop : Nat.ble (ev2Max / (b1 + 1) + 1) P2 with
    | true =>
      exfalso
      have hstop := Nat.le_of_ble_eq_true hb_stop
      have hp : P2 ≤ 2 ^ s1.l := by rw [hP2]; exact pow2_mono_nat hl2_ge
      have hm : (b1 + 1) * P2 ≤ ev2Max := by
        rw [Nat.mul_comm]
        exact Nat.le_trans (Nat.mul_le_mul hp hs2_lo) hev2_hi
      have hdiv : P2 ≤ ev2Max / (b1 + 1) := le_div_of_mul_le (show b1 + 1 ≥ 1 by omega) hm
      exact absurd (Nat.lt_of_lt_of_le (Nat.lt_succ_self (ev2Max / (b1 + 1))) hstop) (Nat.not_lt.mpr hdiv)
    | false =>
      rw [hb_stop] at hok
      dsimp only at hok
      cases hb_exp : Nat.ble expTot 384 with
      | false => rw [hb_exp] at hok; cases hok
      | true =>
        rw [hb_exp] at hok
        dsimp only at hok
        have hexpT_le : expTot ≤ 384 := Nat.le_of_ble_eq_true hb_exp
        rcases hst1 with ⟨hx1_o, hx1_p, hx2_o, hx2_p, hk1_1, hl1_1, hstep1⟩
        rcases hst2 with ⟨hx2_o2, hx2_p2, hx3_o, hx3_p, hk2_1, hl2_1, hstep2⟩
        cases hb_col : Nat.ble (hi - lo + 1) p2Exp with
        | true =>
          rw [hb_col] at hok
          dsimp only at hok
          have hspan_p2 : hi - lo + 1 ≤ p2Exp := Nat.le_of_ble_eq_true hb_col
          subst hk1_eq
          have hdvd := dvd_l_collapse hl2_ge hacc1 hstep1
          have hS_l : S = inv12 * (3 ^ s1.k * g1 + 2 ^ (k1 + l1 + s1.k) * (2 ^ l2Cur - 1)) + (lo + 1) := by
            rw [← hP2]; exact hS
          have hcand := checkRemMod_sound hp2E (by omega) hspan_p2 hS_l hs0_lo hs0_hi hinv12 hdvd hok
          exact checkCandR2_sound hb2_lt hs0_b1 hb12 hs1_lo hs1_hi hs2_lo hs2_hi hx3_lo
            hst0 ⟨hx1_o, hx1_p, hx2_o, hx2_p, hk1_1, hl1_1, hstep1⟩
            ⟨hx2_o2, hx2_p2, hx3_o, hx3_p, hk2_1, hl2_1, hstep2⟩ hcand
        | false =>
          rw [hb_col] at hok
          dsimp only at hok
          cases hb_rem : checkRemMod lo (hi - lo + 1) M S (checkCandR2 b1 b2 exemptIds) with
          | false => rw [hb_rem] at hok; cases hok
          | true =>
            rw [hb_rem] at hok
            dsimp only at hok
            by_cases heq_l2 : s1.l = l2Cur
            · subst heq_l2; subst hk1_eq
              have hacc2 := step_hensel_extend hacc1 hstep1
              have hdvd := dvd_two_step_collapse hk3_ge hl2_1 hacc2 hstep2
              rw [← hexpT] at hdvd
              have hS_l : S = inv12 * (3 ^ s1.k * g1 + 2 ^ (k1 + l1 + s1.k) * (2 ^ s1.l - 1)) + (lo + 1) := by
                rw [← hP2]; exact hS
              have hcand := checkRemMod_sound hM hexpT_le hspanM hS_l hs0_lo hs0_hi hinv12 hdvd hb_rem
              exact checkCandR2_sound hb2_lt hs0_b1 hb12 hs1_lo hs1_hi hs2_lo hs2_hi hx3_lo
                hst0 ⟨hx1_o, hx1_p, hx2_o, hx2_p, hk1_1, hl1_1, hstep1⟩
                ⟨hx2_o2, hx2_p2, hx3_o, hx3_p, hk2_1, hl2_1, hstep2⟩ hcand
            · have hP2_pos : P2 ≥ 1 := by rw [hP2]; exact pow2_pos_nat l2Cur
              have h2P2_sub : 2 * P2 - 1 = (P2 - 1) + P2 := by omega
              have hp2E_mul : p2Exp = 2 ^ (k1 + l1 + k2) * P2 := by rw [hp2E, hP2, Nat.pow_add]
              have hP2_nx : Nat.mul 2 P2 = 2 ^ (l2Cur + 1) := by
                change 2 * P2 = 2 ^ (l2Cur + 1); rw [hP2, Nat.pow_succ, Nat.mul_comm]
              have hp2E_nx : Nat.mul 2 p2Exp = 2 ^ (k1 + l1 + k2 + (l2Cur + 1)) := by
                change 2 * p2Exp = _
                rw [hp2E, show k1 + l1 + k2 + (l2Cur + 1) = (k1 + l1 + k2 + l2Cur) + 1 by omega,
                    Nat.pow_succ, Nat.mul_comm]
              have hexpT_nx : Nat.add expTot 1 = k1 + l1 + k2 + (l2Cur + 1) + k3Fix := by
                change expTot + 1 = _; omega
              have hM_nx : Nat.mul 2 M = 2 ^ Nat.add expTot 1 := by
                change 2 * M = 2 ^ (expTot + 1); rw [hM, Nat.pow_succ, Nat.mul_comm]
              have hspanM_nx : hi - lo + 1 ≤ Nat.mul 2 M := by
                change hi - lo + 1 ≤ 2 * M; omega
              have hS_nx : Nat.add S dS =
                  inv12 * (3 ^ k2 * g1 + 2 ^ (k1 + l1 + k2) * (Nat.mul 2 P2 - 1)) + (lo + 1) := by
                change S + dS = inv12 * (3 ^ k2 * g1 + 2 ^ (k1 + l1 + k2) * (2 * P2 - 1)) + (lo + 1)
                calc
                  S + dS = (inv12 * (3 ^ k2 * g1 + 2 ^ (k1 + l1 + k2) * (P2 - 1)) + (lo + 1)) +
                      inv12 * (2 ^ (k1 + l1 + k2) * P2) := by rw [hS, hdS, hp2E_mul]
                  _ = (inv12 * (3 ^ k2 * g1 + 2 ^ (k1 + l1 + k2) * (P2 - 1)) +
                      inv12 * (2 ^ (k1 + l1 + k2) * P2)) + (lo + 1) := by
                        rw [Nat.add_assoc, Nat.add_comm (lo + 1), ← Nat.add_assoc]
                  _ = inv12 * ((3 ^ k2 * g1 + 2 ^ (k1 + l1 + k2) * (P2 - 1)) +
                      2 ^ (k1 + l1 + k2) * P2) + (lo + 1) := by rw [← Nat.mul_add]
                  _ = inv12 * (3 ^ k2 * g1 + 2 ^ (k1 + l1 + k2) * ((P2 - 1) + P2)) + (lo + 1) := by
                        rw [Nat.add_assoc (3 ^ k2 * g1), ← Nat.mul_add]
                  _ = inv12 * (3 ^ k2 * g1 + 2 ^ (k1 + l1 + k2) * (2 * P2 - 1)) + (lo + 1) := by
                        rw [← h2P2_sub]
              have hdS_nx : Nat.mul 2 dS = inv12 * Nat.mul 2 p2Exp := by
                change 2 * dS = inv12 * (2 * p2Exp)
                rw [hdS, ← Nat.mul_assoc, Nat.mul_comm 2 inv12, Nat.mul_assoc]
              exact loopL2ConstK3_sound hb2_lt hb12 hk1_eq hs0_lo hs0_hi hs0_b1 hs1_lo hs1_hi
                hs2_lo hs2_hi hx3_lo hev2_hi hk3_ge hacc1 hinv12 hst0
                ⟨hx1_o, hx1_p, hx2_o, hx2_p, hk1_1, hl1_1, hstep1⟩
                ⟨hx2_o2, hx2_p2, hx3_o, hx3_p, hk2_1, hl2_1, hstep2⟩
                fuel (l2Cur + 1) (Nat.mul 2 P2) (Nat.mul 2 p2Exp) (Nat.mul 2 M) (Nat.add expTot 1)
                (Nat.add S dS) (Nat.mul 2 dS)
                (by omega) hP2_nx hp2E_nx hexpT_nx hM_nx hspanM_nx hS_nx hdS_nx hok

def stepK2AfterRK3
    (fuelL b1 b2 k1 l1 k2 p3k2 p2K12 inv12 nlo1 nhi1 g1 ev2Min ev2Max l2Min P2_0 hi3_0 k3_i p3_i p2_i : Nat)
    (okCand : Nat -> Bool) : Bool :=
  let spanp1 := nhi1 - nlo1 + 1
  let p2Stop := ev2Max / (b1 + 1) + 1
  let p2Exp0 := p2K12 * P2_0
  let expBase0 := k1 + l1 + k2 + l2Min
  let g2_0 := p3k2 * g1 + p2K12 * (P2_0 - 1)
  let S_0 := inv12 * g2_0 + (nlo1 + 1)
  let p2k3_0 := 2 * p2_i
  match Nat.ble (hi3_0 + 2) p2k3_0 with
  | true => true
  | false =>
    let M_0 := p2Exp0 * p2k3_0
    match Nat.ble spanp1 M_0 with
    | true =>
      let dS_0 := inv12 * p2Exp0
      loopL2ConstK3 nlo1 spanp1 p2Stop okCand fuelL
        P2_0 p2Exp0 M_0 (expBase0 + k3_i) S_0 dS_0
    | false =>
      loopL2R2 b1 b2 inv12 nlo1 (nhi1 - nlo1) (p3k2 * g1)
        p2K12 ev2Min ev2Max okCand fuelL l2Min P2_0 p2Exp0 expBase0 k3_i p3_i p2_i

theorem stepK2AfterRK3_sound
    {fuelL b1 b2 k1 l1 nlo1 nhi1 g1 inv12 ev2Min ev2Max l2Min P2_0 hi3_0 k3_i p3_i p2_i : Nat}
    {exemptIds : List Nat} {s0 s1 s2 : SpiralStepData} {x3 : Nat}
    (hb2_lt : b2 < 2 ^ 256) (hb12 : b1 ≤ b2)
    (hk0_eq : s0.k = k1) (hl0_eq : s0.l = l1)
    (hs0_lo : nlo1 ≤ s0.x) (hs0_hi : s0.x ≤ nhi1) (hs0_b1 : s0.x ≤ b1)
    (hs1_lo : b1 + 1 ≤ s1.x) (hs1_hi : s1.x ≤ b2)
    (hs2_lo : b1 + 1 ≤ s2.x) (hs2_hi : s2.x ≤ b2)
    (hx3_lo : b2 + 1 ≤ x3)
    (hev2_lo : ev2Min ≤ 2 ^ s1.l * s2.x) (hev2_hi : 2 ^ s1.l * s2.x ≤ ev2Max)
    (hl2_ge : l2Min ≤ s1.l) (hP2_0 : P2_0 = 2 ^ l2Min)
    (hs2_le_hi3 : s2.x ≤ hi3_0)
    (hk3_inv : k3_i ≥ 1 ∧ p3_i = 3 ^ (k3_i - 1) ∧ p2_i = 2 ^ (k3_i - 1) ∧
      (k3_i = 1 ∨ 3 ^ (k3_i - 1) * (s2.x + 1) < 2 ^ (k3_i - 1) * (2 * (b2 + 1) + 1)))
    (hacc1 : 2 ^ (k1 + l1) * (s1.x + 1) = 3 ^ k1 * (s0.x + 1) + g1)
    (hinv12 : (3 ^ (k1 + s1.k) * inv12) % 2 ^ 384 = 1)
    (hst0 : ValidSpiralStep s0 s1.x)
    (hst1 : ValidSpiralStep s1 s2.x)
    (hst2 : ValidSpiralStep s2 x3)
    (hok : stepK2AfterRK3 fuelL b1 b2 k1 l1 s1.k (3 ^ s1.k) (2 ^ (k1 + l1 + s1.k)) inv12
      nlo1 nhi1 g1 ev2Min ev2Max l2Min P2_0 hi3_0 k3_i p3_i p2_i (checkCandR2 b1 b2 exemptIds) = true) :
    s0.x ∈ exemptIds := by
  dsimp only [stepK2AfterRK3] at hok
  rcases hst2 with ⟨hx2_o2, hx2_p2, hx3_o, hx3_p, hk2_1, hl2_1, hstep2⟩
  rcases advanceK_inv_implies_le hk2_1 hl2_1 hx3_lo hk3_inv.1 hk3_inv.2.2.1 hk3_inv.2.2.2 hstep2
    with ⟨hk3_ge, hp2k3_eq⟩
  have hp2E_0 : 2 ^ (k1 + l1 + s1.k) * P2_0 = 2 ^ (k1 + l1 + s1.k + l2Min) := by
    rw [hP2_0, ← Nat.pow_add]
  cases hb_hi3 : Nat.ble (hi3_0 + 2) (2 * p2_i) with
  | true =>
    exfalso
    have hhi3_lt := Nat.le_of_ble_eq_true hb_hi3
    rw [hp2k3_eq] at hhi3_lt
    exact no_spiral_step_of_hi_lt_pow2 s2.k k3_i s2.l hi3_0 s2.x x3
      hk3_ge hl2_1 hs2_le_hi3 (by omega) hstep2
  | false =>
    rw [hb_hi3] at hok
    dsimp only at hok
    cases hb_fast : Nat.ble (nhi1 - nlo1 + 1) ((2 ^ (k1 + l1 + s1.k) * P2_0) * (2 * p2_i)) with
    | true =>
      rw [hb_fast] at hok
      dsimp only at hok
      have hspan_M0 : nhi1 - nlo1 + 1 ≤ (2 ^ (k1 + l1 + s1.k) * P2_0) * (2 * p2_i) :=
        Nat.le_of_ble_eq_true hb_fast
      have hM0_eq : (2 ^ (k1 + l1 + s1.k) * P2_0) * (2 * p2_i) =
          2 ^ (k1 + l1 + s1.k + l2Min + k3_i) := by
        rw [hp2E_0, hp2k3_eq, ← Nat.pow_add]
      exact loopL2ConstK3_sound hb2_lt hb12 rfl hs0_lo hs0_hi hs0_b1 hs1_lo hs1_hi
        hs2_lo hs2_hi hx3_lo hev2_hi hk3_ge hacc1 hinv12 hst0 hst1
        ⟨hx2_o2, hx2_p2, hx3_o, hx3_p, hk2_1, hl2_1, hstep2⟩
        fuelL l2Min P2_0 (2 ^ (k1 + l1 + s1.k) * P2_0)
        ((2 ^ (k1 + l1 + s1.k) * P2_0) * (2 * p2_i))
        (k1 + l1 + s1.k + l2Min + k3_i)
        (inv12 * (3 ^ s1.k * g1 + 2 ^ (k1 + l1 + s1.k) * (P2_0 - 1)) + (nlo1 + 1))
        (inv12 * (2 ^ (k1 + l1 + s1.k) * P2_0))
        hl2_ge hP2_0 hp2E_0 rfl hM0_eq hspan_M0 rfl rfl hok
    | false =>
      rw [hb_fast] at hok
      dsimp only at hok
      exact loopL2R2_sound hb2_lt hb12 hk0_eq hl0_eq rfl hs0_lo hs0_hi hs0_b1
        hs1_lo hs1_hi hs2_lo hs2_hi hx3_lo hev2_lo hev2_hi hacc1 hinv12 hst0 hst1
        ⟨hx2_o2, hx2_p2, hx3_o, hx3_p, hk2_1, hl2_1, hstep2⟩
        fuelL l2Min P2_0 (2 ^ (k1 + l1 + s1.k) * P2_0)
        (k1 + l1 + s1.k + l2Min)
        k3_i p3_i p2_i hl2_ge hP2_0 rfl hp2E_0 hk3_inv hok

def stepK2AfterRL2
    (fuelL b1 b2 k1 l1 k2 p3k2 p2K12 inv12 nlo1 nhi1 g1 k3_0 p3_0 p2_0 ev2Min ev2Max l2Min P2_0 : Nat)
    (okCand : Nat -> Bool) : Bool :=
  let spanp1 := nhi1 - nlo1 + 1
  let p2Stop := ev2Max / (b1 + 1) + 1
  match Nat.ble p2Stop P2_0 with
  | true => true
  | false =>
    let p2Exp0 := p2K12 * P2_0
    let expBase0 := k1 + l1 + k2 + l2Min
    let g2_0 := p3k2 * g1 + p2K12 * (P2_0 - 1)
    let S_0 := inv12 * g2_0 + (nlo1 + 1)
    match Nat.ble spanp1 p2Exp0 with
    | true =>
      match Nat.ble expBase0 384 with
      | false => false
      | true => checkRemMod nlo1 spanp1 p2Exp0 S_0 okCand
    | false =>
      let hi3_0 := minNat b2 (ev2Max / P2_0)
      let rk3_i := advanceKFrom hi3_0 (b2 + 1) k3_0 p3_0 p2_0
      stepK2AfterRK3 fuelL b1 b2 k1 l1 k2 p3k2 p2K12 inv12 nlo1 nhi1 g1
        ev2Min ev2Max l2Min P2_0 hi3_0 rk3_i.1 rk3_i.2.1 rk3_i.2.2 okCand

theorem stepK2AfterRL2_sound
    {fuelL b1 b2 k1 l1 nlo1 nhi1 g1 k3_0 p3_0 p2_0 inv12 ev2Min ev2Max l2Min P2_0 : Nat}
    {exemptIds : List Nat} {s0 s1 s2 : SpiralStepData} {x3 : Nat}
    (hb2_lt : b2 < 2 ^ 256) (hb12 : b1 ≤ b2)
    (hk0_eq : s0.k = k1) (hl0_eq : s0.l = l1)
    (hs0_lo : nlo1 ≤ s0.x) (hs0_hi : s0.x ≤ nhi1) (hs0_b1 : s0.x ≤ b1)
    (hs1_lo : b1 + 1 ≤ s1.x) (hs1_hi : s1.x ≤ b2)
    (hs2_lo : b1 + 1 ≤ s2.x) (hs2_hi : s2.x ≤ b2)
    (hx3_lo : b2 + 1 ≤ x3)
    (hev2_lo : ev2Min ≤ 2 ^ s1.l * s2.x) (hev2_hi : 2 ^ s1.l * s2.x ≤ ev2Max)
    (hl2_ge : l2Min ≤ s1.l) (hP2_0 : P2_0 = 2 ^ l2Min)
    (hacc1 : 2 ^ (k1 + l1) * (s1.x + 1) = 3 ^ k1 * (s0.x + 1) + g1)
    (hinv12 : (3 ^ (k1 + s1.k) * inv12) % 2 ^ 384 = 1)
    (hk3_0_inv : k3_0 ≥ 1 ∧ p3_0 = 3 ^ (k3_0 - 1) ∧ p2_0 = 2 ^ (k3_0 - 1) ∧
      (k3_0 = 1 ∨ 3 ^ (k3_0 - 1) * (s2.x + 1) < 2 ^ (k3_0 - 1) * (2 * (b2 + 1) + 1)))
    (hst0 : ValidSpiralStep s0 s1.x)
    (hst1 : ValidSpiralStep s1 s2.x)
    (hst2 : ValidSpiralStep s2 x3)
    (hok : stepK2AfterRL2 fuelL b1 b2 k1 l1 s1.k (3 ^ s1.k) (2 ^ (k1 + l1 + s1.k)) inv12
      nlo1 nhi1 g1 k3_0 p3_0 p2_0 ev2Min ev2Max l2Min P2_0 (checkCandR2 b1 b2 exemptIds) = true) :
    s0.x ∈ exemptIds := by
  dsimp only [stepK2AfterRL2] at hok
  rcases hst1 with ⟨hx1_o, hx1_p, hx2_o, hx2_p, hk1_1, hl1_1, hstep1⟩
  cases hb_stop0 : Nat.ble (ev2Max / (b1 + 1) + 1) P2_0 with
  | true =>
    exfalso
    have hstop0 := Nat.le_of_ble_eq_true hb_stop0
    have hp0 : P2_0 ≤ 2 ^ s1.l := by rw [hP2_0]; exact pow2_mono_nat hl2_ge
    have hm0 : (b1 + 1) * P2_0 ≤ ev2Max := by
      rw [Nat.mul_comm]
      exact Nat.le_trans (Nat.mul_le_mul hp0 hs2_lo) hev2_hi
    have hdiv0 : P2_0 ≤ ev2Max / (b1 + 1) := le_div_of_mul_le (show b1 + 1 ≥ 1 by omega) hm0
    exact absurd (Nat.lt_of_lt_of_le (Nat.lt_succ_self (ev2Max / (b1 + 1))) hstop0) (Nat.not_lt.mpr hdiv0)
  | false =>
    rw [hb_stop0] at hok
    dsimp only at hok
    have hp2E_0 : 2 ^ (k1 + l1 + s1.k) * P2_0 = 2 ^ (k1 + l1 + s1.k + l2Min) := by
      rw [hP2_0, ← Nat.pow_add]
    cases hb_col0 : Nat.ble (nhi1 - nlo1 + 1) (2 ^ (k1 + l1 + s1.k) * P2_0) with
    | true =>
      rw [hb_col0] at hok
      dsimp only at hok
      cases hb_eb0 : Nat.ble (k1 + l1 + s1.k + l2Min) 384 with
      | false => rw [hb_eb0] at hok; cases hok
      | true =>
        rw [hb_eb0] at hok
        dsimp only at hok
        have hexp0_le : k1 + l1 + s1.k + l2Min ≤ 384 := Nat.le_of_ble_eq_true hb_eb0
        have hspan0_le : nhi1 - nlo1 + 1 ≤ 2 ^ (k1 + l1 + s1.k) * P2_0 := Nat.le_of_ble_eq_true hb_col0
        have hdvd0 := dvd_l_collapse hl2_ge hacc1 hstep1
        have hS0_eq : inv12 * (3 ^ s1.k * g1 + 2 ^ (k1 + l1 + s1.k) * (P2_0 - 1)) + (nlo1 + 1) =
            inv12 * (3 ^ s1.k * g1 + 2 ^ (k1 + l1 + s1.k) * (2 ^ l2Min - 1)) + (nlo1 + 1) := by
          rw [← hP2_0]
        have hcand0 := checkRemMod_sound hp2E_0 hexp0_le hspan0_le hS0_eq hs0_lo hs0_hi hinv12 hdvd0 hok
        exact checkCandR2_sound hb2_lt hs0_b1 hb12 hs1_lo hs1_hi hs2_lo hs2_hi hx3_lo
          hst0 ⟨hx1_o, hx1_p, hx2_o, hx2_p, hk1_1, hl1_1, hstep1⟩ hst2 hcand0
    | false =>
      rw [hb_col0] at hok
      dsimp only at hok
      have hs2_le_hi3_0 : s2.x ≤ minNat b2 (ev2Max / P2_0) := by
        have hP2_pos : P2_0 > 0 := by rw [hP2_0]; exact pow2_pos_nat l2Min
        have hp : P2_0 ≤ 2 ^ s1.l := by rw [hP2_0]; exact pow2_mono_nat hl2_ge
        have hm : P2_0 * s2.x ≤ ev2Max :=
          Nat.le_trans (Nat.mul_le_mul_right s2.x hp) hev2_hi
        have hf := le_div_of_mul_le hP2_pos hm
        unfold minNat
        by_cases hc : b2 ≤ ev2Max / P2_0 <;> simp [hc] <;> omega
      have hrk3_i := advanceKFrom_inv hs2_le_hi3_0 hk3_0_inv
      exact stepK2AfterRK3_sound hb2_lt hb12 hk0_eq hl0_eq hs0_lo hs0_hi hs0_b1
        hs1_lo hs1_hi hs2_lo hs2_hi hx3_lo hev2_lo hev2_hi hl2_ge hP2_0 hs2_le_hi3_0
        hrk3_i hacc1 hinv12 hst0 ⟨hx1_o, hx1_p, hx2_o, hx2_p, hk1_1, hl1_1, hstep1⟩ hst2 hok

def stepK2Here (fuelL b1 b2 k1 l1 k2 p2k2 p3k2 p2K12 inv12 nlo1 nhi1 lo2 hi2 g1 k3_0 p3_0 p2_0 : Nat)
    (okCand : Nat -> Bool) : Bool :=
  let u2Min := oddQuotMinP p2k2 lo2
  let u2Max := oddQuotMaxP p2k2 hi2
  if u2Max < u2Min then true
  else
    let ev2Min := p3k2 * u2Min - 1
    let ev2Max := p3k2 * u2Max - 1
    let rl2 := advanceLMinFast ev2Min b2
    stepK2AfterRL2 fuelL b1 b2 k1 l1 k2 p3k2 p2K12 inv12 nlo1 nhi1 g1 k3_0 p3_0 p2_0
      ev2Min ev2Max rl2.1 rl2.2 okCand

theorem stepK2Here_sound
    {fuelL b1 b2 k1 l1 nlo1 nhi1 lo2 hi2 g1 k3_0 p3_0 p2_0 inv12 : Nat} {exemptIds : List Nat}
    {s0 s1 s2 : SpiralStepData} {x3 : Nat}
    (hb2_lt : b2 < 2 ^ 256) (hb12 : b1 ≤ b2)
    (hk0_eq : s0.k = k1) (hl0_eq : s0.l = l1)
    (hs0_lo : nlo1 ≤ s0.x) (hs0_hi : s0.x ≤ nhi1) (hs0_b1 : s0.x ≤ b1)
    (hs1_lo2 : lo2 ≤ s1.x) (hs1_hi2 : s1.x ≤ hi2)
    (hs1_lo : b1 + 1 ≤ s1.x) (hs1_hi : s1.x ≤ b2)
    (hs2_lo : b1 + 1 ≤ s2.x) (hs2_hi : s2.x ≤ b2)
    (hx3_lo : b2 + 1 ≤ x3)
    (hpow_hi2 : 2 ^ s1.k ≤ hi2 + 1)
    (hacc1 : 2 ^ (k1 + l1) * (s1.x + 1) = 3 ^ k1 * (s0.x + 1) + g1)
    (hinv12 : (3 ^ (k1 + s1.k) * inv12) % 2 ^ 384 = 1)
    (hk3_0_inv : k3_0 ≥ 1 ∧ p3_0 = 3 ^ (k3_0 - 1) ∧ p2_0 = 2 ^ (k3_0 - 1) ∧
      (k3_0 = 1 ∨ 3 ^ (k3_0 - 1) * (s2.x + 1) < 2 ^ (k3_0 - 1) * (2 * (b2 + 1) + 1)))
    (hst0 : ValidSpiralStep s0 s1.x)
    (hst1 : ValidSpiralStep s1 s2.x)
    (hst2 : ValidSpiralStep s2 x3)
    (hok_split : stepK2Here fuelL b1 b2 k1 l1 s1.k (2 ^ s1.k) (3 ^ s1.k) (2 ^ (k1 + l1 + s1.k))
      inv12 nlo1 nhi1 lo2 hi2 g1 k3_0 p3_0 p2_0 (checkCandR2 b1 b2 exemptIds) = true) :
    s0.x ∈ exemptIds := by
  rcases hst1 with ⟨hx1_o, hx1_p, hx2_o, hx2_p, hk1_1, hl1_1, hstep1⟩
  rcases oddQuotBounds_sound hl1_1 hs1_lo2 hs1_hi2 hpow_hi2 hstep1 with
    ⟨hu2_le, _hlo2_u, _hhi2_u, hev2_lo, hev2_hi⟩
  have hq2_eq : oddQuotMin s1.k lo2 = oddQuotMinP (2 ^ s1.k) lo2 := rfl
  have hq2M_eq : oddQuotMax s1.k hi2 = oddQuotMaxP (2 ^ s1.k) hi2 := rfl
  rw [hq2_eq] at hu2_le hev2_lo
  rw [hq2M_eq] at hu2_le hev2_hi
  unfold stepK2Here at hok_split
  have hnot_u : ¬ (oddQuotMaxP (2 ^ s1.k) hi2 < oddQuotMinP (2 ^ s1.k) lo2) := by omega
  rw [ite_eq_right hnot_u] at hok_split
  have hrl2 := advanceLMinFast_sound hl1_1 hs2_hi hev2_lo
  exact stepK2AfterRL2_sound hb2_lt hb12 hk0_eq hl0_eq hs0_lo hs0_hi hs0_b1
    hs1_lo hs1_hi hs2_lo hs2_hi hx3_lo hev2_lo hev2_hi hrl2.1 hrl2.2 hacc1 hinv12 hk3_0_inv
    hst0 ⟨hx1_o, hx1_p, hx2_o, hx2_p, hk1_1, hl1_1, hstep1⟩ hst2 hok_split

def loopK2R2 (b1 b2 k1 l1 inv1 nlo1 nhi1 lo2 hi2 g1 k3_0 p3_0 p2_0 : Nat)
    (okCand : Nat -> Bool) :
    Nat -> Nat -> Nat -> Nat -> Nat -> Nat -> Bool
  | 0, _, _, _, _, _ => false
  | fuel + 1, k2, p2k2, p3k2, p2K12, inv12 =>
    let spanp1 := Nat.add (Nat.sub nhi1 nlo1) 1
    match Nat.ble (Nat.add hi2 2) p2k2 with
    | true => true
    | false =>
      match Nat.ble (Nat.add k1 k2) 384 with
      | false => false
      | true =>
        match Nat.ble spanp1 p2K12 with
        | true =>
          match Nat.ble (Nat.add (Nat.add k1 l1) k2) 384 with
          | false => false
          | true =>
            let S_c := Nat.add (Nat.mul inv1 g1) (Nat.add nlo1 1)
            checkRemMod nlo1 spanp1 p2K12 S_c okCand
        | false =>
          stepK2Here 256 b1 b2 k1 l1 k2 p2k2 p3k2 p2K12 inv12 nlo1 nhi1 lo2 hi2 g1 k3_0 p3_0 p2_0 okCand &&
          loopK2R2 b1 b2 k1 l1 inv1 nlo1 nhi1 lo2 hi2 g1 k3_0 p3_0 p2_0 okCand
            fuel (Nat.add k2 1) (Nat.mul 2 p2k2) (Nat.mul 3 p3k2) (Nat.mul 2 p2K12)
            (Nat.mod (Nat.mul inv12 inv3One384) (Nat.mul (2 ^ 192) (2 ^ 192)))

theorem loopK2R2_sound
    {b1 b2 k1 l1 inv1 nlo1 nhi1 lo2 hi2 g1 k3_0 p3_0 p2_0 : Nat} {exemptIds : List Nat}
    {s0 s1 s2 : SpiralStepData} {x3 : Nat}
    (hb2_lt : b2 < 2 ^ 256) (hb12 : b1 ≤ b2)
    (hk0_eq : s0.k = k1) (hl0_eq : s0.l = l1)
    (hs0_lo : nlo1 ≤ s0.x) (hs0_hi : s0.x ≤ nhi1) (hs0_b1 : s0.x ≤ b1)
    (hs1_lo2 : lo2 ≤ s1.x) (hs1_hi2 : s1.x ≤ hi2)
    (hs1_lo : b1 + 1 ≤ s1.x) (hs1_hi : s1.x ≤ b2)
    (hs2_lo : b1 + 1 ≤ s2.x) (hs2_hi : s2.x ≤ b2)
    (hx3_lo : b2 + 1 ≤ x3)
    (hacc1 : 2 ^ (k1 + l1) * (s1.x + 1) = 3 ^ k1 * (s0.x + 1) + g1)
    (hinv1 : (3 ^ k1 * inv1) % 2 ^ 384 = 1)
    (hk3_0_inv : k3_0 ≥ 1 ∧ p3_0 = 3 ^ (k3_0 - 1) ∧ p2_0 = 2 ^ (k3_0 - 1) ∧
      (k3_0 = 1 ∨ 3 ^ (k3_0 - 1) * (s2.x + 1) < 2 ^ (k3_0 - 1) * (2 * (b2 + 1) + 1)))
    (hst0 : ValidSpiralStep s0 s1.x)
    (hst1 : ValidSpiralStep s1 s2.x)
    (hst2 : ValidSpiralStep s2 x3) :
    ∀ (fuel k2Cur p2k2 p3k2 p2K12 inv12 : Nat),
      k2Cur ≤ s1.k ->
      p2k2 = 2 ^ k2Cur ->
      p3k2 = 3 ^ k2Cur ->
      p2K12 = 2 ^ (k1 + l1 + k2Cur) ->
      (3 ^ (k1 + k2Cur) * inv12) % 2 ^ 384 = 1 ->
      loopK2R2 b1 b2 k1 l1 inv1 nlo1 nhi1 lo2 hi2 g1 k3_0 p3_0 p2_0
        (checkCandR2 b1 b2 exemptIds) fuel k2Cur p2k2 p3k2 p2K12 inv12 = true ->
      s0.x ∈ exemptIds
  | 0, _, _, _, _, _, _, _, _, _, _, hok => by cases hok
  | fuel + 1, k2Cur, p2k2, p3k2, p2K12, inv12,
    hk2_ge, hp2k2, hp3k2, hp2K12, hinv12, hok => by
    unfold loopK2R2 at hok
    dsimp only at hok
    rcases hst1 with ⟨hx1_o, hx1_p, hx2_o, hx2_p, hk1_1, hl1_1, hstep1⟩
    cases hb_pow : Nat.ble (Nat.add hi2 2) p2k2 with
    | true =>
      exfalso
      have hpow := Nat.le_of_ble_eq_true hb_pow
      change hi2 + 2 ≤ p2k2 at hpow
      rw [hp2k2] at hpow
      exact no_spiral_step_of_hi_lt_pow2 s1.k k2Cur s1.l hi2 s1.x s2.x
        hk2_ge hl1_1 hs1_hi2 (by omega) hstep1
    | false =>
      rw [hb_pow] at hok
      dsimp only at hok
      cases hb_w384 : Nat.ble (Nat.add k1 k2Cur) 384 with
      | false => rw [hb_w384] at hok; cases hok
      | true =>
        rw [hb_w384] at hok
        dsimp only at hok
        cases hb_col : Nat.ble (Nat.add (Nat.sub nhi1 nlo1) 1) p2K12 with
        | true =>
          rw [hb_col] at hok
          dsimp only at hok
          cases hb_e384 : Nat.ble (Nat.add (Nat.add k1 l1) k2Cur) 384 with
          | false => rw [hb_e384] at hok; cases hok
          | true =>
            rw [hb_e384] at hok
            dsimp only at hok
            have hexp_le : k1 + l1 + k2Cur ≤ 384 := Nat.le_of_ble_eq_true hb_e384
            have hspan_le : nhi1 - nlo1 + 1 ≤ p2K12 := Nat.le_of_ble_eq_true hb_col
            have hdvd := dvd_two_step_collapse hk2_ge hl1_1 hacc1 hstep1
            have hcand := checkRemMod_sound hp2K12 hexp_le hspan_le rfl hs0_lo hs0_hi hinv1 hdvd hok
            exact checkCandR2_sound hb2_lt hs0_b1 hb12 hs1_lo hs1_hi hs2_lo hs2_hi hx3_lo
              hst0 ⟨hx1_o, hx1_p, hx2_o, hx2_p, hk1_1, hl1_1, hstep1⟩ hst2 hcand
        | false =>
          rw [hb_col] at hok
          dsimp only at hok
          simp only [Bool.and_eq_true] at hok
          rcases hok with ⟨hok_split, hmore⟩
          by_cases heq_k2 : s1.k = k2Cur
          · subst heq_k2
            rw [hp2k2, hp3k2, hp2K12] at hok_split
            have hpow_hi2 : 2 ^ s1.k ≤ hi2 + 1 := by
              have hn : ¬ (Nat.add hi2 2 ≤ p2k2) := by
                rw [← Nat.ble_eq, hb_pow]; decide
              change ¬ (hi2 + 2 ≤ p2k2) at hn
              rw [hp2k2] at hn; omega
            exact stepK2Here_sound hb2_lt hb12 hk0_eq hl0_eq hs0_lo hs0_hi hs0_b1
              hs1_lo2 hs1_hi2 hs1_lo hs1_hi hs2_lo hs2_hi hx3_lo hpow_hi2 hacc1 hinv12
              hk3_0_inv hst0 ⟨hx1_o, hx1_p, hx2_o, hx2_p, hk1_1, hl1_1, hstep1⟩ hst2 hok_split
          · have hp2_nx : Nat.mul 2 p2k2 = 2 ^ Nat.add k2Cur 1 := by
              change 2 * p2k2 = 2 ^ (k2Cur + 1); rw [hp2k2, Nat.pow_succ, Nat.mul_comm]
            have hp3_nx : Nat.mul 3 p3k2 = 3 ^ Nat.add k2Cur 1 := by
              change 3 * p3k2 = 3 ^ (k2Cur + 1); rw [hp3k2, Nat.pow_succ, Nat.mul_comm]
            have hp2K_nx : Nat.mul 2 p2K12 = 2 ^ (k1 + l1 + Nat.add k2Cur 1) := by
              change 2 * p2K12 = 2 ^ (k1 + l1 + (k2Cur + 1))
              rw [hp2K12, show k1 + l1 + (k2Cur + 1) = (k1 + l1 + k2Cur) + 1 by omega,
                  Nat.pow_succ, Nat.mul_comm]
            have hinv_nx : (3 ^ (k1 + Nat.add k2Cur 1) *
                Nat.mod (Nat.mul inv12 inv3One384) (Nat.mul (2 ^ 192) (2 ^ 192))) % 2 ^ 384 = 1 := by
              change (3 ^ (k1 + (k2Cur + 1)) * ((inv12 * inv3One384) % (2 ^ 192 * 2 ^ 192))) % 2 ^ 384 = 1
              rw [show (2 ^ 192 * 2 ^ 192 : Nat) = 2 ^ 384 by rw [← Nat.pow_add],
                  show k1 + (k2Cur + 1) = (k1 + k2Cur) + 1 by omega]
              exact inv3_step_spec hinv12
            exact loopK2R2_sound hb2_lt hb12 hk0_eq hl0_eq hs0_lo hs0_hi hs0_b1
              hs1_lo2 hs1_hi2 hs1_lo hs1_hi hs2_lo hs2_hi hx3_lo hacc1 hinv1 hk3_0_inv hst0
              ⟨hx1_o, hx1_p, hx2_o, hx2_p, hk1_1, hl1_1, hstep1⟩ hst2 fuel (Nat.add k2Cur 1)
              (Nat.mul 2 p2k2) (Nat.mul 3 p3k2) (Nat.mul 2 p2K12)
              (Nat.mod (Nat.mul inv12 inv3One384) (Nat.mul (2 ^ 192) (2 ^ 192)))
              (by change k2Cur + 1 ≤ s1.k; omega) hp2_nx hp3_nx hp2K_nx hinv_nx hmore

def loopL1R2 (b1 b2 k1 p2k1 p3k1 inv1 lo1 hi1 evMin evMax k3_0 p3_0 p2_0 : Nat)
    (exemptIds : List Nat) :
    Nat -> Nat -> Nat -> Bool
  | 0, _, _ => false
  | fuel + 1, l1, P1 =>
    if evMax < P1 * (b1 + 1) then true
    else
      let lo2 := maxNat (b1 + 1) (ceilDiv evMin P1)
      let hi2 := minNat b2 (evMax / P1)
      let okHere :=
        if lo2 > hi2 then true
        else
          let p2kl := p2k1 * P1
          let nlo1 := pullbackLo1P p2kl p2k1 p3k1 lo1 lo2
          let nhi1 := pullbackHi1P p2kl p2k1 p3k1 hi1 hi2
          if nlo1 > nhi1 then true
          else
            let g1 := p2k1 * (P1 - 1)
            let rk2 := advanceKFrom hi2 (b1 + 1) 1 1 1
            let k2Min := rk2.1
            let p2k2 := 2 * rk2.2.2
            let p3k2 := 3 * rk2.2.1
            if k1 + k2Min > 384 then false
            else
              let inv12 := inv3At384 (k1 + k2Min)
              loopK2R2 b1 b2 k1 l1 inv1 nlo1 nhi1 lo2 hi2 g1 k3_0 p3_0 p2_0
                (checkCandR2 b1 b2 exemptIds) 256 k2Min p2k2 p3k2 (p2kl * p2k2) inv12
      okHere && loopL1R2 b1 b2 k1 p2k1 p3k1 inv1 lo1 hi1 evMin evMax k3_0 p3_0 p2_0
        exemptIds fuel (l1 + 1) (2 * P1)

theorem loopL1R2_sound
    {b1 b2 k1 inv1 lo1 hi1 evMin evMax k3_0 p3_0 p2_0 : Nat} {exemptIds : List Nat}
    {s0 s1 s2 : SpiralStepData} {x3 : Nat}
    (hb2_lt : b2 < 2 ^ 256) (hb12 : b1 ≤ b2)
    (hk0_eq : s0.k = k1)
    (hs0_lo : lo1 ≤ s0.x) (hs0_hi : s0.x ≤ hi1) (hs0_b1 : s0.x ≤ b1)
    (hs1_lo : b1 + 1 ≤ s1.x) (hs1_hi : s1.x ≤ b2)
    (hs2_lo : b1 + 1 ≤ s2.x) (hs2_hi : s2.x ≤ b2)
    (hx3_lo : b2 + 1 ≤ x3)
    (hev_lo : evMin ≤ 2 ^ s0.l * s1.x) (hev_hi : 2 ^ s0.l * s1.x ≤ evMax)
    (hinv1 : (3 ^ k1 * inv1) % 2 ^ 384 = 1)
    (hk3_0_inv : k3_0 ≥ 1 ∧ p3_0 = 3 ^ (k3_0 - 1) ∧ p2_0 = 2 ^ (k3_0 - 1) ∧
      (k3_0 = 1 ∨ 3 ^ (k3_0 - 1) * (s2.x + 1) < 2 ^ (k3_0 - 1) * (2 * (b2 + 1) + 1)))
    (hst0 : ValidSpiralStep s0 s1.x)
    (hst1 : ValidSpiralStep s1 s2.x)
    (hst2 : ValidSpiralStep s2 x3) :
    ∀ (fuel lCur P1 : Nat),
      lCur ≤ s0.l ->
      P1 = 2 ^ lCur ->
      loopL1R2 b1 b2 k1 (2 ^ k1) (3 ^ k1) inv1 lo1 hi1 evMin evMax k3_0 p3_0 p2_0
        exemptIds fuel lCur P1 = true ->
      s0.x ∈ exemptIds
  | 0, _, _, _, _, hok => by simp [loopL1R2] at hok
  | fuel + 1, lCur, P1, hl_ge, hP1, hok => by
    unfold loopL1R2 at hok
    by_cases hexit : evMax < P1 * (b1 + 1)
    · exfalso
      rw [hP1] at hexit
      have hp : 2 ^ lCur ≤ 2 ^ s0.l := pow2_mono_nat hl_ge
      have hm : 2 ^ lCur * (b1 + 1) ≤ 2 ^ s0.l * s1.x := Nat.mul_le_mul hp hs1_lo
      omega
    · simp only [hexit, ↓reduceIte, Bool.and_eq_true] at hok
      rcases hok with ⟨hokHere, hmore⟩
      by_cases heq_l : s0.l = lCur
      · subst heq_l; subst hk0_eq
        rw [hP1] at hokHere
        let P1v := 2 ^ s0.l
        have hP1v : P1v ≥ 1 := pow2_pos_nat s0.l
        have hlo2 : maxNat (b1 + 1) (ceilDiv evMin P1v) ≤ s1.x := by
          unfold maxNat
          have hc := ceilDiv_le_of_le_mul hP1v hev_lo
          by_cases h : b1 + 1 ≤ ceilDiv evMin P1v <;> simp [h] <;> omega
        have hhi2 : s1.x ≤ minNat b2 (evMax / P1v) := by
          unfold minNat
          have hf := le_div_of_mul_le hP1v hev_hi
          by_cases h : b2 ≤ evMax / P1v <;> simp [h] <;> omega
        have hnot_gt2 : ¬ (maxNat (b1 + 1) (ceilDiv evMin P1v) > minNat b2 (evMax / P1v)) := by omega
        rw [ite_eq_right hnot_gt2] at hokHere
        have hp2kl : 2 ^ s0.k * 2 ^ s0.l = 2 ^ (s0.k + s0.l) := (Nat.pow_add 2 s0.k s0.l).symm
        rw [hp2kl] at hokHere
        rcases hst0 with ⟨hx0_o, hx0_p, hx1_o, hx1_p, hk0_1, hl0_1, hstep0⟩
        rcases pullback_n1_bounds hl0_1 hs0_lo hs0_hi hlo2 hhi2 hstep0 with ⟨hnlo1, hnhi1⟩
        let lo2 := maxNat (b1 + 1) (ceilDiv evMin P1v)
        let hi2 := minNat b2 (evMax / P1v)
        have hnot_gt1 : ¬ (pullbackLo1P (2 ^ (s0.k + s0.l)) (2 ^ s0.k) (3 ^ s0.k) lo1 lo2 >
            pullbackHi1P (2 ^ (s0.k + s0.l)) (2 ^ s0.k) (3 ^ s0.k) hi1 hi2) := by
          change ¬ (pullbackLo1 s0.k s0.l (3 ^ s0.k) lo1 lo2 >
            pullbackHi1 s0.k s0.l (3 ^ s0.k) hi1 hi2)
          dsimp [lo2, hi2]; omega
        rw [ite_eq_right hnot_gt1] at hokHere
        rcases hst1 with ⟨hx1_o2, hx1_p2, hx2_o, hx2_p, hk1_1, hl1_1, hstep1⟩
        have hrk2 := advanceKFrom_inv hhi2 (target := b1 + 1) (k0 := 1) (p3_0 := 1) (p2_0 := 1)
          ⟨by omega, rfl, rfl, Or.inl rfl⟩
        generalize advanceKFrom hi2 (b1 + 1) 1 1 1 = rk2 at hrk2 hokHere
        rcases advanceK_inv_implies_le hk1_1 hl1_1 hs2_lo hrk2.1 hrk2.2.2.1 hrk2.2.2.2 hstep1
          with ⟨hk2_ge, hp2k2_eq⟩
        have hp3k2_eq : 3 * rk2.2.1 = 3 ^ rk2.1 := by
          rw [hrk2.2.1, Nat.mul_comm 3, ← Nat.pow_succ, show (rk2.1 - 1).succ = rk2.1 by omega]
        by_cases hw384 : s0.k + rk2.1 > 384
        · rw [ite_eq_left hw384] at hokHere; simp at hokHere
        · rw [ite_eq_right hw384] at hokHere
          have hacc0 : 2 ^ 0 * (s0.x + 1) = 3 ^ 0 * (s0.x + 1) + 0 := by simp
          have hacc1 := step_hensel_extend hacc0 hstep0
          simp only [Nat.zero_add, Nat.mul_zero] at hacc1
          have hp2K12_0 : 2 ^ (s0.k + s0.l) * (2 * rk2.2.2) = 2 ^ (s0.k + s0.l + rk2.1) := by
            rw [hp2k2_eq, ← Nat.pow_add]
          exact loopK2R2_sound hb2_lt hb12 rfl rfl hnlo1 hnhi1 hs0_b1 hlo2 hhi2
            hs1_lo hs1_hi hs2_lo hs2_hi hx3_lo hacc1 hinv1 hk3_0_inv
            ⟨hx0_o, hx0_p, hx1_o, hx1_p, hk0_1, hl0_1, hstep0⟩
            ⟨hx1_o2, hx1_p2, hx2_o, hx2_p, hk1_1, hl1_1, hstep1⟩ hst2
            256 rk2.1 (2 * rk2.2.2) (3 * rk2.2.1) (2 ^ (s0.k + s0.l) * (2 * rk2.2.2))
            (inv3At384 (s0.k + rk2.1))
            hk2_ge hp2k2_eq hp3k2_eq hp2K12_0 (inv3At384_spec (by omega)) hokHere
      · have hP1_nx : 2 * P1 = 2 ^ (lCur + 1) := by rw [hP1, Nat.pow_succ, Nat.mul_comm]
        exact loopL1R2_sound hb2_lt hb12 hk0_eq hs0_lo hs0_hi hs0_b1 hs1_lo hs1_hi
          hs2_lo hs2_hi hx3_lo hev_lo hev_hi hinv1 hk3_0_inv hst0 hst1 hst2 fuel (lCur + 1)
          (2 * P1) (by omega) hP1_nx hmore

def verifyBandR2 (b1 b2 : Nat) (exemptIds : List Nat) (k1 lo1 hi1 : Nat) : Bool :=
  if lo1 > hi1 then true
  else if k1 > 384 then false
  else
    let p2k1 := 2 ^ k1
    if hi1 + 1 < p2k1 then true
    else
      let p3k1 := 3 ^ k1
      if p3k1 * (hi1 + 1) < p2k1 * (2 * (b1 + 1) + 1) then true
      else
        let uMin := oddQuotMinP p2k1 lo1
        let uMax := oddQuotMaxP p2k1 hi1
        if uMin > uMax then true
        else
          let evMin := p3k1 * uMin - 1
          let evMax := p3k1 * uMax - 1
          let rl1 := advanceLMinFast evMin b2
          let inv1 := inv3At384 k1
          let lo1u := maxNat lo1 (p2k1 * uMin - 1)
          let hi1u := minNat hi1 (p2k1 * uMax - 1)
          let rk3_0 := advanceKFrom b2 (b2 + 1) 1 1 1
          loopL1R2 b1 b2 k1 p2k1 p3k1 inv1 lo1u hi1u evMin evMax
            rk3_0.1 rk3_0.2.1 rk3_0.2.2 exemptIds 256 rl1.1 rl1.2

theorem verifyBandR2_sound
    {b1 b2 k1 lo1 hi1 : Nat} {exemptIds : List Nat}
    {s0 s1 s2 : SpiralStepData} {x3 : Nat}
    (hb2_lt : b2 < 2 ^ 256) (hb12 : b1 ≤ b2)
    (hk0_eq : s0.k = k1)
    (hs0_lo : lo1 ≤ s0.x) (hs0_hi : s0.x ≤ hi1) (hs0_b1 : s0.x ≤ b1)
    (hs1_lo : b1 + 1 ≤ s1.x) (hs1_hi : s1.x ≤ b2)
    (hs2_lo : b1 + 1 ≤ s2.x) (hs2_hi : s2.x ≤ b2)
    (hx3_lo : b2 + 1 ≤ x3)
    (hst0 : ValidSpiralStep s0 s1.x)
    (hst1 : ValidSpiralStep s1 s2.x)
    (hst2 : ValidSpiralStep s2 x3)
    (hok : verifyBandR2 b1 b2 exemptIds k1 lo1 hi1 = true) :
    s0.x ∈ exemptIds := by
  unfold verifyBandR2 at hok
  by_cases hgt : lo1 > hi1
  · omega
  · simp only [hgt, ↓reduceIte] at hok
    by_cases hk384 : k1 > 384
    · simp [hk384] at hok
    · simp only [hk384, ↓reduceIte] at hok
      rcases hst0 with ⟨hx0_o, hx0_p, hx1_o, hx1_p, hk0_1, hl0_1, hstep0⟩
      by_cases hpow : hi1 + 1 < 2 ^ k1
      · exfalso
        exact no_spiral_step_of_hi_lt_pow2 s0.k k1 s0.l hi1 s0.x s1.x
          (by omega) hl0_1 hs0_hi hpow hstep0
      · simp only [hpow, ↓reduceIte] at hok
        by_cases htgt : 3 ^ k1 * (hi1 + 1) < 2 ^ k1 * (2 * (b1 + 1) + 1)
        · exfalso
          exact no_spiral_step_of_pow3_lt_target s0.k k1 s0.l hi1 (b1 + 1) s0.x s1.x
            (by omega) hl0_1 hs0_hi hs1_lo htgt hstep0
        · simp only [htgt, ↓reduceIte] at hok
          subst hk0_eq
          rcases oddQuotBounds_sound hl0_1 hs0_lo hs0_hi (by omega) hstep0 with
            ⟨hu_le, hlo_u, hhi_u, hev_lo, hev_hi⟩
          have hnot_u : ¬ (oddQuotMinP (2 ^ s0.k) lo1 > oddQuotMaxP (2 ^ s0.k) hi1) := by
            change ¬ (oddQuotMin s0.k lo1 > oddQuotMax s0.k hi1); omega
          simp only [hnot_u, ↓reduceIte] at hok
          have hlo1u : maxNat lo1 (2 ^ s0.k * oddQuotMinP (2 ^ s0.k) lo1 - 1) ≤ s0.x := by
            change maxNat lo1 (2 ^ s0.k * oddQuotMin s0.k lo1 - 1) ≤ s0.x
            unfold maxNat
            by_cases hc : lo1 ≤ 2 ^ s0.k * oddQuotMin s0.k lo1 - 1 <;> simp [hc] <;> omega
          have hhi1u : s0.x ≤ minNat hi1 (2 ^ s0.k * oddQuotMaxP (2 ^ s0.k) hi1 - 1) := by
            change s0.x ≤ minNat hi1 (2 ^ s0.k * oddQuotMax s0.k hi1 - 1)
            unfold minNat
            by_cases hc : hi1 ≤ 2 ^ s0.k * oddQuotMax s0.k hi1 - 1 <;> simp [hc] <;> omega
          have hq1_eq : oddQuotMin s0.k lo1 = oddQuotMinP (2 ^ s0.k) lo1 := rfl
          rw [hq1_eq] at hev_lo
          have hrl1 := advanceLMinFast_sound hl0_1 hs1_hi hev_lo
          generalize advanceLMinFast (3 ^ s0.k * oddQuotMinP (2 ^ s0.k) lo1 - 1) b2 = rl1 at hrl1 hok
          have hrk3_0 := advanceKFrom_inv hs2_hi (target := b2 + 1) (k0 := 1) (p3_0 := 1) (p2_0 := 1)
            ⟨by omega, rfl, rfl, Or.inl rfl⟩
          generalize advanceKFrom b2 (b2 + 1) 1 1 1 = rk3_0 at hrk3_0 hok
          exact loopL1R2_sound hb2_lt hb12 rfl hlo1u hhi1u hs0_b1 hs1_lo hs1_hi
            hs2_lo hs2_hi hx3_lo hev_lo hev_hi (inv3At384_spec (by omega)) hrk3_0
            ⟨hx0_o, hx0_p, hx1_o, hx1_p, hk0_1, hl0_1, hstep0⟩ hst1 hst2
            256 rl1.1 rl1.2 hrl1.1 hrl1.2 hok

-- Range verifiers and subcase cores for c = 1 and c = 2:
def verifyRangeR1 (b1 b2 : Nat) (exemptIds : List Nat) (bounds : Nat -> Nat × Nat) :
    Nat -> Nat -> Bool
  | _, 0 => true
  | kStart, cnt + 1 =>
    let lh := bounds kStart
    verifyBandR1 b1 b2 exemptIds kStart lh.1 lh.2 &&
    verifyRangeR1 b1 b2 exemptIds bounds (kStart + 1) cnt

theorem verifyRangeR1_sound {b1 b2 : Nat} {exemptIds : List Nat} {bounds : Nat -> Nat × Nat} :
    ∀ {kStart cnt k : Nat},
      verifyRangeR1 b1 b2 exemptIds bounds kStart cnt = true ->
      kStart ≤ k -> k < kStart + cnt ->
      verifyBandR1 b1 b2 exemptIds k (bounds k).1 (bounds k).2 = true
  | _, 0, _, _, hlo, hhi => by omega
  | kStart, cnt + 1, k, hok, hlo, hhi => by
    unfold verifyRangeR1 at hok
    simp only [Bool.and_eq_true] at hok
    by_cases heq : k = kStart
    · subst heq; exact hok.1
    · exact verifyRangeR1_sound hok.2 (by omega) (by omega)

def verifyRangeR2 (b1 b2 : Nat) (exemptIds : List Nat) (bounds : Nat -> Nat × Nat) :
    Nat -> Nat -> Bool
  | _, 0 => true
  | kStart, cnt + 1 =>
    let lh := bounds kStart
    verifyBandR2 b1 b2 exemptIds kStart lh.1 lh.2 &&
    verifyRangeR2 b1 b2 exemptIds bounds (kStart + 1) cnt

theorem verifyRangeR2_sound {b1 b2 : Nat} {exemptIds : List Nat} {bounds : Nat -> Nat × Nat} :
    ∀ {kStart cnt k : Nat},
      verifyRangeR2 b1 b2 exemptIds bounds kStart cnt = true ->
      kStart ≤ k -> k < kStart + cnt ->
      verifyBandR2 b1 b2 exemptIds k (bounds k).1 (bounds k).2 = true
  | _, 0, _, _, hlo, hhi => by omega
  | kStart, cnt + 1, k, hok, hlo, hhi => by
    unfold verifyRangeR2 at hok
    simp only [Bool.and_eq_true] at hok
    by_cases heq : k = kStart
    · subst heq; exact hok.1
    · exact verifyRangeR2_sound hok.2 (by omega) (by omega)

theorem verifyRangeR2_append {b1 b2 : Nat} {exemptIds : List Nat} {bounds : Nat -> Nat × Nat} :
    ∀ (kStart c1 c2 : Nat),
      verifyRangeR2 b1 b2 exemptIds bounds kStart c1 = true ->
      verifyRangeR2 b1 b2 exemptIds bounds (kStart + c1) c2 = true ->
      verifyRangeR2 b1 b2 exemptIds bounds kStart (c1 + c2) = true
  | kStart, 0, c2, _, h2 => by simpa using h2
  | kStart, c1 + 1, c2, h1, h2 => by
    rw [show c1 + 1 + c2 = (c1 + c2) + 1 by omega]
    simp only [verifyRangeR2, Bool.and_eq_true] at h1 ⊢
    refine ⟨h1.1, ?_⟩
    rw [show kStart + (c1 + 1) = (kStart + 1) + c1 by omega] at h2
    exact verifyRangeR2_append (kStart + 1) c1 c2 h1.2 h2

theorem ge_maxNat {a b x : Nat} (ha : a ≤ x) (hb : b ≤ x) : maxNat a b ≤ x := by
  unfold maxNat; by_cases h : a ≤ b <;> simp [h] <;> omega

theorem le_minNat {a b x : Nat} (ha : x ≤ a) (hb : x ≤ b) : x ≤ minNat a b := by
  unfold minNat; by_cases h : a ≤ b <;> simp [h] <;> omega

def mkBoundsS1 (uMinusM denomHi b1 : Nat) (k : Nat) : Nat × Nat :=
  let M := 2 ^ 256
  let lo := maxNat barinaXMin ((M * (3 ^ k - 2 ^ k)) / (uMinusM * 3 ^ k) + 1)
  let hi := minNat b1 ((M * M * (3 ^ k - 2 ^ k)) / (denomHi * 3 ^ k))
  (lo, hi)

def mkBoundsU (uMinusM b1 : Nat) (k : Nat) : Nat × Nat :=
  let M := 2 ^ 256
  let lo := maxNat barinaXMin ((M * (3 ^ k - 2 ^ k)) / (uMinusM * 3 ^ k) + 1)
  (lo, b1)

def checkSubcaseAux (c m u kCap b1 b2 b3 uMinusM denomHi : Nat) : Bool :=
  let M := 2 ^ 256
  let lu := evalPow2Pow3Aux 256 (u * p43Val) (u * q43Val) 96
  let sig := teleStepCap M b1 [(b2, c), (b3, c + 1), (M, c + 2)] (m - 1)
  let denomCalc := (M - sig) * lu.1 - M * M
  let globHi := (M * M) / denomHi
  (kCap ≥ 2) &&
  (b1 ≤ b2) && (b2 ≤ b3) && (b3 ≤ M) && (b2 < M) &&
  IsNonDecreasing b1 [b2, b3, M] &&
  (M < lu.2) &&
  (lu.2 - M == uMinusM) &&
  (denomCalc == denomHi) &&
  (b1 + 1 < 2 ^ kCap) &&
  (3 ^ (kCap - 1) * (b1 + 1) < 2 ^ (kCap - 1) * (2 * (b2 + 1) + 1)) &&
  (sig < M) &&
  (M * M < (M - sig) * lu.1) &&
  (globHi + 1 < 2 ^ kCap) &&
  (3 ^ (kCap - 1) * (globHi + 1) < 2 ^ (kCap - 1) * (2 * (b2 + 1) + 1))

theorem no_spiral_cycle_c1_core
    {steps : List SpiralStepData} {sLog bLog m u kCap b1 b2 b3 uMinusM denomHi : Nat} {bsS0 exemptIds : List Nat}
    (hbar : BarinaThreshold (2 ^ 71))
    (hcyc : IsNontrivialSpiralCycle steps)
    (hm_eq : steps.length = m) (hm_ge4 : m ≥ 4)
    (hK_eq : spiralChainTotalK steps = u * p43Val)
    (hW_eq : spiralChainTotalW steps = u * q43Val)
    (hp_lt : u * p43Val < 2 ^ 96) (hq_lt : u * q43Val < 2 ^ 96)
    (hok_counts : checkSlabEliminated sLog bLog 256 m (u * q43Val) barinaXMin
      (2 * 2 ^ 256) [2 ^ 71, b1, b2, b3, 2 ^ 256] = true)
    (hok_s0 : checkSlabEliminated sLog bLog 256 m (u * q43Val) (b1 + 1)
      (evalPow2Pow3Aux 256 (u * p43Val) (u * q43Val) 96).1 bsS0 = true)
    (haux : checkSubcaseAux 1 m u kCap b1 b2 b3 uMinusM denomHi = true)
    (hr1 : verifyRangeR1 b1 b2 exemptIds (mkBoundsS1 uMinusM denomHi b1) 1 (kCap - 1) = true)
    (hex_ok : exemptIds.all (fun x => henselSurvivors92To95.any (fun zk => x == zk.1)) = true) :
    False := by
  rcases evalPow2Pow3_eq_subst (S := 256) (nbits := 96)
    (by decide) hp_lt hq_lt hK_eq hW_eq with ⟨hL_raw, hU_raw⟩
  by_cases hall_b1 : ∀ s ∈ steps, s.x ≥ b1 + 1
  · exact checkSlabEliminated_sound hok_s0 hcyc (by omega)
      (by rw [hW_eq]; exact Nat.le_refl _) hall_b1 hL_raw
  · unfold checkSubcaseAux at haux
    generalize evalPow2Pow3Aux 256 (u * p43Val) (u * q43Val) 96 = lu at haux hL_raw hU_raw
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at haux
    rcases haux with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hkCap2, hb12⟩, hb23⟩, hb3M⟩, hb2_lt⟩, hnd⟩,
      hU_gt⟩, huMM_eq⟩, hden_eq⟩, _hb1_pow⟩, _hb1_tgt⟩, hsig_lt⟩, hdenom_pos⟩, hglob_pow⟩, hglob_tgt⟩
    have hfl_bar := nontrivial_cycle_vertex_floor hbar hcyc
    rcases spiralCycle_rotate_at_small hcyc hall_b1 with
      ⟨s0, tail, hs0_le_b1, hcyc_rot, hlen_rot, hK_rot, hW_rot, _, hfl_rot_fn⟩
    have hfl_rot : ∀ s ∈ (s0 :: tail), s.x ≥ barinaXMin := hfl_rot_fn barinaXMin hfl_bar
    have hcnt_all := counts_of_checkSlabEliminated hok_counts hcyc_rot
      (by rw [hlen_rot, hm_eq]; exact Nat.le_refl _)
      (by rw [hW_rot, hW_eq]; exact Nat.le_refl _) hfl_rot
    have hc1 : countLe b1 (spiralVertices (s0 :: tail)) ≤ 1 :=
      hcnt_all (b1, 1) (List.Mem.tail _ (List.Mem.head _))
    have hc2 : countLe b2 (spiralVertices (s0 :: tail)) ≤ 2 :=
      hcnt_all (b2, 2) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    have hc3 : countLe b3 (spiralVertices (s0 :: tail)) ≤ 3 :=
      hcnt_all (b3, 3) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
    have hc4 : countLe (2 ^ 256) (spiralVertices (s0 :: tail)) ≤ 4 :=
      hcnt_all (2 ^ 256, 4) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
    rcases tail_counts_of_head_small hb12 hb23 hb3M hs0_le_b1 hc1 hc2 hc3 hc4 with
      ⟨htail_fl, htail_bcs⟩
    have htail_len : tail.length = m - 1 := by simp at hlen_rot; omega
    cases tail with
    | nil => simp at htail_len; omega
    | cons s1 tail1 =>
      cases tail1 with
      | nil => simp at htail_len; omega
      | cons s2 rest =>
        have ⟨⟨hs0_step, htail_chain⟩, _hbig⟩ := hcyc_rot
        have hxs_len : ((s1 :: s2 :: rest).map (fun s => s.x)).length = m - 1 := by
          simp at htail_len ⊢; exact htail_len
        have hbern_tail := teleBernoulli_ratio_bound (2 ^ 256) b1
          [(b2, 1), (b3, 2), (2 ^ 256, 3)]
          ((s1 :: s2 :: rest).map (fun s => s.x))
          (pow2_pos_nat 256) htail_fl hnd htail_bcs
          (by rw [hxs_len]; exact Nat.le_of_lt hsig_lt)
        rw [hxs_len] at hbern_tail
        simp only [List.map_map, Function.comp_def] at hbern_tail
        let sig := teleStepCap (2 ^ 256) b1 [(b2, 1), (b3, 2), (2 ^ 256, 3)] (m - 1)
        rcases m92_s_ge_1_band_bounds_core (M := 2 ^ 256)
          (K := spiralChainTotalK steps) (W := spiralChainTotalW steps)
          (L43 := lu.1) (U43 := lu.2) (sigma := sig) (denomHi := denomHi)
          (pow2_pos_nat 256) hs0_step htail_chain hK_rot hW_rot
          hL_raw hU_raw hU_gt hbern_tail hsig_lt hdenom_pos hden_eq with
          ⟨hs0_lo_der, hs0_hi_der, hs0_glob⟩
        rw [huMM_eq] at hs0_lo_der
        have hs0_ge_bar : barinaXMin ≤ s0.x := hfl_rot s0 (List.Mem.head _)
        have hs1_ge_b1 : b1 + 1 ≤ s1.x := htail_fl s1.x (List.Mem.head _)
        rcases hs0_step with ⟨hx0_o, hx0_p, hx1_o, hx1_p, hk0_1, hl0_1, hst0_nat⟩
        by_cases hk_hi : kCap ≤ s0.k
        · exact no_spiral_step_of_hi_lt_pow2 s0.k kCap s0.l ((2 ^ 256 * 2 ^ 256) / denomHi)
            s0.x s1.x hk_hi hl0_1 hs0_glob hglob_pow hst0_nat
        · by_cases hs1_gt_b2 : b2 + 1 ≤ s1.x
          · exact no_spiral_step_of_pow3_lt_target s0.k (kCap - 1) s0.l
              ((2 ^ 256 * 2 ^ 256) / denomHi) (b2 + 1) s0.x s1.x
              (by omega) hl0_1 hs0_glob hs1_gt_b2 hglob_tgt hst0_nat
          · have hs1_le_b2 : s1.x ≤ b2 := by omega
            have hc2_tail : countLe b2 ((s1 :: s2 :: rest).map (fun s => s.x)) ≤ 1 :=
              htail_bcs (b2, 1) (List.Mem.head _)
            have hs2_gt_b2 : b2 + 1 ≤ s2.x := second_tail_gt_of_first_le hc2_tail hs1_le_b2
            have hband := verifyRangeR1_sound hr1 hk0_1 (show s0.k < 1 + (kCap - 1) by omega)
            have hs0_lo_b : (mkBoundsS1 uMinusM denomHi b1 s0.k).1 ≤ s0.x :=
              ge_maxNat hs0_ge_bar hs0_lo_der
            have hs0_hi_b : s0.x ≤ (mkBoundsS1 uMinusM denomHi b1 s0.k).2 :=
              le_minNat hs0_le_b1 hs0_hi_der
            have hmem := verifyBandR1_sound hb2_lt hb12 rfl hs0_lo_b hs0_hi_b hs0_le_b1
              hs1_ge_b1 hs1_le_b2 hs2_gt_b2
              ⟨hx0_o, hx0_p, hx1_o, hx1_p, hk0_1, hl0_1, hst0_nat⟩ htail_chain.1 hband
            exact exempt_in_survivors32_excludes_cycle hbar hcyc_rot (List.Mem.head _) hex_ok hmem

theorem no_spiral_cycle_c2_core
    {steps : List SpiralStepData} {sLog bLog m u kCap b1 b2 b3 uMinusM denomHi : Nat} {bsS0 exemptIds : List Nat}
    (hbar : BarinaThreshold (2 ^ 71))
    (hcyc : IsNontrivialSpiralCycle steps)
    (hm_eq : steps.length = m) (hm_ge4 : m ≥ 4)
    (hK_eq : spiralChainTotalK steps = u * p43Val)
    (hW_eq : spiralChainTotalW steps = u * q43Val)
    (hp_lt : u * p43Val < 2 ^ 96) (hq_lt : u * q43Val < 2 ^ 96)
    (hok_counts : checkSlabEliminated sLog bLog 256 m (u * q43Val) barinaXMin
      (2 * 2 ^ 256) [2 ^ 71, 2 ^ 71, b1, b2, b3, 2 ^ 256] = true)
    (hok_s0 : checkSlabEliminated sLog bLog 256 m (u * q43Val) (b1 + 1)
      (evalPow2Pow3Aux 256 (u * p43Val) (u * q43Val) 96).1 bsS0 = true)
    (haux : checkSubcaseAux 2 m u kCap b1 b2 b3 uMinusM denomHi = true)
    (hr1 : verifyRangeR1 b1 b2 exemptIds (mkBoundsU uMinusM b1) 1 (kCap - 1) = true)
    (hr2 : verifyRangeR2 b1 b2 exemptIds (mkBoundsS1 uMinusM denomHi b1) 1 (kCap - 1) = true)
    (hex_ok : exemptIds.all (fun x => henselSurvivors92To95.any (fun zk => x == zk.1)) = true) :
    False := by
  rcases evalPow2Pow3_eq_subst (S := 256) (nbits := 96)
    (by decide) hp_lt hq_lt hK_eq hW_eq with ⟨hL_raw, hU_raw⟩
  by_cases hall_b1 : ∀ s ∈ steps, s.x ≥ b1 + 1
  · exact checkSlabEliminated_sound hok_s0 hcyc (by omega)
      (by rw [hW_eq]; exact Nat.le_refl _) hall_b1 hL_raw
  · unfold checkSubcaseAux at haux
    generalize evalPow2Pow3Aux 256 (u * p43Val) (u * q43Val) 96 = lu at haux hL_raw hU_raw
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at haux
    rcases haux with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hkCap2, hb12⟩, hb23⟩, hb3M⟩, hb2_lt⟩, hnd⟩,
      hU_gt⟩, huMM_eq⟩, hden_eq⟩, hb1_pow⟩, hb1_tgt⟩, hsig_lt⟩, hdenom_pos⟩, _hglob_pow⟩, _hglob_tgt⟩
    have hfl_bar := nontrivial_cycle_vertex_floor hbar hcyc
    have hcnt_orig := counts_of_checkSlabEliminated hok_counts hcyc
      (by rw [hm_eq]; exact Nat.le_refl _) (by rw [hW_eq]; exact Nat.le_refl _) hfl_bar
    have hc1_orig : countLe b1 (spiralVertices steps) ≤ 2 :=
      hcnt_orig (b1, 2) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
    rcases spiralCycle_rotate_small_to_large hcyc (by omega) hall_b1 hc1_orig with
      ⟨s0, s1, tailRest, hs0_le_b1, hs1_ge_b1, hcyc_rot, hlen_rot, hK_rot, hW_rot, hcnt_eq, hfl_rot_fn⟩
    have hfl_rot : ∀ s ∈ (s0 :: s1 :: tailRest), s.x ≥ barinaXMin :=
      hfl_rot_fn barinaXMin hfl_bar
    have _hc1_le2 : countLe b1 (spiralVertices (s0 :: s1 :: tailRest)) ≤ 2 := by
      rw [hcnt_eq b1]; exact hc1_orig
    have hc2_le3 : countLe b2 (spiralVertices (s0 :: s1 :: tailRest)) ≤ 3 := by
      rw [hcnt_eq b2]
      exact hcnt_orig (b2, 3) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))
    have hc3_le4 : countLe b3 (spiralVertices (s0 :: s1 :: tailRest)) ≤ 4 := by
      rw [hcnt_eq b3]
      exact hcnt_orig (b3, 4) (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))))
    have hc4_le5 : countLe (2 ^ 256) (spiralVertices (s0 :: s1 :: tailRest)) ≤ 5 := by
      rw [hcnt_eq (2 ^ 256)]
      exact hcnt_orig (2 ^ 256, 5)
        (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))))))
    have htr_len : tailRest.length = m - 2 := by simp at hlen_rot; omega
    cases tailRest with
    | nil => simp at htr_len; omega
    | cons s2 tr1 =>
      cases tr1 with
      | nil => simp at htr_len; omega
      | cons s3 rest =>
        have ⟨⟨hs0_step, htail_chain⟩, _hbig⟩ := hcyc_rot
        have hs0_lo_u_raw := universal_vertex_lower_bound_of_U (M := 2 ^ 256)
          (K := spiralChainTotalK steps) (W := spiralChainTotalW steps) (U := lu.2)
          (pow2_pos_nat 256) hs0_step htail_chain hK_rot hW_rot hU_raw hU_gt
        rw [huMM_eq] at hs0_lo_u_raw
        have hs0_ge_bar : barinaXMin ≤ s0.x := hfl_rot s0 (List.Mem.head _)
        rcases hs0_step with ⟨hx0_o, hx0_p, hx1_o, hx1_p, hk0_1, hl0_1, hst0_nat⟩
        by_cases hk_hi : kCap ≤ s0.k
        · exact no_spiral_step_of_hi_lt_pow2 s0.k kCap s0.l b1 s0.x s1.x
            hk_hi hl0_1 hs0_le_b1 hb1_pow hst0_nat
        · by_cases hs1_gt_b2 : b2 + 1 ≤ s1.x
          · exact no_spiral_step_of_pow3_lt_target s0.k (kCap - 1) s0.l b1 (b2 + 1) s0.x s1.x
              (by omega) hl0_1 hs0_le_b1 hs1_gt_b2 hb1_tgt hst0_nat
          · have hs1_le_b2 : s1.x ≤ b2 := by omega
            by_cases hs2_gt_b2 : b2 + 1 ≤ s2.x
            · have hband1 := verifyRangeR1_sound hr1 hk0_1 (show s0.k < 1 + (kCap - 1) by omega)
              have hs0_lo_u : (mkBoundsU uMinusM b1 s0.k).1 ≤ s0.x :=
                ge_maxNat hs0_ge_bar hs0_lo_u_raw
              have hmem := verifyBandR1_sound hb2_lt hb12 rfl hs0_lo_u hs0_le_b1 hs0_le_b1
                hs1_ge_b1 hs1_le_b2 hs2_gt_b2
                ⟨hx0_o, hx0_p, hx1_o, hx1_p, hk0_1, hl0_1, hst0_nat⟩ htail_chain.1 hband1
              exact exempt_in_survivors32_excludes_cycle hbar hcyc_rot (List.Mem.head _) hex_ok hmem
            · have hs2_le_b2 : s2.x ≤ b2 := by omega
              have hc1_le1 : countLe b1 (spiralVertices (s0 :: s1 :: s2 :: s3 :: rest)) ≤ 1 := by
                apply Classical.byContradiction
                intro hge2
                exact hs2_gt_b2 (c2_s2_forces_s2_gt_b2 hb12 hkCap2 hb1_pow hb1_tgt
                  hs0_le_b1 hs1_ge_b1 hs1_le_b2 htail_chain.2.1 (by omega) hc2_le3)
              rcases tail_counts_c2_s1 hb12 hb23 hb3M hs0_le_b1 hc1_le1 hc2_le3 hc3_le4 hc4_le5
                with ⟨htail_fl, htail_bcs⟩
              have hs2_ge_b1 : b1 + 1 ≤ s2.x :=
                htail_fl s2.x (List.Mem.tail _ (List.Mem.head _))
              have hc2_tail : countLe b2 ((s1 :: s2 :: s3 :: rest).map (fun s => s.x)) ≤ 2 :=
                htail_bcs (b2, 2) (List.Mem.head _)
              have hs3_gt_b2 : b2 + 1 ≤ s3.x :=
                third_tail_gt_of_two_le hc2_tail hs1_le_b2 hs2_le_b2
              have hxs_len : ((s1 :: s2 :: s3 :: rest).map (fun s => s.x)).length = m - 1 := by
                simp at htr_len ⊢; omega
              have hbern_tail := teleBernoulli_ratio_bound (2 ^ 256) b1
                [(b2, 2), (b3, 3), (2 ^ 256, 4)]
                ((s1 :: s2 :: s3 :: rest).map (fun s => s.x))
                (pow2_pos_nat 256) htail_fl hnd htail_bcs
                (by rw [hxs_len]; exact Nat.le_of_lt hsig_lt)
              rw [hxs_len] at hbern_tail
              simp only [List.map_map, Function.comp_def] at hbern_tail
              let sig := teleStepCap (2 ^ 256) b1 [(b2, 2), (b3, 3), (2 ^ 256, 4)] (m - 1)
              rcases m92_s_ge_1_band_bounds_core (M := 2 ^ 256)
                (K := spiralChainTotalK steps) (W := spiralChainTotalW steps)
                (L43 := lu.1) (U43 := lu.2) (sigma := sig) (denomHi := denomHi)
                (pow2_pos_nat 256) ⟨hx0_o, hx0_p, hx1_o, hx1_p, hk0_1, hl0_1, hst0_nat⟩ htail_chain
                hK_rot hW_rot hL_raw hU_raw hU_gt hbern_tail hsig_lt hdenom_pos hden_eq with
                ⟨hs0_lo_der, hs0_hi_der, _hs0_glob⟩
              rw [huMM_eq] at hs0_lo_der
              have hband2 := verifyRangeR2_sound hr2 hk0_1 (show s0.k < 1 + (kCap - 1) by omega)
              have hs0_lo_b : (mkBoundsS1 uMinusM denomHi b1 s0.k).1 ≤ s0.x :=
                ge_maxNat hs0_ge_bar hs0_lo_der
              have hs0_hi_b : s0.x ≤ (mkBoundsS1 uMinusM denomHi b1 s0.k).2 :=
                le_minNat hs0_le_b1 hs0_hi_der
              have hmem := verifyBandR2_sound hb2_lt hb12 rfl hs0_lo_b hs0_hi_b hs0_le_b1
                hs1_ge_b1 hs1_le_b2 hs2_ge_b1 hs2_le_b2 hs3_gt_b2
                ⟨hx0_o, hx0_p, hx1_o, hx1_p, hk0_1, hl0_1, hst0_nat⟩
                htail_chain.1 htail_chain.2.1 hband2
              exact exempt_in_survivors32_excludes_cycle hbar hcyc_rot (List.Mem.head _) hex_ok hmem

-- ============================================================================
-- 13.8D Parameter Constants for m = 93..96 Zero-Trust-Gap Subcases
-- ============================================================================

def b1M93U2 : Nat := 169748887054766119337399564914
def b2M93U2 : Nat := 10644319466430191210303020409244224905532939537
def b3M93U2 : Nat := 4469159895156783811800830487548991258337749672808908710486360641137668164
def uMMM93U2 : Nat := 20612740864848256815048782341692068180369241495019550097
def denM93U2 : Nat := 2386792250662051975223883770887238557583872112249281727809349514416643691793794864131686606285306836113001885997056104517300948579874
def bsS0M93U2 : List Nat := List.replicate 2 (169748887054766119337399564914) ++ [10644319466430191210303020409244227328685673531, 4469159895156783811800830487548992275730834572067982671249268906537439429, 2 ^ 256]
def exemptM93U2 : List Nat := []

def b1M93U1 : Nat := 186580408057834147633506
def b2M93U1 : Nat := 3823138529586028419114819578588243838
def b3M93U1 : Nat := 4794396471396377056912966965355736849989508610227954665485
def uMMM93U1 : Nat := 10306370432424128407523932538057751909053918823618365351
def denM93U1 : Nat := 1049674666200432227254476991216428505214866257832836918832496244916655023064425547964811242847344180819251374394431537506545656323296
def bsS0M93U1 : List Nat := List.replicate 3 (186580408057834147633506) ++ [3823138529586028419114819578588244707, 4794396471396377056912966965355737940349983565375194239947, 2 ^ 256]
def exemptM93U1 : List Nat := [179507528690102354051071]

def b1M94U3 : Nat := 4903638129317933064380022429
def b2M94U3 : Nat := 38672595001850441544021964689601633525827805
def b3M94U3 : Nat := 607253130609001223218861308634045071740193418029515636979758639808581
def uMMM94U3 : Nat := 30919111297272385222574549490131111985921788623454255744
def denM94U3 : Nat := 3580185760215061343928554540006563229579120632380109481530165595081649768606270781754091001789673451361330218749228700937644147206724
def bsS0M94U3 : List Nat := List.replicate 2 (4903638129317933064380022429) ++ [38672595001850441544021964689601642329547441, 607253130609001223218861308634045209979851496672682214625726385458287, 2 ^ 256]
def exemptM94U3 : List Nat := []

def b1M94U2 : Nat := 169748887054766116687500223505
def b2M94U2 : Nat := 10644319466430190795590479903179073456248915278
def b3M94U2 : Nat := 4469159895156783376191333223971140127745078467008834260408584960120460298
def uMMM94U2 : Nat := 20612740864848256815048782341692068180369241495019550097
def denM94U2 : Nat := 2386792171675920386527024688677820162796035707012405364951087883811720542006997924745138664187217467231834727611658414389518412787362
def bsS0M94U2 : List Nat := List.replicate 3 (169748887054766116687500223505) ++ [10644319466430190795590479903179075879401649272, 4469159895156783376191333223971141145138163366267808462958569824308328964, 2 ^ 256]
def exemptM94U2 : List Nat := []

def b1M95U4 : Nat := 237718470600218158162337
def b2M95U4 : Nat := 5612458709018691051495362848960321110
def b3M95U4 : Nat := 8810482531733075764560844302759407162467944804191266411003
def uMMM95U4 : Nat := 41225481729696513630101233983374882374940437926199873315
def denM95U4 : Nat := 4717182614069971243283365384366016177444853298439090353064767757772354850868860379787885649168317221310380783710788028206829931653501
def bsS0M95U4 : List Nat := List.replicate 2 (237718470600218158162337) ++ [5612458709018691051495362848960322387, 8810482531733075764560844302759409166810479818307415168452, 2 ^ 256]
def exemptM95U4 : List Nat := []

def b1M95U3 : Nat := 4903638129317933018626239943
def b2M95U3 : Nat := 38672595001850440643776780345135796656350066
def b3M95U3 : Nat := 607253130609001187862407681867612122305278660890990230071910190828943
def uMMM95U3 : Nat := 30919111297272385222574549490131111985921788623454255744
def denM95U3 : Nat := 3580183025957847341976132954208640036890661822012062682735274598681164209658296984200399288939251024973112464988800304818464478387488
def bsS0M95U3 : List Nat := List.replicate 3 (4903638129317933018626239943) ++ [38672595001850440643776780345135805460069703, 607253130609001187862407681867612260544936739534148708089799717779084, 2 ^ 256]
def exemptM95U3 : List Nat := [3043056996432649454896063935, 4564585494648974182344095903]

def b1M96U5 : Nat := 123431246604716821339742844255
def b2M96U5 : Nat := 6423739258431203231836461897308788589033055636
def b3M96U5 : Nat := 2007225076006909144250000481982582679886115459680977129654091497824287131
def uMMM96U5 : Nat := 51531852162120642037628835821423380485793582721888429467
def denM96U5 : Nat := 5966980606869020578623564747422818841364487308022525880310354831374156187896987026692976774373661743081732462270516849597693275621784
def bsS0M96U5 : List Nat := List.replicate 3 (123431246604716821339742844255) ++ [6423739258431203231836461897308790051381249489, 2007225076006909144250000481982583136825889393122907626551150653586988448, 2 ^ 256]
def exemptM96U5 : List Nat := [81382151907816510442931486719, 122073227861724765664397230079]

def b1M96U4 : Nat := 237718470600218156980948
def b2M96U4 : Nat := 5612458709018690981996452102945237448
def b3M96U4 : Nat := 8810482531733075491906668020759912362072029299654245247754
def uMMM96U4 : Nat := 41225481729696513630101233983374882374940437926199873315
def denM96U4 : Nat := 4660780568843577747100803222835361927159408698751131326461577660680746522752847775232037641448992374613587029450573634034057939693948
def bsS0M96U4 : List Nat := List.replicate 3 (237718470600218156980948) ++ [5612458709018690981996452102945238724, 8810482531733075491906668020759914366414564313770331502224, 2 ^ 256]
def exemptM96U4 : List Nat := [179507528690102354051071]
end CollatzFormal
