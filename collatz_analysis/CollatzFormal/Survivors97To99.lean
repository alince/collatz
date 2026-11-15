/-
  CollatzFormal/Survivors97To99.lean
  Master pure-kernel drop certificate for all newly discovered m = 97..99 Hensel survivors > 2^71.
-/

import CollatzFormal.Survivors
import CollatzFormal.Survivors97To99A
import CollatzFormal.Survivors97To99B
import CollatzFormal.Survivors97To99C
import CollatzFormal.Survivors97To99D
import CollatzFormal.Survivors97To99E
import CollatzFormal.Survivors97To99F
import CollatzFormal.Survivors97To99G
import CollatzFormal.Survivors97To99H
import CollatzFormal.Survivors97To99I
import CollatzFormal.Survivors97To99J

namespace CollatzFormal

theorem allBatchesCertified_append {n0 : Nat} :
    ∀ {xs ys : List (List (Nat × Nat))},
      AllBatchesCertified n0 xs ->
      AllBatchesCertified n0 ys ->
      AllBatchesCertified n0 (xs ++ ys)
  | [], _, .nil, hy => hy
  | _ :: _, _, .cons hx hxs, hy =>
    AllBatchesCertified.cons hx (allBatchesCertified_append hxs hy)

def m97To99SurvivorBatchList : List (List (Nat × Nat)) :=
  (m97To99BatchListA ++
    (m97To99BatchListB ++
    (m97To99BatchListC ++
    (m97To99BatchListD ++
    (m97To99BatchListE ++
    (m97To99BatchListF ++
    (m97To99BatchListG ++
    (m97To99BatchListH ++
    (m97To99BatchListI ++
    m97To99BatchListJ)))))))))

theorem all_new_m97_to_99_hensel_survivors_drop_below_2_pow_71 :
    AllBatchesCertified (2 ^ 71) m97To99SurvivorBatchList :=
  (allBatchesCertified_append m97_to_99_sub_A_ok
    (allBatchesCertified_append m97_to_99_sub_B_ok
    (allBatchesCertified_append m97_to_99_sub_C_ok
    (allBatchesCertified_append m97_to_99_sub_D_ok
    (allBatchesCertified_append m97_to_99_sub_E_ok
    (allBatchesCertified_append m97_to_99_sub_F_ok
    (allBatchesCertified_append m97_to_99_sub_G_ok
    (allBatchesCertified_append m97_to_99_sub_H_ok
    (allBatchesCertified_append m97_to_99_sub_I_ok
    m97_to_99_sub_J_ok)))))))))

theorem m97_to_99_hensel_survivor_drop_universal :
    ∀ b ∈ m97To99SurvivorBatchList, b.all (checkSurvivorDrop (2 ^ 71)) = true :=
  allBatchesCertified_mem all_new_m97_to_99_hensel_survivors_drop_below_2_pow_71

end CollatzFormal
