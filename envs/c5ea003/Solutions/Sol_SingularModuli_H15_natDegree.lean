-- Prove2me | solution 1 for SingularModuli.H15_natDegree
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T22:56:18.472172+00:00
-- url     : https://prove2.me/submissions/df567781-062a-4c77-9b64-2d04049f44ed

import Mathlib
import Definitions.Def_Cryptography_SingularModuli_Experiments
import Definitions.Def_Cryptography_SingularModuli_SqrtBarrier

open SingularModuli

open Polynomial FactoringBarriers

namespace SingularModuli

private lemma H15_tail_natDegree :
    (C (191025 : ℤ) * X + C (-121287375)).natDegree ≤ 1 := by
  calc (C (191025 : ℤ) * X + C (-121287375)).natDegree
      ≤ max (C (191025 : ℤ) * X).natDegree (C (-121287375)).natDegree :=
        natDegree_add_le _ _
    _ ≤ 1 := by
      refine max_le ?_ ?_
      · calc (C (191025 : ℤ) * X).natDegree
            ≤ (C (191025 : ℤ)).natDegree + X.natDegree := natDegree_mul_le
          _ = 1 := by rw [natDegree_C, zero_add, natDegree_X]
      · simp

theorem solution : H15.natDegree = 2 := by
  have h : H15 = X ^ 2 + (C (191025 : ℤ) * X + C (-121287375)) := by
    rw [H15, sub_eq_add_neg, ← C_neg, add_assoc]
  rw [h, natDegree_add_eq_left_of_natDegree_lt]
  · exact natDegree_X_pow 2
  · rw [natDegree_X_pow]
    exact lt_of_le_of_lt H15_tail_natDegree (by norm_num)

end SingularModuli

open SingularModuli

theorem solution : H15.natDegree = 2 :=
  SingularModuli.solution

#print axioms solution
