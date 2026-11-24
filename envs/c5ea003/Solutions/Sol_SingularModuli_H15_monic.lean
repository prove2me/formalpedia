-- Prove2me | solution 1 for SingularModuli.H15_monic
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T22:56:17.829551+00:00
-- url     : https://prove2.me/submissions/bb9fa89c-5e65-4290-b401-68501929c467

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

theorem solution : H15.Monic := by
  have h : H15 = X ^ 2 + (C (191025 : ℤ) * X + C (-121287375)) := by
    rw [H15, sub_eq_add_neg, ← C_neg, add_assoc]
  rw [h]
  refine monic_X_pow_add ?_
  calc (C (191025 : ℤ) * X + C (-121287375)).degree
      ≤ ↑((C (191025 : ℤ) * X + C (-121287375)).natDegree) := degree_le_natDegree
    _ ≤ (1 : WithBot ℕ) := WithBot.coe_le_coe.mpr H15_tail_natDegree
    _ < (2 : WithBot ℕ) := by norm_num

end SingularModuli

open SingularModuli

theorem solution : H15.Monic :=
  SingularModuli.solution

#print axioms solution
