-- Prove2me | solution 1 for SingularModuli.successPairs_card_le
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T22:56:18.981392+00:00
-- url     : https://prove2.me/submissions/ba6e5c30-6bf5-4cae-9389-90d35b25ee2d

import Mathlib
import Definitions.Def_Cryptography_SingularModuli_RootCount
import Definitions.Def_Cryptography_SingularModuli_SqrtBarrier

open SingularModuli

open Polynomial Finset FactoringBarriers

variable {p q : ℕ} {H : Polynomial ℤ}

namespace SingularModuli

theorem solution (F : Finset (Polynomial ℤ)) (N : ℕ) :
    (successPairs F N).card ≤ ∑ H ∈ F, successCount H N := by
  classical
  rw [successPairs, Finset.card_filter, Finset.sum_product]
  refine Finset.sum_le_sum fun H _ => ?_
  rw [successCount, successSet, Finset.card_filter]

end SingularModuli

open SingularModuli

theorem solution (F : Finset (Polynomial ℤ)) (N : ℕ) :
    (successPairs F N).card ≤ ∑ H ∈ F, successCount H N :=
  SingularModuli.solution F N

#print axioms solution
