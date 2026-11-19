-- Prove2me | solution 2 for A166944Research.a166944_record_is_greater_twin_prime
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tara_sooo
-- created : 2026-11-18T12:31:18.504172+00:00
-- url     : https://prove2.me/submissions/b9810818-df1a-454b-88f3-88c4eeef51b6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_a166944_moving_horizon
import Theorems.Thm_A166944Research_a166944_travel_bound_from_45895573
import Theorems.Thm_A166944Research_a166944_target_of_travel

/-!
Reduction of `a166944_record_is_greater_twin_prime` to the travel bound.

The parent is the A166944 record/twin-prime statement. The child
`a166944_target_of_travel` already proves it *from* the travel bound, and the
sibling child `a166944_travel_bound_from_45895573` *is* that travel bound. Composing
the two gives the parent, so the entire remaining content of the conjecture is the
single travel inequality.

Note the direction: this file does not assume the conjecture. It shows that the
parent follows from a child that is itself Open.
-/

open A166944Research

theorem solution :
    ∀ R : Nat, 5 < R → IsDifferenceRecord R → IsGreaterTwinPrime R :=
  a166944_target_of_travel a166944_travel_bound_from_45895573
