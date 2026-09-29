-- Prove2me | solution 1 for mme_released_interior_owner2_graded_aggregate_counts
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T04:46:59.104318+00:00
-- url     : https://prove2.me/submissions/58b22064-22da-43fc-827f-8e432f6f60f1

import Theorems.Thm_mme_released_interior_owner2_graded_aggregate_counts_lower
import Theorems.Thm_mme_released_interior_owner2_graded_aggregate_counts_upper
import Definitions.Def_mme_released_interior_integer_profiles
import Definitions.Def_mme_complete_split_concatenation
open BigOperators MME MME.ReleasedInterior MME.RecursiveYZ MME.MoreAsymmetryExactSeed MME.CompleteSplit

theorem solution (s : Fin 45) :
    (seed 2 s).boundary = [] →
    ∀ (i : Fin 3) (w : CompleteWord 3),
      (∑ h, (w h).val) = parent s 0 i →
      ((ReleasedGlobal.jointRows 2 s).map
      (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum =
    ∑ r : Fin 6, (seed 2 s).region.getD r.val 0 *
      ∑ c : Split s, splitWeight 2 s r c *
        childMarginal 2 s r c i ((completeWordSplitEquiv 2 (by decide)) w).1 *
        childMarginal 2 s r (complement (parent_total s r) c) i
          ((completeWordSplitEquiv 2 (by decide)) w).2 := by
  by_cases hs : s.val < 25
  · exact mme_released_interior_owner2_graded_aggregate_counts_lower s hs
  · exact mme_released_interior_owner2_graded_aggregate_counts_upper s (Nat.le_of_not_gt hs)


#print axioms solution
