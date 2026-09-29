-- Prove2me | solution 1 for mme_released_interior_owner0_graded_aggregate_counts
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T04:44:39.48407+00:00
-- url     : https://prove2.me/submissions/347ae2f9-be34-4455-8e56-c2ddb66ed5de

import Theorems.Thm_mme_released_interior_owner0_graded_aggregate_counts_lower
import Theorems.Thm_mme_released_interior_owner0_graded_aggregate_counts_upper
import Definitions.Def_mme_released_interior_integer_profiles
import Definitions.Def_mme_complete_split_concatenation
open BigOperators MME MME.ReleasedInterior MME.RecursiveYZ MME.MoreAsymmetryExactSeed MME.CompleteSplit

theorem solution (s : Fin 45) :
    (seed 0 s).boundary = [] →
    ∀ (i : Fin 3) (w : CompleteWord 3),
      (∑ h, (w h).val) = parent s 0 i →
      ((ReleasedGlobal.jointRows 0 s).map
      (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum =
    ∑ r : Fin 6, (seed 0 s).region.getD r.val 0 *
      ∑ c : Split s, splitWeight 0 s r c *
        childMarginal 0 s r c i ((completeWordSplitEquiv 2 (by decide)) w).1 *
        childMarginal 0 s r (complement (parent_total s r) c) i
          ((completeWordSplitEquiv 2 (by decide)) w).2 := by
  by_cases hs : s.val < 25
  · exact mme_released_interior_owner0_graded_aggregate_counts_lower s hs
  · exact mme_released_interior_owner0_graded_aggregate_counts_upper s (Nat.le_of_not_gt hs)


#print axioms solution
