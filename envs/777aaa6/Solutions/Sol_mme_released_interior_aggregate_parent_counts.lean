-- Prove2me | solution 1 for mme_released_interior_aggregate_parent_counts
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T04:50:49.013421+00:00
-- url     : https://prove2.me/submissions/8957d047-7852-46bb-929d-567f701495b8

import Theorems.Thm_mme_released_interior_owner0_graded_aggregate_counts
import Theorems.Thm_mme_released_interior_owner1_graded_aggregate_counts
import Theorems.Thm_mme_released_interior_owner2_graded_aggregate_counts
import Theorems.Thm_mme_released_interior_owner3_graded_aggregate_counts
import Theorems.Thm_mme_released_interior_owner4_graded_aggregate_counts
import Theorems.Thm_mme_released_interior_owner5_graded_aggregate_counts
import Theorems.Thm_mme_released_interior_wrong_grade_aggregate_counts

open BigOperators MME MME.ReleasedInterior MME.RecursiveYZ MME.MoreAsymmetryExactSeed MME.CompleteSplit MME.RegionRealization

/-- The released global marginal is the sum of the regional child products,
before dividing by the common denominator-fourth-power scale. -/
theorem solution
    (owner : Fin 6) (s : Fin 45) (hi : (seed owner s).boundary = [])
    (i : Fin 3) (w : CompleteWord 3) :
    ((ReleasedGlobal.jointRows owner s).map
      (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum =
    ∑ r : Fin 6, (seed owner s).region.getD r.val 0 *
      ∑ c : Split s, splitWeight owner s r c *
        childMarginal owner s r c i ((completeWordSplitEquiv 2 (by decide)) w).1 *
        childMarginal owner s r (complement (parent_total s r) c) i
          ((completeWordSplitEquiv 2 (by decide)) w).2
 := by
  by_cases hw : (∑ h, (w h).val) = parent s 0 i
  · fin_cases owner
    · exact mme_released_interior_owner0_graded_aggregate_counts s hi i w hw
    · exact mme_released_interior_owner1_graded_aggregate_counts s hi i w hw
    · exact mme_released_interior_owner2_graded_aggregate_counts s hi i w hw
    · exact mme_released_interior_owner3_graded_aggregate_counts s hi i w hw
    · exact mme_released_interior_owner4_graded_aggregate_counts s hi i w hw
    · exact mme_released_interior_owner5_graded_aggregate_counts s hi i w hw
  · exact mme_released_interior_wrong_grade_aggregate_counts owner s i w hw


#print axioms solution
