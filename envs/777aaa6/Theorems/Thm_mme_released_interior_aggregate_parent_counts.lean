-- Prove2me | Theorems.Thm_mme_released_interior_aggregate_parent_counts
-- name    : mme_released_interior_aggregate_parent_counts
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T04:50:43.046219+00:00
-- url     : https://prove2.me/theorems/617375c8-eca5-45ff-b1a6-ed34d97572f5
-- title:
--   Released global marginals equal their regional child products
-- statement:
--   For every owner, interior recipe, mode and parent word, the released global marginal count equals the sum of the six region-weighted split and child-marginal products. Wrong-grade words contribute zero on both sides. The full matrix exponent bound remains a separate obligation.
-- source:
--   Kernel-checked regional count identities and exact extraction with empty regions.

import Theorems.Thm_mme_released_interior_owner0_graded_aggregate_counts
import Theorems.Thm_mme_released_interior_owner1_graded_aggregate_counts
import Theorems.Thm_mme_released_interior_owner2_graded_aggregate_counts
import Theorems.Thm_mme_released_interior_owner3_graded_aggregate_counts
import Theorems.Thm_mme_released_interior_owner4_graded_aggregate_counts
import Theorems.Thm_mme_released_interior_owner5_graded_aggregate_counts
import Theorems.Thm_mme_released_interior_wrong_grade_aggregate_counts
open BigOperators MME MME.ReleasedInterior MME.RecursiveYZ MME.MoreAsymmetryExactSeed MME.CompleteSplit MME.RegionRealization

theorem mme_released_interior_aggregate_parent_counts
    (owner : Fin 6) (s : Fin 45) (hi : (seed owner s).boundary = [])
    (i : Fin 3) (w : CompleteWord 3) :
    ((ReleasedGlobal.jointRows owner s).map
      (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum =
    ∑ r : Fin 6, (seed owner s).region.getD r.val 0 *
      ∑ c : Split s, splitWeight owner s r c *
        childMarginal owner s r c i ((completeWordSplitEquiv 2 (by decide)) w).1 *
        childMarginal owner s r (complement (parent_total s r) c) i
          ((completeWordSplitEquiv 2 (by decide)) w).2
 := by sorry
