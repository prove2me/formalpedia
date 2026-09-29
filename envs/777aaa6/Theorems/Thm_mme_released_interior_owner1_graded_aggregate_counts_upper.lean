-- Prove2me | Theorems.Thm_mme_released_interior_owner1_graded_aggregate_counts_upper
-- name    : mme_released_interior_owner1_graded_aggregate_counts_upper
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T04:32:41.046322+00:00
-- url     : https://prove2.me/theorems/f5d5a384-0256-44eb-afed-4f139f52fd6c
-- title:
--   Regional marginal aggregation for owner 1, upper component indices
-- statement:
--   Exact natural-number marginal aggregation for owner 1 and interior component indices at least 25. The global marginal equals the sum of the six weighted child products for every word of the required grade. This partition keeps the verification certificate within the platform time limit.
-- source:
--   Released exact global and regional profile data.

import Definitions.Def_mme_released_interior_integer_profiles
import Definitions.Def_mme_complete_split_concatenation
open BigOperators MME MME.ReleasedInterior MME.RecursiveYZ MME.MoreAsymmetryExactSeed MME.CompleteSplit

theorem mme_released_interior_owner1_graded_aggregate_counts_upper (s : Fin 45) :
    25 ≤ s.val →
    (seed 1 s).boundary = [] →
    ∀ (i : Fin 3) (w : CompleteWord 3),
      (∑ h, (w h).val) = parent s 0 i →
      ((ReleasedGlobal.jointRows 1 s).map
      (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum =
    ∑ r : Fin 6, (seed 1 s).region.getD r.val 0 *
      ∑ c : Split s, splitWeight 1 s r c *
        childMarginal 1 s r c i ((completeWordSplitEquiv 2 (by decide)) w).1 *
        childMarginal 1 s r (complement (parent_total s r) c) i
          ((completeWordSplitEquiv 2 (by decide)) w).2 := by sorry
