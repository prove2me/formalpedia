-- Prove2me | Theorems.Thm_mme_released_interior_owner5_graded_aggregate_counts_lower
-- name    : mme_released_interior_owner5_graded_aggregate_counts_lower
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T04:28:22.834432+00:00
-- url     : https://prove2.me/theorems/5140fff4-6d95-4593-b1e8-5ac52d83afba
-- title:
--   Regional marginal aggregation for owner 5, lower component indices
-- statement:
--   Exact natural-number marginal aggregation for owner 5 and interior component indices below 25. The global marginal equals the sum of the six weighted child products for every word of the required grade. This partition keeps the verification certificate within the platform time limit.
-- source:
--   Released exact global and regional profile data.

import Definitions.Def_mme_released_interior_integer_profiles
import Definitions.Def_mme_complete_split_concatenation
open BigOperators MME MME.ReleasedInterior MME.RecursiveYZ MME.MoreAsymmetryExactSeed MME.CompleteSplit

theorem mme_released_interior_owner5_graded_aggregate_counts_lower (s : Fin 45) :
    s.val < 25 →
    (seed 5 s).boundary = [] →
    ∀ (i : Fin 3) (w : CompleteWord 3),
      (∑ h, (w h).val) = parent s 0 i →
      ((ReleasedGlobal.jointRows 5 s).map
      (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum =
    ∑ r : Fin 6, (seed 5 s).region.getD r.val 0 *
      ∑ c : Split s, splitWeight 5 s r c *
        childMarginal 5 s r c i ((completeWordSplitEquiv 2 (by decide)) w).1 *
        childMarginal 5 s r (complement (parent_total s r) c) i
          ((completeWordSplitEquiv 2 (by decide)) w).2 := by sorry
