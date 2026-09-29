-- Prove2me | Theorems.Thm_mme_released_interior_owner5_graded_aggregate_counts_upper
-- name    : mme_released_interior_owner5_graded_aggregate_counts_upper
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T04:28:32.314934+00:00
-- url     : https://prove2.me/theorems/3c8be766-1ad1-4e2b-a161-790a62e7bc39
-- title:
--   Regional marginal aggregation for owner 5, upper component indices
-- statement:
--   Exact natural-number marginal aggregation for owner 5 and interior component indices at least 25. The global marginal equals the sum of the six weighted child products for every word of the required grade. This partition keeps the verification certificate within the platform time limit.
-- source:
--   Released exact global and regional profile data.

import Definitions.Def_mme_released_interior_integer_profiles
import Definitions.Def_mme_complete_split_concatenation
open BigOperators MME MME.ReleasedInterior MME.RecursiveYZ MME.MoreAsymmetryExactSeed MME.CompleteSplit

theorem mme_released_interior_owner5_graded_aggregate_counts_upper (s : Fin 45) :
    25 ≤ s.val →
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
