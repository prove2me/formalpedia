-- Prove2me | Theorems.Thm_mme_released_interior_owner2_graded_aggregate_counts
-- name    : mme_released_interior_owner2_graded_aggregate_counts
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T04:45:50.801794+00:00
-- url     : https://prove2.me/theorems/ac6ad884-61e2-4e12-b8d9-840250a263e1
-- title:
--   Exact regional marginal aggregation for owner 2
-- statement:
--   For owner 2, every interior recipe and every word of the required parent grade, the released global marginal count equals the sum of the six alpha-weighted independent child marginal products. Counts are natural numbers before normalization; this certificate makes no extraction or matrix exponent claim.
-- source:
--   Exact released global and regional profile data.

import Definitions.Def_mme_released_interior_integer_profiles
import Definitions.Def_mme_complete_split_concatenation
open BigOperators MME MME.ReleasedInterior MME.RecursiveYZ MME.MoreAsymmetryExactSeed MME.CompleteSplit

theorem mme_released_interior_owner2_graded_aggregate_counts (s : Fin 45) :
    (seed 2 s).boundary = [] →
    ∀ (i : Fin 3) (w : CompleteWord 3),
      (∑ h, (w h).val) = parent s 0 i →
      ((ReleasedGlobal.jointRows 2 s).map
      (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum =
    ∑ r : Fin 6, (seed 2 s).region.getD r.val 0 *
      ∑ c : Split s, splitWeight 2 s r c *
        childMarginal 2 s r c i ((completeWordSplitEquiv 2 (by decide)) w).1 *
        childMarginal 2 s r (complement (parent_total s r) c) i
          ((completeWordSplitEquiv 2 (by decide)) w).2 := by sorry
