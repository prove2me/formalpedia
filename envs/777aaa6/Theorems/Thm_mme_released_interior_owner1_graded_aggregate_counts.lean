-- Prove2me | Theorems.Thm_mme_released_interior_owner1_graded_aggregate_counts
-- name    : mme_released_interior_owner1_graded_aggregate_counts
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T04:45:25.397547+00:00
-- url     : https://prove2.me/theorems/7efaa030-9aec-448e-83df-e6f0817ba6b1
-- title:
--   Exact regional marginal aggregation for owner 1
-- statement:
--   For owner 1, every interior recipe and every word of the required parent grade, the released global marginal count equals the sum of the six alpha-weighted independent child marginal products. Counts are natural numbers before normalization; this certificate makes no extraction or matrix exponent claim.
-- source:
--   Exact released global and regional profile data.

import Definitions.Def_mme_released_interior_integer_profiles
import Definitions.Def_mme_complete_split_concatenation
open BigOperators MME MME.ReleasedInterior MME.RecursiveYZ MME.MoreAsymmetryExactSeed MME.CompleteSplit

theorem mme_released_interior_owner1_graded_aggregate_counts (s : Fin 45) :
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
