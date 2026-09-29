-- Prove2me | Theorems.Thm_mme_released_interior_owner4_graded_aggregate_counts
-- name    : mme_released_interior_owner4_graded_aggregate_counts
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T04:42:28.575829+00:00
-- url     : https://prove2.me/theorems/899582a3-ed98-4599-929c-00a3e6bf2749
-- title:
--   Exact regional marginal aggregation for owner 4
-- statement:
--   For owner 4, every interior recipe and every word of the required parent grade, the released global marginal count equals the sum of the six alpha-weighted independent child marginal products. Counts are natural numbers before normalization; this certificate makes no extraction or matrix exponent claim.
-- source:
--   Exact released global and regional profile data.

import Definitions.Def_mme_released_interior_integer_profiles
import Definitions.Def_mme_complete_split_concatenation
open BigOperators MME MME.ReleasedInterior MME.RecursiveYZ MME.MoreAsymmetryExactSeed MME.CompleteSplit

theorem mme_released_interior_owner4_graded_aggregate_counts (s : Fin 45) :
    (seed 4 s).boundary = [] →
    ∀ (i : Fin 3) (w : CompleteWord 3),
      (∑ h, (w h).val) = parent s 0 i →
      ((ReleasedGlobal.jointRows 4 s).map
      (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum =
    ∑ r : Fin 6, (seed 4 s).region.getD r.val 0 *
      ∑ c : Split s, splitWeight 4 s r c *
        childMarginal 4 s r c i ((completeWordSplitEquiv 2 (by decide)) w).1 *
        childMarginal 4 s r (complement (parent_total s r) c) i
          ((completeWordSplitEquiv 2 (by decide)) w).2 := by sorry
