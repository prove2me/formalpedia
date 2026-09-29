-- Prove2me | solution 1 for mme_released_116_aggregate_parent_counts
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T13:10:28.527022+00:00
-- url     : https://prove2.me/submissions/deb523af-2bbb-4efd-affc-cf373d5ae5a7

import Definitions.Def_mme_released_116_integer_profiles
import Definitions.Def_mme_complete_split_concatenation

open BigOperators MME MME.Released116 MME.MoreAsymmetryExactSeed
open MME.RecursiveYZ MME.CompleteSplit
set_option autoImplicit false

/-- Projecting the released joint row to one mode equals the sum of the
six regional products, before dividing by the common denominator d^4. -/
theorem solution :
    ∀ (i : Fin 3) (w : CompleteWord 3),
      ((ReleasedGlobal.jointRows 0 10).map
        (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum =
      ∑ r : Fin 6, seed.region.getD r.val 0 *
        ∑ c : Released116.Split, splitWeight r c *
          childMarginal r c i ((completeWordSplitEquiv 2 (by decide)) w).1 *
          childMarginal r (complement (parent_total r) c) i
            ((completeWordSplitEquiv 2 (by decide)) w).2 := by
  decide +kernel

#print axioms solution
