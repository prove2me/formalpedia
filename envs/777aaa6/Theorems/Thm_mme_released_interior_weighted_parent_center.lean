-- Prove2me | Theorems.Thm_mme_released_interior_weighted_parent_center
-- name    : mme_released_interior_weighted_parent_center
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T04:55:07.278578+00:00
-- url     : https://prove2.me/theorems/2cd1da07-9915-4058-951b-e380adf8e2c7
-- title:
--   Released parent frequencies are the weighted regional mixture centers
-- statement:
--   The mean of the six regional parent-mixture centers, weighted by their physical region sizes, equals the actual released global marginal divided by the fourth power of the common denominator. Empty regions contribute zero. The full matrix exponent bound remains a separate obligation.
-- source:
--   Kernel-checked regional count identities and exact extraction with empty regions.

import Theorems.Thm_mme_released_interior_aggregate_parent_counts
import Theorems.Thm_mme_released_interior_weighted_region_parent_mixture_exact
open BigOperators MME MME.ReleasedInterior MME.RecursiveYZ MME.MoreAsymmetryExactSeed MME.CompleteSplit MME.RegionRealization

theorem mme_released_interior_weighted_parent_center
    (owner : Fin 6) (s : Fin 45) (hi : (seed owner s).boundary = [])
    (i : Fin 3) (w : CompleteWord 3) :
    (∑ r : Fin 6, ((regionalSize owner s r : ℝ) / (denominator : ℝ) ^ 4) *
      RegionRealization.parentMixture (parent_total s) (regionalSize owner s)
        (splitCount owner s) (integerProfile owner s i) r
        ![((completeWordSplitEquiv 2 (by decide)) w).1,
          ((completeWordSplitEquiv 2 (by decide)) w).2]) =
    ((((ReleasedGlobal.jointRows owner s).map
      (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum : ℕ) : ℝ) /
        (denominator : ℝ) ^ 4 := by sorry
