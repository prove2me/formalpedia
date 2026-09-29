-- Prove2me | Theorems.Thm_mme_released_interior_weighted_region_parent_mixture_exact
-- name    : mme_released_interior_weighted_region_parent_mixture_exact
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T04:13:22.605308+00:00
-- url     : https://prove2.me/theorems/f452c8fa-5566-47d5-8cf6-386e2296dc37
-- title:
--   Released interior parent mixtures equal weighted child products
-- statement:
--   For every released interior recipe, owner, region, mode and pair of child words, the regional parent mixture weighted by its region size equals the exact released alpha-weighted product of its child marginals at denominator-fourth-power scale. Empty regions contribute zero. In nonempty regions, the proof cancels the integer profile scale using kernel-checked positivity of every split alpha weight. This is a regional identity; the aggregate equality to the released global joint row and entropy-rate extraction remain separate obligations.
-- source:
--   Released exact profile seed, child marginal mass, positive interior split weights and normalization.

import Definitions.Def_mme_released_interior_integer_profiles
import Definitions.Def_mme_recursive_region_parent_profiles
import Definitions.Def_mme_released_global_profile_data
import Definitions.Def_mme_more_asymmetry_released_exact_profile_seed
import Mathlib.Data.List.Sort
open BigOperators MME MME.ReleasedInterior MME.RecursiveYZ MME.MoreAsymmetryExactSeed MME.CompleteSplit

theorem mme_released_interior_weighted_region_parent_mixture_exact
    (owner : Fin 6) (s : Fin 45) (hi : (seed owner s).boundary = [])
    (i : Fin 3) (r : Fin 6) (w : Fin 2 → CompleteWord 2) :
    ((regionalSize owner s r : ℝ) / (denominator : ℝ) ^ 4) *
      RegionRealization.parentMixture (parent_total s)
        (regionalSize owner s) (splitCount owner s) (integerProfile owner s i) r w =
    ((seed owner s).region.getD r.val 0 : ℝ) / (denominator : ℝ) ^ 4 *
      ∑ c : Split s, (splitWeight owner s r c : ℝ) *
        (childMarginal owner s r c i (w 0) : ℝ) *
        (childMarginal owner s r (complement (parent_total s r) c) i (w 1) : ℝ) := by sorry
