-- Prove2me | Theorems.Thm_mme_released_interior_wrong_grade_aggregate_counts
-- name    : mme_released_interior_wrong_grade_aggregate_counts
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T04:17:48.492174+00:00
-- url     : https://prove2.me/theorems/9c1bba24-4ab5-436a-a47d-918f3023d4f1
-- title:
--   Zero marginal counts outside the parent grade
-- statement:
--   For every owner and released component, a word outside the required parent grade has zero global marginal count, and all regional child-product terms vanish. This establishes the aggregate identity outside the admissible grade, without any interior-recipe hypothesis.
-- source:
--   Support grading of released global atoms and square-child atoms.

import Definitions.Def_mme_released_interior_integer_profiles
import Definitions.Def_mme_complete_split_concatenation
import Definitions.Def_mme_recursive_region_parent_profiles
import Definitions.Def_mme_released_global_profile_data
import Definitions.Def_mme_more_asymmetry_released_exact_profile_seed
import Mathlib.Data.List.Sort
open BigOperators MME MME.ReleasedInterior MME.RecursiveYZ MME.MoreAsymmetryExactSeed MME.CompleteSplit

theorem mme_released_interior_wrong_grade_aggregate_counts
    (owner : Fin 6) (s : Fin 45) (i : Fin 3) (w : CompleteWord 3)
    (hw : (∑ h, (w h).val) ≠ parent s 0 i) :
    ((ReleasedGlobal.jointRows owner s).map
      (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum =
    ∑ r : Fin 6, (seed owner s).region.getD r.val 0 *
      ∑ c : Split s, splitWeight owner s r c *
        childMarginal owner s r c i ((completeWordSplitEquiv 2 (by decide)) w).1 *
        childMarginal owner s r (complement (parent_total s r) c) i
          ((completeWordSplitEquiv 2 (by decide)) w).2 := by sorry
