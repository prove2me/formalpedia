-- Prove2me | solution 1 for mme_released_interior_owner0_region_parent_compatibility
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T01:32:13.845983+00:00
-- url     : https://prove2.me/submissions/336bf9e9-2700-47c9-9c29-3f185e50a72b

import Theorems.Thm_mme_released_interior_owner0_shape10_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner0_shape11_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner0_shape12_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner0_shape13_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner0_shape14_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner0_shape15_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner0_shape18_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner0_shape19_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner0_shape20_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner0_shape21_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner0_shape22_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner0_shape25_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner0_shape26_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner0_shape27_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner0_shape28_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner0_shape31_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner0_shape32_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner0_shape33_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner0_shape36_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner0_shape37_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner0_shape40_region_parent_compatibility
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME MME.RegionRate MME.RegionRealization MME.RecursiveYZ MME.ReleasedInterior
open MME.CompleteSplit

theorem solution
    (s : Fin 45) (r : Fin 6) (i : Fin 2) (hi : (seed 0 s).boundary = [])
    (hn : 0 < (seed 0 s).region.getD r.val 0) :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total s) (regionalSize 0 s)
        (splitCount 0 s) (integerProfile 0 s (yzMode i)) r) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent s) i ⟨r, c⟩)
          (fun c => c.val (yzMode i))
          (fun c w => integerProfile 0 s (yzMode i) ⟨r, c⟩ w) t w : ℝ) /
        regionalSize 0 s r) := by
  fin_cases s
  · exact absurd hi (by decide +kernel)
  · exact absurd hi (by decide +kernel)
  · exact absurd hi (by decide +kernel)
  · exact absurd hi (by decide +kernel)
  · exact absurd hi (by decide +kernel)
  · exact absurd hi (by decide +kernel)
  · exact absurd hi (by decide +kernel)
  · exact absurd hi (by decide +kernel)
  · exact absurd hi (by decide +kernel)
  · exact absurd hi (by decide +kernel)
  · exact mme_released_interior_owner0_shape10_region_parent_compatibility r i hn
  · exact mme_released_interior_owner0_shape11_region_parent_compatibility r i hn
  · exact mme_released_interior_owner0_shape12_region_parent_compatibility r i hn
  · exact mme_released_interior_owner0_shape13_region_parent_compatibility r i hn
  · exact mme_released_interior_owner0_shape14_region_parent_compatibility r i hn
  · exact mme_released_interior_owner0_shape15_region_parent_compatibility r i hn
  · exact absurd hi (by decide +kernel)
  · exact absurd hi (by decide +kernel)
  · exact mme_released_interior_owner0_shape18_region_parent_compatibility r i hn
  · exact mme_released_interior_owner0_shape19_region_parent_compatibility r i hn
  · exact mme_released_interior_owner0_shape20_region_parent_compatibility r i hn
  · exact mme_released_interior_owner0_shape21_region_parent_compatibility r i hn
  · exact mme_released_interior_owner0_shape22_region_parent_compatibility r i hn
  · exact absurd hi (by decide +kernel)
  · exact absurd hi (by decide +kernel)
  · exact mme_released_interior_owner0_shape25_region_parent_compatibility r i hn
  · exact mme_released_interior_owner0_shape26_region_parent_compatibility r i hn
  · exact mme_released_interior_owner0_shape27_region_parent_compatibility r i hn
  · exact mme_released_interior_owner0_shape28_region_parent_compatibility r i hn
  · exact absurd hi (by decide +kernel)
  · exact absurd hi (by decide +kernel)
  · exact mme_released_interior_owner0_shape31_region_parent_compatibility r i hn
  · exact mme_released_interior_owner0_shape32_region_parent_compatibility r i hn
  · exact mme_released_interior_owner0_shape33_region_parent_compatibility r i hn
  · exact absurd hi (by decide +kernel)
  · exact absurd hi (by decide +kernel)
  · exact mme_released_interior_owner0_shape36_region_parent_compatibility r i hn
  · exact mme_released_interior_owner0_shape37_region_parent_compatibility r i hn
  · exact absurd hi (by decide +kernel)
  · exact absurd hi (by decide +kernel)
  · exact mme_released_interior_owner0_shape40_region_parent_compatibility r i hn
  · exact absurd hi (by decide +kernel)
  · exact absurd hi (by decide +kernel)
  · exact absurd hi (by decide +kernel)
  · exact absurd hi (by decide +kernel)
