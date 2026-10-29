-- Prove2me | solution 1 for mme_released_interior_owner1_region_parent_compatibility
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T04:48:04.125987+00:00
-- url     : https://prove2.me/submissions/94fa2d09-70b2-4e61-83f0-0e8ce09b34ac

import Theorems.Thm_mme_released_interior_owner1_shape10_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner1_shape11_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner1_shape12_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner1_shape13_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner1_shape14_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner1_shape15_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner1_shape18_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner1_shape19_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner1_shape20_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner1_shape21_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner1_shape22_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner1_shape25_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner1_shape26_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner1_shape27_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner1_shape28_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner1_shape31_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner1_shape32_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner1_shape33_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner1_shape36_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner1_shape37_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner1_shape40_region_parent_compatibility
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME MME.RegionRate MME.RegionRealization MME.RecursiveYZ MME.ReleasedInterior
open MME.CompleteSplit

theorem solution
    (s : Fin 45) (r : Fin 6) (i : Fin 2) (hi : (seed 1 s).boundary = [])
    (hn : 0 < (seed 1 s).region.getD r.val 0) :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total s) (regionalSize 1 s)
        (splitCount 1 s) (integerProfile 1 s (yzMode i)) r) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent s) i ⟨r, c⟩)
          (fun c => c.val (yzMode i))
          (fun c w => integerProfile 1 s (yzMode i) ⟨r, c⟩ w) t w : ℝ) /
        regionalSize 1 s r) := by
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
  · exact mme_released_interior_owner1_shape10_region_parent_compatibility r i hn
  · exact mme_released_interior_owner1_shape11_region_parent_compatibility r i hn
  · exact mme_released_interior_owner1_shape12_region_parent_compatibility r i hn
  · exact mme_released_interior_owner1_shape13_region_parent_compatibility r i hn
  · exact mme_released_interior_owner1_shape14_region_parent_compatibility r i hn
  · exact mme_released_interior_owner1_shape15_region_parent_compatibility r i hn
  · exact absurd hi (by decide +kernel)
  · exact absurd hi (by decide +kernel)
  · exact mme_released_interior_owner1_shape18_region_parent_compatibility r i hn
  · exact mme_released_interior_owner1_shape19_region_parent_compatibility r i hn
  · exact mme_released_interior_owner1_shape20_region_parent_compatibility r i hn
  · exact mme_released_interior_owner1_shape21_region_parent_compatibility r i hn
  · exact mme_released_interior_owner1_shape22_region_parent_compatibility r i hn
  · exact absurd hi (by decide +kernel)
  · exact absurd hi (by decide +kernel)
  · exact mme_released_interior_owner1_shape25_region_parent_compatibility r i hn
  · exact mme_released_interior_owner1_shape26_region_parent_compatibility r i hn
  · exact mme_released_interior_owner1_shape27_region_parent_compatibility r i hn
  · exact mme_released_interior_owner1_shape28_region_parent_compatibility r i hn
  · exact absurd hi (by decide +kernel)
  · exact absurd hi (by decide +kernel)
  · exact mme_released_interior_owner1_shape31_region_parent_compatibility r i hn
  · exact mme_released_interior_owner1_shape32_region_parent_compatibility r i hn
  · exact mme_released_interior_owner1_shape33_region_parent_compatibility r i hn
  · exact absurd hi (by decide +kernel)
  · exact absurd hi (by decide +kernel)
  · exact mme_released_interior_owner1_shape36_region_parent_compatibility r i hn
  · exact mme_released_interior_owner1_shape37_region_parent_compatibility r i hn
  · exact absurd hi (by decide +kernel)
  · exact absurd hi (by decide +kernel)
  · exact mme_released_interior_owner1_shape40_region_parent_compatibility r i hn
  · exact absurd hi (by decide +kernel)
  · exact absurd hi (by decide +kernel)
  · exact absurd hi (by decide +kernel)
  · exact absurd hi (by decide +kernel)
