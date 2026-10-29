-- Prove2me | solution 1 for mme_released_interior_owner2_region_parent_compatibility
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T04:50:29.657477+00:00
-- url     : https://prove2.me/submissions/4c26d46d-7db1-41c7-ad27-fd405bf27bd3

import Theorems.Thm_mme_released_interior_owner2_shape10_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner2_shape11_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner2_shape12_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner2_shape13_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner2_shape14_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner2_shape15_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner2_shape18_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner2_shape19_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner2_shape20_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner2_shape21_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner2_shape22_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner2_shape25_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner2_shape26_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner2_shape27_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner2_shape28_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner2_shape31_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner2_shape32_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner2_shape33_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner2_shape36_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner2_shape37_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner2_shape40_region_parent_compatibility
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME MME.RegionRate MME.RegionRealization MME.RecursiveYZ MME.ReleasedInterior
open MME.CompleteSplit

theorem solution
    (s : Fin 45) (r : Fin 6) (i : Fin 2) (hi : (seed 2 s).boundary = [])
    (hn : 0 < (seed 2 s).region.getD r.val 0) :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total s) (regionalSize 2 s)
        (splitCount 2 s) (integerProfile 2 s (yzMode i)) r) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent s) i ⟨r, c⟩)
          (fun c => c.val (yzMode i))
          (fun c w => integerProfile 2 s (yzMode i) ⟨r, c⟩ w) t w : ℝ) /
        regionalSize 2 s r) := by
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
  · exact mme_released_interior_owner2_shape10_region_parent_compatibility r i hn
  · exact mme_released_interior_owner2_shape11_region_parent_compatibility r i hn
  · exact mme_released_interior_owner2_shape12_region_parent_compatibility r i hn
  · exact mme_released_interior_owner2_shape13_region_parent_compatibility r i hn
  · exact mme_released_interior_owner2_shape14_region_parent_compatibility r i hn
  · exact mme_released_interior_owner2_shape15_region_parent_compatibility r i hn
  · exact absurd hi (by decide +kernel)
  · exact absurd hi (by decide +kernel)
  · exact mme_released_interior_owner2_shape18_region_parent_compatibility r i hn
  · exact mme_released_interior_owner2_shape19_region_parent_compatibility r i hn
  · exact mme_released_interior_owner2_shape20_region_parent_compatibility r i hn
  · exact mme_released_interior_owner2_shape21_region_parent_compatibility r i hn
  · exact mme_released_interior_owner2_shape22_region_parent_compatibility r i hn
  · exact absurd hi (by decide +kernel)
  · exact absurd hi (by decide +kernel)
  · exact mme_released_interior_owner2_shape25_region_parent_compatibility r i hn
  · exact mme_released_interior_owner2_shape26_region_parent_compatibility r i hn
  · exact mme_released_interior_owner2_shape27_region_parent_compatibility r i hn
  · exact mme_released_interior_owner2_shape28_region_parent_compatibility r i hn
  · exact absurd hi (by decide +kernel)
  · exact absurd hi (by decide +kernel)
  · exact mme_released_interior_owner2_shape31_region_parent_compatibility r i hn
  · exact mme_released_interior_owner2_shape32_region_parent_compatibility r i hn
  · exact mme_released_interior_owner2_shape33_region_parent_compatibility r i hn
  · exact absurd hi (by decide +kernel)
  · exact absurd hi (by decide +kernel)
  · exact mme_released_interior_owner2_shape36_region_parent_compatibility r i hn
  · exact mme_released_interior_owner2_shape37_region_parent_compatibility r i hn
  · exact absurd hi (by decide +kernel)
  · exact absurd hi (by decide +kernel)
  · exact mme_released_interior_owner2_shape40_region_parent_compatibility r i hn
  · exact absurd hi (by decide +kernel)
  · exact absurd hi (by decide +kernel)
  · exact absurd hi (by decide +kernel)
  · exact absurd hi (by decide +kernel)
