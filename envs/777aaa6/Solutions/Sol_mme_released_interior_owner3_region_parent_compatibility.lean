-- Prove2me | solution 1 for mme_released_interior_owner3_region_parent_compatibility
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T07:30:41.317322+00:00
-- url     : https://prove2.me/submissions/5007459e-93b2-4e86-8cf4-4441bc8e2ba8

import Theorems.Thm_mme_released_interior_owner3_shape10_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner3_shape11_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner3_shape12_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner3_shape13_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner3_shape14_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner3_shape15_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner3_shape18_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner3_shape19_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner3_shape20_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner3_shape21_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner3_shape22_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner3_shape25_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner3_shape26_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner3_shape27_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner3_shape28_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner3_shape31_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner3_shape32_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner3_shape33_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner3_shape36_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner3_shape37_region_parent_compatibility
import Theorems.Thm_mme_released_interior_owner3_shape40_region_parent_compatibility
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME MME.RegionRate MME.RegionRealization MME.RecursiveYZ MME.ReleasedInterior
open MME.CompleteSplit

theorem solution
    (s : Fin 45) (r : Fin 6) (i : Fin 2) (hi : (seed 3 s).boundary = [])
    (hn : 0 < (seed 3 s).region.getD r.val 0) :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total s) (regionalSize 3 s)
        (splitCount 3 s) (integerProfile 3 s (yzMode i)) r) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent s) i ⟨r, c⟩)
          (fun c => c.val (yzMode i))
          (fun c w => integerProfile 3 s (yzMode i) ⟨r, c⟩ w) t w : ℝ) /
        regionalSize 3 s r) := by
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
  · exact mme_released_interior_owner3_shape10_region_parent_compatibility r i hn
  · exact mme_released_interior_owner3_shape11_region_parent_compatibility r i hn
  · exact mme_released_interior_owner3_shape12_region_parent_compatibility r i hn
  · exact mme_released_interior_owner3_shape13_region_parent_compatibility r i hn
  · exact mme_released_interior_owner3_shape14_region_parent_compatibility r i hn
  · exact mme_released_interior_owner3_shape15_region_parent_compatibility r i hn
  · exact absurd hi (by decide +kernel)
  · exact absurd hi (by decide +kernel)
  · exact mme_released_interior_owner3_shape18_region_parent_compatibility r i hn
  · exact mme_released_interior_owner3_shape19_region_parent_compatibility r i hn
  · exact mme_released_interior_owner3_shape20_region_parent_compatibility r i hn
  · exact mme_released_interior_owner3_shape21_region_parent_compatibility r i hn
  · exact mme_released_interior_owner3_shape22_region_parent_compatibility r i hn
  · exact absurd hi (by decide +kernel)
  · exact absurd hi (by decide +kernel)
  · exact mme_released_interior_owner3_shape25_region_parent_compatibility r i hn
  · exact mme_released_interior_owner3_shape26_region_parent_compatibility r i hn
  · exact mme_released_interior_owner3_shape27_region_parent_compatibility r i hn
  · exact mme_released_interior_owner3_shape28_region_parent_compatibility r i hn
  · exact absurd hi (by decide +kernel)
  · exact absurd hi (by decide +kernel)
  · exact mme_released_interior_owner3_shape31_region_parent_compatibility r i hn
  · exact mme_released_interior_owner3_shape32_region_parent_compatibility r i hn
  · exact mme_released_interior_owner3_shape33_region_parent_compatibility r i hn
  · exact absurd hi (by decide +kernel)
  · exact absurd hi (by decide +kernel)
  · exact mme_released_interior_owner3_shape36_region_parent_compatibility r i hn
  · exact mme_released_interior_owner3_shape37_region_parent_compatibility r i hn
  · exact absurd hi (by decide +kernel)
  · exact absurd hi (by decide +kernel)
  · exact mme_released_interior_owner3_shape40_region_parent_compatibility r i hn
  · exact absurd hi (by decide +kernel)
  · exact absurd hi (by decide +kernel)
  · exact absurd hi (by decide +kernel)
  · exact absurd hi (by decide +kernel)
