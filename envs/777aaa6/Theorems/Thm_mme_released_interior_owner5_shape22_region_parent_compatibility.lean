-- Prove2me | Theorems.Thm_mme_released_interior_owner5_shape22_region_parent_compatibility
-- name    : mme_released_interior_owner5_shape22_region_parent_compatibility
-- status  : Open
-- author  : @Robertboy18
-- created : 2026-09-23T09:14:49.945348+00:00
-- url     : https://prove2.me/theorems/2c2f6121-f9b3-4be2-b2b4-f9d7b1db80df
-- title:
--   Parent compatibility margins for owner 5, recipe 22
-- statement:
--   Every nonempty region of this released interior recipe has parent-mixture entropy minus normalized compatibility entropy at least two fifths, in both directions. The proof uses unchanged exact rational certificates from the locally checked owner proof, separated by recipe to fit remote compilation limits. The full matrix exponent bound remains a separate obligation.
-- source:
--   Released integer profiles and kernel-checked rational entropy certificates.

import Theorems.Thm_mme_rational_parent_compatibility_certificate
import Definitions.Def_mme_released_interior_integer_profiles
open scoped BigOperators
open MME MME.RegionRate MME.RegionRealization MME.RecursiveYZ MME.ReleasedInterior
open MME.CompleteSplit

theorem mme_released_interior_owner5_shape22_region_parent_compatibility
    (r : Fin 6) (i : Fin 2)
    (hn : 0 < (seed 5 22).region.getD r.val 0) :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 22) (regionalSize 5 22)
        (splitCount 5 22) (integerProfile 5 22 (yzMode i)) r) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 22) i ⟨r, c⟩)
          (fun c => c.val (yzMode i))
          (fun c w => integerProfile 5 22 (yzMode i) ⟨r, c⟩ w) t w : ℝ) /
        regionalSize 5 22 r) := by sorry
