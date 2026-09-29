-- Prove2me | Theorems.Thm_mme_released_interior_owner2_shape13_region_parent_compatibility
-- name    : mme_released_interior_owner2_shape13_region_parent_compatibility
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T08:47:13.99177+00:00
-- url     : https://prove2.me/theorems/8f09e11f-d59b-4696-a83f-df3f3e8cabf8
-- title:
--   Parent compatibility margins for owner 2, recipe 13
-- statement:
--   Every nonempty region of this released interior recipe has parent-mixture entropy minus normalized compatibility entropy at least two fifths, in both directions. The proof uses unchanged exact rational certificates from the locally checked owner proof, separated by recipe to fit remote compilation limits. The full matrix exponent bound remains a separate obligation.
-- source:
--   Released integer profiles and kernel-checked rational entropy certificates.

import Theorems.Thm_mme_rational_parent_compatibility_certificate
import Definitions.Def_mme_released_interior_integer_profiles
open scoped BigOperators
open MME MME.RegionRate MME.RegionRealization MME.RecursiveYZ MME.ReleasedInterior
open MME.CompleteSplit

theorem mme_released_interior_owner2_shape13_region_parent_compatibility
    (r : Fin 6) (i : Fin 2)
    (hn : 0 < (seed 2 13).region.getD r.val 0) :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 13) (regionalSize 2 13)
        (splitCount 2 13) (integerProfile 2 13 (yzMode i)) r) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 13) i ⟨r, c⟩)
          (fun c => c.val (yzMode i))
          (fun c w => integerProfile 2 13 (yzMode i) ⟨r, c⟩ w) t w : ℝ) /
        regionalSize 2 13 r) := by sorry
