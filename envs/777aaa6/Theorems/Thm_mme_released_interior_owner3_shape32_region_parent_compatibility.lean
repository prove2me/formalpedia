-- Prove2me | Theorems.Thm_mme_released_interior_owner3_shape32_region_parent_compatibility
-- name    : mme_released_interior_owner3_shape32_region_parent_compatibility
-- status  : Open
-- author  : @Robertboy18
-- created : 2026-09-23T09:09:03.508711+00:00
-- url     : https://prove2.me/theorems/31eaa2e6-fd87-4dc4-b78e-ed3b975dd3d0
-- title:
--   Parent compatibility margins for owner 3, recipe 32
-- statement:
--   Every nonempty region of this released interior recipe has parent-mixture entropy minus normalized compatibility entropy at least two fifths, in both directions. The proof uses unchanged exact rational certificates from the locally checked owner proof, separated by recipe to fit remote compilation limits. The full matrix exponent bound remains a separate obligation.
-- source:
--   Released integer profiles and kernel-checked rational entropy certificates.

import Theorems.Thm_mme_rational_parent_compatibility_certificate
import Definitions.Def_mme_released_interior_integer_profiles
open scoped BigOperators
open MME MME.RegionRate MME.RegionRealization MME.RecursiveYZ MME.ReleasedInterior
open MME.CompleteSplit

theorem mme_released_interior_owner3_shape32_region_parent_compatibility
    (r : Fin 6) (i : Fin 2)
    (hn : 0 < (seed 3 32).region.getD r.val 0) :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 32) (regionalSize 3 32)
        (splitCount 3 32) (integerProfile 3 32 (yzMode i)) r) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 32) i ⟨r, c⟩)
          (fun c => c.val (yzMode i))
          (fun c w => integerProfile 3 32 (yzMode i) ⟨r, c⟩ w) t w : ℝ) /
        regionalSize 3 32 r) := by sorry
