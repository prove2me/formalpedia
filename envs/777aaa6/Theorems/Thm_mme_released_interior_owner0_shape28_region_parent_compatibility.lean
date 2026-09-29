-- Prove2me | Theorems.Thm_mme_released_interior_owner0_shape28_region_parent_compatibility
-- name    : mme_released_interior_owner0_shape28_region_parent_compatibility
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T08:28:57.605131+00:00
-- url     : https://prove2.me/theorems/7a62e2e9-9a21-4c56-b79a-2ca8b93a9128
-- title:
--   Parent compatibility margins for owner 0, recipe 28
-- statement:
--   Every nonempty region of this released interior recipe has parent-mixture entropy minus normalized compatibility entropy at least two fifths, in both directions. The proof uses unchanged exact rational certificates from the locally checked owner proof, separated by recipe to fit remote compilation limits. The full matrix exponent bound remains a separate obligation.
-- source:
--   Released integer profiles and kernel-checked rational entropy certificates.

import Theorems.Thm_mme_rational_parent_compatibility_certificate
import Definitions.Def_mme_released_interior_integer_profiles
open scoped BigOperators
open MME MME.RegionRate MME.RegionRealization MME.RecursiveYZ MME.ReleasedInterior
open MME.CompleteSplit

theorem mme_released_interior_owner0_shape28_region_parent_compatibility
    (r : Fin 6) (i : Fin 2)
    (hn : 0 < (seed 0 28).region.getD r.val 0) :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 28) (regionalSize 0 28)
        (splitCount 0 28) (integerProfile 0 28 (yzMode i)) r) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 28) i ⟨r, c⟩)
          (fun c => c.val (yzMode i))
          (fun c w => integerProfile 0 28 (yzMode i) ⟨r, c⟩ w) t w : ℝ) /
        regionalSize 0 28 r) := by sorry
