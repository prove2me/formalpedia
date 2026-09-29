-- Prove2me | Theorems.Thm_mme_released_interior_owner2_shape21_region_parent_compatibility
-- name    : mme_released_interior_owner2_shape21_region_parent_compatibility
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T08:49:59.592982+00:00
-- url     : https://prove2.me/theorems/91378707-3bdf-4410-845a-041f076d2d74
-- title:
--   Parent compatibility margins for owner 2, recipe 21
-- statement:
--   Every nonempty region of this released interior recipe has parent-mixture entropy minus normalized compatibility entropy at least two fifths, in both directions. The proof uses unchanged exact rational certificates from the locally checked owner proof, separated by recipe to fit remote compilation limits. The full matrix exponent bound remains a separate obligation.
-- source:
--   Released integer profiles and kernel-checked rational entropy certificates.

import Theorems.Thm_mme_rational_parent_compatibility_certificate
import Definitions.Def_mme_released_interior_integer_profiles
open scoped BigOperators
open MME MME.RegionRate MME.RegionRealization MME.RecursiveYZ MME.ReleasedInterior
open MME.CompleteSplit

theorem mme_released_interior_owner2_shape21_region_parent_compatibility
    (r : Fin 6) (i : Fin 2)
    (hn : 0 < (seed 2 21).region.getD r.val 0) :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 21) (regionalSize 2 21)
        (splitCount 2 21) (integerProfile 2 21 (yzMode i)) r) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 21) i ⟨r, c⟩)
          (fun c => c.val (yzMode i))
          (fun c w => integerProfile 2 21 (yzMode i) ⟨r, c⟩ w) t w : ℝ) /
        regionalSize 2 21 r) := by sorry
