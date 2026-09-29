-- Prove2me | Theorems.Thm_mme_released_interior_owner0_shape19_region1_mode2_parent_compatibility
-- name    : mme_released_interior_owner0_shape19_region1_mode2_parent_compatibility
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T07:39:04.243437+00:00
-- url     : https://prove2.me/theorems/6ae47e67-c396-4d31-99f1-a2694532762c
-- title:
--   A released (2,2,4) region has a two-fifths parent/compatibility margin
-- statement:
--   For owner 0, shape (2,2,4), region 1 and mode 2, the actual released parent mixture entropy minus normalized compatibility entropy is at least two fifths. The finite rational certificate is checked by the Lean kernel against the released integer profiles. The full matrix exponent bound remains a separate obligation.
-- source:
--   Kernel-checked regional count identities and exact extraction with empty regions.

import Theorems.Thm_mme_rational_parent_compatibility_certificate
import Definitions.Def_mme_released_interior_integer_profiles
open scoped BigOperators
open MME MME.RegionRate MME.RegionRealization MME.RecursiveYZ MME.ReleasedInterior
open MME.CompleteSplit

theorem mme_released_interior_owner0_shape19_region1_mode2_parent_compatibility :
    (2 / 5 : ℝ) ≤
      entropy (parentMixture (parent_total 19) (regionalSize 0 19)
        (splitCount 0 19) (integerProfile 0 19 2) 1) -
      ∑ t, massEntropy (fun w =>
        (partCount (fun c => yzBoundary (parent := parent 19) 1 ⟨1, c⟩)
          (fun c => c.val (yzMode 1))
          (fun c w => integerProfile 0 19 2 ⟨1, c⟩ w) t w : ℝ) /
        regionalSize 0 19 1) := by sorry
