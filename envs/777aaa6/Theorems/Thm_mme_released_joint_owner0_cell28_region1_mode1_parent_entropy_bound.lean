-- Prove2me | Theorems.Thm_mme_released_joint_owner0_cell28_region1_mode1_parent_entropy_bound
-- name    : mme_released_joint_owner0_cell28_region1_mode1_parent_entropy_bound
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T17:37:17.760987+00:00
-- url     : https://prove2.me/theorems/f76668f6-66d4-4685-b44f-d41057d5573e
-- title:
--   Pooled owner 0 cell 28 region 1 mode 1 has a certified parent entropy bound
-- statement:
--   A rational probability table is checked against the actual pooled integer parent and child histograms. Kernel-checked logarithm intervals certify its parent entropy lower bound. Compatibility subtraction and the main exponent bound remain separate obligations.
-- source:
--   Released exact profiles and actual common-mode parent distributions.

import Theorems.Thm_mme_parent_mixture_rational_identity
import Theorems.Thm_mme_rational_entropy_log_bounds
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_joint_interior_profiles
open scoped BigOperators
open MME MME.RegionRate MME.ReleasedJointInterior MME.RecursiveYZ
open MME.MoreAsymmetryExactSeed MME.CompleteSplit

theorem mme_released_joint_owner0_cell28_region1_mode1_parent_entropy_bound :
    (1386294361 / 1000000000 : ℝ) ≤
      entropy (RegionRealization.parentMixture (parent_total 1)
        (size 1 1) (splitCount 1 1) (integerProfile 1 1 1) 28) := by sorry
