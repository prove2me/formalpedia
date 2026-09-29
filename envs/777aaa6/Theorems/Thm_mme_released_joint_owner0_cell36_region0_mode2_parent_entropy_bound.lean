-- Prove2me | Theorems.Thm_mme_released_joint_owner0_cell36_region0_mode2_parent_entropy_bound
-- name    : mme_released_joint_owner0_cell36_region0_mode2_parent_entropy_bound
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T12:18:14.98395+00:00
-- url     : https://prove2.me/theorems/1e293f0d-8577-433c-9df3-46479e3ea3a2
-- title:
--   Pooled owner 0 cell 36 region 0 mode 2 has a certified parent entropy bound
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

theorem mme_released_joint_owner0_cell36_region0_mode2_parent_entropy_bound :
    (1903207513 / 1000000000 : ℝ) ≤
      entropy (RegionRealization.parentMixture (parent_total 0)
        (size 0 1) (splitCount 0 1) (integerProfile 0 1 2) 36) := by sorry
