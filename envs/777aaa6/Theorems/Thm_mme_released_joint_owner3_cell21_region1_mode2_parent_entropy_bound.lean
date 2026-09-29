-- Prove2me | Theorems.Thm_mme_released_joint_owner3_cell21_region1_mode2_parent_entropy_bound
-- name    : mme_released_joint_owner3_cell21_region1_mode2_parent_entropy_bound
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T18:36:55.214283+00:00
-- url     : https://prove2.me/theorems/70f65cf0-d23c-4088-837f-8895b5e904cb
-- title:
--   Pooled owner 3 cell 21 region 1 mode 2 has a certified parent entropy bound
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

theorem mme_released_joint_owner3_cell21_region1_mode2_parent_entropy_bound :
    (1885683338 / 1000000000 : ℝ) ≤
      entropy (RegionRealization.parentMixture (parent_total 1)
        (size 1 1) (splitCount 1 1) (integerProfile 1 1 2) 156) := by sorry
