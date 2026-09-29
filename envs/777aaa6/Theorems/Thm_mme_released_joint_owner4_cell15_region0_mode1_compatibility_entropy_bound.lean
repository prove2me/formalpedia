-- Prove2me | Theorems.Thm_mme_released_joint_owner4_cell15_region0_mode1_compatibility_entropy_bound
-- name    : mme_released_joint_owner4_cell15_region0_mode1_compatibility_entropy_bound
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T13:46:01.01296+00:00
-- url     : https://prove2.me/theorems/a3debff8-26ad-4a25-8432-b296ccdfa3b2
-- title:
--   Pooled owner 4 cell 15 region 0 mode 1 has a certified compatibility entropy bound
-- statement:
--   A rational mass table is checked against the actual integer compatibility histograms in one parent component. Boundary cells remain separate and interior cells are pooled by the retained coordinate. Kernel-checked logarithm intervals certify an upper bound for their homogeneous entropy sum. Regional aggregation and the main exponent bound remain separate obligations.
-- source:
--   Released exact profiles and actual parent-component compatibility classes.

import Theorems.Thm_mme_rational_scaled_mass_entropy_sum_upper_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_joint_interior_profiles
import Definitions.Def_mme_regional_split_entropy_data
open scoped BigOperators Classical
open MME MME.RegionRate MME.ReleasedJointInterior MME.RecursiveYZ
open MME.MoreAsymmetryExactSeed MME.CompleteSplit

theorem mme_released_joint_owner4_cell15_region0_mode1_compatibility_entropy_bound :
    ((∑ c : MME.RecursiveThinSplit.Split 4 (parent 0 195),
        if yzBoundary 0 ⟨195, c⟩ then massEntropy (fun w ↦ ((integerProfile 0 1 1) ⟨195, c⟩ w : ℝ)) else 0) +
      ∑ a : Fin 5, massEntropy (fun w ↦ ∑ c : MME.RecursiveThinSplit.Split 4 (parent 0 195),
        if ¬ yzBoundary 0 ⟨195, c⟩ ∧ c.val 1 = a then ((integerProfile 0 1 1) ⟨195, c⟩ w : ℝ) else 0)) ≤
      (denominator : ℝ) ^ 5 * (76414217 / 1000000000000 : ℝ) := by sorry
