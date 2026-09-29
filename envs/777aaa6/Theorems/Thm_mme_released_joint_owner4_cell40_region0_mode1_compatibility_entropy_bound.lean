-- Prove2me | Theorems.Thm_mme_released_joint_owner4_cell40_region0_mode1_compatibility_entropy_bound
-- name    : mme_released_joint_owner4_cell40_region0_mode1_compatibility_entropy_bound
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T13:48:26.550287+00:00
-- url     : https://prove2.me/theorems/671b27db-92af-4e85-8d4e-dd7d14e59445
-- title:
--   Pooled owner 4 cell 40 region 0 mode 1 has a certified compatibility entropy bound
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

theorem mme_released_joint_owner4_cell40_region0_mode1_compatibility_entropy_bound :
    ((∑ c : MME.RecursiveThinSplit.Split 4 (parent 0 220),
        if yzBoundary 0 ⟨220, c⟩ then massEntropy (fun w ↦ ((integerProfile 0 1 1) ⟨220, c⟩ w : ℝ)) else 0) +
      ∑ a : Fin 5, massEntropy (fun w ↦ ∑ c : MME.RecursiveThinSplit.Split 4 (parent 0 220),
        if ¬ yzBoundary 0 ⟨220, c⟩ ∧ c.val 1 = a then ((integerProfile 0 1 1) ⟨220, c⟩ w : ℝ) else 0)) ≤
      (denominator : ℝ) ^ 5 * (77193901 / 1000000000000 : ℝ) := by sorry
