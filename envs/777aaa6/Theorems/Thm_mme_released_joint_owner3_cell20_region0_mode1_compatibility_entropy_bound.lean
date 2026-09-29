-- Prove2me | Theorems.Thm_mme_released_joint_owner3_cell20_region0_mode1_compatibility_entropy_bound
-- name    : mme_released_joint_owner3_cell20_region0_mode1_compatibility_entropy_bound
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T13:42:25.720024+00:00
-- url     : https://prove2.me/theorems/51ae45b0-407b-43ec-9ed5-46a26d279e08
-- title:
--   Pooled owner 3 cell 20 region 0 mode 1 has a certified compatibility entropy bound
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

theorem mme_released_joint_owner3_cell20_region0_mode1_compatibility_entropy_bound :
    ((∑ c : MME.RecursiveThinSplit.Split 4 (parent 0 155),
        if yzBoundary 0 ⟨155, c⟩ then massEntropy (fun w ↦ ((integerProfile 0 1 1) ⟨155, c⟩ w : ℝ)) else 0) +
      ∑ a : Fin 5, massEntropy (fun w ↦ ∑ c : MME.RecursiveThinSplit.Split 4 (parent 0 155),
        if ¬ yzBoundary 0 ⟨155, c⟩ ∧ c.val 1 = a then ((integerProfile 0 1 1) ⟨155, c⟩ w : ℝ) else 0)) ≤
      (denominator : ℝ) ^ 5 * (25075235847 / 1000000000000 : ℝ) := by sorry
