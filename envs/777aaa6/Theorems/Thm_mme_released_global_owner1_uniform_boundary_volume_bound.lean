-- Prove2me | Theorems.Thm_mme_released_global_owner1_uniform_boundary_volume_bound
-- name    : mme_released_global_owner1_uniform_boundary_volume_bound
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T04:40:39.279984+00:00
-- url     : https://prove2.me/theorems/6bad83fe-4703-4404-bbd2-193a8c989be9
-- title:
--   Outer owner 1 has boundary bounds uniform in the free-mode choice
-- statement:
--   The checked cell certificates give one explicit lower bound per boundary shape, valid for every zero coordinate selected by extraction. The finite comparison takes a minimum only among the free-mode choices of that one boundary cell. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Theorems.Thm_mme_released_global_owner1_cell0_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner1_cell1_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner1_cell2_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner1_cell3_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner1_cell4_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner1_cell5_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner1_cell6_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner1_cell7_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner1_cell8_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner1_cell9_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner1_cell16_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner1_cell17_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner1_cell23_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner1_cell24_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner1_cell29_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner1_cell30_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner1_cell34_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner1_cell35_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner1_cell38_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner1_cell39_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner1_cell41_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner1_cell42_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner1_cell43_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner1_cell44_boundary_volume_bound
open scoped BigOperators
open MME MME.RegionRate MME.ReleasedGlobal MME.MoreAsymmetryExactSeed
open MME.RecursiveYZ.Boundary

theorem mme_released_global_owner1_uniform_boundary_volume_bound (s : Fin 45) (z : Fin 3)
    (hz : ((shape s).val z).val = 0) :
    (denominator : ℝ) ^ 5 * ((([0, 49820906, 2487243242, 30161916128, 85578723810, 30067934123, 2518649441, 49990101, 0, 49245656, 0, 0, 0, 0, 0, 0, 49294690, 2462639231, 0, 0, 0, 0, 0, 2501614000, 29848152952, 0, 0, 0, 0, 29843357938, 85534235882, 0, 0, 0, 83900425454, 30294238639, 0, 0, 29918440055, 2562591995, 0, 2532957755, 50087514, 49684414, 0] : List ℕ).getD s.val 0 : ℝ) / 1000000000000) ≤
      massEntropy (fun w ↦ (wordCounts 1 (z + 1) (shapeEquiv s) w : ℝ)) +
        (∑ w, (wordCounts 1 (z + 1) (shapeEquiv s) w : ℝ) * (ones w : ℝ)) * Real.log 5 := by sorry
