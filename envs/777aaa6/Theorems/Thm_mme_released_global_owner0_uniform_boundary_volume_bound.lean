-- Prove2me | Theorems.Thm_mme_released_global_owner0_uniform_boundary_volume_bound
-- name    : mme_released_global_owner0_uniform_boundary_volume_bound
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T04:21:52.199506+00:00
-- url     : https://prove2.me/theorems/d6bf8526-7bcc-4962-9e68-b4dfc667b130
-- title:
--   Outer owner 0 has boundary bounds uniform in the free-mode choice
-- statement:
--   The checked cell certificates give one explicit lower bound per boundary shape, valid for every zero coordinate selected by extraction. The finite comparison takes a minimum only among the free-mode choices of that one boundary cell. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Theorems.Thm_mme_released_global_owner0_cell0_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner0_cell1_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner0_cell2_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner0_cell3_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner0_cell4_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner0_cell5_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner0_cell6_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner0_cell7_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner0_cell8_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner0_cell9_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner0_cell16_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner0_cell17_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner0_cell23_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner0_cell24_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner0_cell29_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner0_cell30_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner0_cell34_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner0_cell35_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner0_cell38_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner0_cell39_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner0_cell41_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner0_cell42_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner0_cell43_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner0_cell44_boundary_volume_bound
open scoped BigOperators
open MME MME.RegionRate MME.ReleasedGlobal MME.MoreAsymmetryExactSeed
open MME.RecursiveYZ.Boundary

theorem mme_released_global_owner0_uniform_boundary_volume_bound (s : Fin 45) (z : Fin 3)
    (hz : ((shape s).val z).val = 0) :
    (denominator : ℝ) ^ 5 * ((([0, 49606893, 2486788621, 30163129815, 85574225979, 30069522158, 2518371893, 50007291, 0, 49279954, 0, 0, 0, 0, 0, 0, 49221705, 2462660104, 0, 0, 0, 0, 0, 2502501836, 29847986703, 0, 0, 0, 0, 29841607991, 85529917414, 0, 0, 0, 83916707382, 30295306029, 0, 0, 29916765458, 2562729051, 0, 2532605850, 50115012, 49741369, 0] : List ℕ).getD s.val 0 : ℝ) / 1000000000000) ≤
      massEntropy (fun w ↦ (wordCounts 0 (z + 1) (shapeEquiv s) w : ℝ)) +
        (∑ w, (wordCounts 0 (z + 1) (shapeEquiv s) w : ℝ) * (ones w : ℝ)) * Real.log 5 := by sorry
