-- Prove2me | Theorems.Thm_mme_released_global_owner5_uniform_boundary_volume_bound
-- name    : mme_released_global_owner5_uniform_boundary_volume_bound
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T05:49:42.466755+00:00
-- url     : https://prove2.me/theorems/c70d3556-8bd1-45ce-89c8-9ff9cb650678
-- title:
--   Outer owner 5 has boundary bounds uniform in the free-mode choice
-- statement:
--   The checked cell certificates give one explicit lower bound per boundary shape, valid for every zero coordinate selected by extraction. The finite comparison takes a minimum only among the free-mode choices of that one boundary cell. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Theorems.Thm_mme_released_global_owner5_cell0_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner5_cell1_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner5_cell2_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner5_cell3_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner5_cell4_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner5_cell5_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner5_cell6_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner5_cell7_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner5_cell8_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner5_cell9_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner5_cell16_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner5_cell17_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner5_cell23_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner5_cell24_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner5_cell29_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner5_cell30_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner5_cell34_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner5_cell35_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner5_cell38_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner5_cell39_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner5_cell41_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner5_cell42_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner5_cell43_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner5_cell44_boundary_volume_bound
open scoped BigOperators
open MME MME.RegionRate MME.ReleasedGlobal MME.MoreAsymmetryExactSeed
open MME.RecursiveYZ.Boundary

theorem mme_released_global_owner5_uniform_boundary_volume_bound (s : Fin 45) (z : Fin 3)
    (hz : ((shape s).val z).val = 0) :
    (denominator : ℝ) ^ 5 * ((([0, 49647854, 2487425428, 30161682257, 85580652520, 30068852496, 2518420453, 49984871, 0, 49396635, 0, 0, 0, 0, 0, 0, 49298498, 2462054477, 0, 0, 0, 0, 0, 2502852454, 29848185450, 0, 0, 0, 0, 29843118026, 85535730403, 0, 0, 0, 83899420204, 30295651400, 0, 0, 29918250959, 2562399822, 0, 2531327790, 49892168, 49891812, 0] : List ℕ).getD s.val 0 : ℝ) / 1000000000000) ≤
      massEntropy (fun w ↦ (wordCounts 5 (z + 1) (shapeEquiv s) w : ℝ)) +
        (∑ w, (wordCounts 5 (z + 1) (shapeEquiv s) w : ℝ) * (ones w : ℝ)) * Real.log 5 := by sorry
