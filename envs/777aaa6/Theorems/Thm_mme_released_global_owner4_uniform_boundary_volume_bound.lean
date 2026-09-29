-- Prove2me | Theorems.Thm_mme_released_global_owner4_uniform_boundary_volume_bound
-- name    : mme_released_global_owner4_uniform_boundary_volume_bound
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T05:31:24.225475+00:00
-- url     : https://prove2.me/theorems/72b15e5b-5ef4-4ea8-9cda-f7cf67aa65d8
-- title:
--   Outer owner 4 has boundary bounds uniform in the free-mode choice
-- statement:
--   The checked cell certificates give one explicit lower bound per boundary shape, valid for every zero coordinate selected by extraction. The finite comparison takes a minimum only among the free-mode choices of that one boundary cell. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Theorems.Thm_mme_released_global_owner4_cell0_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner4_cell1_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner4_cell2_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner4_cell3_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner4_cell4_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner4_cell5_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner4_cell6_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner4_cell7_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner4_cell8_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner4_cell9_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner4_cell16_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner4_cell17_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner4_cell23_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner4_cell24_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner4_cell29_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner4_cell30_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner4_cell34_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner4_cell35_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner4_cell38_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner4_cell39_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner4_cell41_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner4_cell42_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner4_cell43_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner4_cell44_boundary_volume_bound
open scoped BigOperators
open MME MME.RegionRate MME.ReleasedGlobal MME.MoreAsymmetryExactSeed
open MME.RecursiveYZ.Boundary

theorem mme_released_global_owner4_uniform_boundary_volume_bound (s : Fin 45) (z : Fin 3)
    (hz : ((shape s).val z).val = 0) :
    (denominator : ℝ) ^ 5 * ((([0, 49711049, 2486699145, 30158552205, 85573552848, 30073749198, 2518160978, 49964227, 0, 49385212, 0, 0, 0, 0, 0, 0, 49309756, 2461960971, 0, 0, 0, 0, 0, 2502955864, 29853036253, 0, 0, 0, 0, 29838417750, 85528069838, 0, 0, 0, 83902935981, 30289370898, 0, 0, 29921870728, 2563482978, 0, 2532716737, 50113951, 49674360, 0] : List ℕ).getD s.val 0 : ℝ) / 1000000000000) ≤
      massEntropy (fun w ↦ (wordCounts 4 (z + 1) (shapeEquiv s) w : ℝ)) +
        (∑ w, (wordCounts 4 (z + 1) (shapeEquiv s) w : ℝ) * (ones w : ℝ)) * Real.log 5 := by sorry
