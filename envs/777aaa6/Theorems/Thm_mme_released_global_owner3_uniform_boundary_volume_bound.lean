-- Prove2me | Theorems.Thm_mme_released_global_owner3_uniform_boundary_volume_bound
-- name    : mme_released_global_owner3_uniform_boundary_volume_bound
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T05:16:10.26598+00:00
-- url     : https://prove2.me/theorems/f0a11654-bde8-48a5-a888-52b6a2c26a70
-- title:
--   Outer owner 3 has boundary bounds uniform in the free-mode choice
-- statement:
--   The checked cell certificates give one explicit lower bound per boundary shape, valid for every zero coordinate selected by extraction. The finite comparison takes a minimum only among the free-mode choices of that one boundary cell. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Theorems.Thm_mme_released_global_owner3_cell0_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner3_cell1_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner3_cell2_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner3_cell3_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner3_cell4_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner3_cell5_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner3_cell6_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner3_cell7_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner3_cell8_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner3_cell9_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner3_cell16_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner3_cell17_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner3_cell23_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner3_cell24_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner3_cell29_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner3_cell30_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner3_cell34_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner3_cell35_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner3_cell38_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner3_cell39_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner3_cell41_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner3_cell42_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner3_cell43_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner3_cell44_boundary_volume_bound
open scoped BigOperators
open MME MME.RegionRate MME.ReleasedGlobal MME.MoreAsymmetryExactSeed
open MME.RecursiveYZ.Boundary

theorem mme_released_global_owner3_uniform_boundary_volume_bound (s : Fin 45) (z : Fin 3)
    (hz : ((shape s).val z).val = 0) :
    (denominator : ℝ) ^ 5 * ((([0, 49668638, 2487054614, 30163457323, 85576822698, 30067821815, 2517127730, 49831181, 0, 49330957, 0, 0, 0, 0, 0, 0, 49418204, 2462068005, 0, 0, 0, 0, 0, 2503068561, 29847084297, 0, 0, 0, 0, 29843979565, 85531596254, 0, 0, 0, 83903297232, 30295951027, 0, 0, 29916676812, 2563402632, 0, 2532342617, 49928473, 49653342, 0] : List ℕ).getD s.val 0 : ℝ) / 1000000000000) ≤
      massEntropy (fun w ↦ (wordCounts 3 (z + 1) (shapeEquiv s) w : ℝ)) +
        (∑ w, (wordCounts 3 (z + 1) (shapeEquiv s) w : ℝ) * (ones w : ℝ)) * Real.log 5 := by sorry
