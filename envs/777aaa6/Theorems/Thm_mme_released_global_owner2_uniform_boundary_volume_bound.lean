-- Prove2me | Theorems.Thm_mme_released_global_owner2_uniform_boundary_volume_bound
-- name    : mme_released_global_owner2_uniform_boundary_volume_bound
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T04:56:23.459982+00:00
-- url     : https://prove2.me/theorems/5b014eec-2e34-4bfb-a50c-81be53fdd12f
-- title:
--   Outer owner 2 has boundary bounds uniform in the free-mode choice
-- statement:
--   The checked cell certificates give one explicit lower bound per boundary shape, valid for every zero coordinate selected by extraction. The finite comparison takes a minimum only among the free-mode choices of that one boundary cell. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Theorems.Thm_mme_released_global_owner2_cell0_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner2_cell1_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner2_cell2_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner2_cell3_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner2_cell4_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner2_cell5_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner2_cell6_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner2_cell7_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner2_cell8_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner2_cell9_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner2_cell16_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner2_cell17_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner2_cell23_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner2_cell24_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner2_cell29_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner2_cell30_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner2_cell34_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner2_cell35_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner2_cell38_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner2_cell39_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner2_cell41_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner2_cell42_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner2_cell43_boundary_volume_bound
import Theorems.Thm_mme_released_global_owner2_cell44_boundary_volume_bound
open scoped BigOperators
open MME MME.RegionRate MME.ReleasedGlobal MME.MoreAsymmetryExactSeed
open MME.RecursiveYZ.Boundary

theorem mme_released_global_owner2_uniform_boundary_volume_bound (s : Fin 45) (z : Fin 3)
    (hz : ((shape s).val z).val = 0) :
    (denominator : ℝ) ^ 5 * ((([0, 49580151, 2486893764, 30162367654, 85581298089, 30068911217, 2518251968, 49951019, 0, 49419391, 0, 0, 0, 0, 0, 0, 49254970, 2460953691, 0, 0, 0, 0, 0, 2503308762, 29847430147, 0, 0, 0, 0, 29843034277, 85538626345, 0, 0, 0, 83898043062, 30296172800, 0, 0, 29916272233, 2563639178, 0, 2532488064, 50129517, 49757258, 0] : List ℕ).getD s.val 0 : ℝ) / 1000000000000) ≤
      massEntropy (fun w ↦ (wordCounts 2 (z + 1) (shapeEquiv s) w : ℝ)) +
        (∑ w, (wordCounts 2 (z + 1) (shapeEquiv s) w : ℝ) * (ones w : ℝ)) * Real.log 5 := by sorry
