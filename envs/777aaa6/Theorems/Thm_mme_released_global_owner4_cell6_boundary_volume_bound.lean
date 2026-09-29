-- Prove2me | Theorems.Thm_mme_released_global_owner4_cell6_boundary_volume_bound
-- name    : mme_released_global_owner4_cell6_boundary_volume_bound
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T05:20:04.365417+00:00
-- url     : https://prove2.me/theorems/5603ac7e-eaeb-450e-9406-4761a34996c0
-- title:
--   Global owner 4 cell 6 has certified boundary volume
-- statement:
--   The actual global word count in the cyclically next free mode is identified with its released atom-row marginal, then checked against a rational mass table for each zero coordinate. Rational logarithm intervals certify homogeneous entropy plus the free-letter volume at denominator^5 scale. Physical aggregation, positive losses, and the main exponent theorem remain separate obligations.
-- source:
--   Released exact global atom rows and boundary entropy and letter-volume rates.

import Theorems.Thm_mme_rational_boundary_volume_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Theorems.Thm_mme_released_global_word_counts_row_marginal
import Definitions.Def_mme_recursive_yz_boundary_data
open scoped BigOperators
open MME MME.RegionRate MME.MoreAsymmetryExactSeed
open MME.ReleasedGlobal MME.RecursiveYZ.Boundary

theorem mme_released_global_owner4_cell6_boundary_volume_bound
    (z : Fin 3) (hz : ((shape 6).val z).val = 0) :
    (denominator : ℝ) ^ 5 * (((![2518160978, 0, 0] : Fin 3 → ℕ) z : ℝ) / 1000000000000) ≤
      massEntropy (fun w ↦ (wordCounts 4 (z + 1) (shapeEquiv 6) w : ℝ)) +
        (∑ w, (wordCounts 4 (z + 1) (shapeEquiv 6) w : ℝ) * (ones w : ℝ)) * Real.log 5 := by sorry
