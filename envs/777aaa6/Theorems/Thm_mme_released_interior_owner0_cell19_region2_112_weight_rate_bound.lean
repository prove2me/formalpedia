-- Prove2me | Theorems.Thm_mme_released_interior_owner0_cell19_region2_112_weight_rate_bound
-- name    : mme_released_interior_owner0_cell19_region2_112_weight_rate_bound
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T06:41:02.360996+00:00
-- url     : https://prove2.me/theorems/df7474d5-ec3e-4b9c-aaca-71480ce2c9a0
-- title:
--   Released owner 0 cell 19 region 2 has certified 112 child rates
-- statement:
--   The integer child parameter is checked against the actual released recipe for every admissible 112 split. Rational logarithm intervals certify the complete entropy and matrix-dimension rate at tau = 3952233 / 5000000. Physical aggregation, positive losses, and the main exponent theorem remain separate obligations.
-- source:
--   Released exact child parameters and the physical 112 extraction rate.

import Theorems.Thm_mme_rational_112_weight_rate_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles
open scoped BigOperators
open MME MME.RegionRate MME.MoreAsymmetryExactSeed

theorem mme_released_interior_owner0_cell19_region2_112_weight_rate_bound
    (c : ReleasedInterior.Split 19) (z : Fin 3)
    (hshape : ∀ i : Fin 3, (c.val i).val = if i = z then 2 else 1) :
    let q : ℝ := ((((((ReleasedInterior.seed 0 19).children.find?
      (fun a => a.1 == 2 && a.2.1 == ReleasedInterior.sourceShape 0 c)).getD
        (0, [], 0)).2.2)) : ℝ) / denominator
    (((![36249640597923, 36249640611802, 36122822859548] : Fin 3 → ℕ) z : ℝ) / 1000000000000) ≤
      4 * (entropy ![q, q, 1 - 2 * q] + 2 * Real.log 2) +
        24 * (1 - q) * (3952233 / 5000000 : ℝ) * Real.log 5 := by sorry
