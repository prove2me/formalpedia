-- Prove2me | Theorems.Thm_mme_released_interior_owner2_cell27_region2_112_weight_rate_bound
-- name    : mme_released_interior_owner2_cell27_region2_112_weight_rate_bound
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T15:38:12.025018+00:00
-- url     : https://prove2.me/theorems/d836c26e-5bf5-4cdf-9c75-81b8b321b6e2
-- title:
--   Released owner 2 cell 27 region 2 has certified 112 child rates
-- statement:
--   The integer child parameter is checked against the actual released recipe for every admissible 112 split. Rational logarithm intervals certify the complete entropy and matrix-dimension rate at tau = 3952233 / 5000000. Physical aggregation, positive losses, and the main exponent theorem remain separate obligations.
-- source:
--   Released exact child parameters and the physical 112 extraction rate.

import Theorems.Thm_mme_rational_112_weight_rate_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles
open scoped BigOperators
open MME MME.RegionRate MME.MoreAsymmetryExactSeed

theorem mme_released_interior_owner2_cell27_region2_112_weight_rate_bound
    (c : ReleasedInterior.Split 27) (z : Fin 3)
    (hshape : ∀ i : Fin 3, (c.val i).val = if i = z then 2 else 1) :
    let q : ℝ := ((((((ReleasedInterior.seed 2 27).children.find?
      (fun a => a.1 == 2 && a.2.1 == ReleasedInterior.sourceShape 2 c)).getD
        (0, [], 0)).2.2)) : ℝ) / denominator
    (((![36249640627024, 36202920700418, 36247848208246] : Fin 3 → ℕ) z : ℝ) / 1000000000000) ≤
      4 * (entropy ![q, q, 1 - 2 * q] + 2 * Real.log 2) +
        24 * (1 - q) * (3952233 / 5000000 : ℝ) * Real.log 5 := by sorry
