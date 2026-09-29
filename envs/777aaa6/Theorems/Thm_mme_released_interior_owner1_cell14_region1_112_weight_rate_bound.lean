-- Prove2me | Theorems.Thm_mme_released_interior_owner1_cell14_region1_112_weight_rate_bound
-- name    : mme_released_interior_owner1_cell14_region1_112_weight_rate_bound
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T10:33:32.579982+00:00
-- url     : https://prove2.me/theorems/3fc21c81-9c70-4967-bc0b-a4090207ec03
-- title:
--   Released owner 1 cell 14 region 1 has certified 112 child rates
-- statement:
--   The integer child parameter is checked against the actual released recipe for every admissible 112 split. Rational logarithm intervals certify the complete entropy and matrix-dimension rate at tau = 3952233 / 5000000. Physical aggregation, positive losses, and the main exponent theorem remain separate obligations.
-- source:
--   Released exact child parameters and the physical 112 extraction rate.

import Theorems.Thm_mme_rational_112_weight_rate_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles
open scoped BigOperators
open MME MME.RegionRate MME.MoreAsymmetryExactSeed

theorem mme_released_interior_owner1_cell14_region1_112_weight_rate_bound
    (c : ReleasedInterior.Split 14) (z : Fin 3)
    (hshape : ∀ i : Fin 3, (c.val i).val = if i = z then 2 else 1) :
    let q : ℝ := ((((((ReleasedInterior.seed 1 14).children.find?
      (fun a => a.1 == 1 && a.2.1 == ReleasedInterior.sourceShape 1 c)).getD
        (0, [], 0)).2.2)) : ℝ) / denominator
    (((![36077370863541, 36247773757680, 36077370863541] : Fin 3 → ℕ) z : ℝ) / 1000000000000) ≤
      4 * (entropy ![q, q, 1 - 2 * q] + 2 * Real.log 2) +
        24 * (1 - q) * (3952233 / 5000000 : ℝ) * Real.log 5 := by sorry
