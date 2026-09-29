-- Prove2me | Theorems.Thm_mme_released_global_owner4_coarse_entropy_bound
-- name    : mme_released_global_owner4_coarse_entropy_bound
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T15:11:47.536004+00:00
-- url     : https://prove2.me/theorems/4da1d004-206a-4069-94fb-a2fbe2200960
-- title:
--   Outer owner 4 has certified directional coarse entropies
-- statement:
--   All three normalized coarse marginal entropies are bounded using rational logarithm intervals and the actual released coarse counts. The finite shape index is proved equal to the profile shape index. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Theorems.Thm_mme_rational_mass_entropy_log_bounds
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.RegionRate MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner4_coarse_entropy_bound (i : Fin 3) :
    (((![1490678804, 1489860946, 1488368546] : Fin 3 → ℕ) i : ℝ) / 1000000000) ≤
      (profile 4).coarse i 0 := by sorry
