-- Prove2me | Theorems.Thm_mme_released_interior_owner3_cell27_region4_product_dual_penalty
-- name    : mme_released_interior_owner3_cell27_region4_product_dual_penalty
-- status  : Open
-- author  : @Robertboy18
-- created : 2026-09-23T16:29:19.517696+00:00
-- url     : https://prove2.me/theorems/09e9b07c-8e9a-4b9c-af77-e61a9c1048d3
-- title:
--   Interior owner 3 cell 27 region 4 has a certified entropy penalty
-- statement:
--   A normalized positive rational product dual and kernel-checked logarithm enclosures bound the natural-log entropy penalty of the actual released split distribution. The main exponent bound remains a separate obligation.
-- source:
--   Released exact profile counts and normalized product-dual weights.

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles
open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

theorem mme_released_interior_owner3_cell27_region4_product_dual_penalty :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 27 =>
        (splitWeight 3 27 4 c : ℝ) / 1000000000000) ≤
          (440 / 1000000000 : ℝ) := by sorry
