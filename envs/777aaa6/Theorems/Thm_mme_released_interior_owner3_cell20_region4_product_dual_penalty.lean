-- Prove2me | Theorems.Thm_mme_released_interior_owner3_cell20_region4_product_dual_penalty
-- name    : mme_released_interior_owner3_cell20_region4_product_dual_penalty
-- status  : Open
-- author  : @Robertboy18
-- created : 2026-09-23T16:19:32.748983+00:00
-- url     : https://prove2.me/theorems/6eda34a4-7575-4751-88ef-19a7af58cad2
-- title:
--   Interior owner 3 cell 20 region 4 has a certified entropy penalty
-- statement:
--   A normalized positive rational product dual and kernel-checked logarithm enclosures bound the natural-log entropy penalty of the actual released split distribution. The main exponent bound remains a separate obligation.
-- source:
--   Released exact profile counts and normalized product-dual weights.

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles
open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

theorem mme_released_interior_owner3_cell20_region4_product_dual_penalty :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 20 =>
        (splitWeight 3 20 4 c : ℝ) / 1000000000000) ≤
          (1642 / 1000000000 : ℝ) := by sorry
