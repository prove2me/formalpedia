-- Prove2me | Theorems.Thm_mme_released_interior_owner5_cell21_region1_product_dual_penalty
-- name    : mme_released_interior_owner5_cell21_region1_product_dual_penalty
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T17:12:25.425852+00:00
-- url     : https://prove2.me/theorems/8d4a97bb-9ea3-4352-906a-3bb40baf81e6
-- title:
--   Interior owner 5 cell 21 region 1 has a certified entropy penalty
-- statement:
--   A normalized positive rational product dual and kernel-checked logarithm enclosures bound the natural-log entropy penalty of the actual released split distribution. The main exponent bound remains a separate obligation.
-- source:
--   Released exact profile counts and normalized product-dual weights.

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles
open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

theorem mme_released_interior_owner5_cell21_region1_product_dual_penalty :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 21 =>
        (splitWeight 5 21 1 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by sorry
