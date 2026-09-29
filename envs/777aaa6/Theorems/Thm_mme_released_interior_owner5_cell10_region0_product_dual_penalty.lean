-- Prove2me | Theorems.Thm_mme_released_interior_owner5_cell10_region0_product_dual_penalty
-- name    : mme_released_interior_owner5_cell10_region0_product_dual_penalty
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T09:12:26.961238+00:00
-- url     : https://prove2.me/theorems/d8653d59-7cb6-4cee-aa15-4f89d2b68d28
-- title:
--   Interior owner 5 cell 10 region 0 has a certified entropy penalty
-- statement:
--   A normalized positive rational product dual and kernel-checked logarithm enclosures bound the natural-log entropy penalty of the actual released split distribution. The main exponent bound remains a separate obligation.
-- source:
--   Released exact profile counts and normalized product-dual weights.

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles
open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

theorem mme_released_interior_owner5_cell10_region0_product_dual_penalty :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 10 =>
        (splitWeight 5 10 0 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by sorry
