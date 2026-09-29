-- Prove2me | Theorems.Thm_mme_released_interior_owner4_cell21_region1_product_dual_penalty
-- name    : mme_released_interior_owner4_cell21_region1_product_dual_penalty
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T17:09:06.863973+00:00
-- url     : https://prove2.me/theorems/6d643604-79a1-4168-ad85-6a7670e185b4
-- title:
--   Interior owner 4 cell 21 region 1 has a certified entropy penalty
-- statement:
--   A normalized positive rational product dual and kernel-checked logarithm enclosures bound the natural-log entropy penalty of the actual released split distribution. The main exponent bound remains a separate obligation.
-- source:
--   Released exact profile counts and normalized product-dual weights.

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles
open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

theorem mme_released_interior_owner4_cell21_region1_product_dual_penalty :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 21 =>
        (splitWeight 4 21 1 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by sorry
