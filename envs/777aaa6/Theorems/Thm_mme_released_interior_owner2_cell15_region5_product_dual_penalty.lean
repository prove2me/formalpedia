-- Prove2me | Theorems.Thm_mme_released_interior_owner2_cell15_region5_product_dual_penalty
-- name    : mme_released_interior_owner2_cell15_region5_product_dual_penalty
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T15:34:28.442001+00:00
-- url     : https://prove2.me/theorems/8ec4b6d7-e8e9-4bde-ae15-0aa51f4da6d7
-- title:
--   Interior owner 2 cell 15 region 5 has a certified entropy penalty
-- statement:
--   A normalized positive rational product dual and kernel-checked logarithm enclosures bound the natural-log entropy penalty of the actual released split distribution. The main exponent bound remains a separate obligation.
-- source:
--   Released exact profile counts and normalized product-dual weights.

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles
open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

theorem mme_released_interior_owner2_cell15_region5_product_dual_penalty :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 15 =>
        (splitWeight 2 15 5 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by sorry
