-- Prove2me | Theorems.Thm_mme_released_interior_owner0_cell31_region5_product_dual_penalty
-- name    : mme_released_interior_owner0_cell31_region5_product_dual_penalty
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T12:38:16.669173+00:00
-- url     : https://prove2.me/theorems/261b91d5-909c-4d01-8009-bbfb3745b4fe
-- title:
--   Interior owner 0 cell 31 region 5 has a certified entropy penalty
-- statement:
--   A normalized positive rational product dual and kernel-checked logarithm enclosures bound the natural-log entropy penalty of the actual released split distribution. The main exponent bound remains a separate obligation.
-- source:
--   Released exact profile counts and normalized product-dual weights.

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles
open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

theorem mme_released_interior_owner0_cell31_region5_product_dual_penalty :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 31 =>
        (splitWeight 0 31 5 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by sorry
