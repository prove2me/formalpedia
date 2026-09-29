-- Prove2me | Theorems.Thm_mme_released_interior_owner3_cell27_region5_product_dual_penalty
-- name    : mme_released_interior_owner3_cell27_region5_product_dual_penalty
-- status  : Open
-- author  : @Robertboy18
-- created : 2026-09-23T16:28:25.847717+00:00
-- url     : https://prove2.me/theorems/1ab56b36-0642-42c1-9e18-1fbf60842751
-- title:
--   Interior owner 3 cell 27 region 5 has a certified entropy penalty
-- statement:
--   A normalized positive rational product dual and kernel-checked logarithm enclosures bound the natural-log entropy penalty of the actual released split distribution. The main exponent bound remains a separate obligation.
-- source:
--   Released exact profile counts and normalized product-dual weights.

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles
open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

theorem mme_released_interior_owner3_cell27_region5_product_dual_penalty :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 27 =>
        (splitWeight 3 27 5 c : ℝ) / 1000000000000) ≤
          (1592 / 1000000000 : ℝ) := by sorry
