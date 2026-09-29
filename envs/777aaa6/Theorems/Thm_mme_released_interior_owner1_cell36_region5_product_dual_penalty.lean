-- Prove2me | Theorems.Thm_mme_released_interior_owner1_cell36_region5_product_dual_penalty
-- name    : mme_released_interior_owner1_cell36_region5_product_dual_penalty
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T14:54:57.185984+00:00
-- url     : https://prove2.me/theorems/a2aab475-b13e-49a0-9758-7abe729e118d
-- title:
--   Interior owner 1 cell 36 region 5 has a certified entropy penalty
-- statement:
--   A normalized positive rational product dual and kernel-checked logarithm enclosures bound the natural-log entropy penalty of the actual released split distribution. The main exponent bound remains a separate obligation.
-- source:
--   Released exact profile counts and normalized product-dual weights.

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles
open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

theorem mme_released_interior_owner1_cell36_region5_product_dual_penalty :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 36 =>
        (splitWeight 1 36 5 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by sorry
