-- Prove2me | Theorems.Thm_mme_released_interior_owner0_cell36_region2_product_dual_penalty
-- name    : mme_released_interior_owner0_cell36_region2_product_dual_penalty
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T12:39:10.742368+00:00
-- url     : https://prove2.me/theorems/7295b22f-467d-4d5e-849f-4879485f853b
-- title:
--   Interior owner 0 cell 36 region 2 has a certified entropy penalty
-- statement:
--   A normalized positive rational product dual and kernel-checked logarithm enclosures bound the natural-log entropy penalty of the actual released split distribution. The main exponent bound remains a separate obligation.
-- source:
--   Released exact profile counts and normalized product-dual weights.

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles
open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

theorem mme_released_interior_owner0_cell36_region2_product_dual_penalty :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 36 =>
        (splitWeight 0 36 2 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by sorry
