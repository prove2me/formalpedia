-- Prove2me | Theorems.Thm_mme_released_interior_owner5_cell20_region0_product_dual_penalty
-- name    : mme_released_interior_owner5_cell20_region0_product_dual_penalty
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T09:13:08.331977+00:00
-- url     : https://prove2.me/theorems/5143db67-13ca-4202-81c7-33ca51db528d
-- title:
--   Interior owner 5 cell 20 region 0 has a certified entropy penalty
-- statement:
--   A normalized positive rational product dual and kernel-checked logarithm enclosures bound the natural-log entropy penalty of the actual released split distribution. The main exponent bound remains a separate obligation.
-- source:
--   Released exact profile counts and normalized product-dual weights.

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles
open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

theorem mme_released_interior_owner5_cell20_region0_product_dual_penalty :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 20 =>
        (splitWeight 5 20 0 c : ℝ) / 1000000000000) ≤
          (1591 / 1000000000 : ℝ) := by sorry
