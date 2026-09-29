-- Prove2me | Theorems.Thm_mme_released_interior_owner2_cell26_region4_product_dual_penalty
-- name    : mme_released_interior_owner2_cell26_region4_product_dual_penalty
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T15:39:34.693264+00:00
-- url     : https://prove2.me/theorems/20a5abf8-479a-4987-8898-e58da5452ea2
-- title:
--   Interior owner 2 cell 26 region 4 has a certified entropy penalty
-- statement:
--   A normalized positive rational product dual and kernel-checked logarithm enclosures bound the natural-log entropy penalty of the actual released split distribution. The main exponent bound remains a separate obligation.
-- source:
--   Released exact profile counts and normalized product-dual weights.

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles
open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

theorem mme_released_interior_owner2_cell26_region4_product_dual_penalty :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 26 =>
        (splitWeight 2 26 4 c : ℝ) / 1000000000000) ≤
          (428 / 1000000000 : ℝ) := by sorry
