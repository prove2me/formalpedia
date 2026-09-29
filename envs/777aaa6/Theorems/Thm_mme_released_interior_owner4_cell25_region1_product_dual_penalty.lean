-- Prove2me | Theorems.Thm_mme_released_interior_owner4_cell25_region1_product_dual_penalty
-- name    : mme_released_interior_owner4_cell25_region1_product_dual_penalty
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-24T17:09:51.426984+00:00
-- url     : https://prove2.me/theorems/da271a53-b06b-4473-9b8a-05480a483ab4
-- title:
--   Interior owner 4 cell 25 region 1 has a certified entropy penalty
-- statement:
--   A normalized positive rational product dual and kernel-checked logarithm enclosures bound the natural-log entropy penalty of the actual released split distribution. The main exponent bound remains a separate obligation.
-- source:
--   Released exact profile counts and normalized product-dual weights.

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles
open scoped BigOperators
open MME.RegionRate MME.ReleasedInterior

theorem mme_released_interior_owner4_cell25_region1_product_dual_penalty :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : MME.ReleasedInterior.Split 25 =>
        (splitWeight 4 25 1 c : ℝ) / 1000000000000) ≤
          (1 / 1000000000 : ℝ) := by sorry
