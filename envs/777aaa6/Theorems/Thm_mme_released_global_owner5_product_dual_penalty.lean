-- Prove2me | Theorems.Thm_mme_released_global_owner5_product_dual_penalty
-- name    : mme_released_global_owner5_product_dual_penalty
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T11:55:28.997887+00:00
-- url     : https://prove2.me/theorems/118a87e6-e42a-4f4b-bc74-f10bbb9a705d
-- title:
--   Released outer profile 5 has a certified product-dual penalty
-- statement:
--   An explicit rational bound controls the natural-log entropy penalty of actual released outer profile 5. The kernel checks positive dual weights, normalization, finite logarithm enclosures, and the identity with the released coarse counts. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Theorems.Thm_mme_rational_product_dual_penalty_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.RegionRate MME.ReleasedGlobal MME.MoreAsymmetryExactSeed

theorem mme_released_global_owner5_product_dual_penalty :
    Real.log 2 * MME.RecursiveThinSplit.entropyPenalty
      (fun c : Shape => (coarseCounts 5 c : ℝ) / (denominator : ℝ) ^ 5) ≤
        (15161 / 1000000000 : ℝ) := by sorry
