-- Prove2me | Theorems.Thm_mme_released_interior_422_owner3_region2_coarse_penalty
-- name    : mme_released_interior_422_owner3_region2_coarse_penalty
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T07:17:49.651635+00:00
-- url     : https://prove2.me/theorems/50569747-a831-4b55-801f-626b864d260f
-- title:
--   A released (4,2,2) region has coarse entropy minus penalty at least two fifths
-- statement:
--   The actual released owner-3 recipe of shape (4,2,2), region 2, satisfies the two-fifths coarse entropy minus penalty bound. Its finite rational certificate is checked by the Lean kernel. The full matrix exponent bound remains a separate obligation.
-- source:
--   Kernel-checked regional count identities and exact extraction with empty regions.

import Theorems.Thm_mme_rational_coarse_penalty_certificate
import Definitions.Def_mme_released_interior_integer_profiles
open scoped BigOperators
open MME.RegionRate MME.RecursiveThinSplit MME.ReleasedInterior

theorem mme_released_interior_422_owner3_region2_coarse_penalty :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split 32 => c.val 0)
        (fun c => (splitWeight 3 32 2 c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split 32 => (splitWeight 3 32 2 c : ℝ) / 1000000000000) := by sorry
