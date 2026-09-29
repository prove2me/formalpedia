-- Prove2me | Theorems.Thm_mme_released_interior_owner3_region_coarse_penalty
-- name    : mme_released_interior_owner3_region_coarse_penalty
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T07:17:18.096603+00:00
-- url     : https://prove2.me/theorems/96935853-8f25-49f7-be53-912093b82e44
-- title:
--   Every nonempty interior region for owner 3 has a two-fifths entropy margin
-- statement:
--   For owner 3, every nonempty region of every released interior recipe has coarse entropy minus the maximum-entropy penalty at least two fifths. All 88 finite region certificates are checked against the released integer data. The full matrix exponent bound remains a separate obligation.
-- source:
--   Kernel-checked regional count identities and exact extraction with empty regions.

import Theorems.Thm_mme_rational_coarse_penalty_certificate
import Definitions.Def_mme_released_interior_integer_profiles
open scoped BigOperators
open MME.RegionRate MME.RecursiveThinSplit MME.ReleasedInterior

theorem mme_released_interior_owner3_region_coarse_penalty
    (s : Fin 45) (r : Fin 6) (hi : (seed 3 s).boundary = [])
    (hn : 0 < (seed 3 s).region.getD r.val 0) :
    (2 / 5 : ℝ) ≤
      entropy (mme_modern_marginal (fun c : MME.ReleasedInterior.Split s => c.val 0)
        (fun c => (splitWeight 3 s r c : ℝ) / 1000000000000)) -
      Real.log 2 * entropyPenalty
        (fun c : MME.ReleasedInterior.Split s => (splitWeight 3 s r c : ℝ) / 1000000000000) := by sorry
