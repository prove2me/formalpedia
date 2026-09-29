-- Prove2me | Theorems.Thm_mme_released_interior_scaled_coarse_penalty_lower_bound
-- name    : mme_released_interior_scaled_coarse_penalty_lower_bound
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T07:43:52.564026+00:00
-- url     : https://prove2.me/theorems/76a3c856-2850-45e0-94e9-e1c6f9d67995
-- title:
--   Released interior recipes have a two-fifths coarse rate at every scale
-- statement:
--   For every released interior recipe and every natural replication scale k, coarsePotential minus penaltyPotential is at least (2/5) times k times the fourth power of the released denominator. This includes k=0 and empty regions. The other two components of regionalRate remain separate obligations. The full matrix exponent bound remains a separate obligation.
-- source:
--   Kernel-checked regional count identities and exact extraction with empty regions.

import Theorems.Thm_mme_regional_coarse_penalty_lower_bound
import Theorems.Thm_mme_released_interior_region_coarse_penalty
import Theorems.Thm_mme_released_interior_scaled_integer_profile_constraints_exact
open scoped BigOperators
open MME MME.RegionRate MME.ReleasedInterior MME.MoreAsymmetryExactSeed

theorem mme_released_interior_scaled_coarse_penalty_lower_bound
    (owner : Fin 6) (s : Fin 45) (hi : (seed owner s).boundary = []) (k : ℕ) :
    (2 / 5 : ℝ) * (k : ℝ) * (denominator : ℝ) ^ 4 ≤
      coarsePotential (fun r c => k * splitCount owner s r c) 0 -
        penaltyPotential (fun r => k * regionalSize owner s r)
          (fun r c => k * splitCount owner s r c) := by sorry
