-- Prove2me | Theorems.Thm_mme_certified_regional_rate_bounds
-- name    : mme_certified_regional_rate_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-23T05:17:09.346794+00:00
-- url     : https://prove2.me/theorems/d44173f7-acd5-4d87-9547-2da9132a4c84
-- title:
--   Certified bounds for the coarse and penalty potentials of a regional rate
-- statement:
--   The two remaining potentials of a regional rate, bounded by exact arithmetic.
--
--   A regional rate is the smallest of three potentials. Two of them are added and so need lower bounds,
--   and one is subtracted and so needs an upper bound. This gives the remaining two cases: a certified
--   rational floor for a coarse potential, built from a reference table for each region's normalized
--   marginal counts; and a certified rational ceiling for a whole penalty potential, built from
--   per-region reference tables for the normalized split weights.
--
--   Both statements are generic in the half-size, the number of regions and the parent shapes, so one
--   instance serves every level of the recursion.
-- source:
--   Duan-Wu-Zhou fourth-power recursive construction (https://arxiv.org/html/2210.10173v5, section 7) combined with the More-Asymmetry regional extraction (https://arxiv.org/html/2404.16349v2, section 6). Exact finite or asymptotic-rate statement as written; no exponent claim.

import Mathlib
import Definitions.Def_mme_certified_generic_rate_data
import Definitions.Def_mme_certified_generic_floor_data
import Definitions.Def_mme_certified_entropy_rational_data
import Definitions.Def_mme_certified_entropy_bridge_data
import Definitions.Def_mme_regional_split_entropy_data
import Definitions.Def_mme_recursive_thin_split_data
import Theorems.Thm_mme_certified_parent_potential_floor
import Theorems.Thm_mme_certified_entropy_bridge
import Theorems.Thm_mme_certified_entropy_penalty_rational

open BigOperators MME MME.RegionRate MME.RecursiveYZ MME.RecursiveThinSplit MME.Cert
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem mme_certified_regional_rate_bounds :
    (∀ {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
      (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ) (i : Fin 3),
      (∀ r, 0 < ∑ j, marginalCounts m i r j) →
      ∀ (e : Fin R → Fin (half + 1) → Fin 4 → ℤ) (f : Fin R → ℚ),
      (∀ r, f r ≤ regFloorG (normQ (marginalCounts m i r)) (e r)) →
      (∑ r : Fin R, ((∑ j, marginalCounts m i r j : ℕ) : ℝ) * ((f r : ℚ) : ℝ)) ≤
        coarsePotential m i) ∧
    ∀ {half R : ℕ} {parent : Fin R → Fin 3 → ℕ} (n : Fin R → ℕ)
      (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ),
      (∀ r, 0 < n r) → (∀ r, ∑ c, m r c = n r) →
      ∀ (E : Fin R → Fin 3 → Fin (half + 1) → (Fin 4 → ℤ)) (g : Fin R → ℚ),
      (∀ r, ((∑ c : RecursiveThinSplit.Split half (parent r),
          qvalQ (fun k ↦ ∑ i, E r i (c.val i) k)) - 2 +
        ∑ c : RecursiveThinSplit.Split half (parent r),
          (alphaG n m r c) ^ 2 / qvalQ (fun k ↦ ∑ i, E r i (c.val i) k)) ≤ g r) →
      penaltyPotential n m ≤ ∑ r : Fin R, ((n r : ℕ) : ℝ) * ((g r : ℚ) : ℝ) := by sorry
