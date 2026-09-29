-- Prove2me | Theorems.Thm_mme_certified_rate_entry
-- name    : mme_certified_rate_entry
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-23T05:20:34.61044+00:00
-- url     : https://prove2.me/theorems/4aa05aee-1d34-483a-bb12-84c187e15b03
-- title:
--   From bounds on the three potentials to a bound on the regional rate
-- statement:
--   Two small facts that turn certified bounds on the individual potentials into a bound on a regional
--   rate.
--
--   First, the marginal counts of a region, summed over the grade, total the region's split weights —
--   grouping the splits by one coordinate loses nothing. This is what makes the positivity hypothesis of
--   the coarse potential immediate from the published count theorems.
--
--   Second, a regional rate exceeds a value as soon as each of its three potentials does, the rate being
--   their minimum.
-- source:
--   Duan-Wu-Zhou fourth-power recursive construction (https://arxiv.org/html/2210.10173v5, section 7) combined with the More-Asymmetry regional extraction (https://arxiv.org/html/2404.16349v2, section 6). Exact finite or asymptotic-rate statement as written; no exponent claim.

import Mathlib
import Definitions.Def_mme_regional_split_entropy_data
import Definitions.Def_mme_recursive_thin_split_data
import Definitions.Def_mme_recursive_region_parent_profiles

open BigOperators MME MME.RegionRate MME.RecursiveYZ MME.RecursiveThinSplit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
universe u

theorem mme_certified_rate_entry :
    (∀ {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
      (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ) (i : Fin 3) (r : Fin R),
      ∑ j, marginalCounts m i r j = ∑ c, m r c) ∧
    ∀ {half R : ℕ} {parent : Fin R → Fin 3 → ℕ} {W : Type u} [Fintype W]
      (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
      (n : Fin R → ℕ) (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
      (mu : Fin 3 → Cell half R parent → W → ℕ) (T : ℝ),
      T < coarsePotential m 0 - penaltyPotential n m →
      T < parentPotential htotal n m (mu 1) - compatibilityPotential 0 (mu 1) →
      T < parentPotential htotal n m (mu 2) - compatibilityPotential 1 (mu 2) →
      T < regionalRate htotal n m mu := by sorry
