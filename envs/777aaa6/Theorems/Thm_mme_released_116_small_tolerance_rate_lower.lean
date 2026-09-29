-- Prove2me | Theorems.Thm_mme_released_116_small_tolerance_rate_lower
-- name    : mme_released_116_small_tolerance_rate_lower
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T00:14:53.461346+00:00
-- url     : https://prove2.me/theorems/292556ea-9584-4807-b6c8-a15e3aa5a4c7
-- title:
--   A fixed small tolerance preserves released 116 rate at least 3N/20
-- statement:
--   There exists a positive tolerance eps0 such that every nonnegative eps <= eps0 leaves regionalRate minus N times the entropy modulus at least 3N/20. This uses the exact certified rate >= N/5 and uniform entropy continuity with modulus bound 1/20.
-- source:
--   Certified entropy bounds for the released 116 integer profile: exact rational parent mixtures, retained-grade support bounds on the actual compatibility partition, and zero split penalty.

import Theorems.Thm_mme_regional_entropy_uniform_modulus
import Theorems.Thm_mme_regional_mass_entropy_algebra
import Theorems.Thm_mme_released_116_regional_split_mass
import Definitions.Def_mme_regional_split_entropy_data
import Theorems.Thm_mme_released_116_integer_profile_support
import Definitions.Def_mme_recursive_thin_split_data
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
open BigOperators MME MME.RegionRate MME.RecursiveThinSplit
open BigOperators MME.RegionRate
open MME.RecursiveYZ
open scoped Classical
open MME
open BigOperators MME MME.RecursiveThinSplit
open BigOperators MME MME.RegionRate
set_option autoImplicit false
universe u

theorem mme_released_116_small_tolerance_rate_lower :
    ∃ eps₀ : ℝ, 0 < eps₀ ∧ ∀ eps : ℝ, 0 ≤ eps → eps ≤ eps₀ →
      (3 / 20 : ℝ) * ((∑ r : Fin 6, Released116.regionalSize r : ℕ) : ℝ) ≤
        regionalRate Released116.parent_total Released116.regionalSize
          Released116.splitCount Released116.integerProfile -
        ((∑ r : Fin 6, Released116.regionalSize r : ℕ) : ℝ) *
          entropyModulus (Fin 2 → CompleteSplit.CompleteWord 2) eps := by sorry
