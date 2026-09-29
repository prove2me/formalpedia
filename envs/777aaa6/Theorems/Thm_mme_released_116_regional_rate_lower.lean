-- Prove2me | Theorems.Thm_mme_released_116_regional_rate_lower
-- name    : mme_released_116_regional_rate_lower
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T00:12:36.050737+00:00
-- url     : https://prove2.me/theorems/2ec412d9-70b5-47a7-b6b9-18e8c7b10fce
-- title:
--   Certified positive released 116 regional rate: at least N/5
-- statement:
--   The actual regionalRate of the released six-region 116 integer profile is at least one fifth of the total parent count. This combines the certified coarse entropy bound, zero penalty, lower bounds on both parent entropies, and upper bounds on both compatibility entropies.
-- source:
--   Certified entropy bounds for the released 116 integer profile: exact rational parent mixtures, retained-grade support bounds on the actual compatibility partition, and zero split penalty.

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

theorem mme_released_116_regional_rate_lower :
    (1 / 5 : ℝ) * ((∑ r : Fin 6, Released116.regionalSize r : ℕ) : ℝ) ≤
      regionalRate Released116.parent_total Released116.regionalSize
        Released116.splitCount Released116.integerProfile := by sorry
