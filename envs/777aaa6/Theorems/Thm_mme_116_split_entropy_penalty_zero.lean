-- Prove2me | Theorems.Thm_mme_116_split_entropy_penalty_zero
-- name    : mme_116_split_entropy_penalty_zero
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T23:48:35.431045+00:00
-- url     : https://prove2.me/theorems/66308589-8bc9-46ce-a299-874f1243b424
-- title:
--   The 116 split maximum-entropy penalty is zero
-- statement:
--   Every probability distribution on the four admissible splits of (1,1,6) has zero maximum-entropy penalty: the set of distributions sharing its coordinate marginals is a singleton.
-- source:
--   Exact simplification of the entropy penalty for the released 116 integer profiles. The four split weights are recovered from their coordinate marginals.

import Theorems.Thm_mme_released_116_regional_split_mass
import Definitions.Def_mme_regional_split_entropy_data
import Definitions.Def_mme_recursive_thin_split_data
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
open BigOperators MME MME.RecursiveThinSplit
open scoped Classical
set_option autoImplicit false
universe u

theorem mme_116_split_entropy_penalty_zero (alpha : Split 4 ![1, 1, 6] → ℝ)
    (hnonneg : ∀ c, 0 ≤ alpha c) (hmass : ∑ c, alpha c = 1) :
    entropyPenalty alpha = 0 := by sorry
