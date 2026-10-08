-- Prove2me | Theorems.Thm_fare_sum_nonneg
-- name    : fare_sum_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T14:50:28.378527+00:00
-- url     : https://prove2.me/theorems/b2637c8b-556a-4e34-96c5-74171d457e78
-- title:
--   fare_sum_nonneg
-- statement:
--   Automatically extracted helper theorem fare_sum_nonneg from oversized parent candidate 90d98a5ab03646dfb4a92e3e1eeda044d4c91525920aa358e1f2faf29db915dd.
-- source:
--   candidate-decomposition:e5c4f26f-0565-4b78-9161-3b3ae9b93077:90d98a5ab03646dfb4a92e3e1eeda044d4c91525920aa358e1f2faf29db915dd

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem fare_sum_nonneg (f : ℕ → ℝ) (k : ℕ) :
    0 ≤ ∑ i ∈ Finset.Icc 1 k, |f i| := by sorry
