-- Prove2me | Theorems.Thm_fare_abs_le_sum
-- name    : fare_abs_le_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T14:50:42.623924+00:00
-- url     : https://prove2.me/theorems/5314d542-fcdb-4458-8fcc-301950915cc9
-- title:
--   fare_abs_le_sum
-- statement:
--   Automatically extracted helper theorem fare_abs_le_sum from oversized parent candidate 90d98a5ab03646dfb4a92e3e1eeda044d4c91525920aa358e1f2faf29db915dd.
-- source:
--   candidate-decomposition:e5c4f26f-0565-4b78-9161-3b3ae9b93077:90d98a5ab03646dfb4a92e3e1eeda044d4c91525920aa358e1f2faf29db915dd

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem fare_abs_le_sum (f : ℕ → ℝ) (k j : ℕ)
    (hj : 1 ≤ j) (hjk : j ≤ k) :
    |f j| ≤ ∑ i ∈ Finset.Icc 1 k, |f i| := by sorry
