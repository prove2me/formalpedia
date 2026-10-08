-- Prove2me | Theorems.Thm_revenue_abs_bound
-- name    : revenue_abs_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T14:50:29.872171+00:00
-- url     : https://prove2.me/theorems/22cc8a7a-a769-4f0d-87f3-eec9e54427a8
-- title:
--   revenue_abs_bound
-- statement:
--   Automatically extracted helper theorem revenue_abs_bound from oversized parent candidate 90d98a5ab03646dfb4a92e3e1eeda044d4c91525920aa358e1f2faf29db915dd.
-- source:
--   candidate-decomposition:e5c4f26f-0565-4b78-9161-3b3ae9b93077:90d98a5ab03646dfb4a92e3e1eeda044d4c91525920aa358e1f2faf29db915dd

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem revenue_abs_bound
    (f p x : ℕ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hp : ∀ j, 1 ≤ j → 0 ≤ p j) (hx : ∀ j, 0 ≤ x j) :
    ∀ n s, 0 ≤ s → (∀ j, 1 ≤ j → j ≤ n → |f j| ≤ M) →
      |revenue f p x n s| ≤ (n : ℝ) * M * s := by sorry
