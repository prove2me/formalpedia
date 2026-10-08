-- Prove2me | Theorems.Thm_revenue_update_of_gt
-- name    : revenue_update_of_gt
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T14:50:24.950516+00:00
-- url     : https://prove2.me/theorems/150a8c1e-d021-42a1-9231-36e25156fe90
-- title:
--   revenue_update_of_gt
-- statement:
--   Automatically extracted helper theorem revenue_update_of_gt from oversized parent candidate 90d98a5ab03646dfb4a92e3e1eeda044d4c91525920aa358e1f2faf29db915dd.
-- source:
--   candidate-decomposition:e5c4f26f-0565-4b78-9161-3b3ae9b93077:90d98a5ab03646dfb4a92e3e1eeda044d4c91525920aa358e1f2faf29db915dd

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem revenue_update_of_gt (f p x : ℕ → ℝ) :
    ∀ (n i : ℕ), n < i → ∀ (y s : ℝ),
      revenue f p (Function.update x i y) n s = revenue f p x n s := by sorry
