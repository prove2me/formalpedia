-- Prove2me | Theorems.Thm_revenue_update_succ_eq
-- name    : revenue_update_succ_eq
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T19:03:34.726185+00:00
-- url     : https://prove2.me/theorems/061a0a77-456d-4d46-9afa-c4386249bb2f
-- title:
--   revenue_update_succ_eq
-- statement:
--   Automatically extracted helper theorem revenue_update_succ_eq from oversized parent candidate 90d98a5ab03646dfb4a92e3e1eeda044d4c91525920aa358e1f2faf29db915dd.
-- source:
--   candidate-decomposition:e5c4f26f-0565-4b78-9161-3b3ae9b93077:90d98a5ab03646dfb4a92e3e1eeda044d4c91525920aa358e1f2faf29db915dd

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Theorems.Thm_revenue_update_of_gt

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem revenue_update_succ_eq
    (f p x : ℕ → ℝ) (k : ℕ) (hk : 1 ≤ k) (y s : ℝ) :
    revenue f p (Function.update x (k + 1) y) (k + 1) s =
      if s < p k then revenue f p x k s
      else if s < p k + y then (s - p k) * f (k + 1) + revenue f p x k (p k)
      else y * f (k + 1) + revenue f p x k (s - y) := by sorry
