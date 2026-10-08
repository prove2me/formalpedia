-- Prove2me | Theorems.Thm_concaveOn_mul_const
-- name    : concaveOn_mul_const
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T14:50:24.768271+00:00
-- url     : https://prove2.me/theorems/3e0f629c-b73e-409e-8b6e-1dfc4c919cba
-- title:
--   concaveOn_mul_const
-- statement:
--   Automatically extracted helper theorem concaveOn_mul_const from oversized parent candidate 90d98a5ab03646dfb4a92e3e1eeda044d4c91525920aa358e1f2faf29db915dd.
-- source:
--   candidate-decomposition:e5c4f26f-0565-4b78-9161-3b3ae9b93077:90d98a5ab03646dfb4a92e3e1eeda044d4c91525920aa358e1f2faf29db915dd

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem concaveOn_mul_const (c : ℝ) :
    ConcaveOn ℝ (Set.Ici 0) (fun s => c * s) := by sorry
