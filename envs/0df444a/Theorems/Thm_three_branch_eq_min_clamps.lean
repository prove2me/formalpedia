-- Prove2me | Theorems.Thm_three_branch_eq_min_clamps
-- name    : three_branch_eq_min_clamps
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T14:50:14.316988+00:00
-- url     : https://prove2.me/theorems/8b168430-bd69-484a-8e50-ead5bea60cb0
-- title:
--   three_branch_eq_min_clamps
-- statement:
--   Automatically extracted helper theorem three_branch_eq_min_clamps from oversized parent candidate 90d98a5ab03646dfb4a92e3e1eeda044d4c91525920aa358e1f2faf29db915dd.
-- source:
--   candidate-decomposition:e5c4f26f-0565-4b78-9161-3b3ae9b93077:90d98a5ab03646dfb4a92e3e1eeda044d4c91525920aa358e1f2faf29db915dd

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem three_branch_eq_min_clamps
    (g h : ℝ → ℝ) (a c y s : ℝ) (ha : 0 ≤ a) (hy : 0 ≤ y)
    (hs : 0 ≤ s) (hg : ∀ t, g t = c * t + h t)
    (hleft : MonotoneOn h (Set.Icc 0 a))
    (hright : AntitoneOn h (Set.Ici a)) :
    (if s < a then g s else if s < a + y then (s - a) * c + g a
      else y * c + g (s - y)) =
      c * s + min (h (min s a)) (h (max (s - y) a)) := by sorry
