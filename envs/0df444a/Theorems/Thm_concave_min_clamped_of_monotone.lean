-- Prove2me | Theorems.Thm_concave_min_clamped_of_monotone
-- name    : concave_min_clamped_of_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T14:50:17.770475+00:00
-- url     : https://prove2.me/theorems/5a63f362-997b-4507-b7e4-342ea47cfc97
-- title:
--   concave_min_clamped_of_monotone
-- statement:
--   Automatically extracted helper theorem concave_min_clamped_of_monotone from oversized parent candidate 90d98a5ab03646dfb4a92e3e1eeda044d4c91525920aa358e1f2faf29db915dd.
-- source:
--   candidate-decomposition:e5c4f26f-0565-4b78-9161-3b3ae9b93077:90d98a5ab03646dfb4a92e3e1eeda044d4c91525920aa358e1f2faf29db915dd

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem concave_min_clamped_of_monotone
    (a y : ℝ) (ha : 0 ≤ a) (hy : 0 ≤ y) (h : ℝ → ℝ)
    (hh : ConcaveOn ℝ (Set.Ici 0) h)
    (hleft : MonotoneOn h (Set.Icc 0 a))
    (hright : AntitoneOn h (Set.Ici a)) :
    ConcaveOn ℝ (Set.Ici 0)
      (fun s => min (h (min s a)) (h (max (s - y) a))) := by sorry
