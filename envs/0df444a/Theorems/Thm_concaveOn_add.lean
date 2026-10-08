-- Prove2me | Theorems.Thm_concaveOn_add
-- name    : concaveOn_add
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T14:50:16.575975+00:00
-- url     : https://prove2.me/theorems/db7f7276-39bb-4456-a977-491b708a2756
-- title:
--   concaveOn_add
-- statement:
--   Automatically extracted helper theorem concaveOn_add from oversized parent candidate 90d98a5ab03646dfb4a92e3e1eeda044d4c91525920aa358e1f2faf29db915dd.
-- source:
--   candidate-decomposition:e5c4f26f-0565-4b78-9161-3b3ae9b93077:90d98a5ab03646dfb4a92e3e1eeda044d4c91525920aa358e1f2faf29db915dd

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem concaveOn_add {f g : ℝ → ℝ} {s : Set ℝ}
    (hf : ConcaveOn ℝ s f) (hg : ConcaveOn ℝ s g) :
    ConcaveOn ℝ s (fun x => f x + g x) := by sorry
