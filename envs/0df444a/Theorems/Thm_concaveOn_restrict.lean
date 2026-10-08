-- Prove2me | Theorems.Thm_concaveOn_restrict
-- name    : concaveOn_restrict
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T14:50:15.173984+00:00
-- url     : https://prove2.me/theorems/63f43418-75ec-49b1-93d6-20656fc83c72
-- title:
--   concaveOn_restrict
-- statement:
--   Automatically extracted helper theorem concaveOn_restrict from oversized parent candidate 90d98a5ab03646dfb4a92e3e1eeda044d4c91525920aa358e1f2faf29db915dd.
-- source:
--   candidate-decomposition:e5c4f26f-0565-4b78-9161-3b3ae9b93077:90d98a5ab03646dfb4a92e3e1eeda044d4c91525920aa358e1f2faf29db915dd

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem concaveOn_restrict {g : ℝ → ℝ} {s t : Set ℝ}
    (hst : t ⊆ s) (hconc : ConcaveOn ℝ s g) : ConcaveOn ℝ t g := by sorry
