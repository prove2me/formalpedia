-- Prove2me | Theorems.Thm_measurable_prefixRevenueRebuild
-- name    : measurable_prefixRevenueRebuild
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T19:57:02.925581+00:00
-- url     : https://prove2.me/theorems/ffa7a070-5fb4-4a29-a7f6-bab77da98ae5
-- title:
--   measurable_prefixRevenueRebuild
-- statement:
--   Automatically extracted helper theorem measurable_prefixRevenueRebuild from oversized parent candidate 59ffb1bb8675d25e48599cc53041274ab0775a9f9692cf9cf3e88f765f8bfe17.
-- source:
--   candidate-decomposition:4204a6a5-95d4-4ce8-a739-2e52d3e9523a:59ffb1bb8675d25e48599cc53041274ab0775a9f9692cf9cf3e88f765f8bfe17

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Theorems.Thm_revenue_abs_bound
import Theorems.Thm_revenue_joint_measurable
import Theorems.Thm_NestedSeatAlloc_IntPolicy_revenue_extensional_on_prefix
import Definitions.Def_prefixRevenueRebuild
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem measurable_prefixRevenueRebuild (k : ℕ) :
    Measurable (prefixRevenueRebuild k) := by sorry
