-- Prove2me | Theorems.Thm_normalized_concave
-- name    : normalized_concave
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T14:50:20.464977+00:00
-- url     : https://prove2.me/theorems/dd7a36e1-eb45-4efc-94ff-fd39b2ec4887
-- title:
--   normalized_concave
-- statement:
--   Automatically extracted helper theorem normalized_concave from oversized parent candidate 90d98a5ab03646dfb4a92e3e1eeda044d4c91525920aa358e1f2faf29db915dd.
-- source:
--   candidate-decomposition:e5c4f26f-0565-4b78-9161-3b3ae9b93077:90d98a5ab03646dfb4a92e3e1eeda044d4c91525920aa358e1f2faf29db915dd

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem normalized_concave
    (g : ℝ → ℝ) (c : ℝ) (hconc : ConcaveOn ℝ (Set.Ici 0) g) :
    ConcaveOn ℝ (Set.Ici 0) (fun t => g t - c * t) := by sorry
