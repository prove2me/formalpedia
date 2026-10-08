-- Prove2me | Theorems.Thm_normalized_mono_of_endpoint_secants
-- name    : normalized_mono_of_endpoint_secants
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T14:50:53.039565+00:00
-- url     : https://prove2.me/theorems/b87a96b3-6031-4560-8b63-15c8c31905d4
-- title:
--   normalized_mono_of_endpoint_secants
-- statement:
--   Automatically extracted helper theorem normalized_mono_of_endpoint_secants from oversized parent candidate 90d98a5ab03646dfb4a92e3e1eeda044d4c91525920aa358e1f2faf29db915dd.
-- source:
--   candidate-decomposition:e5c4f26f-0565-4b78-9161-3b3ae9b93077:90d98a5ab03646dfb4a92e3e1eeda044d4c91525920aa358e1f2faf29db915dd

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem normalized_mono_of_endpoint_secants
    (g : ℝ → ℝ) (a c : ℝ) (ha : 0 ≤ a)
    (hconc : ConcaveOn ℝ (Set.Ici 0) g)
    (hleft : ∀ x, x ∈ Set.Icc 0 a → x < a → c ≤ slope g x a)
    (hright : ∀ y, a < y → slope g a y ≤ c) :
    MonotoneOn (fun x => g x - c * x) (Set.Icc 0 a) ∧
      AntitoneOn (fun x => g x - c * x) (Set.Ici a) := by sorry
