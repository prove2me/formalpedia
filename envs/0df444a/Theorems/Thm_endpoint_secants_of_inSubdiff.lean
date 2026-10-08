-- Prove2me | Theorems.Thm_endpoint_secants_of_inSubdiff
-- name    : endpoint_secants_of_inSubdiff
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T16:51:46.494747+00:00
-- url     : https://prove2.me/theorems/237d9212-e261-4f61-b7ee-7ca132b36b32
-- title:
--   endpoint_secants_of_inSubdiff
-- statement:
--   Automatically extracted helper theorem endpoint_secants_of_inSubdiff from oversized parent candidate 91ef759688a2cae856ea58212d83c96db7320add32dc3ced0a1cc8b9ffbbe3d2.
-- source:
--   candidate-decomposition:e5c4f26f-0565-4b78-9161-3b3ae9b93077:91ef759688a2cae856ea58212d83c96db7320add32dc3ced0a1cc8b9ffbbe3d2

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem endpoint_secants_of_inSubdiff
    (g : ℝ → ℝ) (a c : ℝ) (ha : 0 ≤ a)
    (hconc : ConcaveOn ℝ (Set.Ici 0) g) (hsub : InSubdiff g a c) :
    (∀ x, x ∈ Set.Icc 0 a → x < a → c ≤ slope g x a) ∧
      (∀ y, a < y → slope g a y ≤ c) := by sorry
