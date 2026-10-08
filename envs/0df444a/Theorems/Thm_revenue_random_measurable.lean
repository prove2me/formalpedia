-- Prove2me | Theorems.Thm_revenue_random_measurable
-- name    : revenue_random_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T17:27:55.480142+00:00
-- url     : https://prove2.me/theorems/8b8ce95a-a6d5-49fe-b7cb-15cc6d4fb395
-- title:
--   revenue_random_measurable
-- statement:
--   Automatically extracted helper theorem revenue_random_measurable from oversized parent candidate 91ef759688a2cae856ea58212d83c96db7320add32dc3ced0a1cc8b9ffbbe3d2.
-- source:
--   candidate-decomposition:e5c4f26f-0565-4b78-9161-3b3ae9b93077:91ef759688a2cae856ea58212d83c96db7320add32dc3ced0a1cc8b9ffbbe3d2

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Theorems.Thm_revenue_joint_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem revenue_random_measurable
    {Ω : Type*} [MeasurableSpace Ω] (X : ℕ → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (f p : ℕ → ℝ) (n : ℕ) (s : ℝ) :
    Measurable (fun ω => revenue f p (fun i => X i ω) n s) := by sorry
