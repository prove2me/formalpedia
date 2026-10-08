-- Prove2me | Theorems.Thm_condRevenue_three_branch
-- name    : condRevenue_three_branch
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T19:31:50.239618+00:00
-- url     : https://prove2.me/theorems/62ebab2a-e5f8-43ef-a16b-e5a27a84ee44
-- title:
--   condRevenue_three_branch
-- statement:
--   Automatically extracted helper theorem condRevenue_three_branch from oversized parent candidate a932e2b77ae3ebac0a95992c600dc31aaadc2129d9b6daf54864cef9c3cf2fc1.
-- source:
--   candidate-decomposition:e5c4f26f-0565-4b78-9161-3b3ae9b93077:a932e2b77ae3ebac0a95992c600dc31aaadc2129d9b6daf54864cef9c3cf2fc1

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Theorems.Thm_revenue_update_of_gt
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem condRevenue_three_branch
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ) (k : ℕ)
    (hk : 1 ≤ k) (hpk : 0 ≤ p k) (y s : ℝ) (hy : 0 ≤ y)
    (hIs : Integrable (fun ω => revenue f p (fun i => X i ω) k s) P)
    (hIa : Integrable (fun ω => revenue f p (fun i => X i ω) k (p k)) P)
    (hIr : 0 ≤ s - y →
      Integrable (fun ω => revenue f p (fun i => X i ω) k (s - y)) P) :
    condRevenue P X f p (k + 1) y s =
      if s < p k then expRevenue P X f p k s
      else if s < p k + y then (s - p k) * f (k + 1) +
        expRevenue P X f p k (p k)
      else y * f (k + 1) + expRevenue P X f p k (s - y) := by sorry
