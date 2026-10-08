-- Prove2me | Theorems.Thm_revenue_integrable
-- name    : revenue_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T19:32:07.674873+00:00
-- url     : https://prove2.me/theorems/334faed4-8787-4e65-9587-7ce64a71d107
-- title:
--   revenue_integrable
-- statement:
--   Automatically extracted helper theorem revenue_integrable from oversized parent candidate a932e2b77ae3ebac0a95992c600dc31aaadc2129d9b6daf54864cef9c3cf2fc1.
-- source:
--   candidate-decomposition:e5c4f26f-0565-4b78-9161-3b3ae9b93077:a932e2b77ae3ebac0a95992c600dc31aaadc2129d9b6daf54864cef9c3cf2fc1

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Theorems.Thm_revenue_random_measurable
import Theorems.Thm_revenue_abs_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem revenue_integrable
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (f p : ℕ → ℝ) (hp : ∀ j, 1 ≤ j → 0 ≤ p j)
    (hXnonneg : ∀ i ω, 0 ≤ X i ω) (M : ℝ) (hM : 0 ≤ M)
    (n : ℕ) (hfare : ∀ j, 1 ≤ j → j ≤ n → |f j| ≤ M)
    (s : ℝ) (hs : 0 ≤ s) :
    Integrable (fun ω => revenue f p (fun i => X i ω) n s) P := by sorry
