-- Prove2me | Theorems.Thm_revenue_integrable_of_seat_model
-- name    : revenue_integrable_of_seat_model
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T19:48:36.36015+00:00
-- url     : https://prove2.me/theorems/7bf8f2a4-d4ec-4756-9d3c-981a2ceb1393
-- title:
--   revenue_integrable_of_seat_model
-- statement:
--   Automatically extracted helper theorem revenue_integrable_of_seat_model from oversized parent candidate 59ffb1bb8675d25e48599cc53041274ab0775a9f9692cf9cf3e88f765f8bfe17.
-- source:
--   candidate-decomposition:4204a6a5-95d4-4ce8-a739-2e52d3e9523a:59ffb1bb8675d25e48599cc53041274ab0775a9f9692cf9cf3e88f765f8bfe17

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Theorems.Thm_revenue_abs_bound
import Theorems.Thm_revenue_joint_measurable
import Theorems.Thm_NestedSeatAlloc_IntPolicy_revenue_extensional_on_prefix
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem revenue_integrable_of_seat_model
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ) (hM : IsSeatModel P X f)
    (hp : IsProtectionPolicy p) (k : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    Integrable (fun ω => revenue f p (fun i => X i ω) (k + 1) s) P := by sorry
