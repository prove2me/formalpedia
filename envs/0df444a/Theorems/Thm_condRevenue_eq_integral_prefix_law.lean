-- Prove2me | Theorems.Thm_condRevenue_eq_integral_prefix_law
-- name    : condRevenue_eq_integral_prefix_law
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T19:48:30.478915+00:00
-- url     : https://prove2.me/theorems/ece4ad20-ded2-4a30-ac70-92b03f6becb3
-- title:
--   condRevenue_eq_integral_prefix_law
-- statement:
--   Automatically extracted helper theorem condRevenue_eq_integral_prefix_law from oversized parent candidate 59ffb1bb8675d25e48599cc53041274ab0775a9f9692cf9cf3e88f765f8bfe17.
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

theorem condRevenue_eq_integral_prefix_law
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ) (k : ℕ)
    (U : Ω → Finset.Icc 1 k → ℝ)
    (rebuild : ℝ × (Finset.Icc 1 k → ℝ) → ℕ → ℝ)
    (hU : Measurable U)
    (hJoint : ∀ s, Measurable (fun z => revenue f p (rebuild z) (k + 1) s))
    (hUpdate : ∀ ω y s,
      revenue f p (Function.update (fun i => X i ω) (k + 1) y) (k + 1) s =
        revenue f p (rebuild (y, U ω)) (k + 1) s)
    (y s : ℝ) :
    ∫ u, revenue f p (rebuild (y, u)) (k + 1) s ∂Measure.map U P =
      condRevenue P X f p (k + 1) y s := by sorry
