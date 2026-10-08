-- Prove2me | Theorems.Thm_clbi_integrable_affine_revenue_event
-- name    : clbi_integrable_affine_revenue_event
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T09:41:48.316391+00:00
-- url     : https://prove2.me/theorems/eb34c7ec-9bf3-4fe9-8eec-b5bb0238173f
-- title:
--   clbi_integrable_affine_revenue_event
-- statement:
--   Automatically extracted helper theorem clbi_integrable_affine_revenue_event from oversized parent candidate 74b92e97eaac56ec69849bb07ea290e064cd6c2948f401a7245125fe013e42f7.
-- source:
--   candidate-decomposition:4d6786ca-689f-452c-8268-ee26d45fe3f2:74b92e97eaac56ec69849bb07ea290e064cd6c2948f401a7245125fe013e42f7

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Theorems.Thm_NestedSeatAlloc_IntPolicy_revenue_succ_eq_atom_tail_pointwise
import Theorems.Thm_NestedSeatAlloc_IntPolicy_integral_expRevenue_mul_next_event_indicator
import Theorems.Thm_revenue_joint_measurable
import Theorems.Thm_revenue_abs_bound
import Theorems.Thm_clbi_integrable_revenue_event
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem clbi_integrable_affine_revenue_event
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f q : ℕ → ℝ) (hM : IsSeatModel P X f)
    (k : ℕ) (t c : ℝ) (ht : 0 ≤ t) (hq : ∀ i, 0 ≤ q i)
    (E : Set ℝ) (hE : MeasurableSet E)
    [DecidablePred (fun ω => X (k + 1) ω ∈ E)] :
    Integrable (fun ω => (c + revenue f q (fun i => X i ω) k t) *
      (if X (k + 1) ω ∈ E then (1 : ℝ) else 0)) P := by sorry
