-- Prove2me | Theorems.Thm_clbi_integrable_revenue_event
-- name    : clbi_integrable_revenue_event
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T08:26:02.975864+00:00
-- url     : https://prove2.me/theorems/7f89f0db-16ad-41aa-a559-1a1c8f316a87
-- title:
--   clbi_integrable_revenue_event
-- statement:
--   Automatically extracted helper theorem clbi_integrable_revenue_event from oversized parent candidate 301528b083909060eb766db4d2a2a1644f76dd3fd1fb67fac3bdd32a1814eb1f.
-- source:
--   candidate-decomposition:4d6786ca-689f-452c-8268-ee26d45fe3f2:301528b083909060eb766db4d2a2a1644f76dd3fd1fb67fac3bdd32a1814eb1f

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Theorems.Thm_NestedSeatAlloc_IntPolicy_revenue_succ_eq_atom_tail_pointwise
import Theorems.Thm_NestedSeatAlloc_IntPolicy_integral_expRevenue_mul_next_event_indicator
import Theorems.Thm_revenue_joint_measurable
import Theorems.Thm_revenue_abs_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem clbi_integrable_revenue_event
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (f q : ℕ → ℝ) (hM : IsSeatModel P X f)
    (k : ℕ) (t : ℝ) (ht : 0 ≤ t) (hq : ∀ i, 0 ≤ q i)
    (E : Set ℝ) (hE : MeasurableSet E)
    [DecidablePred (fun ω => X (k + 1) ω ∈ E)] :
    Integrable (fun ω => revenue f q (fun i => X i ω) k t *
      (if X (k + 1) ω ∈ E then (1 : ℝ) else 0)) P := by sorry
