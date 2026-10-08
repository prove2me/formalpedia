-- Prove2me | Theorems.Thm_clbi_integral_sum_range
-- name    : clbi_integral_sum_range
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T09:00:32.806855+00:00
-- url     : https://prove2.me/theorems/bfd9236d-0460-4024-a1b1-d26a193e567a
-- title:
--   clbi_integral_sum_range
-- statement:
--   Automatically extracted helper theorem clbi_integral_sum_range from oversized parent candidate 301528b083909060eb766db4d2a2a1644f76dd3fd1fb67fac3bdd32a1814eb1f.
-- source:
--   candidate-decomposition:4d6786ca-689f-452c-8268-ee26d45fe3f2:301528b083909060eb766db4d2a2a1644f76dd3fd1fb67fac3bdd32a1814eb1f

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Theorems.Thm_NestedSeatAlloc_IntPolicy_revenue_succ_eq_atom_tail_pointwise
import Theorems.Thm_NestedSeatAlloc_IntPolicy_integral_expRevenue_mul_next_event_indicator
import Theorems.Thm_revenue_joint_measurable
import Theorems.Thm_revenue_abs_bound
import Theorems.Thm_clbi_integrable_sum_range
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem clbi_integral_sum_range {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (F : ℕ → Ω → ℝ) :
    ∀ n, (∀ i ≤ n, Integrable (F i) P) →
      ∫ ω, (∑ i ∈ Finset.range (n + 1), F i ω) ∂P =
        ∑ i ∈ Finset.range (n + 1), ∫ ω, F i ω ∂P := by sorry
