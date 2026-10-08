-- Prove2me | Theorems.Thm_clbi_integrable_sum_range
-- name    : clbi_integrable_sum_range
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T08:19:28.259448+00:00
-- url     : https://prove2.me/theorems/578a1732-0d7f-45c2-a14e-37830b6ef96f
-- title:
--   clbi_integrable_sum_range
-- statement:
--   Automatically extracted helper theorem clbi_integrable_sum_range from oversized parent candidate cfeb58e8a13ec8428968405c11db363e015948bd2e8c68b59ec1d05448a3fa6e.
-- source:
--   candidate-decomposition:4d6786ca-689f-452c-8268-ee26d45fe3f2:cfeb58e8a13ec8428968405c11db363e015948bd2e8c68b59ec1d05448a3fa6e

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

theorem clbi_integrable_sum_range {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (F : ℕ → Ω → ℝ) :
    ∀ n, (∀ i ≤ n, Integrable (F i) P) →
      Integrable (fun ω => ∑ i ∈ Finset.range (n + 1), F i ω) P := by sorry
