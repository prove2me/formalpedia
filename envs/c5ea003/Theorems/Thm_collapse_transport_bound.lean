-- Prove2me | Theorems.Thm_collapse_transport_bound
-- name    : collapse_transport_bound
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T16:53:23.12888+00:00
-- url     : https://prove2.me/theorems/6c2f8b7f-254e-4206-8e83-017508146ac9
-- title:
--   Collapse transport bound
-- statement:
--   Formal statement of `collapse_transport_bound` from the Aether Catalog (Evergreen). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem collapse_transport_bound{α : Type*} [Fintype α] [PseudoMetricSpace α]
--       [BoundedSpace α] (f : α → α) :
--       collapseDisplacement f ≤
--       (Fintype.card α : ℝ) * Metric.diam (Set.univ : Set α) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Evergreen/IdempotentCollapse2/OptimalCollapse.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Evergreen/IdempotentCollapse2/OptimalCollapse.lean#L39

-- Thm stub generated from Evergreen/IdempotentCollapse2/OptimalCollapse.lean
import Mathlib
import Definitions.Def_Evergreen_IdempotentCollapse2_OptimalCollapse

/-!
# Optimal Collapse: Nearest-Point Projections and Optimal Transport

The "best" idempotent collapse moves each point as little as possible.
-/

open Set Function Metric

noncomputable section


/-
PROBLEM
An idempotent with zero displacement is the identity.

PROVIDED SOLUTION
collapseDisplacement f = ∑ dist(x, f(x)) = 0. Since dist ≥ 0, each term must be 0. dist(x, f(x)) = 0 implies f(x) = x in a MetricSpace. Use Finset.sum_eq_zero_iff_of_nonneg with dist_nonneg.
-/

/-
PROBLEM
Transport cost bounded by card × diameter.

PROVIDED SOLUTION
Each dist(x, f(x)) ≤ diam(univ). Sum over all x gives ∑ dist(x,f(x)) ≤ card α * diam(univ). Use Finset.sum_le_card_nsmul and dist_le_diam_of_mem (trivial: x and f(x) are in univ).
-/

theorem collapse_transport_bound{α : Type*} [Fintype α] [PseudoMetricSpace α]
    [BoundedSpace α] (f : α → α) :
    collapseDisplacement f ≤
    (Fintype.card α : ℝ) * Metric.diam (Set.univ : Set α) := by sorry
