-- Prove2me | Definitions.Def_Evergreen_IdempotentCollapse2_OptimalCollapse
-- name    : Evergreen_IdempotentCollapse2_OptimalCollapse
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T16:37:37.389674+00:00
-- url     : https://prove2.me/theorems/1795473b-da99-4aff-b20f-c98a0123a09f
-- title:
--   Aether Catalog definitions — Evergreen_IdempotentCollapse2_OptimalCollapse
-- statement:
--   Definition bundle for the Aether Catalog module `Evergreen.IdempotentCollapse2.OptimalCollapse`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Evergreen/IdempotentCollapse2/OptimalCollapse.lean by skeleton subtraction
import Mathlib

/-!
# Optimal Collapse: Nearest-Point Projections and Optimal Transport

The "best" idempotent collapse moves each point as little as possible.
-/

open Set Function Metric

noncomputable section

/-- Total displacement caused by a map on a finite metric space. -/
def collapseDisplacement {α : Type*} [Fintype α] [PseudoMetricSpace α] (f : α → α) : ℝ :=
  ∑ x : α, dist x (f x)

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


end


