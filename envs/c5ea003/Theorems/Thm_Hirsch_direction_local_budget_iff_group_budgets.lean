-- Prove2me | Theorems.Thm_Hirsch_direction_local_budget_iff_group_budgets
-- name    : Hirsch.direction_local_budget_iff_group_budgets
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-13T18:23:51.037681+00:00
-- url     : https://prove2.me/theorems/f18c9025-ee8a-4a89-97d9-ac3bd239dbb6
-- title:
--   Direction-local group budgets exactly characterize a covered global edge budget
-- statement:
--   Suppose nonnegative candidate scales contribute nonnegative lengths to a family of edge-capacity constraints. Assume every edge has a certified group containing all candidates with nonzero contribution on that edge. Then the full global capacity inequalities hold exactly when every listed group satisfies its corresponding restricted inequalities. Groups may overlap; no partition or disjointness assumption is required. This is the finite budget identity used by direction-local Minkowski extraction, while the geometric proof that candidate edge contributions admit such a cover is a separate ingredient.
-- source:
--   Standalone Lean proof from PR #210 direction-local extraction work: https://github.com/jjoshua2/prove2me-work/blob/formal/dual-wall-carrier-routing/research/publication_packets/pr210_catchup/direction_local_budget/solution.lean

import Mathlib
open scoped BigOperators
set_option autoImplicit false
noncomputable section

theorem Hirsch.direction_local_budget_iff_group_budgets
    {ι ε : Type*} [Fintype ι] [DecidableEq ι]
    (groups : Finset (Finset ι)) (length : ε → ι → ℝ)
    (capacity : ε → ℝ) (scale : ι → ℝ)
    (hs : ∀ i, 0 ≤ scale i) (hl : ∀ e i, 0 ≤ length e i)
    (hcover : ∀ e, ∃ I ∈ groups, ∀ i, i ∉ I → length e i = 0) :
    (∀ e, (∑ i, scale i * length e i) ≤ capacity e) ↔
      (∀ I ∈ groups, ∀ e, (∑ i ∈ I, scale i * length e i) ≤ capacity e) := by sorry
