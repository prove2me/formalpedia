-- Prove2me | Theorems.Thm_Hirsch_weighted_transition_lower_bound
-- name    : Hirsch.weighted_transition_lower_bound
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-13T18:26:41.842807+00:00
-- url     : https://prove2.me/theorems/7e735eb5-bb09-4f10-9a2b-780f1407dd92
-- title:
--   Fractional transition packing lower-bounds route length
-- statement:
--   Consider a route of L transitions and a collection of required factor changes. Assign nonnegative weights to the factors. If each factor's required demand is no larger than the total amount it changes along the route, and every single route transition carries weighted change at most one, then the weighted total demand is at most L. This supplies a reusable fractional lower bound for ordinary-edge routes when one edge may change several overlapping Minkowski factors at once.
-- source:
--   Standalone Lean proof from PR #210 direction-local extraction work: https://github.com/jjoshua2/prove2me-work/blob/formal/dual-wall-carrier-routing/research/publication_packets/pr210_catchup/weighted_transition/solution.lean

import Mathlib
open scoped BigOperators
set_option autoImplicit false
noncomputable section

theorem Hirsch.weighted_transition_lower_bound
    {ι : Type*} [Fintype ι]
    (L : ℕ) (weight demand : ι → ℝ) (change : ι → Fin L → ℝ)
    (hw : ∀ i, 0 ≤ weight i)
    (hd : ∀ i, demand i ≤ ∑ j, change i j)
    (hstep : ∀ j, (∑ i, weight i * change i j) ≤ 1) :
    (∑ i, weight i * demand i) ≤ (L : ℝ) := by sorry
