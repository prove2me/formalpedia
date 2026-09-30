-- Prove2me | Theorems.Thm_Hirsch_nonnegative_packing_region_downward_closed
-- name    : Hirsch.nonnegative_packing_region_downward_closed
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-13T18:25:20.483557+00:00
-- url     : https://prove2.me/theorems/ba1e8a52-7453-4bc2-b1ea-b022512a8977
-- title:
--   Nonnegative linear packing regions are downward closed
-- statement:
--   Let a feasible scale vector t satisfy a finite family of linear packing inequalities whose coefficients are all nonnegative. Any other nonnegative vector s bounded coordinatewise by t is feasible as well. This elementary downward-closure property is used for exact simultaneous Minkowski-summand extraction regions: once a collection of candidate scales can be removed, reducing any subset of those scales preserves feasibility.
-- source:
--   Standalone Lean proof from PR #210 finite-summand packing work: https://github.com/jjoshua2/prove2me-work/blob/formal/dual-wall-carrier-routing/research/publication_packets/pr210_catchup/packing_downward/solution.lean

import Mathlib
open scoped BigOperators
set_option autoImplicit false
noncomputable section

theorem Hirsch.nonnegative_packing_region_downward_closed
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Γ : κ → ι → ℝ) (b : κ → ℝ)
    (hΓ : ∀ j i, 0 ≤ Γ j i) {s t : ι → ℝ}
    (ht_nonnegative : ∀ i, 0 ≤ t i)
    (ht_rows : ∀ j, (∑ i, Γ j i * t i) ≤ b j)
    (hs_nonnegative : ∀ i, 0 ≤ s i)
    (hst : ∀ i, s i ≤ t i) :
    (∀ i, 0 ≤ s i) ∧ ∀ j, (∑ i, Γ j i * s i) ≤ b j := by sorry
