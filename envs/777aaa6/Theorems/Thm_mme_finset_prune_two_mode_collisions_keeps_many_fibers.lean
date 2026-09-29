-- Prove2me | Theorems.Thm_mme_finset_prune_two_mode_collisions_keeps_many_fibers
-- name    : mme_finset_prune_two_mode_collisions_keeps_many_fibers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T00:44:52.778459+00:00
-- url     : https://prove2.me/theorems/34d36fc7-96f0-4819-9446-5d0e3323fc9c
-- title:
--   Two-mode collision pruning preserves all but a collision-budgeted number of large fibers
-- statement:
--   Let E be a finite family with X-, Y-, and Z-labels. Suppose every selected Z-fiber has size at least K, where H≤K. There is a subset I⊆E that is isolated in the X and Y labels relative to E, and the number of selected Z-fibers whose retained size is below H satisfies $$(K-H+1)|\mathrm{Bad}|\le |\{(e,e')\in E^2:e\ne e',\ x(e)=x(e')\text{ or }y(e)=y(e')\}|.$$ Thus two-mode pruning preserves shared Z-multiplicity with the exact per-destroyed-fiber deletion cost.
-- source:
--   Finite collision deletion and disjoint Z-fiber counting

import Mathlib
import Theorems.Thm_mme_finset_prune_two_mode_collisions_isolated

open BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem mme_finset_prune_two_mode_collisions_keeps_many_fibers
    {α β γ ζ : Type}
    [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq ζ]
    (E : Finset α) (x : α → β) (y : α → γ) (z : α → ζ)
    (Good : Finset ζ) (K H : ℕ)
    (hHK : H ≤ K)
    (hdegree : ∀ c ∈ Good, K ≤ (E.filter (fun e => z e = c)).card) :
    ∃ I : Finset α,
      I ⊆ E ∧
      (∀ e ∈ I, ∀ e' ∈ E,
        x e = x e' ∨ y e = y e' → e = e') ∧
      (K - H + 1) *
          (Good.filter (fun c => ¬ H ≤
            (I.filter (fun e => z e = c)).card)).card ≤
        ((E.product E).filter (fun p =>
          p.1 ≠ p.2 ∧
            (x p.1 = x p.2 ∨ y p.1 = y p.2))).card := by
  sorry
