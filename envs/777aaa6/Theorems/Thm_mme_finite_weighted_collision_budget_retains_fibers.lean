-- Prove2me | Theorems.Thm_mme_finite_weighted_collision_budget_retains_fibers
-- name    : mme_finite_weighted_collision_budget_retains_fibers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T01:00:03.895703+00:00
-- url     : https://prove2.me/theorems/714b0ac0-e7be-47ae-9811-320ac2ad671e
-- title:
--   Weighted collision averaging retains many shared fibers at one parameter
-- statement:
--   Let Ω be a nonempty finite parameter space. For each ω, let Eω be a finite family with X-, Y-, and Z-labels, and let Gω be selected Z-labels whose Eω-fibers all have size at least K. Fix H≤K, a positive weight R, and a desired retained count Q. If the aggregate good-fiber mass dominates both the baseline and the ordered X/Y collision mass according to $$|Ω|(K-H+1)RQ+R\sum_ω c(ω)\le (K-H+1)R\sum_ω |G_ω|,$$ then one parameter ω has an X/Y-isolated subset retaining at least Q selected Z-fibers of size at least H. This is a generic same-parameter averaging and shared-fiber pruning kernel.
-- source:
--   Finite weighted averaging combined with quantitative two-mode collision pruning

import Mathlib
import Theorems.Thm_mme_finset_prune_two_mode_collisions_keeps_many_fibers

open BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem mme_finite_weighted_collision_budget_retains_fibers
    {Ω α β γ ζ : Type}
    [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq ζ]
    (E : Ω → Finset α) (x : α → β) (y : α → γ) (z : α → ζ)
    (Good : Ω → Finset ζ) (K H Q R : ℕ)
    (hHK : H ≤ K) (hR : 0 < R)
    (hdegree : ∀ ω, ∀ c ∈ Good ω,
      K ≤ ((E ω).filter (fun e => z e = c)).card)
    (hbudget :
      Fintype.card Ω * ((K - H + 1) * R * Q) +
          R * ∑ ω, (((E ω).product (E ω)).filter (fun p =>
            p.1 ≠ p.2 ∧
              (x p.1 = x p.2 ∨ y p.1 = y p.2))).card ≤
        (K - H + 1) * R * ∑ ω, (Good ω).card) :
    ∃ ω : Ω, ∃ I : Finset α,
      I ⊆ E ω ∧
      (∀ e ∈ I, ∀ e' ∈ E ω,
        x e = x e' ∨ y e = y e' → e = e') ∧
      Q ≤ ((Good ω).filter (fun c =>
        H ≤ (I.filter (fun e => z e = c)).card)).card := by
  sorry
