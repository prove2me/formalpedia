-- Prove2me | Theorems.Thm_mme_finset_two_mode_collision_pairs_card_le_of_fiber_degree
-- name    : mme_finset_two_mode_collision_pairs_card_le_of_fiber_degree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T00:13:38.93461+00:00
-- url     : https://prove2.me/theorems/93053daf-1548-4b42-b9b8-7c1fe0734e26
-- title:
--   Two-mode collision pairs are bounded by uniform fiber degree
-- statement:
--   Let E be a finite set carrying two labels x and y. If every X-label fiber and every Y-label fiber has cardinality at most D, then the number C of ordered distinct pairs sharing at least one label satisfies $$|C|\le 2|E|D.$$ This deterministic double-counting bound is useful for affine-hash collision budgets and does not assume regularity beyond the two stated fiber-degree bounds.
-- source:
--   Elementary finite double counting of two labeled collision relations

import Mathlib

set_option autoImplicit false

theorem mme_finset_two_mode_collision_pairs_card_le_of_fiber_degree
    {α β γ : Type} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (E : Finset α) (x : α → β) (y : α → γ) (D : ℕ)
    (hx : ∀ a ∈ E, (E.filter (fun b => x b = x a)).card ≤ D)
    (hy : ∀ a ∈ E, (E.filter (fun b => y b = y a)).card ≤ D) :
    ((E.product E).filter (fun p =>
      p.1 ≠ p.2 ∧ (x p.1 = x p.2 ∨ y p.1 = y p.2))).card ≤
        2 * E.card * D := by
  sorry
