-- Prove2me | Theorems.Thm_mme_finset_equal_or_opposite_code_pairs_card_le
-- name    : mme_finset_equal_or_opposite_code_pairs_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T22:16:59.855573+00:00
-- url     : https://prove2.me/theorems/17bf006f-06aa-4039-9bb9-027a1b3041df
-- title:
--   At most two dependent partners under an injective additive code
-- statement:
--   Let $c$ be an injective map from a finite set $A$ into an additive group. Then the number of ordered pairs whose codes are equal or opposite satisfies
--
--   $$
--   \bigl|\{(a,b)\in A^2:c(a)=c(b)\text{ or }c(a)=-c(b)\}\bigr|\le2|A|.
--   $$
--
--   For each fixed first element, injectivity allows at most one equal-code partner and at most one opposite-code partner. The result is formulated without assuming that opposite partners exist or that the two classes are disjoint, which makes it suitable as a robust dependency bound in finite second-moment calculations.
-- source:
--   Elementary finite combinatorics; union bound for the equal and opposite fibers of an injective code

import Mathlib

set_option autoImplicit false

theorem mme_finset_equal_or_opposite_code_pairs_card_le
    {α R : Type} [DecidableEq α] [DecidableEq R] [AddGroup R]
    (A : Finset α) (c : α → R) (hc : Function.Injective c) :
    (((A.product A).filter (fun p =>
      c p.1 = c p.2 ∨ c p.1 = -c p.2)).card) ≤ 2 * A.card := by
  sorry
