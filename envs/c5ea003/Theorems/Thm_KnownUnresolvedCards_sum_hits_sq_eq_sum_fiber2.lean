-- Prove2me | Theorems.Thm_KnownUnresolvedCards_sum_hits_sq_eq_sum_fiber2
-- name    : KnownUnresolvedCards.sum_hits_sq_eq_sum_fiber2
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-18T00:09:09.760873+00:00
-- url     : https://prove2.me/theorems/1a1fc351-3b42-49bd-97e3-577f91d6c301
-- title:
--   Expansion of the second moment as a double sum of two-slot fibre counts.
-- statement:
--   Expansion of the second moment as a double sum of two-slot fibre counts.
--
--   ```lean
--   theorem KnownUnresolvedCards.sum_hits_sq_eq_sum_fiber₂(g : α → α) :
--       ∑ σ : Equiv.Perm α, (hits g σ) ^ 2 = ∑ i, ∑ j, (fiber₂ i j (g i) (g j)).card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/KnownUnresolvedCards/PermCount.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/KnownUnresolvedCards/PermCount.lean#L181

-- Thm stub generated from MachineLearning/KnownUnresolvedCards/PermCount.lean
import Mathlib
import Definitions.Def_MachineLearning_KnownUnresolvedCards_PermCount
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license.

# Known versus unresolved cards — II. Fibre counting for shuffled decks

The unresolved part of a deck is modelled by a uniformly random bijection
`σ : α ≃ α` between *slots* and *cards*.  A *strategy* is an arbitrary function
`g : α → α` ("in slot `i` I predict card `g i`"); it need not be injective, so a
gambler is allowed to name the same card twice.

Everything about the mean and variance of the score of such a strategy is
controlled by two combinatorial counts:

* `fiber i a`  — permutations with `σ i = a`;
* `fiber₂ i j a b` — permutations with `σ i = a` and `σ j = b`.

We compute both **without ever mentioning a factorial**, using only the
transitivity of the left translation action of transpositions on
`Equiv.Perm α`:

* `card_fiber_mul`  : `|α| * |fiber i a| = |Perm α|`;
* `card_fiber₂_mul` : `(|α| - 1) * |fiber₂ i j a b| = |fiber i a|` for `i ≠ j`, `a ≠ b`.

## Main results

* `card_fiber_eq`, `card_fiber₂_eq` — transposition symmetry of the fibres.
* `card_fiber_mul`, `card_fiber₂_mul` — the two counting identities.
* `sum_hits_eq_card_perm` — **strategy invariance of the mean**: for *every*
  `g : α → α`, `∑ σ, hits g σ = |Perm α|`, i.e. the mean score is exactly `1`.
* `sum_hits_sq_eq_two_mul` — for an *injective* strategy the second moment is
  `2 |Perm α|`.
* `sum_hits_sq_collision` — the second moment of an **arbitrary** strategy,
  governed by its collision profile `distinctCallPairs`.
* `hits_const_eq_one` — a constant strategy scores exactly `1`, deterministically.
-/


open KnownUnresolvedCards

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ## The two fibres -/







/-! ## Transposition symmetry -/



/-! ## The counting identities -/





/-! ## The score of a strategy -/

theorem KnownUnresolvedCards.sum_hits_sq_eq_sum_fiber2(g : α → α) :
    ∑ σ : Equiv.Perm α, (hits g σ) ^ 2 = ∑ i, ∑ j, (fiber₂ i j (g i) (g j)).card := by sorry
