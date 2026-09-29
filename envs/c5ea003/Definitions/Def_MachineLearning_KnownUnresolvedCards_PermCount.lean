-- Prove2me | Definitions.Def_MachineLearning_KnownUnresolvedCards_PermCount
-- name    : MachineLearning_KnownUnresolvedCards_PermCount
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:45:44.323984+00:00
-- url     : https://prove2.me/theorems/cc292097-22be-4a61-a1c8-2950155b7514
-- title:
--   Aether Catalog definitions — MachineLearning_KnownUnresolvedCards_PermCount
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.KnownUnresolvedCards.PermCount`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/KnownUnresolvedCards/PermCount.lean by skeleton subtraction
import Mathlib
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


namespace KnownUnresolvedCards

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ## The two fibres -/

/-- Permutations placing card `a` in slot `i`. -/
def fiber (i a : α) : Finset (Equiv.Perm α) := univ.filter (fun σ => σ i = a)

/-- Permutations placing card `a` in slot `i` and card `b` in slot `j`. -/
def fiber₂ (i j a b : α) : Finset (Equiv.Perm α) :=
  univ.filter (fun σ => σ i = a ∧ σ j = b)





/-! ## Transposition symmetry -/



/-! ## The counting identities -/





/-! ## The score of a strategy -/

/-- The number of slots in which the strategy `g` correctly names the card. -/
def hits (g : α → α) (σ : Equiv.Perm α) : ℕ := (univ.filter (fun i => σ i = g i)).card






/-! ## The collision profile of a strategy -/

/-- The number of slots whose call differs from the call made at slot `i`. -/
def distinctCalls (g : α → α) (i : α) : ℕ := (univ.filter (fun j => g i ≠ g j)).card

/-- The **collision profile** of a strategy: the number of *ordered* pairs of
slots receiving distinct calls.  It is `u(u-1)` for an injective strategy and `0`
for a constant one. -/
def distinctCallPairs (g : α → α) : ℕ := ∑ i, distinctCalls g i









end KnownUnresolvedCards


