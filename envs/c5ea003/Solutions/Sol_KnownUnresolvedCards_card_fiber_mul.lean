-- Prove2me | solution 1 for KnownUnresolvedCards.card_fiber_mul
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T21:34:00.550983+00:00
-- url     : https://prove2.me/submissions/500c9dc5-a41d-4277-ba02-0dd1a2a2ba93

-- Sol generated from MachineLearning/KnownUnresolvedCards/PermCount.lean
import Mathlib
import Definitions.Def_MachineLearning_KnownUnresolvedCards_PermCount
import Theorems.Thm_KnownUnresolvedCards_card_fiber_eq
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

lemma sum_card_fiber (i : α) : ∑ a, (fiber i a).card = Fintype.card (Equiv.Perm α) := by
  have h := Finset.card_eq_sum_card_fiberwise
    (f := fun σ : Equiv.Perm α => σ i) (s := (univ : Finset (Equiv.Perm α)))
    (t := (univ : Finset α)) (fun σ _ => mem_univ _)
  rw [Finset.card_univ] at h
  rw [h]
  exact Finset.sum_congr rfl fun a _ => by rw [fiber]




/-! ## The score of a strategy -/







/-! ## The collision profile of a strategy -/












open KnownUnresolvedCards in
theorem solution(i a : α) :
    Fintype.card α * (fiber i a).card = Fintype.card (Equiv.Perm α) := by
  rw [← sum_card_fiber i]
  rw [Finset.sum_congr rfl (fun b (_ : b ∈ (univ : Finset α)) => card_fiber_eq i b a)]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
