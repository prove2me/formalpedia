-- Prove2me | solution 1 for KnownUnresolvedCards.card_fiber2_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-18T00:06:50.886132+00:00
-- url     : https://prove2.me/submissions/61db0cde-099d-4011-89a9-946fd2c90f55

-- Sol generated from MachineLearning/KnownUnresolvedCards/PermCount.lean
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




@[simp] lemma mem_fiber₂ {i j a b : α} {σ : Equiv.Perm α} :
    σ ∈ fiber₂ i j a b ↔ σ i = a ∧ σ j = b := by
  simp [fiber₂]



/-! ## Transposition symmetry -/



/-! ## The counting identities -/





/-! ## The score of a strategy -/







/-! ## The collision profile of a strategy -/












open KnownUnresolvedCards in
theorem solution(i j a b b' : α) (hb : a ≠ b) (hb' : a ≠ b') :
    (fiber₂ i j a b).card = (fiber₂ i j a b').card := by
  refine Finset.card_nbij' (fun σ => Equiv.swap b b' * σ) (fun σ => Equiv.swap b b' * σ)
    ?_ ?_ ?_ ?_
  · intro σ hσ
    have h : σ i = a ∧ σ j = b := by simpa using hσ
    refine Finset.mem_coe.mpr (mem_fiber₂.mpr ⟨?_, ?_⟩)
    · simp [Equiv.Perm.mul_apply, h.1, Equiv.swap_apply_of_ne_of_ne hb hb']
    · simp [Equiv.Perm.mul_apply, h.2]
  · intro σ hσ
    have h : σ i = a ∧ σ j = b' := by simpa using hσ
    refine Finset.mem_coe.mpr (mem_fiber₂.mpr ⟨?_, ?_⟩)
    · simp [Equiv.Perm.mul_apply, h.1, Equiv.swap_apply_of_ne_of_ne hb hb']
    · simp [Equiv.Perm.mul_apply, h.2]
  · intro σ _
    simp [← mul_assoc, Equiv.swap_mul_self]
  · intro σ _
    simp [← mul_assoc, Equiv.swap_mul_self]
