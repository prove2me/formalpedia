-- Prove2me | solution 1 for KnownUnresolvedCards.expScore_step
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T21:38:30.010032+00:00
-- url     : https://prove2.me/submissions/a803fd03-9eed-473a-a08b-3df79dde3144

-- Sol generated from MachineLearning/KnownUnresolvedCards/FeedbackGame.lean
import Mathlib
import Definitions.Def_MachineLearning_KnownUnresolvedCards_DeckGame
import Definitions.Def_MachineLearning_KnownUnresolvedCards_FeedbackGame
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.Defs
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license.

# Known versus unresolved cards — IV. Feedback, and what information is worth

`DeckGame.lean` shows that a *blind* pass through an unresolved block of `u`
cards yields expected score exactly `1` under unit scoring and exactly `0` under
fair odds, for every strategy.  This file isolates the resource that actually
changes the picture: **feedback**.

A feedback strategy sees each card after calling it, so the only state it needs
is the set `S` of cards still unseen; a strategy is therefore a map
`g : Finset α → α`, and it is *admissible* when it names a card that is still
live, `g S ∈ S`.  The score of such a strategy on a uniformly random arrangement
of `S` satisfies the exact recursion `expScore_step`.

Two theorems then pull in opposite directions:

* `expScore_hits_eq_harmonic` — under unit scoring the expected number of
  correct calls is the harmonic number `H_u`, *unbounded* in `u`
  (`feedback_edge_unbounded`, via the Oresme bound `harmonic_two_pow_ge`).
  Feedback is worth `H_u - 1 ≈ log u` extra cards.
* `expScore_fair_eq_zero` — under stagewise fair odds, the expected payoff is
  `0` for *every* admissible feedback strategy.

So the principle "uncertainty supplies no positive edge" is not fragile:
information does not create value against a correctly priced book, it only
changes the price.  What information does buy is visible only when the book is
mispriced — and then it buys exactly `H_u - 1`.

## Main results

* `expScore_step` — the exact one-stage recursion of the feedback game.
* `expScore_fair_eq_zero` — fair odds are information-proof.
* `expScore_hits_eq_harmonic` — feedback scores `H_u` hits.
* `harmonic_two_pow_ge` — Oresme's bound `1 + n/2 ≤ H_{2^n}`.
* `feedback_edge_unbounded` — the unit-scoring edge of feedback is unbounded.
* `feedback_strictly_beats_blind` — the quantitative dichotomy.
* `fair_odds_are_information_proof` — both games are worth `0` at fair odds.
-/


open KnownUnresolvedCards

open Finset

/-! ## Harmonic preliminaries -/







/-! ## The feedback game -/

variable {α : Type*} [DecidableEq α]






/-! ## What feedback is worth -/






open KnownUnresolvedCards in
theorem solution(hit miss : ℕ → ℚ) (g : Finset α → α) {S : Finset α} (hS : S.Nonempty)
    (hg : g S ∈ S) :
    expScore hit miss g S =
      ((S.card : ℚ) * miss S.card + (hit S.card - miss S.card)
        + ∑ a ∈ S, expScore hit miss g (S.erase a)) / S.card := by
  rw [expScore.eq_def, dif_pos hS]
  congr 1
  rw [Finset.sum_attach S (fun a => (if g S = a then hit S.card else miss S.card)
      + expScore hit miss g (S.erase a))]
  rw [Finset.sum_add_distrib]
  congr 1
  have hsplit : ∀ a ∈ S, (if g S = a then hit S.card else miss S.card)
      = miss S.card + (if g S = a then hit S.card - miss S.card else 0) := by
    intro a _; by_cases h : g S = a <;> simp [h]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
    Finset.sum_ite_eq S (g S) (fun _ => hit S.card - miss S.card), if_pos hg]
