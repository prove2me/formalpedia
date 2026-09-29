-- Prove2me | solution 1 for KnownUnresolvedCards.expScore_hits_eq_harmonic
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T21:41:25.650346+00:00
-- url     : https://prove2.me/submissions/473d7f78-a376-4205-8a52-82c140c6a73c

-- Sol generated from MachineLearning/KnownUnresolvedCards/FeedbackGame.lean
import Mathlib
import Definitions.Def_MachineLearning_KnownUnresolvedCards_DeckGame
import Definitions.Def_MachineLearning_KnownUnresolvedCards_FeedbackGame
import Theorems.Thm_KnownUnresolvedCards_expScore_step
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


@[simp] lemma expScore_empty (hit miss : ℕ → ℚ) (g : Finset α → α) :
    expScore hit miss g (∅ : Finset α) = 0 := by
  rw [expScore.eq_def]; simp




/-! ## What feedback is worth -/






open KnownUnresolvedCards in
theorem solution(g : Finset α → α) (hg : ∀ T : Finset α, T.Nonempty → g T ∈ T)
    (S : Finset α) : expScore (fun _ => 1) (fun _ => 0) g S = harmonic S.card := by
  induction S using Finset.strongInduction with
  | _ S ih =>
    rcases S.eq_empty_or_nonempty with rfl | hS
    · simp
    · obtain ⟨k, hk⟩ : ∃ k, S.card = k + 1 :=
        ⟨S.card - 1, by have := Finset.card_pos.mpr hS; omega⟩
      rw [expScore_step _ _ _ hS (hg S hS)]
      have h0 : ∀ a ∈ S, expScore (fun _ => (1 : ℚ)) (fun _ => 0) g (S.erase a) = harmonic k := by
        intro a ha
        rw [ih (S.erase a) (Finset.erase_ssubset ha), Finset.card_erase_of_mem ha, hk]
        simp
      rw [Finset.sum_congr rfl h0, Finset.sum_const, nsmul_eq_mul, hk, harmonic_succ]
      push_cast
      field_simp
      ring
