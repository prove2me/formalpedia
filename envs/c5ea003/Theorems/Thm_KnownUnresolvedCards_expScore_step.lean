-- Prove2me | Theorems.Thm_KnownUnresolvedCards_expScore_step
-- name    : KnownUnresolvedCards.expScore_step
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:40:22.307883+00:00
-- url     : https://prove2.me/theorems/66c310d5-d65c-4afd-b2a5-14847f291c71
-- title:
--   One-stage recursion.
-- statement:
--   **One-stage recursion.**  For an admissible call `g S ∈ S`, exactly one of
--   the `|S|` equally likely cards is a hit.
--
--   ```lean
--   theorem KnownUnresolvedCards.expScore_step(hit miss : ℕ → ℚ) (g : Finset α → α) {S : Finset α} (hS : S.Nonempty)
--       (hg : g S ∈ S) :
--       expScore hit miss g S =
--         ((S.card : ℚ) * miss S.card + (hit S.card - miss S.card)
--           + ∑ a ∈ S, expScore hit miss g (S.erase a)) / S.card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/KnownUnresolvedCards/FeedbackGame.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/KnownUnresolvedCards/FeedbackGame.lean#L122

-- Thm stub generated from MachineLearning/KnownUnresolvedCards/FeedbackGame.lean
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

theorem KnownUnresolvedCards.expScore_step(hit miss : ℕ → ℚ) (g : Finset α → α) {S : Finset α} (hS : S.Nonempty)
    (hg : g S ∈ S) :
    expScore hit miss g S =
      ((S.card : ℚ) * miss S.card + (hit S.card - miss S.card)
        + ∑ a ∈ S, expScore hit miss g (S.erase a)) / S.card := by sorry
