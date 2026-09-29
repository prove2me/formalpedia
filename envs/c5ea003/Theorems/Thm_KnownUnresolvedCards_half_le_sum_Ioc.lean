-- Prove2me | Theorems.Thm_KnownUnresolvedCards_half_le_sum_Ioc
-- name    : KnownUnresolvedCards.half_le_sum_Ioc
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:40:42.896983+00:00
-- url     : https://prove2.me/theorems/96c3b3a0-ea2a-449a-b115-d14fd8054d62
-- title:
--   Half le sum Ioc
-- statement:
--   Formal statement of `KnownUnresolvedCards.half_le_sum_Ioc` from the Aether Catalog (MachineLearning). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem KnownUnresolvedCards.half_le_sum_Ioc{m : ℕ} (hm : 1 ≤ m) :
--       (1 : ℚ) / 2 ≤ ∑ i ∈ Finset.Ioc m (2 * m), (i : ℚ)⁻¹ := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/KnownUnresolvedCards/FeedbackGame.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/KnownUnresolvedCards/FeedbackGame.lean#L55

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

theorem KnownUnresolvedCards.half_le_sum_Ioc{m : ℕ} (hm : 1 ≤ m) :
    (1 : ℚ) / 2 ≤ ∑ i ∈ Finset.Ioc m (2 * m), (i : ℚ)⁻¹ := by sorry
