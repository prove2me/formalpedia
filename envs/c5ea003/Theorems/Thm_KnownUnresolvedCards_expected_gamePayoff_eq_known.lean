-- Prove2me | Theorems.Thm_KnownUnresolvedCards_expected_gamePayoff_eq_known
-- name    : KnownUnresolvedCards.expected_gamePayoff_eq_known
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:40:28.063886+00:00
-- url     : https://prove2.me/theorems/a59c0332-e7c1-4abb-9caa-b73312748b4e
-- title:
--   Headline theorem: known versus unresolved cards.
-- statement:
--   **Headline theorem: known versus unresolved cards.**  If `d` cards are
--   predicted with certainty and the remaining `u = |α|` cards are fair guesses,
--   the expected payoff is exactly `d`.  Uncertainty supplies no positive edge.
--
--   ```lean
--   theorem KnownUnresolvedCards.expected_gamePayoff_eq_known[Nonempty α] (d : ℕ) (g : α → α) :
--       E (fun σ : Equiv.Perm α => ∑ c : Fin d ⊕ α, gamePayoff d g c σ) = (d : ℚ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/KnownUnresolvedCards/DeckGame.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/KnownUnresolvedCards/DeckGame.lean#L137

-- Thm stub generated from MachineLearning/KnownUnresolvedCards/DeckGame.lean
import Mathlib
import Definitions.Def_MachineLearning_KnownUnresolvedCards_Basic
import Definitions.Def_MachineLearning_KnownUnresolvedCards_DeckGame
import Definitions.Def_MachineLearning_KnownUnresolvedCards_PermCount
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license.

# Known versus unresolved cards — III. The deck game

We now assemble the pieces.  A deck consists of

* `d` **resolved** cards, each paying a deterministic unit;
* an **unresolved** block indexed by a nonempty finite type `α`, whose true
  arrangement is a uniformly random bijection `σ : α ≃ α` and on which the
  predictor plays an arbitrary strategy `g : α → α`.

The scoring of an unresolved slot is `w` on a hit and `l` on a miss.

## Main results

* `E_slotScore` — the **master formula** for a single unresolved slot:
  `E = (w - l)/|α| + l`, *independent of the slot and of the strategy*.
* `expected_deckScore` — for the whole unresolved block,
  `E = (w - l) + l * |α|`.
* `fair_odds_iff` — **rigidity of fair odds**: the unresolved block has zero
  expected value iff `w = l * (1 - |α|)`; for `l = -1` this is exactly the
  `(|α| - 1) : 1` payout.  So the "no edge" phenomenon is not an accident of a
  lucky normalisation: it *characterises* fair odds.
* `expected_gamePayoff_eq_known` — **the headline theorem**: with `d` resolved
  cards and a fair-odds unresolved block, the expected payoff is exactly `d`.
* `expected_unit_score_eq_known_add_one` — **the counting anomaly**: with naive
  unit scoring (`1` for a hit, `0` for a miss) the expected payoff is `d + 1`,
  for *every* strategy and *every* size of the unresolved block.  The apparent
  "edge" of uncertainty is one single card, and it is a scoring artefact.
* `Var_hits_collision` — the exact variance of an arbitrary strategy, equal to
  its normalised collision profile.
* `Var_hits_injective`, `Var_hits_const` — **second-moment dichotomy**: the mean score
  is strategy-invariant but the variance is not (`1` for an injective strategy,
  `0` for a constant one).  Uncertainty offers no edge in the mean, yet the
  strategy fully controls the risk.
-/


open KnownUnresolvedCards

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ## A single unresolved slot -/




/-! ## The whole unresolved block -/






/-! ## The full game: resolved cards plus an unresolved block -/

theorem KnownUnresolvedCards.expected_gamePayoff_eq_known[Nonempty α] (d : ℕ) (g : α → α) :
    E (fun σ : Equiv.Perm α => ∑ c : Fin d ⊕ α, gamePayoff d g c σ) = (d : ℚ) := by sorry
