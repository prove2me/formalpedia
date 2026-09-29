-- Prove2me | Definitions.Def_MachineLearning_KnownUnresolvedCards_DeckGame
-- name    : MachineLearning_KnownUnresolvedCards_DeckGame
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:46:32.189264+00:00
-- url     : https://prove2.me/theorems/603b27f5-2ac4-4692-80b4-fa603601c12f
-- title:
--   Aether Catalog definitions — MachineLearning_KnownUnresolvedCards_DeckGame
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.KnownUnresolvedCards.DeckGame`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/KnownUnresolvedCards/DeckGame.lean by skeleton subtraction
import Mathlib
import Definitions.Def_MachineLearning_KnownUnresolvedCards_Basic
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


namespace KnownUnresolvedCards

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ## A single unresolved slot -/

/-- Score of one unresolved slot: `w` if the predicted card is right, `l` if not. -/
def slotScore (w l : ℚ) (i a : α) (σ : Equiv.Perm α) : ℚ := if σ i = a then w else l



/-! ## The whole unresolved block -/

/-- Total score of the unresolved block under strategy `g`. -/
def deckScore (w l : ℚ) (g : α → α) (σ : Equiv.Perm α) : ℚ :=
  ∑ i, slotScore w l i (g i) σ





/-! ## The full game: resolved cards plus an unresolved block -/

/-- Payoff of the full deck game: `d` resolved cards paying one unit each, and
an unresolved block priced at fair odds. -/
def gamePayoff (d : ℕ) (g : α → α) : (Fin d ⊕ α) → Equiv.Perm α → ℚ :=
  Sum.elim (fun _ _ => (1 : ℚ)) (fun i σ => slotScore ((Fintype.card α : ℚ) - 1) (-1) i (g i) σ)



/-! ## Second-moment dichotomy -/







end KnownUnresolvedCards


