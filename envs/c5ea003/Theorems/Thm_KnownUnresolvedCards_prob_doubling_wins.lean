-- Prove2me | Theorems.Thm_KnownUnresolvedCards_prob_doubling_wins
-- name    : KnownUnresolvedCards.prob_doubling_wins
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:41:11.544643+00:00
-- url     : https://prove2.me/theorems/731afd3b-e995-4400-b9b7-85e07e740ee9
-- title:
--   …yet it wins with probability `1 - 2^{-n}`.
-- statement:
--   **…yet it wins with probability `1 - 2^{-n}`.**
--
--   ```lean
--   theorem KnownUnresolvedCards.prob_doubling_wins(n : ℕ) :
--       E (fun w : Fin n → Bool => if 0 < doublingGain n w then (1 : ℚ) else 0) = 1 - (1 / 2) ^ n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/KnownUnresolvedCards/BettingSystem.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/KnownUnresolvedCards/BettingSystem.lean#L107

-- Thm stub generated from MachineLearning/KnownUnresolvedCards/BettingSystem.lean
import Mathlib
import Definitions.Def_MachineLearning_KnownUnresolvedCards_Basic
import Definitions.Def_MachineLearning_KnownUnresolvedCards_BettingSystem
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license.

# Known versus unresolved cards — VI. No betting system beats a fair book

The previous files price a *fixed* menu of cards.  This file closes the loop by
letting the gambler be maximally adaptive: after every fair coin toss she may
choose a completely arbitrary new stake — of either sign, of any size, depending
on the whole history — and she may quit at any time (encoded by staking `0`).

`expGain_eq_zero` says that the expected net gain of *any* such system over any
finite horizon is exactly `0`.  This is the finite-horizon optional stopping
theorem, proved here by a two-line induction on the horizon, and it is the
strongest form of "uncertainty supplies no positive edge": not only does a
random card have no value, no adaptive scheme built out of random cards has any
value either.

The second half of the file is the standard adversarial objection — the
**doubling (martingale) system**, which wins with probability `1 - 2^{-n}` — and
its resolution: the rare loss is exactly large enough to cancel the frequent
gain.  `doubling_paradox` states the two facts side by side.

## Main results

* `expGain_eq_zero` — no adaptive betting system has an edge at fair odds.
* `optional_stopping_no_edge` — the same with an explicit stopping rule.
* `doubling_net_after_win` — the geometric-series identity `2^k - (2^k - 1) = 1`
  that makes the doubling system's net gain equal to `1` after any win.
* `E_doublingGain` — the doubling system has zero expected gain, and
* `prob_doubling_wins` — it nevertheless wins with probability `1 - 2^{-n}`.
* `doubling_paradox` — both, together with the fact that the win probability can
  be pushed arbitrarily close to `1`.
-/


open KnownUnresolvedCards

open Finset

/-! ## Adaptive betting systems -/





/-! ## The doubling system -/

theorem KnownUnresolvedCards.prob_doubling_wins(n : ℕ) :
    E (fun w : Fin n → Bool => if 0 < doublingGain n w then (1 : ℚ) else 0) = 1 - (1 / 2) ^ n := by sorry
