-- Prove2me | Definitions.Def_MachineLearning_KnownUnresolvedCards_BettingSystem
-- name    : MachineLearning_KnownUnresolvedCards_BettingSystem
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:45:58.549481+00:00
-- url     : https://prove2.me/theorems/bb0854e7-6d19-4c85-bfe6-c572682ca32e
-- title:
--   Aether Catalog definitions — MachineLearning_KnownUnresolvedCards_BettingSystem
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.KnownUnresolvedCards.BettingSystem`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/KnownUnresolvedCards/BettingSystem.lean by skeleton subtraction
import Mathlib
import Definitions.Def_MachineLearning_KnownUnresolvedCards_Basic
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


namespace KnownUnresolvedCards

open Finset

/-! ## Adaptive betting systems -/

/-- Expected net gain of the adaptive system `stake` over `n` further fair
`±1` tosses, starting from the history `h`.  A stake of `0` encodes "stop", so
this covers optional stopping; the stake may be negative, so it covers switching
sides. -/
def expGain (stake : List Bool → ℚ) : ℕ → List Bool → ℚ
  | 0, _ => 0
  | (n + 1), h =>
      ((stake h + expGain stake n (h ++ [true]))
        + (-(stake h) + expGain stake n (h ++ [false]))) / 2


/-- Betting `bet h` until the stopping rule `stop` fires. -/
def stoppedStake (stop : List Bool → Bool) (bet : List Bool → ℚ) : List Bool → ℚ :=
  fun h => if stop h then 0 else bet h


/-! ## The doubling system -/


/-- The all-tails outcome. -/
def allFalse (n : ℕ) : Fin n → Bool := fun _ => false

/-- Net gain of the doubling system over a horizon of `n` fair tosses: by
`doubling_net_after_win` it is `+1` as soon as one toss comes up heads, and
`-(2^n - 1)` on the single all-tails outcome. -/
noncomputable def doublingGain (n : ℕ) (w : Fin n → Bool) : ℚ :=
  if w = allFalse n then -(2 ^ n - 1) else 1





end KnownUnresolvedCards


