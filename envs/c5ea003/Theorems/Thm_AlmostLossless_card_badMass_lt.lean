-- Prove2me | Theorems.Thm_AlmostLossless_card_badMass_lt
-- name    : AlmostLossless.card_badMass_lt
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:06:17.432137+00:00
-- url     : https://prove2.me/theorems/9ff3678a-4823-49cc-9340-c580cd1e46fa
-- title:
--   Markov counting bound.
-- statement:
--   **Markov counting bound.**  Strictly fewer than half of the keys make the
--   collision mass inside `A` exceed twice its average value `|S|·μ(A)/M`.  The
--   degenerate case (average `0`) is covered as well: then *no* key is bad, because
--   all the summands of a vanishing sum of non-negative terms vanish.
--
--   ```lean
--   theorem AlmostLossless.card_badMass_lt(μ : FinProbDist α) {H : Fin K → α → Fin M}
--       (hU : Universal2 H) (hK : 0 < K) (S A : Finset α) :
--       ((badMassKeys μ H S A).card : ℝ) * 2 < K := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/AlmostLosslessSharpSilent.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/AlmostLosslessSharpSilent.lean#L50

-- Thm stub generated from Bridges/AlmostLosslessSharpSilent.lean
import Mathlib
import Definitions.Def_Bridges_AlmostLosslessRandomCoding
import Definitions.Def_Bridges_AlmostLosslessSharpSilent
import Definitions.Def_Bridges_MinEntropy
/-
Copyright (c) 2025 Non-Archimedean Information Theory Project. All rights reserved.

# Almost-Lossless Compression VII: Silent Corruption is Rarer than Failure

## Bridge: Universal hashing (algebra) ↔ two-sided Markov counting (probability)

`exists_almost_lossless_scheme` produces a key whose *failure* probability is at
most `δ + |S|/M` and whose *silent corruption* probability is at most `|S|/M`.
That silent bound is wasteful: a silent error requires a symbol to be **outside**
the codebook (inside the codebook the decoder provably abstains rather than
lying) *and* to collide with the codebook.  The first event has probability at
most `δ`, so the first moment of the silent-error mass carries an extra factor
`δ`.

This file proves that the two guarantees can be obtained **simultaneously for a
single key**:

* `card_badMass_lt` — a Markov/counting bound: fewer than half of the keys are
  twice as bad as the average, for any region `A`;
* `exists_doubly_good_key` — a key that is good for the region `Sᶜ` *and* for
  the whole space at once (both bad sets have size `< K/2`, so they cannot
  cover the key space);
* `exists_sharp_almost_lossless_scheme` — **the deliverable**: a single explicit
  key with failure probability `≤ δ + 2|S|/M`, silent-corruption probability
  `≤ 2δ|S|/M` (a factor `δ` better), and decoding cost still exactly `|S|`.

This settles Conjecture 2 of the previous cycle's `FUTURE_DIRECTIONS.md`.

## Impact: sharp_silent_error_bound, two_sided_derandomization
-/


open Finset BigOperators NonArchInfoTheory

open AlmostLossless


variable {α : Type*} [Fintype α] [DecidableEq α] {K M : ℕ}

theorem AlmostLossless.card_badMass_lt(μ : FinProbDist α) {H : Fin K → α → Fin M}
    (hU : Universal2 H) (hK : 0 < K) (S A : Finset α) :
    ((badMassKeys μ H S A).card : ℝ) * 2 < K := by sorry
