-- Prove2me | Definitions.Def_Bridges_AlmostLosslessSharpSilent
-- name    : Bridges_AlmostLosslessSharpSilent
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:12:12.836612+00:00
-- url     : https://prove2.me/theorems/26c36caa-17c7-416c-ad6f-e00c68dcabf7
-- title:
--   Aether Catalog definitions — Bridges_AlmostLosslessSharpSilent
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.AlmostLosslessSharpSilent`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/AlmostLosslessSharpSilent.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Bridges_AlmostLosslessCompression
import Definitions.Def_Bridges_AlmostLosslessRandomCoding
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

namespace AlmostLossless

section SharpSilent

variable {α : Type*} [Fintype α] [DecidableEq α] {K M : ℕ}

/-- The keys that are more than twice as bad as the average on the region `A`. -/
noncomputable def badMassKeys (μ : FinProbDist α) (H : Fin K → α → Fin M) (S A : Finset α) :
    Finset (Fin K) :=
  Finset.univ.filter (fun k =>
    2 * ((S.card : ℝ) * setMass μ A)
      < (M : ℝ) * setMass μ (A.filter (fun x => Collides H k S x)))




end SharpSilent

end AlmostLossless


