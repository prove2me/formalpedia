-- Prove2me | Theorems.Thm_AlmostLossless_exists_sharp_almost_lossless_scheme
-- name    : AlmostLossless.exists_sharp_almost_lossless_scheme
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:08:12.971645+00:00
-- url     : https://prove2.me/theorems/fdce2de7-5eae-440b-b48d-40f2616e0201
-- title:
--   Sharp almost-lossless scheme (settles Conjecture 2).
-- statement:
--   **Sharp almost-lossless scheme (settles Conjecture 2).**
--
--   One explicit key gives, simultaneously:
--
--   1. failure probability `≤ δ + 2|l|/M`;
--   2. **silent** corruption probability `≤ 2δ·|l|/M` — a factor `δ` better than the
--      failure bound, because a silent error needs both an atypical symbol and a
--      collision;
--   3. decoding cost exactly `|l|` hash evaluations.
--
--   Together with `hashScheme_neverSilent_on_codebook` (no silent error is ever
--   possible on a codebook symbol) this makes silent corruption a second-order
--   event: it is quadratically small in the accuracy parameters.
--
--   ```lean
--   theorem AlmostLossless.exists_sharp_almost_lossless_scheme(μ : FinProbDist α)
--       {H : Fin K → α → Fin M} (hU : Universal2 H) (hK : 0 < K) (hM : 0 < M)
--       (l : List α) (hnd : l.Nodup) (δ : ℝ) (hδ : setMass μ (l.toFinset)ᶜ ≤ δ) :
--       ∃ k : Fin K,
--         setMass μ (Finset.univ.filter (fun x => ¬ (hashScheme l (H k)).Succeeds x))
--             ≤ δ + 2 * (l.length : ℝ) / M
--         ∧ setMass μ (Finset.univ.filter (fun x => (hashScheme l (H k)).SilentError x))
--             ≤ 2 * δ * (l.length : ℝ) / M
--         ∧ ∀ i : Fin M, (scanCost (H k) i l).2 = l.length := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/AlmostLosslessSharpSilent.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/AlmostLosslessSharpSilent.lean#L145

-- Thm stub generated from Bridges/AlmostLosslessSharpSilent.lean
import Mathlib
import Definitions.Def_Bridges_AlmostLosslessCompression
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

theorem AlmostLossless.exists_sharp_almost_lossless_scheme(μ : FinProbDist α)
    {H : Fin K → α → Fin M} (hU : Universal2 H) (hK : 0 < K) (hM : 0 < M)
    (l : List α) (hnd : l.Nodup) (δ : ℝ) (hδ : setMass μ (l.toFinset)ᶜ ≤ δ) :
    ∃ k : Fin K,
      setMass μ (Finset.univ.filter (fun x => ¬ (hashScheme l (H k)).Succeeds x))
          ≤ δ + 2 * (l.length : ℝ) / M
      ∧ setMass μ (Finset.univ.filter (fun x => (hashScheme l (H k)).SilentError x))
          ≤ 2 * δ * (l.length : ℝ) / M
      ∧ ∀ i : Fin M, (scanCost (H k) i l).2 = l.length := by sorry
