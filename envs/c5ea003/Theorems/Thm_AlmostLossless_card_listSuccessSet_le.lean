-- Prove2me | Theorems.Thm_AlmostLossless_card_listSuccessSet_le
-- name    : AlmostLossless.card_listSuccessSet_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:06:59.764337+00:00
-- url     : https://prove2.me/theorems/a17a5f1f-2622-48b7-9055-ddefa86b0b66
-- title:
--   Pigeonhole for list decoders.
-- statement:
--   **Pigeonhole for list decoders.**  Each codeword can rescue at most `T`
--   symbols, so at most `T·|Code|` symbols are recovered.
--
--   ```lean
--   theorem AlmostLossless.card_listSuccessSet_le[Fintype Code] [DecidableEq Code]
--       (s : ListScheme α Code) (T : ℕ) (hT : ∀ c, (s.dec c).length ≤ T) :
--       (listSuccessSet s).card ≤ Fintype.card Code * T := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/AlmostLosslessListDecoding.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/AlmostLosslessListDecoding.lean#L63

-- Thm stub generated from Bridges/AlmostLosslessListDecoding.lean
import Mathlib
import Definitions.Def_Bridges_AlmostLosslessListDecoding
import Definitions.Def_Bridges_AlmostLosslessRandomCoding
/-
Copyright (c) 2025 Non-Archimedean Information Theory Project. All rights reserved.

# Almost-Lossless Compression VI: List Decoding and the Rate–List Trade-off

## Bridge: Markov's inequality (probability) ↔ pigeonhole counting (combinatorics)

A list decoder answers with a short set of candidates instead of a single
symbol.  This relaxes the pigeonhole bound a second time — now by the list size
`T` rather than by the failure probability — and it *simultaneously* improves
the achievable failure probability, because a codeword only has to be discarded
when more than `T` codebook entries collide.

Main results:

* `card_listSuccessSet_le` / `list_card_code_ge_of_success` — **converse**:
  a decoder emitting lists of length `≤ T` has `P(success) ≤ T·|Code|·p_max`,
  i.e. `log|Code| + log T ≥ H_∞ + log(1−ε)`.  At `T = 1` this is the ordinary
  relaxed pigeonhole bound.
* `card_badKeysT_mul_le` — **Markov step**: at most a `|S|/(T·M)` fraction of
  keys give `x` more than `T` collision partners.
* `exists_list_almost_lossless_scheme` — **achievability**: an explicit key with
  failure probability `≤ δ + |S|/(T·M)`, decoding cost still exactly `|S|`, and
  the guarantee that a non-empty answer *always contains the true symbol*.

So list size `T` buys a factor `T` in the failure probability and costs
`log T` bits in the converse: the two sides of the trade-off match.

## Impact: list_decoding_tradeoff, no_silent_corruption
-/


open Finset BigOperators NonArchInfoTheory

open AlmostLossless

/-! ## Section 1: List schemes and the rate–list converse -/


variable {α : Type*} [Fintype α] [DecidableEq α] {Code : Type*}

theorem AlmostLossless.card_listSuccessSet_le[Fintype Code] [DecidableEq Code]
    (s : ListScheme α Code) (T : ℕ) (hT : ∀ c, (s.dec c).length ≤ T) :
    (listSuccessSet s).card ≤ Fintype.card Code * T := by sorry
