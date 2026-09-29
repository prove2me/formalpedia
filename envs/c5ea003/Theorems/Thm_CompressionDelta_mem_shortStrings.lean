-- Prove2me | Theorems.Thm_CompressionDelta_mem_shortStrings
-- name    : CompressionDelta.mem_shortStrings
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T08:34:24.950892+00:00
-- url     : https://prove2.me/theorems/e807d90d-2020-48a7-ac28-86b08fc605e3
-- title:
--   Mem shortStrings
-- statement:
--   Formal statement of `CompressionDelta.mem_shortStrings` from the Aether Catalog (Tropical). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem CompressionDelta.mem_shortStrings: ∀ (t : ℕ) (l : List Bool),
--       l ∈ shortStrings t ↔ l.length ≤ t := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Tropical/CompressionDelta/Pigeonhole.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Tropical/CompressionDelta/Pigeonhole.lean#L38

-- Thm stub generated from Tropical/CompressionDelta/Pigeonhole.lean
import Mathlib
import Definitions.Def_Tropical_CompressionDelta_Pigeonhole

/-!
# Amortized model-delta compression, III: the counting (pigeonhole) floor

The falsifiability gate of this research thread demands *lossless* compression with the
delta counted as part of the transmitted message.  This file supplies the hard information
theoretic floor that no such scheme can cross, in a form that is agnostic about *what* the
decompressor is: the decoder may be a gzip table, a context mixer or a 16 GB pretrained
language model — only injectivity of the encoder is used.

## Main results

* `CompressionDelta.card_shortStrings` — there are exactly `2 ^ (t + 1) - 1` bitstrings of
  length at most `t` (stated without truncated subtraction).
* `CompressionDelta.card_compressible_le` — for an injective encoder, the number of
  sources whose *entire* transmission (model delta included) is at most `t` bits is at
  most `2 ^ (t + 1) - 1`; so compressible objects are exponentially rare.
* `CompressionDelta.exists_long_codeword` — the pigeonhole bound: some source must be
  transmitted in more than `t` bits as soon as there are `2 ^ (t + 1)` sources.
* `CompressionDelta.stream_counting_bound` — the streaming form: a stream of `n` messages
  from a `2 ^ s`-symbol source needs `n * s` bits for some stream, however clever the
  shared decompressor and its transmitted delta are.
-/

open CompressionDelta

open Finset

/-! ## Counting bitstrings of bounded length -/


@[simp]

theorem CompressionDelta.mem_shortStrings: ∀ (t : ℕ) (l : List Bool),
    l ∈ shortStrings t ↔ l.length ≤ t := by sorry
