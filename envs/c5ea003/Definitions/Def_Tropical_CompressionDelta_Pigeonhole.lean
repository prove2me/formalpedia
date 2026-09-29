-- Prove2me | Definitions.Def_Tropical_CompressionDelta_Pigeonhole
-- name    : Tropical_CompressionDelta_Pigeonhole
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T08:29:47.286448+00:00
-- url     : https://prove2.me/theorems/a084bc3e-62bb-43c3-ad6b-343eb520c656
-- title:
--   Aether Catalog definitions — Tropical_CompressionDelta_Pigeonhole
-- statement:
--   Definition bundle for the Aether Catalog module `Tropical.CompressionDelta.Pigeonhole`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Tropical/CompressionDelta/Pigeonhole.lean by skeleton subtraction
import Mathlib

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

namespace CompressionDelta

open Finset

/-! ## Counting bitstrings of bounded length -/

/-- `shortStrings t` is the finite set of all bitstrings of length at most `t`. -/
def shortStrings : ℕ → Finset (List Bool)
  | 0 => {[]}
  | t + 1 =>
      insert [] (((shortStrings t).image (fun l => true :: l)) ∪
        ((shortStrings t).image (fun l => false :: l)))



/-! ## The counting floor for lossless codes -/




end CompressionDelta


