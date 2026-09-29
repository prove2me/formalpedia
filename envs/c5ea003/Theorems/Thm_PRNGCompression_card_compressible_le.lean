-- Prove2me | Theorems.Thm_PRNGCompression_card_compressible_le
-- name    : PRNGCompression.card_compressible_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:44:50.731225+00:00
-- url     : https://prove2.me/theorems/1ce2dd9e-9bda-426a-acb2-d8e0e85a803b
-- title:
--   Quantitative pigeonhole.
-- statement:
--   **Quantitative pigeonhole.**  Saving `d` bits costs a factor `2 ^ d` in
--   coverage: at most a `2 ^ (1 - d)` fraction of all `2 ^ n` strings can be coded
--   in `n - d` bits.  (Stated multiplicatively to avoid truncated subtraction.)
--
--   ```lean
--   theorem PRNGCompression.card_compressible_le(n d : ℕ) (c : Bits n → List Bool)
--       (hc : Function.Injective c) :
--       2 ^ d * (univ.filter (fun x : Bits n => (c x).length + d ≤ n)).card ≤ 2 ^ (n + 1) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/PRNGCompressionCore.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/PRNGCompressionCore.lean#L148

-- Thm stub generated from MachineLearning/PRNGCompressionCore.lean
import Mathlib
import Definitions.Def_MachineLearning_PRNGCompressionCore
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Counting Core for Lossless Compression: the Pigeonhole Bound

This module develops, from first principles, the counting machinery behind the
classical statement that *no lossless code can shorten all inputs*.  It is the
foundation for the negative result about pseudo-random number generators
(`MachineLearning.PRNGCompressionBound`): a PRNG is just another decompressor,
and every decompressor obeys the bounds proved here.

## Central Idea

A codeword is a finite bit string `List Bool`.  Reading a codeword as a binary
numeral *with a leading `1` prepended* gives an injection
`codeNat : List Bool → ℕ` with `2 ^ len ≤ codeNat l < 2 ^ (len + 1)`.
Hence there are fewer than `2 ^ (k+1)` codewords of length `≤ k`, and any
injective encoding of a set of size `2 ^ n` must use a codeword of length `≥ n`.

## Main Definitions

* `codeNat` — self-delimiting numeric index of a bit string
* `Bits n` — the type of `n`-bit strings, `Fin n → Bool`

## Main Results

* `codeNat_injective` — the numeric index of a bit string determines the string
* `card_short_le` — at most `2 ^ (k+1) - 1` inputs receive a codeword of length `≤ k`
* `exists_long_codeword` — pigeonhole: some `n`-bit string needs `≥ n` code bits
* `card_compressible_le` — at most a `2 ^ (1-d)` fraction of inputs can be
  compressed by `d` bits ("`d` bits of gain costs a factor `2 ^ d` of coverage")
* `card_bits` — `#(Bits n) = 2 ^ n`

## Application Keywords

lossless compression, pigeonhole bound, Kraft inequality, counting argument,
incompressibility, data compression limits
-/


open Finset

open PRNGCompression

theorem PRNGCompression.card_compressible_le(n d : ℕ) (c : Bits n → List Bool)
    (hc : Function.Injective c) :
    2 ^ d * (univ.filter (fun x : Bits n => (c x).length + d ≤ n)).card ≤ 2 ^ (n + 1) := by sorry
