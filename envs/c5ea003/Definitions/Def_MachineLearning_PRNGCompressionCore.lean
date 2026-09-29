-- Prove2me | Definitions.Def_MachineLearning_PRNGCompressionCore
-- name    : MachineLearning_PRNGCompressionCore
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:49:54.128366+00:00
-- url     : https://prove2.me/theorems/599417dd-a8d6-45cb-aef3-ace9ea6252c6
-- title:
--   Aether Catalog definitions — MachineLearning_PRNGCompressionCore
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.PRNGCompressionCore`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/PRNGCompressionCore.lean by skeleton subtraction
import Mathlib
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

namespace PRNGCompression

/-- The type of `n`-bit strings. -/
abbrev Bits (n : ℕ) : Type := Fin n → Bool


/-- Numeric index of a bit string: read it as a binary numeral with an extra
leading `1`, so that the length is recoverable and the map is injective. -/
def codeNat : List Bool → ℕ
  | [] => 1
  | b :: l => 2 * codeNat l + (if b then 1 else 0)







end PRNGCompression


