-- Prove2me | Theorems.Thm_PRNGCompression_compressible_fraction_le
-- name    : PRNGCompression.compressible_fraction_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:45:32.39092+00:00
-- url     : https://prove2.me/theorems/cafb68cb-524a-4731-ba8f-eec675fa08c0
-- title:
--   Fraction of compressible files.
-- statement:
--   **Fraction of compressible files.**  At most a `2 ^ (1-d)` fraction of the
--   `2 ^ n` strings can be described in `n - d` bits by a given decompressor.
--
--   ```lean
--   theorem PRNGCompression.compressible_fraction_le{n : ℕ} (d : ℕ) (D : List Bool → Bits n)
--       (hD : Function.Surjective D) :
--       (((univ.filter (fun x : Bits n => KC D x + d ≤ n)).card : ℝ)) / 2 ^ n ≤ 2 / 2 ^ d := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/PRNGCompressionRates.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/PRNGCompressionRates.lean#L35

-- Thm stub generated from MachineLearning/PRNGCompressionRates.lean
import Mathlib
import Definitions.Def_MachineLearning_PRNGCompressionBound
import Definitions.Def_MachineLearning_PRNGCompressionCore
import Definitions.Def_MachineLearning_PRNGCompressionDepth
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Compression Rates over the Reals

The counting theorems of `MachineLearning.PRNGCompressionCore`,
`…PRNGCompressionBound` and `…PRNGCompressionDepth` are stated in `ℕ` (exact
cardinalities).  This file transports them to `ℝ`, where they read as the
statements a practitioner cares about: *fractions of files* and *average bits
per file*.

## Main Results

* `compressible_fraction_le` — for any decompressor (PRNG-driven or not), the
  fraction of `n`-bit strings whose description shrinks by `d` bits is at most
  `2 ^ (1 - d)`.  Saving one byte works for at most one file in `128`.
* `average_length_lower_real` — the average codeword length of any injective
  code over all `2 ^ n` strings is at least `(n - k)(1 - 2 ^ (-k))` for every
  `k < n`; the average rate is `n - O(log n)` bits per file.
* `average_KC_lower_real` — the same for description complexity relative to an
  arbitrary decompressor.

## Application Keywords

compression rate, average code length, incompressibility fraction, PRNG,
information theory
-/


open Finset

open PRNGCompression

theorem PRNGCompression.compressible_fraction_le{n : ℕ} (d : ℕ) (D : List Bool → Bits n)
    (hD : Function.Surjective D) :
    (((univ.filter (fun x : Bits n => KC D x + d ≤ n)).card : ℝ)) / 2 ^ n ≤ 2 / 2 ^ d := by sorry
