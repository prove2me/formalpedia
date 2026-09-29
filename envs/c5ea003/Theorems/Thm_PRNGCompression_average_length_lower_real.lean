-- Prove2me | Theorems.Thm_PRNGCompression_average_length_lower_real
-- name    : PRNGCompression.average_length_lower_real
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:45:20.617902+00:00
-- url     : https://prove2.me/theorems/536dfa74-7026-4c91-ae06-beecf8dfe37f
-- title:
--   Average bits per file.
-- statement:
--   **Average bits per file.**  For every injective code and every `k < n`, the
--   mean codeword length over all `2 ^ n` strings is at least `(n - k)(1 - 2 ^ (-k))`.
--   Choosing `k ≈ log₂ n` gives a mean of `n - O(log n)` bits: no code beats the
--   pigeonhole bound even on average.
--
--   ```lean
--   theorem PRNGCompression.average_length_lower_real(n k : ℕ) (hk : k + 1 ≤ n) (c : Bits n → List Bool)
--       (hc : Function.Injective c) :
--       ((n : ℝ) - k) * (1 - (2 : ℝ)⁻¹ ^ k) ≤ (∑ x, ((c x).length : ℝ)) / 2 ^ n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/PRNGCompressionRates.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/PRNGCompressionRates.lean#L54

-- Thm stub generated from MachineLearning/PRNGCompressionRates.lean
import Mathlib
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

theorem PRNGCompression.average_length_lower_real(n k : ℕ) (hk : k + 1 ≤ n) (c : Bits n → List Bool)
    (hc : Function.Injective c) :
    ((n : ℝ) - k) * (1 - (2 : ℝ)⁻¹ ^ k) ≤ (∑ x, ((c x).length : ℝ)) / 2 ^ n := by sorry
