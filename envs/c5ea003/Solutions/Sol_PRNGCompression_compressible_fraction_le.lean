-- Prove2me | solution 1 for PRNGCompression.compressible_fraction_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T22:37:02.054667+00:00
-- url     : https://prove2.me/submissions/82a8ef18-7a71-4313-86df-2369b840b162

-- Sol generated from MachineLearning/PRNGCompressionRates.lean
import Mathlib
import Definitions.Def_MachineLearning_PRNGCompressionBound
import Definitions.Def_MachineLearning_PRNGCompressionCore
import Definitions.Def_MachineLearning_PRNGCompressionDepth
import Theorems.Thm_PRNGCompression_KC_compressible_count
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





open PRNGCompression in
theorem solution{n : ℕ} (d : ℕ) (D : List Bool → Bits n)
    (hD : Function.Surjective D) :
    (((univ.filter (fun x : Bits n => KC D x + d ≤ n)).card : ℝ)) / 2 ^ n ≤ 2 / 2 ^ d := by
  classical
  have hnat := KC_compressible_count d D hD
  have hcast : (2:ℝ) ^ d * ((univ.filter (fun x : Bits n => KC D x + d ≤ n)).card : ℝ)
      ≤ 2 ^ (n + 1) := by
    have := (Nat.cast_le (α := ℝ)).mpr hnat
    push_cast at this
    exact this
  have h2n : (0:ℝ) < 2 ^ n := by positivity
  have h2d : (0:ℝ) < 2 ^ d := by positivity
  rw [div_le_div_iff₀ h2n h2d]
  have hexp : (2:ℝ) ^ (n + 1) = 2 * 2 ^ n := by ring
  rw [hexp] at hcast
  nlinarith [hcast]
