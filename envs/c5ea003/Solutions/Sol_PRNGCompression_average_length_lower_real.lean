-- Prove2me | solution 1 for PRNGCompression.average_length_lower_real
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T22:36:59.782167+00:00
-- url     : https://prove2.me/submissions/9257340c-111d-4c5f-88ca-b50541fc4ff8

-- Sol generated from MachineLearning/PRNGCompressionRates.lean
import Mathlib
import Definitions.Def_MachineLearning_PRNGCompressionCore
import Definitions.Def_MachineLearning_PRNGCompressionDepth
import Theorems.Thm_PRNGCompression_sum_length_lower
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
theorem solution(n k : ℕ) (hk : k + 1 ≤ n) (c : Bits n → List Bool)
    (hc : Function.Injective c) :
    ((n : ℝ) - k) * (1 - (2 : ℝ)⁻¹ ^ k) ≤ (∑ x, ((c x).length : ℝ)) / 2 ^ n := by
  have hnat := sum_length_lower n k hk c hc
  have hle : (2:ℕ) ^ (n - k) ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hcast : ((n : ℝ) - k) * ((2:ℝ) ^ n - 2 ^ (n - k)) ≤ ∑ x, ((c x).length : ℝ) := by
    have hc' := (Nat.cast_le (α := ℝ)).mpr hnat
    push_cast [Nat.cast_sub hle, Nat.cast_sub (by omega : k ≤ n)] at hc'
    convert hc' using 2
  have hpow : (2:ℝ) ^ (n - k) * 2 ^ k = 2 ^ n := by
    rw [← pow_add]; congr 1; omega
  have h2n : (0:ℝ) < 2 ^ n := by positivity
  have h2k : (0:ℝ) < 2 ^ k := by positivity
  have hsub : (2:ℝ) ^ (n - k) = 2 ^ n / 2 ^ k := by
    field_simp
    linarith [hpow]
  rw [le_div_iff₀ h2n]
  have hkey : ((n : ℝ) - k) * (1 - (2 : ℝ)⁻¹ ^ k) * 2 ^ n
      = ((n : ℝ) - k) * ((2:ℝ) ^ n - 2 ^ (n - k)) := by
    rw [hsub, inv_pow]
    field_simp
  rw [hkey]
  exact hcast
