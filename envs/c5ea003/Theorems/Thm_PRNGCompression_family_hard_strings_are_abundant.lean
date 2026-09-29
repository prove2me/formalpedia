-- Prove2me | Theorems.Thm_PRNGCompression_family_hard_strings_are_abundant
-- name    : PRNGCompression.family_hard_strings_are_abundant
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:46:20.941521+00:00
-- url     : https://prove2.me/theorems/f0dfd985-167b-4b21-8c74-df90c4ba8094
-- title:
--   Hard strings are the rule, not the exception.
-- statement:
--   **Hard strings are the rule, not the exception.**  The strings that *some*
--   member of the library compresses to `s` bits or fewer number at most
--   `2 ^ (m + s + 1)`, a `2 ^ (m + s + 1 - n)` fraction of all `n`-bit strings.
--
--   ```lean
--   theorem PRNGCompression.family_hard_strings_are_abundant{n m s : ℕ} (F : Bits m → List Bool → Bits n)
--       (hF : ∀ i, Function.Surjective (F i)) (hms : m + s + 1 ≤ n) :
--       2 ^ (n - (m + s)) *
--           (univ.filter (fun x : Bits n => ∃ i, KC (F i) x ≤ s)).card ≤ 2 ^ (n + 1) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/PRNGCompressionUniversal.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/PRNGCompressionUniversal.lean#L109

-- Thm stub generated from MachineLearning/PRNGCompressionUniversal.lean
import Mathlib
import Definitions.Def_MachineLearning_PRNGCompressionBound
import Definitions.Def_MachineLearning_PRNGCompressionCore
import Definitions.Def_MachineLearning_PRNGCompressionDepth
import Definitions.Def_MachineLearning_PRNGCompressionUniversal
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Invariance and Uniform Hardness against a Whole Family of Generators

Third research cycle on top of `MachineLearning.PRNGCompressionBound` and
`MachineLearning.PRNGCompressionDepth`.

The previous cycles show that a *fixed* PRNG cannot help.  A natural retreat is:
*"then let me keep a library of `2 ^ m` generators and, for each file, use the
one that happens to fit"*.  This file closes that retreat in the strongest form:
there is a **single** string that is simultaneously hard for **every** member of
the library.

## Central Idea

Two standard ingredients, formalized from scratch:

* **Invariance.**  If a decompressor `D` can simulate `D'` after reading a fixed
  `q`-bit prefix, then `KC D x ≤ |q| + KC D' x` (`KC_le_of_simulates`).
* **A universal machine for a finite family.**  `familyDecoder F` reads `m` index
  bits and then runs `F i` on the rest; it satisfies
  `KC (familyDecoder F) x ≤ m + KC (F i) x` for every member `i`.

Applying the incompressibility theorem to `familyDecoder F` and pushing the
bound back through the members yields uniform hardness.

## Main Results

* `KC_le_of_simulates` — invariance theorem for description complexity
* `familyDecoder_surjective`, `KC_familyDecoder_le` — the universal machine
* `exists_hard_for_whole_family` — one string `x` with `n ≤ m + KC (F i) x`
  for *every* generator `i` in a library of `2 ^ m` generators
* `family_hard_strings_are_abundant` — such hard strings are not exceptional:
  strings that are easy for *some* member of the library number at most
  `2 ^ (m + s + 1)` when each member compresses to `s` bits

## Application Keywords

invariance theorem, universal decompressor, Kolmogorov complexity, generator
library, uniform incompressibility, compression lower bounds
-/


open Finset

open PRNGCompression

/-! ## Invariance -/


/-! ## A universal machine for a library of `2 ^ m` decompressors -/

theorem PRNGCompression.family_hard_strings_are_abundant{n m s : ℕ} (F : Bits m → List Bool → Bits n)
    (hF : ∀ i, Function.Surjective (F i)) (hms : m + s + 1 ≤ n) :
    2 ^ (n - (m + s)) *
        (univ.filter (fun x : Bits n => ∃ i, KC (F i) x ≤ s)).card ≤ 2 ^ (n + 1) := by sorry
