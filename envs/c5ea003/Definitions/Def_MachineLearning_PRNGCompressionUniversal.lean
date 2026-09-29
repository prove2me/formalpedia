-- Prove2me | Definitions.Def_MachineLearning_PRNGCompressionUniversal
-- name    : MachineLearning_PRNGCompressionUniversal
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:53:11.324393+00:00
-- url     : https://prove2.me/theorems/ce05f598-a99f-4911-a758-4b2b6e72d346
-- title:
--   Aether Catalog definitions — MachineLearning_PRNGCompressionUniversal
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.PRNGCompressionUniversal`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/PRNGCompressionUniversal.lean by skeleton subtraction
import Mathlib
import Definitions.Def_MachineLearning_PRNGCompressionBound
import Definitions.Def_MachineLearning_PRNGCompressionCore
import Definitions.Def_MachineLearning_PRNGCompressionDepth
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

namespace PRNGCompression

/-! ## Invariance -/


/-! ## A universal machine for a library of `2 ^ m` decompressors -/

/-- The universal decompressor for the family `F`: read `m` index bits, then run
the selected member on the remaining program. -/
def familyDecoder {n m : ℕ} (F : Bits m → List Bool → Bits n) (p : List Bool) : Bits n :=
  F (bitsOfList m (p.take m)) (p.drop m)






end PRNGCompression


