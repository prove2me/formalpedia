-- Prove2me | Theorems.Thm_evalBergWord_injective
-- name    : evalBergWord_injective
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T03:09:34.960049+00:00
-- url     : https://prove2.me/theorems/6e4cc09f-7531-461d-a3a1-830c42b49724
-- title:
--   Injectivity of the matrix evaluation: the free semigroup theorem.
-- statement:
--   **Injectivity of the matrix evaluation**: the free semigroup theorem.
--
--   ```lean
--   theorem evalBergWord_injective: Function.Injective evalBergWord := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/BerggrenTrees/BerggrenFreeMonoid.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/BerggrenTrees/BerggrenFreeMonoid.lean#L141

-- Thm stub generated from Cryptography/PosetTheory/BerggrenGreenIncomparability.lean
import Mathlib
import Definitions.Def_Cryptography_PosetTheory_BerggrenGreenIncomparability

/-!
# Berggren Semigroup: Green-Order Incomparability and LCM-Free Pair Extraction

We prove that the three Berggren generators, realized as 2×2 integer matrices,
generate a **free semigroup** of rank 3 inside `GL₂(ℤ)`, and use this to
establish two-sided divisibility geometry theorems: the Green-order incomparability
of non-overlapping words in finite balls, and the extraction of lcm-free pairs.

## Overview

The Berggren tree generators A, B, C act on pairs (m,n) with m > n > 0 and
produce a free semigroup. The matrix evaluation map `evalBergWord` is injective,
which means divisibility in the semigroup corresponds exactly to prefix/suffix
relationships at the word level. From this we derive:

1. **Left/Right overlap rigidity**: Equal products force one factor to extend another.
2. **Green-order incomparability**: Non-overlapping words have no common left or right
   multiples, ruling out "merge attacks" in cryptographic applications.
3. **LCM-free pair extraction**: Every ball of radius ≥ 1 contains an explicit pair
   with neither a common left nor right multiple.

## Main Results

* `list_eq_append_overlap` — pure list overlap decomposition lemma
* `berggren_word_left_overlap` — left overlap rigidity for Berggren words
* `berggren_word_right_overlap` — right overlap rigidity for Berggren words
* `no_common_left_multiple_of_no_suffix_overlap` — Green L-incomparability
* `no_common_right_multiple_of_no_prefix_overlap` — Green R-incomparability
* `berggren_green_incomparable_of_no_overlap` — full two-sided incomparability
* `exists_lcm_free_pair_in_ball` — explicit lcm-free pair extraction

## References

* Berggren, B. (1934). Pytagoreiska trianglar.
* Hall, A. (1970). Genealogy of Pythagorean triads.
-/

set_option linter.unusedVariables false

/-! ## Generator Type -/




/-! ## Pair-Based Evaluation (for proving injectivity) -/













/-! ## Matrix Formulation -/

theorem evalBergWord_injective: Function.Injective evalBergWord := by sorry
