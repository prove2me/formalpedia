-- Prove2me | Definitions.Def_Cryptography_PosetTheory_BerggrenGreenIncomparability
-- name    : Cryptography_PosetTheory_BerggrenGreenIncomparability
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:20:02.363535+00:00
-- url     : https://prove2.me/theorems/b5e7b4da-cc5e-48c2-8e26-ff4f3475e82d
-- title:
--   Aether Catalog definitions — Cryptography_PosetTheory_BerggrenGreenIncomparability
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.PosetTheory.BerggrenGreenIncomparability`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/PosetTheory/BerggrenGreenIncomparability.lean by skeleton subtraction
import Mathlib

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

/-- The three Berggren generators. -/
inductive BergGen : Type
  | A | B | C
  deriving DecidableEq, Repr

instance : Fintype BergGen where
  elems := {.A, .B, .C}
  complete := by intro x; cases x <;> simp

/-- A Berggren word is a list of generators. -/
abbrev BergWord := List BergGen

/-! ## Pair-Based Evaluation (for proving injectivity) -/

/-- Action of a generator on a pair (m, n). -/
def actGen (g : BergGen) (p : ℤ × ℤ) : ℤ × ℤ :=
  match g with
  | .A => (2 * p.1 - p.2, p.1)
  | .B => (2 * p.1 + p.2, p.1)
  | .C => (p.1 + 2 * p.2, p.2)

/-- The root pair (2, 1). -/
def rootPair : ℤ × ℤ := (2, 1)

/-- Evaluate a word by acting on the root pair. -/
def evalPair : BergWord → ℤ × ℤ
  | [] => rootPair
  | g :: rest => actGen g (evalPair rest)

/-- A valid pair has 0 < n < m. -/
def ValidPair (p : ℤ × ℤ) : Prop := 0 < p.2 ∧ p.2 < p.1









/-! ## Matrix Formulation -/

/-- Matrix representation of each Berggren generator. -/
def bergMat : BergGen → Matrix (Fin 2) (Fin 2) ℤ
  | .A => !![2, -1; 1, 0]
  | .B => !![2, 1; 1, 0]
  | .C => !![1, 2; 0, 1]

/-- Evaluate a Berggren word as a matrix product. -/
def evalBergWord : BergWord → Matrix (Fin 2) (Fin 2) ℤ
  | [] => 1
  | g :: rest => bergMat g * evalBergWord rest



/-- Bridge between pair evaluation and matrix evaluation. -/
def pairOfMat (M : Matrix (Fin 2) (Fin 2) ℤ) : ℤ × ℤ :=
  (2 * M 0 0 + M 0 1, 2 * M 1 0 + M 1 1)




/-! ## Basic Properties -/


/-! ## Cancellation -/



/-! ## List Overlap Lemma (Pure Combinatorics) -/


/-! ## Left Overlap Rigidity -/


/-! ## Right Overlap Rigidity -/


/-! ## Matrix-Level Overlap Rigidity -/



/-! ## Green-Order Incomparability: No Common Left/Right Multiples -/



/-! ## Finite-Ball Green-Order Incomparability -/


/-! ## Supporting Lemmas for Singleton Words -/



/-! ## LCM-Free Pair Extraction -/


