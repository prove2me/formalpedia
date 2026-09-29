-- Prove2me | Definitions.Def_MachineLearning_TropicalAlgebra_SemiringRelativeReality
-- name    : MachineLearning_TropicalAlgebra_SemiringRelativeReality
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T19:17:04.424932+00:00
-- url     : https://prove2.me/theorems/b6db084d-c46b-4d8a-8742-1037ef7a29fb
-- title:
--   Aether Catalog definitions — MachineLearning_TropicalAlgebra_SemiringRelativeReality
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.TropicalAlgebra.SemiringRelativeReality`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/TropicalAlgebra/SemiringRelativeReality.lean by skeleton subtraction
import Mathlib

/-!
# Semiring-Relative Mathematical Reality

## Overview

This module formalizes the thesis that **different semirings support different mathematics**.
We prove that idempotent semirings collapse multiplicity information, so that polynomial
evaluation depends only on which monomials appear (the *support*), not on how many times
they appear. We then exhibit a concrete separating witness showing that this collapse
is genuinely non-trivial: the same expression evaluates differently over `ℕ`.

## Main Results

* `evalListIdem_dedup` — In any idempotent commutative semiring, list-based
  polynomial evaluation is invariant under deduplication. This is the **Alien Shadow
  Theorem**: multiplicity disappears for idempotent civilizations.

* `evalListIdem_perm_dedup` — Evaluation is invariant under any rewriting that
  preserves the underlying set of exponents (permutation of dedup).

* `separation_nat_vs_idempotent` — There exists a concrete list and evaluation point
  where `ℕ`-evaluation distinguishes the original list from its dedup.

* `tropical_not_nat_separator` — The canonical multiplicity-collapse separator:
  `max a a = a` holds universally over `ℝ` with `max`, but `n + n = n` fails in `ℕ`.

* `eval_support_invariance` — In a finset-based formulation, polynomial evaluation
  with arbitrary positive coefficients equals evaluation with unit coefficients.

* `counting_obstruction` — In `ℕ`, evaluation recovers list length (counting);
  in an idempotent semiring, this information is irreversibly destroyed.

## Interpretation

Classical civilizations (over `ℕ`, `ℤ`, `ℚ`, `ℝ`) perceive multiplicity-sensitive
identities. Tropical/idempotent civilizations perceive only support and extremal
structure. The overlap — the **combinatorial core** — is exactly the set of identities
that depend only on which monomials have nonzero coefficients.
-/

open Finset List

noncomputable section

/-! ## Part 1: List-based polynomial evaluation -/

/-- Evaluate a list of exponents as a polynomial expression `∑ xⁱ` ∈ a commutative semiring.
    Each entry `i` in the list contributes a term `x ^ i`. -/
def evalListSemiring {α : Type*} [CommSemiring α] (x : α) : List ℕ → α
  | [] => 0
  | i :: is => x ^ i + evalListSemiring x is

/-! ## Part 2: Idempotent addition collapses duplicates -/


/-
Prepending a duplicate exponent doesn't change evaluation in an
    idempotent commutative semiring.
-/


/-! ## Part 3: Separation — ℕ distinguishes what idempotent semirings cannot -/



/-! ## Part 4: Coefficient invariance -/




/-! ## Part 5: Permutation invariance -/




/-! ## Part 6: Concrete examples -/




/-! ## Part 7: Quantum obstruction — multiplicity destruction -/




end


