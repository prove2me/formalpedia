-- Prove2me | Theorems.Thm_idem_eval_loses_length
-- name    : idem_eval_loses_length
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T20:01:55.800764+00:00
-- url     : https://prove2.me/theorems/3bdc076f-b29d-41be-892a-212a27502fd2
-- title:
--   In an idempotent commutative semiring, any nonempty all-zero-exponent list
-- statement:
--   In an idempotent commutative semiring, any nonempty all-zero-exponent list
--       evaluates to 1 at x=1. Length information is destroyed.
--
--   ```lean
--   theorem idem_eval_loses_length    {α : Type*} [IdemCommSemiring α]
--       (L : List ℕ) (hL : ∀ i ∈ L, i = 0) (hne : L ≠ []) :
--       evalListSemiring (1 : α) L = 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/TropicalAlgebra/SemiringRelativeReality.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/TropicalAlgebra/SemiringRelativeReality.lean#L202

-- Thm stub generated from MachineLearning/TropicalAlgebra/SemiringRelativeReality.lean
import Mathlib
import Definitions.Def_MachineLearning_TropicalAlgebra_SemiringRelativeReality

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

theorem idem_eval_loses_length    {α : Type*} [IdemCommSemiring α]
    (L : List ℕ) (hL : ∀ i ∈ L, i = 0) (hne : L ≠ []) :
    evalListSemiring (1 : α) L = 1 := by sorry
