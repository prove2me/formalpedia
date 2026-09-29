-- Prove2me | Definitions.Def_MachineLearning_NumberTheory_SemiprimeScaffolding
-- name    : MachineLearning_NumberTheory_SemiprimeScaffolding
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:49:23.984987+00:00
-- url     : https://prove2.me/theorems/000483c2-038f-481c-9513-56cc1a71daec
-- title:
--   Aether Catalog definitions — MachineLearning_NumberTheory_SemiprimeScaffolding
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.NumberTheory.SemiprimeScaffolding`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/NumberTheory/SemiprimeScaffolding.lean by skeleton subtraction
import Mathlib
/-
  # Semiprime Scaffolding for n² + 1

  This file defines the semiprime predicate and proves basic properties,
  creating the vocabulary needed for future formalization of Iwaniec's theorem
  that infinitely many values n² + 1 have at most 2 prime factors.

  ## Definitions

  - `IsSemiprime`: A number that is a product of exactly two primes.

  ## Key results

  - `IsSemiprime.two_le`: Every semiprime is at least 2.
  - `Nat.Prime.not_isSemiprime`: A prime is never semiprime.
  - `isSemiprime_four`, `isSemiprime_six`: Concrete examples.
-/

/-- A natural number is semiprime if it is a product of exactly two primes
(not necessarily distinct). -/
def IsSemiprime (n : ℕ) : Prop :=
  ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p * q = n

/-
Every semiprime is at least 2.
-/

/-
A prime number is not semiprime: one cannot write a prime as a product
of two primes.
-/


