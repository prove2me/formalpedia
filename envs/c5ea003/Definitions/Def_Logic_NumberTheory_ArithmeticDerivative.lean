-- Prove2me | Definitions.Def_Logic_NumberTheory_ArithmeticDerivative
-- name    : Logic_NumberTheory_ArithmeticDerivative
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T13:59:46.434643+00:00
-- url     : https://prove2.me/theorems/49b0ccc5-e87f-4cb2-b53f-17634d0bae75
-- title:
--   Aether Catalog definitions — Logic_NumberTheory_ArithmeticDerivative
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.NumberTheory.ArithmeticDerivative`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/NumberTheory/ArithmeticDerivative.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Algebra.Core.ArithmeticDerivative

Auto-generated from theorem catalog database.
Domain: Algebra/Core
Declarations: 5
-/


noncomputable section

/-- The arithmetic derivative of a positive natural number, defined via
the formula n' = n · ∑(eᵢ/pᵢ) where n = ∏ pᵢ^eᵢ.
For the purpose of this formalization, we define it as the sum
n' = ∑ (n / p) * e over the prime factorization. -/
def arithmeticDerivative (n : ℕ) : ℕ :=
  if n ≤ 1 then 0
  else (n.primeFactors).sum fun p => (n / p) * (n.factorization p)




















end


