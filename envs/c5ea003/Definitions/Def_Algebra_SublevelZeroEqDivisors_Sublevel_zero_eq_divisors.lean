-- Prove2me | Definitions.Def_Algebra_SublevelZeroEqDivisors_Sublevel_zero_eq_divisors
-- name    : Algebra_SublevelZeroEqDivisors_Sublevel_zero_eq_divisors
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T10:13:46.404254+00:00
-- url     : https://prove2.me/theorems/1908faba-4f5f-4aec-91c9-a965d281462d
-- title:
--   Aether Catalog definitions — Algebra_SublevelZeroEqDivisors_Sublevel_zero_eq_divisors
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.SublevelZeroEqDivisors.Sublevel.zero.eq.divisors`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/SublevelZeroEqDivisors/Sublevel_zero_eq_divisors.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Shared.Sublevel_zero_eq_divisors

Auto-generated from theorem catalog database.
Domain: Shared
Declarations: 3

Repaired: the statistic `E` is defined here and `sublevel_set` placed before its
uses.
-/

/-- The remainder statistic `E N x = N % x` on which the sublevel sets are
based (it was used but never declared in the generated file). -/
def E (N x : ℕ) : ℕ := N % x

/-- Sublevel set: the set of x ∈ [1,N] with E(x) ≤ t. -/
def sublevel_set (N t : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun x => E N x ≤ t)


