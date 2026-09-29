-- Prove2me | Definitions.Def_Bridges_SublevelZeroEqDivisors_Sublevel_zero_eq_divisors
-- name    : Bridges_SublevelZeroEqDivisors_Sublevel_zero_eq_divisors
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:40:13.149526+00:00
-- url     : https://prove2.me/theorems/0472a103-1c3b-4bcd-91cd-1e04e1a5d901
-- title:
--   Aether Catalog definitions — Bridges_SublevelZeroEqDivisors_Sublevel_zero_eq_divisors
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.SublevelZeroEqDivisors.Sublevel.zero.eq.divisors`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/SublevelZeroEqDivisors/Sublevel_zero_eq_divisors.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Shared.Sublevel_zero_eq_divisors

Auto-generated from theorem catalog database.
Domain: Shared
Declarations: 3

As delivered, this file used two names that were never defined — the error function `E`
and `sublevel_set`, the latter also being used before its definition — so it did not
elaborate.  Both are supplied below, in the only reading consistent with the statements
that use them: `E N x` is the remainder of `N` on division by `x`, so that the sublevel
set at level `0` is exactly the set of divisors of `N`.  The declarations are also put in
dependency order.
-/

/-- The division error of `x` against `N`: the remainder `N % x`.  It vanishes exactly
when `x` divides `N`. -/
def E (N x : ℕ) : ℕ := N % x

/-- Sublevel set: the set of `x ∈ [1,N]` with `E N x ≤ t`. -/
def sublevel_set (N t : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun x => E N x ≤ t)


