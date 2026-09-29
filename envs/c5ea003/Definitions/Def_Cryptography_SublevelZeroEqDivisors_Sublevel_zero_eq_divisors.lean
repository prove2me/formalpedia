-- Prove2me | Definitions.Def_Cryptography_SublevelZeroEqDivisors_Sublevel_zero_eq_divisors
-- name    : Cryptography_SublevelZeroEqDivisors_Sublevel_zero_eq_divisors
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:23:20.298054+00:00
-- url     : https://prove2.me/theorems/ef203c77-a145-4db6-99fd-03f08babefe7
-- title:
--   Aether Catalog definitions — Cryptography_SublevelZeroEqDivisors_Sublevel_zero_eq_divisors
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.SublevelZeroEqDivisors.Sublevel.zero.eq.divisors`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/SublevelZeroEqDivisors/Sublevel_zero_eq_divisors.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Shared.Sublevel_zero_eq_divisors

Auto-generated from theorem catalog database.
Domain: Shared
Declarations: 3
-/


/-- `E N x` is the remainder of `N` on division by `x`; the sublevel filtration
below is by the size of this remainder, and `E N x = 0` says exactly `x ∣ N`. -/
def E (N x : ℕ) : ℕ := N % x

/-- Sublevel set: the set of x ∈ [1,N] with E(x) ≤ t. -/
def sublevel_set (N t : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun x => E N x ≤ t)


