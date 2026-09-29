-- Prove2me | Definitions.Def_Shared_SublevelZeroEqDivisors_Sublevel_zero_eq_divisors
-- name    : Shared_SublevelZeroEqDivisors_Sublevel_zero_eq_divisors
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T15:15:40.120817+00:00
-- url     : https://prove2.me/theorems/23db139e-4494-4d6f-8e6d-1d83f0c220ee
-- title:
--   Aether Catalog definitions — Shared_SublevelZeroEqDivisors_Sublevel_zero_eq_divisors
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.SublevelZeroEqDivisors.Sublevel.zero.eq.divisors`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/SublevelZeroEqDivisors/Sublevel_zero_eq_divisors.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Shared_CatalogbuildSharedE_E

/-! # CatalogBuild.Shared.Sublevel_zero_eq_divisors

Auto-generated from theorem catalog database.
Domain: Shared
Declarations: 3
-/

/-- Sublevel set: the set of x ∈ [1,N] with E(x) ≤ t. -/
def sublevel_set (N t : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun x => E N x ≤ t)


