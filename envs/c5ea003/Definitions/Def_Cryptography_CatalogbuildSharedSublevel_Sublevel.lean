-- Prove2me | Definitions.Def_Cryptography_CatalogbuildSharedSublevel_Sublevel
-- name    : Cryptography_CatalogbuildSharedSublevel_Sublevel
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:12:14.816485+00:00
-- url     : https://prove2.me/theorems/5839e9e7-e3f5-4aca-a356-0213ed41f9db
-- title:
--   Aether Catalog definitions — Cryptography_CatalogbuildSharedSublevel_Sublevel
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.CatalogbuildSharedSublevel.Sublevel`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/CatalogbuildSharedSublevel/Sublevel.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Shared.Sublevel

Auto-generated from theorem catalog database.
Domain: Shared
Declarations: 5
-/


/-- `E N x` is the remainder of `N` on division by `x`; the sublevel filtration
below is by the size of this remainder, and `E N x = 0` says exactly `x ∣ N`. -/
def E (N x : ℕ) : ℕ := N % x

/-- [Section: # CatalogBuild.Shared.Sublevel
Auto-generated from theorem catalog database.
Domain: Speculative
Declarations: 5] -/
def sublevel (N t : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun x => E N x ≤ t)


