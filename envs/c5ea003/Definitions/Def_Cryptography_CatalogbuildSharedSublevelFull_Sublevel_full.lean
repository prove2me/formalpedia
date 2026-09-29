-- Prove2me | Definitions.Def_Cryptography_CatalogbuildSharedSublevelFull_Sublevel_full
-- name    : Cryptography_CatalogbuildSharedSublevelFull_Sublevel_full
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:12:08.69581+00:00
-- url     : https://prove2.me/theorems/fe4b60ef-af94-493b-be6f-b7fd2211db39
-- title:
--   Aether Catalog definitions — Cryptography_CatalogbuildSharedSublevelFull_Sublevel_full
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.CatalogbuildSharedSublevelFull.Sublevel.full`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/CatalogbuildSharedSublevelFull/Sublevel_full.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Shared.Sublevel_full

Auto-generated from theorem catalog database.
Domain: Speculative
Declarations: 5
-/


/-- `E N x` is the remainder of `N` on division by `x`; the sublevel filtration
below is by the size of this remainder, and `E N x = 0` says exactly `x ∣ N`. -/
def E (N x : ℕ) : ℕ := N % x

def sublevel (N t : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun x => E N x ≤ t)


