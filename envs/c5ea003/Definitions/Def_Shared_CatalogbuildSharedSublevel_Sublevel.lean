-- Prove2me | Definitions.Def_Shared_CatalogbuildSharedSublevel_Sublevel
-- name    : Shared_CatalogbuildSharedSublevel_Sublevel
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T14:48:48.589486+00:00
-- url     : https://prove2.me/theorems/81e9d2d2-6f11-4a19-9694-c81c06e384c4
-- title:
--   Aether Catalog definitions — Shared_CatalogbuildSharedSublevel_Sublevel
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.CatalogbuildSharedSublevel.Sublevel`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/CatalogbuildSharedSublevel/Sublevel.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Shared_CatalogbuildSharedE_E

/-! # CatalogBuild.Shared.Sublevel

Auto-generated from theorem catalog database.
Domain: Shared
Declarations: 5
-/

/-- [Section: # CatalogBuild.Shared.Sublevel
Auto-generated from theorem catalog database.
Domain: Speculative
Declarations: 5] -/
def sublevel (N t : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun x => E N x ≤ t)


