-- Prove2me | Definitions.Def_Bridges_CatalogbuildSharedSublevel_Sublevel
-- name    : Bridges_CatalogbuildSharedSublevel_Sublevel
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:16:54.509974+00:00
-- url     : https://prove2.me/theorems/c847be05-40c3-42c4-b203-86ed242b23c6
-- title:
--   Aether Catalog definitions — Bridges_CatalogbuildSharedSublevel_Sublevel
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.CatalogbuildSharedSublevel.Sublevel`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/CatalogbuildSharedSublevel/Sublevel.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Shared.Sublevel

Auto-generated from theorem catalog database.
Domain: Shared
Declarations: 5
-/

/-- The remainder of `N` on division by `x`; the "energy" whose sublevel sets are
studied below. -/
def E (N x : ℕ) : ℕ := N % x

/-- [Section: # CatalogBuild.Shared.Sublevel
Auto-generated from theorem catalog database.
Domain: Speculative
Declarations: 5] -/
def sublevel (N t : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun x => E N x ≤ t)


