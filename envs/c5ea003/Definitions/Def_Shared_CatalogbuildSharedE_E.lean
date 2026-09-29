-- Prove2me | Definitions.Def_Shared_CatalogbuildSharedE_E
-- name    : Shared_CatalogbuildSharedE_E
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T07:34:56.677906+00:00
-- url     : https://prove2.me/theorems/07e353d4-15e4-4892-afb2-cf9597cb5044
-- title:
--   Aether Catalog definitions — Shared_CatalogbuildSharedE_E
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.CatalogbuildSharedE.E`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/CatalogbuildSharedE/E.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Shared.E

Auto-generated from theorem catalog database.
Domain: Shared
Declarations: 1
-/

/-- The factoring energy function. -/
def E (N x : ℕ) : ℕ := N % x


