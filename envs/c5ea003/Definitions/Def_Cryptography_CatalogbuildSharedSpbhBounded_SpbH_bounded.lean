-- Prove2me | Definitions.Def_Cryptography_CatalogbuildSharedSpbhBounded_SpbH_bounded
-- name    : Cryptography_CatalogbuildSharedSpbhBounded_SpbH_bounded
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:12:06.215062+00:00
-- url     : https://prove2.me/theorems/cbf98d4d-5b08-416a-b756-b0a954b1126c
-- title:
--   Aether Catalog definitions — Cryptography_CatalogbuildSharedSpbhBounded_SpbH_bounded
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.CatalogbuildSharedSpbhBounded.SpbH.bounded`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/CatalogbuildSharedSpbhBounded/SpbH_bounded.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Shared.SpbH_bounded

Auto-generated from theorem catalog database.
Domain: Shared
Declarations: 3
-/

noncomputable section

/-- The hyperbolic (Einstein) velocity-addition law. -/
def spbH (u v : ℝ) : ℝ := (u + v) / (1 + u * v)




end


