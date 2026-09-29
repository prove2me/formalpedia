-- Prove2me | Definitions.Def_Shared_CatalogbuildSharedSpbcirc_SpbCirc
-- name    : Shared_CatalogbuildSharedSpbcirc_SpbCirc
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T07:34:55.926139+00:00
-- url     : https://prove2.me/theorems/b8dfd637-3815-42b0-87af-7e877e97b79f
-- title:
--   Aether Catalog definitions — Shared_CatalogbuildSharedSpbcirc_SpbCirc
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.CatalogbuildSharedSpbcirc.SpbCirc`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/CatalogbuildSharedSpbcirc/SpbCirc.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Shared.SpbCirc

Auto-generated from theorem catalog database.
Domain: Shared
Declarations: 4
-/

noncomputable section

/-- The circular SPB. -/
def spbCirc (x y : ℝ) : ℝ := (x + y) / (1 - x * y)




end


