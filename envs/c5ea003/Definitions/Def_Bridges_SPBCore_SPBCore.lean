-- Prove2me | Definitions.Def_Bridges_SPBCore_SPBCore
-- name    : Bridges_SPBCore_SPBCore
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:39:09.536259+00:00
-- url     : https://prove2.me/theorems/45959de8-0434-43c6-808e-26aef2dd178b
-- title:
--   Aether Catalog definitions — Bridges_SPBCore_SPBCore
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.SPBCore.SPBCore`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/SPBCore/SPBCore.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Bridges.SPBCore

Auto-generated from theorem catalog database.
Domain: Bridges
Declarations: 5
-/

noncomputable section

/-- SPB over an arbitrary field. -/
def spbF {F : Type*} [Field F] (x y : F) : F := (x + y) / (1 - x * y)





end


