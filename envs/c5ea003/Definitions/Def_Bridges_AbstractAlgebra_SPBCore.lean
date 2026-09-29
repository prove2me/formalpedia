-- Prove2me | Definitions.Def_Bridges_AbstractAlgebra_SPBCore
-- name    : Bridges_AbstractAlgebra_SPBCore
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:07:00.623095+00:00
-- url     : https://prove2.me/theorems/b114bf79-66e0-495c-91ab-7e807817ef43
-- title:
--   Aether Catalog definitions — Bridges_AbstractAlgebra_SPBCore
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.AbstractAlgebra.SPBCore`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/AbstractAlgebra/SPBCore.lean by skeleton subtraction
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


