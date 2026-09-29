-- Prove2me | Definitions.Def_Speculative_Logic_SpbCirc
-- name    : Speculative_Logic_SpbCirc
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:32:42.029078+00:00
-- url     : https://prove2.me/theorems/200b4e2e-bc38-48b0-b31c-d21fd5f408d8
-- title:
--   Aether Catalog definitions — Speculative_Logic_SpbCirc
-- statement:
--   Definition bundle for the Aether Catalog module `Speculative.Logic.SpbCirc`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Speculative/Logic/SpbCirc.lean by skeleton subtraction
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


