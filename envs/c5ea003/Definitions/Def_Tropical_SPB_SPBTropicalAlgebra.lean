-- Prove2me | Definitions.Def_Tropical_SPB_SPBTropicalAlgebra
-- name    : Tropical_SPB_SPBTropicalAlgebra
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T08:32:37.362277+00:00
-- url     : https://prove2.me/theorems/ee492aab-0103-46c2-afbb-f8e51daa3156
-- title:
--   Aether Catalog definitions — Tropical_SPB_SPBTropicalAlgebra
-- statement:
--   Definition bundle for the Aether Catalog module `Tropical.SPB.SPBTropicalAlgebra`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Tropical/SPB/SPBTropicalAlgebra.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.EML.SPBTropicalAlgebra

Auto-generated from theorem catalog database.
Domain: EML
Declarations: 9
-/

noncomputable section

/-- Tropical SPB: tropicalization of (x+y)/(1-xy). -/
def tropSPB' (x y : ℝ) : ℝ := min x y - max 0 (x + y)









end


