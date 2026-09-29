-- Prove2me | Definitions.Def_EML_TropicalAlgebra_SPBTropicalAlgebra
-- name    : EML_TropicalAlgebra_SPBTropicalAlgebra
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:21:55.81769+00:00
-- url     : https://prove2.me/theorems/c75e61c5-1468-401e-9aa5-98a513211efa
-- title:
--   Aether Catalog definitions — EML_TropicalAlgebra_SPBTropicalAlgebra
-- statement:
--   Definition bundle for the Aether Catalog module `EML.TropicalAlgebra.SPBTropicalAlgebra`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from EML/TropicalAlgebra/SPBTropicalAlgebra.lean by skeleton subtraction
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


