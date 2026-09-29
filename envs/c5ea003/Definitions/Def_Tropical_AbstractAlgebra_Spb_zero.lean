-- Prove2me | Definitions.Def_Tropical_AbstractAlgebra_Spb_zero
-- name    : Tropical_AbstractAlgebra_Spb_zero
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T08:29:02.260421+00:00
-- url     : https://prove2.me/theorems/485f1efd-ad90-4df9-85fe-cea6215060ee
-- title:
--   Aether Catalog definitions — Tropical_AbstractAlgebra_Spb_zero
-- statement:
--   Definition bundle for the Aether Catalog module `Tropical.AbstractAlgebra.Spb.zero`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Tropical/AbstractAlgebra/Spb_zero.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Shared.Spb_zero

Auto-generated from theorem catalog database.
Domain: Shared
Declarations: 5
-/

open Real

noncomputable section

/-- The SPB (stereographic projection bridge) operation,
`spb x y = (x + y) / (1 - x * y)`. -/
def spb (x y : ℝ) : ℝ := (x + y) / (1 - x * y)






end


