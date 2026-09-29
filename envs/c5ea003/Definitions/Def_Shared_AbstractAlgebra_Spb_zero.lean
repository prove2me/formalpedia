-- Prove2me | Definitions.Def_Shared_AbstractAlgebra_Spb_zero
-- name    : Shared_AbstractAlgebra_Spb_zero
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T14:48:25.841398+00:00
-- url     : https://prove2.me/theorems/7d69f2bf-1d71-4f89-99b9-8d9267594b02
-- title:
--   Aether Catalog definitions — Shared_AbstractAlgebra_Spb_zero
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.AbstractAlgebra.Spb.zero`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/AbstractAlgebra/Spb_zero.lean by skeleton subtraction
import Mathlib

open Real

/-! # CatalogBuild.Shared.Spb_zero

Auto-generated from theorem catalog database.
Domain: Shared
Declarations: 5
-/

noncomputable section

/-- The speed-addition law `spb x y = (x + y) / (1 - x y)`. -/
def spb (x y : ℝ) : ℝ := (x + y) / (1 - x * y)






end


