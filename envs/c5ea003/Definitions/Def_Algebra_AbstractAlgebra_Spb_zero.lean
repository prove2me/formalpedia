-- Prove2me | Definitions.Def_Algebra_AbstractAlgebra_Spb_zero
-- name    : Algebra_AbstractAlgebra_Spb_zero
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:05:22.902882+00:00
-- url     : https://prove2.me/theorems/f4c913ef-7539-45d4-bfe3-764065bdc453
-- title:
--   Aether Catalog definitions — Algebra_AbstractAlgebra_Spb_zero
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.AbstractAlgebra.Spb.zero`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/AbstractAlgebra/Spb_zero.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Shared.Spb_zero

Auto-generated from theorem catalog database.
Domain: Shared
Declarations: 5

Repaired: the operation `spb` is defined here and `open Real` added so that the
bare `exp` and `log` of `spb_eml_decomposition` resolve.
-/

noncomputable section

open Real

/-- The SPB (Stereographic Projection Bridge) operation. -/
def spb (x y : ℝ) : ℝ := (x + y) / (1 - x * y)






end


