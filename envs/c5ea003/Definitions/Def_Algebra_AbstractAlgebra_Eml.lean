-- Prove2me | Definitions.Def_Algebra_AbstractAlgebra_Eml
-- name    : Algebra_AbstractAlgebra_Eml
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:04:47.066426+00:00
-- url     : https://prove2.me/theorems/61fd74cf-849f-4bac-8a26-cd36765c1328
-- title:
--   Aether Catalog definitions — Algebra_AbstractAlgebra_Eml
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.AbstractAlgebra.Eml`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/AbstractAlgebra/Eml.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Shared.Eml

Auto-generated from theorem catalog database.
Domain: Shared
Declarations: 17

Repaired: the EML operation `eml x y = exp x - log y`, which the file used but
never defined, is supplied here.
-/

noncomputable section

/-- The EML (exp-minus-log) operation `eml x y = exp x - log y`. -/
def eml (x y : ℝ) : ℝ := Real.exp x - Real.log y


















end


