-- Prove2me | Definitions.Def_NumberTheory_AbstractAlgebra_Eml
-- name    : NumberTheory_AbstractAlgebra_Eml
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:06:43.373669+00:00
-- url     : https://prove2.me/theorems/9a5c2ded-155d-4c12-b17d-000fab5f6ce4
-- title:
--   Aether Catalog definitions — NumberTheory_AbstractAlgebra_Eml
-- statement:
--   Definition bundle for the Aether Catalog module `NumberTheory.AbstractAlgebra.Eml`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from NumberTheory/AbstractAlgebra/Eml.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Shared.Eml

Auto-generated from theorem catalog database.
Domain: Shared
Declarations: 17
-/

noncomputable section

/-- The EML operation `eml x y = eˣ - log y` (supplied here: the catalog module that originally
provided it is not part of this repository). -/
def eml (x y : ℝ) : ℝ := Real.exp x - Real.log y


















end


