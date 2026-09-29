-- Prove2me | Definitions.Def_Shared_AbstractAlgebra_EmlDiag
-- name    : Shared_AbstractAlgebra_EmlDiag
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T07:34:05.20335+00:00
-- url     : https://prove2.me/theorems/a71ba875-01df-4b44-8f99-4c997b80d13a
-- title:
--   Aether Catalog definitions — Shared_AbstractAlgebra_EmlDiag
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.AbstractAlgebra.EmlDiag`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/AbstractAlgebra/EmlDiag.lean by skeleton subtraction
import Mathlib

open Set

/-! # CatalogBuild.Shared.EmlDiag

Auto-generated from theorem catalog database.
Domain: Shared
Declarations: 3
-/

noncomputable section

/-- The diagonal of `eml`: `emlDiag z = exp z - log z`. -/
def emlDiag (z : ℝ) : ℝ := Real.exp z - Real.log z




end


