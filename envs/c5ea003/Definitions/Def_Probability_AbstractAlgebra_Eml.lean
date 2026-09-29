-- Prove2me | Definitions.Def_Probability_AbstractAlgebra_Eml
-- name    : Probability_AbstractAlgebra_Eml
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:06:12.853297+00:00
-- url     : https://prove2.me/theorems/e0b92a41-e695-4852-b89d-756e956042d3
-- title:
--   Aether Catalog definitions — Probability_AbstractAlgebra_Eml
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.AbstractAlgebra.Eml`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/AbstractAlgebra/Eml.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Shared.Eml

Auto-generated from theorem catalog database.
Domain: Shared
Declarations: 17
-/

noncomputable section

/-- The EML ("exponential minus logarithm") operation `eml x y = eˣ - log y`.
(The auto-generated catalog file used this definition without stating it.) -/
def eml (x y : ℝ) : ℝ := Real.exp x - Real.log y


















end


