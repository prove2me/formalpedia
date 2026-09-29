-- Prove2me | Definitions.Def_Speculative_EML_FixedPointTheory
-- name    : Speculative_EML_FixedPointTheory
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:32:21.985201+00:00
-- url     : https://prove2.me/theorems/34fa4472-8dde-420d-b122-426df44b2eff
-- title:
--   Aether Catalog definitions — Speculative_EML_FixedPointTheory
-- statement:
--   Definition bundle for the Aether Catalog module `Speculative.EML.FixedPointTheory`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Speculative/EML/FixedPointTheory.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.EML.FixedPointTheory

Auto-generated from theorem catalog database.
Domain: EML
Declarations: 12
-/

noncomputable section










/-- The EML iteration z_{n+1} = exp(z_n) - log(y). -/
def emlIterate (y : ℝ) : ℕ → ℝ → ℝ
  | 0, z => z
  | n + 1, z => Real.exp (emlIterate y n z) - Real.log y



end


