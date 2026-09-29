-- Prove2me | Definitions.Def_Tropical_Connection_TropicalConnection
-- name    : Tropical_Connection_TropicalConnection
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T08:29:54.495985+00:00
-- url     : https://prove2.me/theorems/469d8391-5940-410d-b6ca-6ce43de391e1
-- title:
--   Aether Catalog definitions — Tropical_Connection_TropicalConnection
-- statement:
--   Definition bundle for the Aether Catalog module `Tropical.Connection.TropicalConnection`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Tropical/Connection/TropicalConnection.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Computation.TropicalConnection

Auto-generated from theorem catalog database.
Domain: Computation
Declarations: 12
-/


noncomputable section

/-- [Section: # CatalogBuild.Computation.TropicalConnection
Auto-generated from theorem catalog database.
Domain: Computation
Declarations: 12] -/
def EML_trop (a b : ℝ) : ℝ := Real.exp a - Real.log b








def tropVal (x : ℝ) : ℝ := Real.log x








def logSumExp (a b : ℝ) : ℝ := Real.log (Real.exp a + Real.exp b)




















def EML_poly1 (a b c x : ℝ) : ℝ := EML_trop (a + b * x) c












end


