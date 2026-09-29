-- Prove2me | Definitions.Def_Tropical_Computation_TropicalConnection
-- name    : Tropical_Computation_TropicalConnection
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T08:29:48.832174+00:00
-- url     : https://prove2.me/theorems/b0fb140e-6f3e-40d2-8bdf-c4f9228865ab
-- title:
--   Aether Catalog definitions — Tropical_Computation_TropicalConnection
-- statement:
--   Definition bundle for the Aether Catalog module `Tropical.Computation.TropicalConnection`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Tropical/Computation/TropicalConnection.lean by skeleton subtraction
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


