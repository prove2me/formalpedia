-- Prove2me | Definitions.Def_EML_NumberTheory_HyperbolicGeometry
-- name    : EML_NumberTheory_HyperbolicGeometry
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:21:40.793837+00:00
-- url     : https://prove2.me/theorems/1107366e-e708-4618-a6c4-d2f2032a932b
-- title:
--   Aether Catalog definitions — EML_NumberTheory_HyperbolicGeometry
-- statement:
--   Definition bundle for the Aether Catalog module `EML.NumberTheory.HyperbolicGeometry`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from EML/NumberTheory/HyperbolicGeometry.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.EML.HyperbolicGeometry

Auto-generated from theorem catalog database.
Domain: EML
Declarations: 12
-/

noncomputable section

/-- The hyperbolic SPB (Einstein velocity addition). -/
def spbH_hyp (x y : ℝ) : ℝ := (x + y) / (1 + x * y)

/-- Hyperbolic distance in the Poincaré disk model.
d(x, y) = arctanh(|spbH(x, -y)|) = arctanh(|(x-y)/(1-xy)|). -/
def hypDist (x y : ℝ) : ℝ := Real.log ((1 + |spbH_hyp x (-y)|) / (1 - |spbH_hyp x (-y)|)) / 2











end


