-- Prove2me | Definitions.Def_Geometry_Other_CrystallizerFormalization
-- name    : Geometry_Other_CrystallizerFormalization
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:45:28.8756+00:00
-- url     : https://prove2.me/theorems/950d8a90-5aa6-49af-8c99-0756d51bd9e8
-- title:
--   Aether Catalog definitions — Geometry_Other_CrystallizerFormalization
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.Other.CrystallizerFormalization`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/Other/CrystallizerFormalization.lean by skeleton subtraction
import Mathlib

open Real
/-! # CatalogBuild.Speculative.Other.CrystallizerFormalization

Auto-generated from theorem catalog database.
Domain: Speculative/Other
Declarations: 20
-/

noncomputable section





/-- The crystallization loss function for a single parameter. -/
def crystallizationLoss (m : ℝ) : ℝ := sin (π * m) ^ 2






/-- Inner product of two 2D vectors. -/
def inner2 (v w : ℝ × ℝ) : ℝ := v.1 * w.1 + v.2 * w.2

/-- Norm squared of a 2D vector. -/
def normSq2 (v : ℝ × ℝ) : ℝ := v.1 ^ 2 + v.2 ^ 2

/-- The Gram-Schmidt projection: remove the component of w along v. -/
def gramSchmidtProj (v w : ℝ × ℝ) : ℝ × ℝ :=
  (w.1 - inner2 v w * v.1, w.2 - inner2 v w * v.2)








end


