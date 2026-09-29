-- Prove2me | Definitions.Def_Geometry_Stereographic_ConformalBackprop
-- name    : Geometry_Stereographic_ConformalBackprop
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:55:59.719884+00:00
-- url     : https://prove2.me/theorems/6f58968e-ba66-4944-b152-ad7b2303bbaf
-- title:
--   Aether Catalog definitions — Geometry_Stereographic_ConformalBackprop
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.Stereographic.ConformalBackprop`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/Stereographic/ConformalBackprop.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Geometry.Stereographic.ConformalBackprop

Auto-generated from theorem catalog database.
Domain: Geometry/Stereographic
Declarations: 10
-/


noncomputable section

/-- The gradient scaling factor for a conformal map with conformal factor λ. -/
def conformalGradScale (lambda : ℝ) (gradNorm : ℝ) : ℝ :=
  lambda * gradNorm




/-- The stereographic conformal factor. -/
def stereoLambda (n : ℕ) (x : Fin n → ℝ) : ℝ :=
  2 / (1 + ∑ i, (x i) ^ 2)
















/-- For a composition of L stereographic layers, the total gradient
scaling factor is the product of individual conformal factors.
Each factor is in (0, 2], so the product is in (0, 2^L]. -/
def composedGradScale (L : ℕ) (lambdas : Fin L → ℝ) : ℝ :=
  ∏ i, lambdas i




















end


