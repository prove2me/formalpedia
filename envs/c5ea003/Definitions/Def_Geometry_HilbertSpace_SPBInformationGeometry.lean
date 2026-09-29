-- Prove2me | Definitions.Def_Geometry_HilbertSpace_SPBInformationGeometry
-- name    : Geometry_HilbertSpace_SPBInformationGeometry
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:18:01.328463+00:00
-- url     : https://prove2.me/theorems/f80fe46f-b457-4c1b-9e6d-4615c657f616
-- title:
--   Aether Catalog definitions — Geometry_HilbertSpace_SPBInformationGeometry
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.HilbertSpace.SPBInformationGeometry`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/HilbertSpace/SPBInformationGeometry.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Speculative.SPBInformationGeometry

Auto-generated from theorem catalog database.
Domain: Speculative
Declarations: 10
-/

noncomputable section

/-- The standard Cauchy density (μ=0, γ=1). -/
def stdCauchyDensity (x : ℝ) : ℝ := 1 / (Real.pi * (1 + x ^ 2))


/-- The SPB operator. -/
def spbIG (x y : ℝ) : ℝ := (x + y) / (1 - x * y)

/-- The Jacobian of SPB w.r.t. the first variable: (1+y²)/(1-xy)². -/
def spbJacobian (x y : ℝ) : ℝ := (1 + y ^ 2) / (1 - x * y) ^ 2




/-- The hyperbolic distance between two points on the upper half-plane.
For the Cauchy manifold parametrized by (μ, γ), this is the Fisher metric. -/
def hyperbolicDist (μ₁ γ₁ μ₂ γ₂ : ℝ) : ℝ :=
  Real.log ((μ₁ - μ₂) ^ 2 + (γ₁ + γ₂) ^ 2) -
  Real.log ((μ₁ - μ₂) ^ 2 + (γ₁ - γ₂) ^ 2)



end


