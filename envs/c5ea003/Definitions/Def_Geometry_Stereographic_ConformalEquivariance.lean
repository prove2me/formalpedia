-- Prove2me | Definitions.Def_Geometry_Stereographic_ConformalEquivariance
-- name    : Geometry_Stereographic_ConformalEquivariance
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:55:59.667565+00:00
-- url     : https://prove2.me/theorems/f0997a34-97da-477b-8bf7-928d75a1e77e
-- title:
--   Aether Catalog definitions — Geometry_Stereographic_ConformalEquivariance
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.Stereographic.ConformalEquivariance`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/Stereographic/ConformalEquivariance.lean by skeleton subtraction
import Mathlib
/-! # CatalogBuild.Geometry.Stereographic.ConformalEquivariance

Auto-generated from theorem catalog database.
Domain: Geometry/Stereographic
Declarations: 17
-/


noncomputable section

/-- Rotation action: applies an orthogonal matrix to ℝⁿ. -/
def rotationAction (n : ℕ) (R : Fin n → Fin n → ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => ∑ j, R i j * x j




/-- Dilation action: scales a vector by a positive factor. -/
def dilationAction (lambda : ℝ) (n : ℕ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => lambda * x i








/-- The squared norm of a vector. -/
def vecSqNorm' (n : ℕ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, (x i) ^ 2




/-- The stereographic kernel. -/
def stereoKernel' (n : ℕ) (x y : Fin n → ℝ) : ℝ :=
  (4 * ∑ i, x i * y i + (vecSqNorm' n x - 1) * (vecSqNorm' n y - 1)) /
  ((1 + vecSqNorm' n x) * (1 + vecSqNorm' n y))




















































end


