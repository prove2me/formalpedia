-- Prove2me | Definitions.Def_Geometry_Algebra_DifferentialGeometry
-- name    : Geometry_Algebra_DifferentialGeometry
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T23:34:29.523495+00:00
-- url     : https://prove2.me/theorems/00896426-0832-4c2e-85ac-88922d01bb9d
-- title:
--   Aether Catalog definitions — Geometry_Algebra_DifferentialGeometry
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.Algebra.DifferentialGeometry`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/Algebra/DifferentialGeometry.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Algebra.DifferentialGeometry

Auto-generated from theorem catalog database.
Domain: Algebra
Declarations: 9
-/














/-- The generator of so(2): J = [[0,-1],[1,0]]. -/
def so2_generator : Matrix (Fin 2) (Fin 2) ℤ := !![0, -1; 1, 0]


