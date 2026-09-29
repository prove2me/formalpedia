-- Prove2me | Definitions.Def_Geometry_CosmicHorror_HalfPlaneMobius
-- name    : Geometry_CosmicHorror_HalfPlaneMobius
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:03:59.430173+00:00
-- url     : https://prove2.me/theorems/36f6acc0-8d6b-4fba-b8b2-4c295a20fc2e
-- title:
--   Aether Catalog definitions — Geometry_CosmicHorror_HalfPlaneMobius
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.CosmicHorror.HalfPlaneMobius`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/CosmicHorror/HalfPlaneMobius.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Geometry_CosmicHorror_HyperbolicIdealArea

/-!
# Boundary triples, real Möbius maps, and normalisation of ideal triangles

`HyperbolicIdealArea.lean` computes the hyperbolic area of the ideal triangle
whose vertices are two finite boundary points `a < b` and the boundary point
`∞`.  To know that this covers *every* ideal triangle one needs the classical
fact that the orientation-preserving isometry group of the half-plane model,
namely the real Möbius group `PSL(2, ℝ)`, acts **sharply three-transitively** on
the boundary circle `ℝ ∪ {∞}`.  This file proves exactly that, in an elementary
and fully explicit form, together with the two facts that make such maps
isometries of the hyperbolic plane:

* `mobius_im`:  `Im T(z) = det · Im z / ‖Cz + D‖²`, so a positive determinant
  forces the upper half-plane to be preserved (`mobius_mapsTo_upperHalfPlane`).
* `mobius_conformal_factor`:  `‖T'(z)‖ / Im T(z) = 1 / Im z`, i.e. `T` preserves
  the hyperbolic line element `|dz| / y` pointwise.  This is the infinitesimal
  statement of "`T` is a hyperbolic isometry".
* `exists_mobius_normalising`:  every triple `p < q < r` of finite boundary
  points is carried to the normal form `(0, 1, ∞)` by a real Möbius map of
  positive determinant, and `mobius_eq_id_of_fixes_zero_one_infty` shows that
  the normalising map is unique.  Hence three distinct boundary points do
  determine an ideal triangle, uniquely up to hyperbolic isometry.
-/

namespace CosmicHorrorGeometry

open Real Set Filter Topology Complex

/-! ### The real Möbius action -/

/-- A real Möbius transformation acting on the complex upper half-plane. -/
noncomputable def mobiusC (A B C D : ℝ) (z : ℂ) : ℂ := ((A : ℂ) * z + B) / ((C : ℂ) * z + D)

/-- The induced action on the boundary line `ℝ` (away from the pole). -/
noncomputable def mobiusR (A B C D : ℝ) (x : ℝ) : ℝ := (A * x + B) / (C * x + D)





/-! ### Sharp three-transitivity on the boundary -/










end CosmicHorrorGeometry


