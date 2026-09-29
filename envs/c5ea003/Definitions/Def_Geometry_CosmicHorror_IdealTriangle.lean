-- Prove2me | Definitions.Def_Geometry_CosmicHorror_IdealTriangle
-- name    : Geometry_CosmicHorror_IdealTriangle
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T23:55:08.125155+00:00
-- url     : https://prove2.me/theorems/ebb52078-2195-4465-a787-72395dc347f3
-- title:
--   Aether Catalog definitions — Geometry_CosmicHorror_IdealTriangle
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.CosmicHorror.IdealTriangle`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/CosmicHorror/IdealTriangle.lean by skeleton subtraction
import Mathlib

/-!
# Ideal triangles and maximal hyperbolic area

For constant curvature `-κ` with `κ > 0`, Gauss--Bonnet gives the area of a
hyperbolic triangle with angles `α, β, γ` as

`(π - (α + β + γ)) / κ`.

This file isolates that invariant and proves its extremal rigidity: among
triangles whose angles are nonnegative, the maximal area `π / κ` is attained
exactly when all three angles vanish. Thus a triangle whose angle sum is zero
is naturally an *ideal* triangle (its vertices lie at infinity), rather than an
ordinary finite-vertex triangle.
-/

namespace CosmicHorrorGeometry

/-- The Gauss--Bonnet area determined by curvature magnitude `κ` and three
interior angles. -/
noncomputable def hyperbolicArea (κ α β γ : ℝ) : ℝ :=
  (Real.pi - (α + β + γ)) / κ

/-- An angle triple is admissible when its entries are nonnegative and its sum
is at most `π`. -/
def AdmissibleAngles (α β γ : ℝ) : Prop :=
  0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ α + β + γ ≤ Real.pi















end CosmicHorrorGeometry


