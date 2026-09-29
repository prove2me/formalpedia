-- Prove2me | Definitions.Def_Geometry_CosmicHorror_OneIdealVertex
-- name    : Geometry_CosmicHorror_OneIdealVertex
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:03:57.396492+00:00
-- url     : https://prove2.me/theorems/6bda9614-4b7a-46a0-ba9b-8f021d8df279
-- title:
--   Aether Catalog definitions — Geometry_CosmicHorror_OneIdealVertex
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.CosmicHorror.OneIdealVertex`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/CosmicHorror/OneIdealVertex.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Geometry_CosmicHorror_HyperbolicIdealArea

/-!
# Gauss–Bonnet with one ideal vertex, derived from the metric

This file carries the programme of `HyperbolicIdealArea.lean` one step further.
There we computed the area of a *fully* ideal triangle (all three angles `0`).
Here we compute the area of a hyperbolic triangle with **one** ideal vertex and
two genuine finite vertices, and we do not postulate the interior angles: we
*define* them as angles between the tangent vectors of the two geodesic sides
and prove the Gauss–Bonnet identity

`area = (π - (α + β + 0)) / κ = hyperbolicArea κ α β 0`.

Because the half-plane metric `(dx² + dy²)/(κ y²)` is a pointwise positive
multiple of the Euclidean one, hyperbolic angles coincide with Euclidean
angles; this is recorded formally by `angleBetween_smul_left` and
`angleBetween_smul_right`, which say the angle functional is invariant under
positive rescaling of either tangent vector, hence under conformal change of
metric.

## The configuration

Fix `0 < φ < θ < π`.  The triangle has

* geodesic sides the two vertical rays `x = cos θ` and `x = cos φ` (these are
  half-plane geodesics), and the unit semicircle `|z| = 1` (also a geodesic);
* vertices `(cos θ, sin θ)`, `(cos φ, sin φ)` and the ideal point `∞`.

## Main results

* `angleBetween_vertical_circleRight`, `angleBetween_vertical_circleLeft`:  the
  interior angles are `π - θ` and `φ`.
* `oneIdealVertex_area`:  the hyperbolic area equals `(θ - φ)/κ`.  The result is
  proved for `0 ≤ φ < θ ≤ π`, so it covers one, two (`twoIdealVertices_area`)
  and three (`threeIdealVertices_area`) ideal vertices in one statement.
* `oneIdealVertex_gauss_bonnet`:  the area equals `hyperbolicArea κ α β 0`,
  the algebraic Gauss–Bonnet invariant evaluated at the two computed angles.
* `oneIdealVertex_angles_pos`:  both finite angles are *strictly* positive, so
  a triangle with a finite vertex is never ideal — angle sum `0` really does
  require adjoining the boundary.
* `oneIdealVertex_area_lt_ideal`:  consequently its area is strictly below the
  ideal maximum `π / κ`.
-/

namespace CosmicHorrorGeometry

open Real Set MeasureTheory Filter Topology

/-! ### Euclidean = hyperbolic angles -/

/-- The angle between two nonzero plane vectors.  Since the half-plane metric is
conformal to the Euclidean metric, this is also the hyperbolic angle. -/
noncomputable def angleBetween (u v : ℝ × ℝ) : ℝ :=
  Real.arccos ((u.1 * v.1 + u.2 * v.2) /
    (Real.sqrt (u.1 ^ 2 + u.2 ^ 2) * Real.sqrt (v.1 ^ 2 + v.2 ^ 2)))



/-- The upward tangent vector of a vertical geodesic. -/
def verticalTangent : ℝ × ℝ := (0, 1)

/-- The tangent vector, pointing in the direction of increasing `x`, of the unit
semicircle geodesic at the point `(cos θ, sin θ)`. -/
noncomputable def circleTangentRight (θ : ℝ) : ℝ × ℝ := (Real.sin θ, -Real.cos θ)

/-- The tangent vector, pointing in the direction of decreasing `x`, of the unit
semicircle geodesic at the point `(cos φ, sin φ)`. -/
noncomputable def circleTangentLeft (φ : ℝ) : ℝ × ℝ := (-Real.sin φ, Real.cos φ)



/-! ### The unit semicircle as the lower boundary -/




/-! ### The area of a triangle with one ideal vertex -/

/-- The hyperbolic area, at curvature `-κ`, of the triangle with vertices
`(cos θ, sin θ)`, `(cos φ, sin φ)` and `∞`, bounded by the two vertical
geodesics and the unit semicircle. -/
noncomputable def oneIdealVertexArea (κ θ φ : ℝ) : ℝ :=
  slicedArea κ (Real.cos θ) (Real.cos φ) (chordHeight (-1) 1)










end CosmicHorrorGeometry


