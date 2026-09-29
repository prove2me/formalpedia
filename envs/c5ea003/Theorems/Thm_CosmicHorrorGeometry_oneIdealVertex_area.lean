-- Prove2me | Theorems.Thm_CosmicHorrorGeometry_oneIdealVertex_area
-- name    : CosmicHorrorGeometry.oneIdealVertex_area
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:11:09.470182+00:00
-- url     : https://prove2.me/theorems/d13f354e-5ad1-4661-b075-411dd424aa1e
-- title:
--   The area computation.
-- statement:
--   **The area computation.**  The triangle with at least one ideal vertex has
--   area `(θ - φ)/κ`.  The hypotheses `0 ≤ φ < θ ≤ π` allow the two "finite"
--   vertices to sit *on* the boundary as well (`φ = 0` or `θ = π`), so this single
--   statement covers triangles with one, two or three ideal vertices.
--
--   ```lean
--   theorem CosmicHorrorGeometry.oneIdealVertex_area{κ θ φ : ℝ} (hφ : 0 ≤ φ) (hφθ : φ < θ) (hθ : θ ≤ π) :
--       oneIdealVertexArea κ θ φ = (θ - φ) / κ := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/CosmicHorror/OneIdealVertex.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/CosmicHorror/OneIdealVertex.lean#L154

-- Thm stub generated from Geometry/CosmicHorror/OneIdealVertex.lean
import Mathlib
import Definitions.Def_Geometry_CosmicHorror_HyperbolicIdealArea
import Definitions.Def_Geometry_CosmicHorror_OneIdealVertex

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

open CosmicHorrorGeometry

open Real Set MeasureTheory Filter Topology

/-! ### Euclidean = hyperbolic angles -/









/-! ### The unit semicircle as the lower boundary -/




/-! ### The area of a triangle with one ideal vertex -/

theorem CosmicHorrorGeometry.oneIdealVertex_area{κ θ φ : ℝ} (hφ : 0 ≤ φ) (hφθ : φ < θ) (hθ : θ ≤ π) :
    oneIdealVertexArea κ θ φ = (θ - φ) / κ := by sorry
