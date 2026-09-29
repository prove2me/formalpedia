-- Prove2me | solution 1 for CosmicHorrorGeometry.angleBetween_smul_right
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:52:45.483002+00:00
-- url     : https://prove2.me/submissions/85e34d06-cb3c-4516-ac16-8d4caff72f67

-- Sol generated from Geometry/CosmicHorror/OneIdealVertex.lean
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












open CosmicHorrorGeometry in
theorem solution(c : ℝ) (hc : 0 < c) (u v : ℝ × ℝ) :
    angleBetween u (c * v.1, c * v.2) = angleBetween u v := by
  unfold angleBetween
  have h : Real.sqrt ((c * v.1) ^ 2 + (c * v.2) ^ 2)
      = c * Real.sqrt (v.1 ^ 2 + v.2 ^ 2) := by
    rw [show (c * v.1) ^ 2 + (c * v.2) ^ 2 = c ^ 2 * (v.1 ^ 2 + v.2 ^ 2) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq hc.le]
  rw [h]
  congr 1
  rw [show u.1 * (c * v.1) + u.2 * (c * v.2) = c * (u.1 * v.1 + u.2 * v.2) by ring,
    show Real.sqrt (u.1 ^ 2 + u.2 ^ 2) * (c * Real.sqrt (v.1 ^ 2 + v.2 ^ 2))
      = c * (Real.sqrt (u.1 ^ 2 + u.2 ^ 2) * Real.sqrt (v.1 ^ 2 + v.2 ^ 2)) by ring]
  exact mul_div_mul_left _ _ hc.ne'
