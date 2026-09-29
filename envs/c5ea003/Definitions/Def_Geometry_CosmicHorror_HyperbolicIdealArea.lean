-- Prove2me | Definitions.Def_Geometry_CosmicHorror_HyperbolicIdealArea
-- name    : Geometry_CosmicHorror_HyperbolicIdealArea
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T23:59:20.527566+00:00
-- url     : https://prove2.me/theorems/6526d564-8afb-42b8-b658-a0f75acba304
-- title:
--   Aether Catalog definitions — Geometry_CosmicHorror_HyperbolicIdealArea
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.CosmicHorror.HyperbolicIdealArea`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/CosmicHorror/HyperbolicIdealArea.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Geometry_CosmicHorror_IdealTriangle

/-!
# From angle data to a Riemannian area integral: ideal triangles in the half-plane

The companion file `Geometry/CosmicHorror/IdealTriangle.lean` studies the
*algebraic* Gauss–Bonnet invariant

`hyperbolicArea κ α β γ = (π - (α + β + γ)) / κ`

as a function of angle data only.  The present file replaces the angle data by
an honest Riemannian computation in the **upper half-plane model** of the
hyperbolic plane of constant curvature `-κ`, whose area element is

`dA = dx dy / (κ y²)`.

## Main results

* `hasDerivAt_arcsinChord` / `intervalIntegrable_invSqrtChord`:  the analytic
  core, an explicit antiderivative for the chordal density
  `x ↦ (√((x - a)(b - x)))⁻¹` together with its (improper) integrability.
* `integral_invSqrtChord`:  `∫ x in a..b, (√((x - a)(b - x)))⁻¹ = π`.
  This is the whole geometry of an ideal triangle compressed into one identity.
* `integral_Ioi_inv_sq`:  the vertical fibre integral `∫_{c}^{∞} y⁻² dy = c⁻¹`,
  i.e. the hyperbolic length of the fibre measure above a point.
* `idealTriangleArea_eq`:  **the area of the ideal triangle with vertices
  `a < b` on the real line and `∞` equals `π / κ`**, computed from the area
  element by Fubini-style slicing.  Together with
  `idealTriangleArea_eq_hyperbolicArea` this *derives* the value that
  `IdealTriangle.lean` obtained from Gauss–Bonnet with all angles `0`.
* `idealPolygonArea_eq`:  the ideal `(m+2)`-gon with finite vertices
  `v 0 < ⋯ < v m` and last vertex `∞` has area `m · π / κ = ((n - 2) π)/κ`.
* `truncatedIdealTriangleArea_lt` and `tendsto_truncatedIdealTriangleArea`:
  the degeneration statement — the compact exhaustion of an ideal triangle by
  truncated regions has strictly smaller area, converging to `π / κ`.
* `angles_tendsto_zero_of_area_tendsto_max`:  conversely, on the angle side, a
  sequence of admissible triangles whose Gauss–Bonnet area tends to the maximum
  `π / κ` must have *all three* angles tending to `0`; the ideal triangle is the
  unique limiting shape.
-/

namespace CosmicHorrorGeometry

open Real Set MeasureTheory intervalIntegral Filter Topology

/-! ### The analytic core: the chordal density and its antiderivative -/

/-- The antiderivative of the chordal density on the interval `[a, b]`:
`x ↦ arcsin ((2x - a - b)/(b - a))`, normalised so that it runs from `-π/2` to
`π/2`. -/
noncomputable def arcsinChord (a b x : ℝ) : ℝ := Real.arcsin ((2 * x - a - b) / (b - a))

/-- The hyperbolic lower boundary of the ideal triangle with real vertices
`a < b`: the euclidean semicircle with diameter `[a, b]`, which is the geodesic
of the half-plane model joining the two boundary points. -/
noncomputable def chordHeight (a b x : ℝ) : ℝ := Real.sqrt ((x - a) * (b - x))









/-! ### The vertical fibre of the hyperbolic area element -/


/-! ### The hyperbolic area of a vertically sliced region -/

/-- The hyperbolic area, at curvature `-κ`, of the region of the upper
half-plane lying over the interval `(a, b)` and above the graph of `low`,
computed by slicing:  `∫_a^b ∫_{low x}^∞ dy dx / (κ y²)`. -/
noncomputable def slicedArea (κ a b : ℝ) (low : ℝ → ℝ) : ℝ :=
  ∫ x in a..b, ∫ y in Ioi (low x), (κ * y ^ 2)⁻¹


/-! ### The ideal triangle -/

/-- The ideal triangle of the half-plane model with vertices `a < b` on the
boundary line and third vertex at `∞`: the region above the geodesic semicircle
with diameter `[a, b]` and between the two vertical geodesics `x = a`, `x = b`. -/
def idealTriangleRegion (a b : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Ioo a b ∧ chordHeight a b p.1 < p.2}






/-! ### Ideal polygons -/

/-- The ideal `(m+2)`-gon with finite boundary vertices `v 0 < v 1 < ⋯ < v m`
and last vertex `∞`.  Its region is the union of the vertical strips over the
consecutive intervals, so its area is the corresponding sum. -/
noncomputable def idealPolygonArea (κ : ℝ) (m : ℕ) (v : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range m, slicedArea κ (v i) (v (i + 1)) (chordHeight (v i) (v (i + 1)))



/-! ### Degeneration: exhausting the ideal triangle by truncated regions -/

/-- The truncated ideal triangle: the part of the ideal triangle over
`[a + t, b - t]`.  For `t > 0` this is a compact-in-the-model piece with finite
"vertices". -/
noncomputable def truncatedIdealTriangleArea (κ a b t : ℝ) : ℝ :=
  slicedArea κ (a + t) (b - t) (chordHeight a b)




/-! ### The angle side of the degeneration -/


end CosmicHorrorGeometry


