-- Prove2me | Theorems.Thm_CosmicHorrorGeometry_slicedArea_eq
-- name    : CosmicHorrorGeometry.slicedArea_eq
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:10:11.729392+00:00
-- url     : https://prove2.me/theorems/49df5b5d-6478-4559-9e11-916912381989
-- title:
--   Slicing reduces a two-dimensional hyperbolic area to a one-dimensional
-- statement:
--   Slicing reduces a two-dimensional hyperbolic area to a one-dimensional
--   integral of the reciprocal height of the lower boundary.
--
--   ```lean
--   theorem CosmicHorrorGeometry.slicedArea_eq{κ a b : ℝ} (hab : a < b) (low : ℝ → ℝ)
--       (hlow : ∀ x ∈ Ioo a b, 0 < low x) :
--       slicedArea κ a b low = (∫ x in a..b, (low x)⁻¹) / κ := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/CosmicHorror/HyperbolicIdealArea.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/CosmicHorror/HyperbolicIdealArea.lean#L181

-- Thm stub generated from Geometry/CosmicHorror/HyperbolicIdealArea.lean
import Mathlib
import Definitions.Def_Geometry_CosmicHorror_HyperbolicIdealArea
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

open CosmicHorrorGeometry

open Real Set MeasureTheory intervalIntegral Filter Topology

/-! ### The analytic core: the chordal density and its antiderivative -/











/-! ### The vertical fibre of the hyperbolic area element -/


/-! ### The hyperbolic area of a vertically sliced region -/

theorem CosmicHorrorGeometry.slicedArea_eq{κ a b : ℝ} (hab : a < b) (low : ℝ → ℝ)
    (hlow : ∀ x ∈ Ioo a b, 0 < low x) :
    slicedArea κ a b low = (∫ x in a..b, (low x)⁻¹) / κ := by sorry
