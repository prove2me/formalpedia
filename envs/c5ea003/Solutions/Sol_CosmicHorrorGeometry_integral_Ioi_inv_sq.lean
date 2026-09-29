-- Prove2me | solution 1 for CosmicHorrorGeometry.integral_Ioi_inv_sq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:05:32.096688+00:00
-- url     : https://prove2.me/submissions/fadfd560-25f4-4f1e-8c57-20b2a5b45556

-- Sol generated from Geometry/CosmicHorror/HyperbolicIdealArea.lean
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



/-! ### The ideal triangle -/







/-! ### Ideal polygons -/




/-! ### Degeneration: exhausting the ideal triangle by truncated regions -/





/-! ### The angle side of the degeneration -/



open CosmicHorrorGeometry in
theorem solution{c : ℝ} (hc : 0 < c) :
    ∫ y in Ioi c, (y ^ 2)⁻¹ = c⁻¹ := by
  have hcongr : ∫ y in Ioi c, (y ^ 2)⁻¹ = ∫ y in Ioi c, y ^ (-2 : ℝ) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
    have hy0 : (0 : ℝ) < y := hc.trans hy
    rw [show (-2 : ℝ) = -(2 : ℕ) by norm_num, Real.rpow_neg hy0.le, Real.rpow_natCast]
  rw [hcongr, integral_Ioi_rpow_of_lt (by norm_num) hc]
  rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
  ring
