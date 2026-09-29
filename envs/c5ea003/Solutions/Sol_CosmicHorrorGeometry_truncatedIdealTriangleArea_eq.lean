-- Prove2me | solution 1 for CosmicHorrorGeometry.truncatedIdealTriangleArea_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:15:50.214296+00:00
-- url     : https://prove2.me/submissions/0158cdd8-6981-4b63-9c44-31de9912726c

-- Sol generated from Geometry/CosmicHorror/HyperbolicIdealArea.lean
import Mathlib
import Definitions.Def_Geometry_CosmicHorror_HyperbolicIdealArea
import Definitions.Def_Geometry_CosmicHorror_IdealTriangle
import Theorems.Thm_CosmicHorrorGeometry_chordHeight_pos
import Theorems.Thm_CosmicHorrorGeometry_hasDerivAt_arcsinChord
import Theorems.Thm_CosmicHorrorGeometry_intervalIntegrable_invSqrtChord
import Theorems.Thm_CosmicHorrorGeometry_slicedArea_eq

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
theorem solution{κ a b t : ℝ} (ht : 0 < t) (htb : a + t < b - t) :
    truncatedIdealTriangleArea κ a b t
      = (arcsinChord a b (b - t) - arcsinChord a b (a + t)) / κ := by
  have hab : a < b := by linarith
  have hsub : Ioo (a + t) (b - t) ⊆ Ioo a b := by
    intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  rw [truncatedIdealTriangleArea,
    slicedArea_eq htb _ (fun x hx => chordHeight_pos (hsub hx))]
  congr 1
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => ?_)
    ((intervalIntegrable_invSqrtChord a b).mono_set ?_)
  · refine hasDerivAt_arcsinChord ?_
    rw [Set.uIcc_of_le htb.le] at hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  · rw [Set.uIcc_of_le htb.le, Set.uIcc_of_le hab.le]
    intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
