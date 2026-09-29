-- Prove2me | solution 1 for CosmicHorrorGeometry.slicedArea_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:07:55.758737+00:00
-- url     : https://prove2.me/submissions/7f982b73-d93b-4352-9b00-2de37b40dbc3

-- Sol generated from Geometry/CosmicHorror/HyperbolicIdealArea.lean
import Mathlib
import Definitions.Def_Geometry_CosmicHorror_HyperbolicIdealArea
import Definitions.Def_Geometry_CosmicHorror_IdealTriangle
import Theorems.Thm_CosmicHorrorGeometry_integral_Ioi_inv_sq

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
theorem solution{κ a b : ℝ} (hab : a < b) (low : ℝ → ℝ)
    (hlow : ∀ x ∈ Ioo a b, 0 < low x) :
    slicedArea κ a b low = (∫ x in a..b, (low x)⁻¹) / κ := by
  have hae : ∀ᵐ x : ℝ, x ∈ Set.uIoc a b → (∫ y in Ioi (low x), (κ * y ^ 2)⁻¹)
      = (low x)⁻¹ / κ := by
    have hne : ∀ᵐ x : ℝ, x ≠ b := by
      have : volume {b} = 0 := by simp
      filter_upwards [MeasureTheory.compl_mem_ae_iff.2 this] with x hx
      simpa using hx
    filter_upwards [hne] with x hx hmem
    rw [Set.uIoc_of_le hab.le] at hmem
    have hx' : x ∈ Ioo a b := ⟨hmem.1, lt_of_le_of_ne hmem.2 hx⟩
    have hpos := hlow x hx'
    have : ∀ y : ℝ, (κ * y ^ 2)⁻¹ = κ⁻¹ * (y ^ 2)⁻¹ := by
      intro y; rw [mul_inv]
    simp_rw [this]
    rw [MeasureTheory.integral_const_mul, integral_Ioi_inv_sq hpos, div_eq_inv_mul]
  rw [slicedArea, intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_div]
