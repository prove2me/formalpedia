-- Prove2me | solution 1 for CosmicHorrorGeometry.angles_tendsto_zero_of_area_tendsto_max
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:52:46.03876+00:00
-- url     : https://prove2.me/submissions/b5e662d9-d2e5-4979-bf0f-b08e600f27ce

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
theorem solution{κ : ℝ} (hκ : 0 < κ)
    (α β γ : ℕ → ℝ) (hadm : ∀ n, AdmissibleAngles (α n) (β n) (γ n))
    (hA : Tendsto (fun n => hyperbolicArea κ (α n) (β n) (γ n)) atTop (𝓝 (Real.pi / κ))) :
    Tendsto α atTop (𝓝 0) ∧ Tendsto β atTop (𝓝 0) ∧ Tendsto γ atTop (𝓝 0) := by
  have hsum : Tendsto (fun n => α n + β n + γ n) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => Real.pi - κ * hyperbolicArea κ (α n) (β n) (γ n))
        atTop (𝓝 (Real.pi - κ * (Real.pi / κ))) :=
      (tendsto_const_nhds.sub (hA.const_mul κ))
    have h2 : Real.pi - κ * (Real.pi / κ) = 0 := by
      field_simp
      ring
    rw [h2] at h1
    refine h1.congr (fun n => ?_)
    simp only [hyperbolicArea]
    field_simp
    ring
  refine ⟨?_, ?_, ?_⟩
  · refine squeeze_zero (fun n => (hadm n).1) (fun n => ?_) hsum
    have := hadm n
    linarith [this.2.1, this.2.2.1]
  · refine squeeze_zero (fun n => (hadm n).2.1) (fun n => ?_) hsum
    have := hadm n
    linarith [this.1, this.2.2.1]
  · refine squeeze_zero (fun n => (hadm n).2.2.1) (fun n => ?_) hsum
    have := hadm n
    linarith [this.1, this.2.1]
