-- Prove2me | solution 1 for CosmicHorrorGeometry.hasDerivAt_arcsinChord
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:55:43.626192+00:00
-- url     : https://prove2.me/submissions/128db2b0-afa1-4357-bb52-6ab0db58a599

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
theorem solution{a b x : ℝ} (hx : x ∈ Ioo a b) :
    HasDerivAt (arcsinChord a b) (chordHeight a b x)⁻¹ x := by
  obtain ⟨hxa, hxb⟩ := hx
  have hba : 0 < b - a := by linarith
  set u : ℝ := (2 * x - a - b) / (b - a) with hu
  have hu1 : u ≠ 1 := by
    intro h
    rw [hu, div_eq_one_iff_eq hba.ne'] at h
    linarith
  have hu2 : u ≠ -1 := by
    intro h
    rw [hu, div_eq_iff hba.ne'] at h
    linarith
  have hinner : HasDerivAt (fun t : ℝ => (2 * t - a - b) / (b - a)) (2 / (b - a)) x := by
    have h2 : HasDerivAt (fun t : ℝ => 2 * t - a - b) 2 x := by
      simpa using ((hasDerivAt_id x).const_mul (2 : ℝ)).sub_const a |>.sub_const b
    simpa [div_eq_mul_inv] using h2.div_const (b - a)
  have hcomp := (Real.hasDerivAt_arcsin hu2 hu1).comp x hinner
  convert hcomp using 1
  have hq : 1 - u ^ 2 = 4 * ((x - a) * (b - x)) / (b - a) ^ 2 := by
    rw [hu]; field_simp; ring
  have hpos : 0 < (x - a) * (b - x) := by nlinarith
  have hs : Real.sqrt (1 - u ^ 2) = 2 * Real.sqrt ((x - a) * (b - x)) / (b - a) := by
    rw [hq, show (4 : ℝ) * ((x - a) * (b - x)) / (b - a) ^ 2
        = (2 * Real.sqrt ((x - a) * (b - x)) / (b - a)) ^ 2 by
      rw [div_pow, mul_pow, Real.sq_sqrt hpos.le]; ring]
    exact Real.sqrt_sq (by positivity)
  have hsp : 0 < Real.sqrt ((x - a) * (b - x)) := Real.sqrt_pos.2 hpos
  simp only [chordHeight, hs]
  field_simp
