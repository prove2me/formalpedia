-- Prove2me | solution 1 for CosmicHorrorGeometry.integral_invSqrtChord_subinterval
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:03:08.339726+00:00
-- url     : https://prove2.me/submissions/7410e9ce-6fec-42d5-bb54-c20eb2f53781

-- Sol generated from Geometry/CosmicHorror/HyperbolicIdealArea.lean
import Mathlib
import Definitions.Def_Geometry_CosmicHorror_HyperbolicIdealArea
import Definitions.Def_Geometry_CosmicHorror_IdealTriangle
import Theorems.Thm_CosmicHorrorGeometry_hasDerivAt_arcsinChord
import Theorems.Thm_CosmicHorrorGeometry_intervalIntegrable_invSqrtChord

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





lemma continuous_arcsinChord (a b : ℝ) : Continuous (arcsinChord a b) :=
  Real.continuous_arcsin.comp (by fun_prop)






/-! ### The vertical fibre of the hyperbolic area element -/


/-! ### The hyperbolic area of a vertically sliced region -/



/-! ### The ideal triangle -/







/-! ### Ideal polygons -/




/-! ### Degeneration: exhausting the ideal triangle by truncated regions -/





/-! ### The angle side of the degeneration -/



open CosmicHorrorGeometry in
theorem solution{a b u v : ℝ} (hab : a < b) (hau : a ≤ u)
    (huv : u < v) (hvb : v ≤ b) :
    ∫ x in u..v, (chordHeight a b x)⁻¹ = arcsinChord a b v - arcsinChord a b u := by
  have hderiv : ∀ x ∈ Ioo u v, HasDerivAt (arcsinChord a b) (chordHeight a b x)⁻¹ x :=
    fun x hx => hasDerivAt_arcsinChord ⟨lt_of_le_of_lt hau hx.1, lt_of_lt_of_le hx.2 hvb⟩
  have hint : IntervalIntegrable (fun x => (chordHeight a b x)⁻¹) volume u v := by
    refine (intervalIntegrable_invSqrtChord a b).mono_set ?_
    rw [Set.uIcc_of_le huv.le, Set.uIcc_of_le hab.le]
    exact fun x hx => ⟨le_trans hau hx.1, le_trans hx.2 hvb⟩
  have hu : Tendsto (arcsinChord a b) (𝓝[>] u) (𝓝 (arcsinChord a b u)) :=
    ((continuous_arcsinChord a b).tendsto u).mono_left nhdsWithin_le_nhds
  have hv : Tendsto (arcsinChord a b) (𝓝[<] v) (𝓝 (arcsinChord a b v)) :=
    ((continuous_arcsinChord a b).tendsto v).mono_left nhdsWithin_le_nhds
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto huv hderiv hint hu hv
