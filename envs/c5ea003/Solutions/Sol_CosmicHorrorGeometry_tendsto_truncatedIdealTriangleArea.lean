-- Prove2me | solution 1 for CosmicHorrorGeometry.tendsto_truncatedIdealTriangleArea
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:17:37.670211+00:00
-- url     : https://prove2.me/submissions/21596d81-3821-4e41-bf15-2b2c61f87f57

-- Sol generated from Geometry/CosmicHorror/HyperbolicIdealArea.lean
import Mathlib
import Definitions.Def_Geometry_CosmicHorror_HyperbolicIdealArea
import Definitions.Def_Geometry_CosmicHorror_IdealTriangle
import Theorems.Thm_CosmicHorrorGeometry_truncatedIdealTriangleArea_eq

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
theorem solution{κ a b : ℝ} (hab : a < b) :
    Tendsto (fun t => truncatedIdealTriangleArea κ a b t) (𝓝[>] 0) (𝓝 (Real.pi / κ)) := by
  have hba : 0 < b - a := by linarith
  have key : Tendsto (fun t : ℝ =>
      (arcsinChord a b (b - t) - arcsinChord a b (a + t)) / κ) (𝓝 0)
      (𝓝 (Real.pi / κ)) := by
    have hc : Continuous (fun t : ℝ =>
        (arcsinChord a b (b - t) - arcsinChord a b (a + t)) / κ) := by
      exact (((continuous_arcsinChord a b).comp (by fun_prop)).sub
        ((continuous_arcsinChord a b).comp (by fun_prop))).div_const κ
    have hval : (arcsinChord a b b - arcsinChord a b a) / κ = Real.pi / κ := by
      have h1 : arcsinChord a b b = π / 2 := by
        simp only [arcsinChord]
        rw [show (2 * b - a - b) / (b - a) = 1 by rw [div_eq_one_iff_eq hba.ne']; ring]
        simp
      have h2 : arcsinChord a b a = -(π / 2) := by
        simp only [arcsinChord]
        rw [show (2 * a - a - b) / (b - a) = -1 by rw [div_eq_iff hba.ne']; ring]
        simp
      rw [h1, h2]; ring_nf
    have h := hc.tendsto 0
    simp only [sub_zero, add_zero] at h
    rwa [hval] at h
  refine Tendsto.congr' ?_ (key.mono_left nhdsWithin_le_nhds)
  have hev : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t ∧ a + t < b - t := by
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT (show (0:ℝ) < (b - a)/2 by linarith)]
      with t ht ht2
    exact ⟨ht, by simp only [Set.mem_Ioo] at ht2; linarith [ht2.2]⟩
  filter_upwards [hev] with t ht
  exact (truncatedIdealTriangleArea_eq ht.1 ht.2).symm
