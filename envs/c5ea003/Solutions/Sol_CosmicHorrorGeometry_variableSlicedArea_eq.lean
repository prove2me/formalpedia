-- Prove2me | solution 1 for CosmicHorrorGeometry.variableSlicedArea_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:10:24.234706+00:00
-- url     : https://prove2.me/submissions/3dbf8b8c-9723-4040-9d6b-ee7570df2eda

-- Sol generated from Geometry/CosmicHorror/VariableCurvature.lean
import Mathlib
import Definitions.Def_Geometry_CosmicHorror_HyperbolicIdealArea
import Definitions.Def_Geometry_CosmicHorror_VariableCurvature
import Theorems.Thm_CosmicHorrorGeometry_integral_Ioi_inv_sq

/-!
# Comparison estimates for ideal triangles under variable curvature

The previous files work at *constant* curvature `-κ`, where the area element is
`dx dy / (κ y²)`.  Here we allow the curvature to vary — the area element
becomes `dx dy / (K(x) y²)` for a positive function `K` — and prove the
expected comparison inequalities:

`κ₁ ≤ K ≤ κ₂  ⟹  π / κ₂ ≤ area ≤ π / κ₁`.

In words: *pinching the curvature between `-κ₂` and `-κ₁` pinches the area of an
ideal triangle between `π/κ₂` and `π/κ₁`*, and more negative curvature means a
smaller ideal triangle.  At `K` constant both bounds collapse to the exact value
`π / κ` of `idealTriangleArea_eq`, so the comparison theorem is sharp.

## Main results

* `variableSlicedArea_eq`:  slicing formula in the variable-curvature setting
  (no hypothesis on `K` is needed).
* `variableSlicedArea_le_of_le` / `le_variableSlicedArea_of_le`:  the two
  comparison inequalities.
* `variableSlicedArea_pinched`:  the two-sided pinching statement.
* `variableSlicedArea_const`:  sharpness — for constant curvature the bounds are
  attained.
-/

open CosmicHorrorGeometry

open Real Set MeasureTheory Filter Topology











open CosmicHorrorGeometry in
theorem solution{a b : ℝ} (hab : a < b) (K low : ℝ → ℝ)
    (hlow : ∀ x ∈ Ioo a b, 0 < low x) :
    variableSlicedArea K low a b = ∫ x in a..b, (K x * low x)⁻¹ := by
  have hae : ∀ᵐ x : ℝ, x ∈ Set.uIoc a b →
      (∫ y in Ioi (low x), (K x * y ^ 2)⁻¹) = (K x * low x)⁻¹ := by
    have hne : ∀ᵐ x : ℝ, x ≠ b := by
      have hb : volume {b} = 0 := by simp
      filter_upwards [MeasureTheory.compl_mem_ae_iff.2 hb] with x hx
      simpa using hx
    filter_upwards [hne] with x hx hmem
    rw [Set.uIoc_of_le hab.le] at hmem
    have hpos := hlow x ⟨hmem.1, lt_of_le_of_ne hmem.2 hx⟩
    have hsplit : ∀ y : ℝ, (K x * y ^ 2)⁻¹ = (K x)⁻¹ * (y ^ 2)⁻¹ := fun y => mul_inv _ _
    simp_rw [hsplit]
    rw [MeasureTheory.integral_const_mul, integral_Ioi_inv_sq hpos, mul_inv]
  rw [variableSlicedArea, intervalIntegral.integral_congr_ae hae]
