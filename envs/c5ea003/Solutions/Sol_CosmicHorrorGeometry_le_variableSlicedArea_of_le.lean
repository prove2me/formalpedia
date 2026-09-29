-- Prove2me | solution 1 for CosmicHorrorGeometry.le_variableSlicedArea_of_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:12:31.737226+00:00
-- url     : https://prove2.me/submissions/71e28c96-fa99-4ed0-8dd9-f19ad55849b9

-- Sol generated from Geometry/CosmicHorror/VariableCurvature.lean
import Mathlib
import Definitions.Def_Geometry_CosmicHorror_HyperbolicIdealArea
import Definitions.Def_Geometry_CosmicHorror_VariableCurvature
import Theorems.Thm_CosmicHorrorGeometry_chordHeight_pos
import Theorems.Thm_CosmicHorrorGeometry_integral_invSqrtChord
import Theorems.Thm_CosmicHorrorGeometry_intervalIntegrable_invSqrtChord
import Theorems.Thm_CosmicHorrorGeometry_variableSlicedArea_eq

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



/-- Integrability of the variable-curvature density of an ideal triangle. -/
theorem intervalIntegrable_variable_density {a b : ℝ} {K : ℝ → ℝ}
    (hK : ContinuousOn K (uIcc a b)) (hKne : ∀ x ∈ uIcc a b, K x ≠ 0) :
    IntervalIntegrable (fun x => (K x)⁻¹ * (chordHeight a b x)⁻¹) volume a b :=
  (intervalIntegrable_invSqrtChord a b).continuousOn_mul (hK.inv₀ hKne)

/-- The reference integral at constant curvature. -/
theorem integral_const_curvature {a b κ : ℝ} (hab : a < b) :
    ∫ x in a..b, (κ⁻¹ * (chordHeight a b x)⁻¹) = Real.pi / κ := by
  rw [intervalIntegral.integral_const_mul, integral_invSqrtChord hab, div_eq_inv_mul]







open CosmicHorrorGeometry in
theorem solution{a b κ₂ : ℝ} {K : ℝ → ℝ} (hab : a < b) (hκ : 0 < κ₂)
    (hK : ContinuousOn K (uIcc a b)) (hpos : ∀ x ∈ uIcc a b, 0 < K x)
    (hle : ∀ x ∈ uIcc a b, K x ≤ κ₂) :
    Real.pi / κ₂ ≤ variableSlicedArea K (chordHeight a b) a b := by
  have hKne : ∀ x ∈ uIcc a b, K x ≠ 0 := fun x hx => (hpos x hx).ne'
  rw [variableSlicedArea_eq hab _ _ (fun x hx => chordHeight_pos hx)]
  have hrw : ∀ x : ℝ, (K x * chordHeight a b x)⁻¹ = (K x)⁻¹ * (chordHeight a b x)⁻¹ :=
    fun x => mul_inv _ _
  simp_rw [hrw]
  rw [← integral_const_curvature (κ := κ₂) hab]
  refine intervalIntegral.integral_mono_on hab.le
    (intervalIntegrable_variable_density continuousOn_const (fun x _ => hκ.ne'))
    (intervalIntegrable_variable_density hK hKne) ?_
  intro x hx
  have hxu : x ∈ uIcc a b := by rwa [Set.uIcc_of_le hab.le]
  have hc : 0 ≤ (chordHeight a b x)⁻¹ := by
    unfold chordHeight; positivity
  have hinv : κ₂⁻¹ ≤ (K x)⁻¹ := inv_anti₀ (hpos x hxu) (hle x hxu)
  exact mul_le_mul_of_nonneg_right hinv hc
