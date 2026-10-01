-- Prove2me | solution 1 for MeasureTheory.Measure.map_withDensity_eq_smul_add_smul
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-30T15:45:38.694018+00:00
-- url     : https://prove2.me/submissions/a6afe39e-5f4e-4e2d-bae2-8bc4dddf3f3f

import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Map

set_option autoImplicit false

open Set
open scoped ENNReal
open MeasureTheory MeasureTheory.Measure

theorem solution {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) {φ : α → β} (hφ : Measurable φ) (a b : ℝ≥0∞) {w w₁ w₂ : α → ℝ≥0∞}
    (h₁ : Measurable w₁) (h₂ : Measurable w₂) (hw : ∀ x, w x = a * w₁ x + b * w₂ x) :
    Measure.map φ (μ.withDensity w) =
      a • Measure.map φ (μ.withDensity w₁) + b • Measure.map φ (μ.withDensity w₂) := by
  have hwfun : w = a • w₁ + b • w₂ := funext hw
  rw [hwfun, withDensity_add_left (h₁.const_smul a), withDensity_smul _ h₁,
    withDensity_smul _ h₂, Measure.map_add _ _ hφ, Measure.map_smul _ _ _,
    Measure.map_smul _ _ _]
