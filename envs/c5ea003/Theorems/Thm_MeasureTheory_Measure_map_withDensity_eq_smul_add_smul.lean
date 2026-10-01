-- Prove2me | Theorems.Thm_MeasureTheory_Measure_map_withDensity_eq_smul_add_smul
-- name    : MeasureTheory.Measure.map_withDensity_eq_smul_add_smul
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-30T15:45:32.417483+00:00
-- url     : https://prove2.me/theorems/b25c641b-cd34-4bf3-b9e5-db293bfa011f
-- title:
--   Pushforward is linear in the weight
-- statement:
--   Pushing a weighted measure forward is linear in a pointwise weight combination. Drift repair: explicit map_smul args.
-- source:
--   https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofa/ForMathlib/MeasureTheory/Measure/WithDensity.lean#L27-L31

import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Map
open Set
open scoped ENNReal

namespace MeasureTheory.Measure

theorem map_withDensity_eq_smul_add_smul {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) {φ : α → β} (hφ : Measurable φ) (a b : ℝ≥0∞) {w w₁ w₂ : α → ℝ≥0∞}
    (h₁ : Measurable w₁) (h₂ : Measurable w₂) (hw : ∀ x, w x = a * w₁ x + b * w₂ x) :
    Measure.map φ (μ.withDensity w) =
      a • Measure.map φ (μ.withDensity w₁) + b • Measure.map φ (μ.withDensity w₂) := by sorry

end MeasureTheory.Measure
