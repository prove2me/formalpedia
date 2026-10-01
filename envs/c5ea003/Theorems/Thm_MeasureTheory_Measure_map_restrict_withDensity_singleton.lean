-- Prove2me | Theorems.Thm_MeasureTheory_Measure_map_restrict_withDensity_singleton
-- name    : MeasureTheory.Measure.map_restrict_withDensity_singleton
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-30T15:40:56.276556+00:00
-- url     : https://prove2.me/theorems/d30bb26a-07dc-4b14-94ee-ff9995e452db
-- title:
--   Weighted restriction pushes singletons to zero
-- statement:
--   An injective image of a weighted restriction preserves null singleton masses. Drift repair: NoAtoms for NullSingletonClass.
-- source:
--   https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofa/ForMathlib/MeasureTheory/Measure/WithDensity.lean#L10-L13

import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Map
open Set
open scoped ENNReal

namespace MeasureTheory.Measure

theorem map_restrict_withDensity_singleton {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : Measure α) [NoAtoms μ] (f : α → β) (hf : Measurable f)
    (s : Set α) (hinj : Set.InjOn f s) (w : α → ℝ≥0∞) {x : α} (hx : x ∈ s) :
    Measure.map f ((μ.restrict s).withDensity w) {f x} = 0 := by sorry

end MeasureTheory.Measure
