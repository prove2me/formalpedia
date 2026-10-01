-- Prove2me | Theorems.Thm_MeasureTheory_sum_measureReal_mul_le_setIntegral
-- name    : MeasureTheory.sum_measureReal_mul_le_setIntegral
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-30T14:06:28.070203+00:00
-- url     : https://prove2.me/theorems/214bbd5d-8e3e-48f4-8db1-a5e78c27547a
-- title:
--   Atomic sum bounded by the integral
-- statement:
--   A finite atomic sum over $D\subseteq E$ of a nonnegative integrable $f$ is bounded by its set integral over $E$.
-- source:
--   https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofa/ForMathlib/MeasureTheory/Integral/AtomicBounds.lean#L9-L14

import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Set
open MeasureTheory

namespace MeasureTheory

theorem sum_measureReal_mul_le_setIntegral {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] (μ : MeasureTheory.Measure α) (D : Finset α) {E : Set α} {f : α → ℝ} (hE : MeasurableSet E) (hDE : (D : Set α) ⊆ E) (hf : MeasureTheory.IntegrableOn f E μ) (hnonneg : ∀ x ∈ E, 0 ≤ f x) : ∑ x ∈ D, (μ {x}).toReal * f x ≤ ∫ x in E, f x ∂μ := by sorry

end MeasureTheory
