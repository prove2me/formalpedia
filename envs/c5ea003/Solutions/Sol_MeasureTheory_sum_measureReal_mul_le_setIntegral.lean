-- Prove2me | solution 1 for MeasureTheory.sum_measureReal_mul_le_setIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-30T14:07:23.500884+00:00
-- url     : https://prove2.me/submissions/842bcdac-de34-49bb-92a2-5a8e589c71be

import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false

open MeasureTheory

theorem solution {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] (μ : MeasureTheory.Measure α) (D : Finset α)
    {E : Set α} {f : α → ℝ} (hE : MeasurableSet E)
    (hDE : (D : Set α) ⊆ E) (hf : MeasureTheory.IntegrableOn f E μ)
    (hnonneg : ∀ x ∈ E, 0 ≤ f x) :
    ∑ x ∈ D, (μ {x}).toReal * f x ≤ ∫ x in E, f x ∂μ := by
  have hfinite := MeasureTheory.setIntegral_finset D (hf.mono_set hDE)
  simp only [smul_eq_mul, MeasureTheory.measureReal_def] at hfinite
  rw [← hfinite]
  apply MeasureTheory.setIntegral_mono_set hf
  · exact (MeasureTheory.ae_restrict_iff' hE).mpr (Filter.Eventually.of_forall hnonneg)
  · exact Filter.Eventually.of_forall hDE
