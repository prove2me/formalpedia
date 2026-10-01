-- Prove2me | solution 1 for MeasureTheory.Measure.map_restrict_withDensity_singleton
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-30T15:41:13.273558+00:00
-- url     : https://prove2.me/submissions/dd53196f-a500-409d-96a1-7ef08bae68a2

import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Map

set_option autoImplicit false

open Set
open scoped ENNReal
open MeasureTheory MeasureTheory.Measure

theorem solution {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : Measure α) [NoAtoms μ] (f : α → β) (hf : Measurable f)
    (s : Set α) (hinj : Set.InjOn f s) (w : α → ℝ≥0∞) {x : α} (hx : x ∈ s) :
    Measure.map f ((μ.restrict s).withDensity w) {f x} = 0 := by
  rw [Measure.map_apply hf (measurableSet_singleton _)]
  apply withDensity_absolutelyContinuous
  rw [Measure.restrict_apply (hf (measurableSet_singleton _))]
  have heq : f ⁻¹' {f x} ∩ s = {x} := by
    ext y
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff]
    exact ⟨fun h ↦ hinj h.2 hx h.1, fun h ↦ by subst y; exact ⟨rfl, hx⟩⟩
  rw [heq, measure_singleton]
