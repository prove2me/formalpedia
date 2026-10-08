-- Prove2me | solution 2 for MeasurableEmbedding.exists_vectorMeasure_image_integral
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-10-06T20:07:44.10199+00:00
-- url     : https://prove2.me/submissions/255bf41d-d8a1-48a4-ae14-c422b5b59126

import Mathlib.MeasureTheory.VectorMeasure.WithDensity
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
open Set MeasureTheory

theorem solution
    {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : α → β} (hf : MeasurableEmbedding f) (μ : Measure β) (g : β → E)
    (hg : Integrable g μ) :
    ∃ ν : VectorMeasure α E, ∀ s, MeasurableSet s → ν s = ∫ x in f '' s, g x ∂μ := by
  have hint : Integrable (g ∘ f) (μ.comap f) := by
    rw [← hf.integrable_map_iff, hf.map_comap]
    exact hg.restrict
  refine ⟨(μ.comap f).withDensityᵥ (g ∘ f), fun s hs => ?_⟩
  rw [withDensityᵥ_apply hint hs]
  have h1 := hf.setIntegral_map (μ := μ.comap f) g (f '' s)
  rw [hf.injective.preimage_image, hf.map_comap,
    Measure.restrict_restrict (hf.measurableSet_image' hs),
    inter_eq_left.mpr (image_subset_range f s)] at h1
  exact h1.symm
