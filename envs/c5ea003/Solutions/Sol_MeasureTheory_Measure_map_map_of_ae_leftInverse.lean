-- Prove2me | solution 1 for MeasureTheory.Measure.map_map_of_ae_leftInverse
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-29T23:03:53.823385+00:00
-- url     : https://prove2.me/submissions/c69a2006-796e-489a-8293-9016b6acd7c4

import Mathlib.MeasureTheory.Measure.Map

set_option autoImplicit false

open MeasureTheory MeasureTheory.Measure

theorem solution {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
    {f : α → β} (hf : Measurable f) {g : β → α}
    (hg : Measurable g) (h : ∀ᵐ a ∂μ, g (f a) = a) :
    (μ.map f).map g = μ := by
  rw [map_map hg hf, show μ.map (g ∘ f) = μ.map id from map_congr h, map_id]
