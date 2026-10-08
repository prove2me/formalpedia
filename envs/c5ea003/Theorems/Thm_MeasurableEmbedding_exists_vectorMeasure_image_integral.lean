-- Prove2me | Theorems.Thm_MeasurableEmbedding_exists_vectorMeasure_image_integral
-- name    : MeasurableEmbedding.exists_vectorMeasure_image_integral
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-10-03T20:02:33.460799+00:00
-- url     : https://prove2.me/theorems/809f00a1-dc17-4689-a89b-e0c02365b1eb
-- title:
--   Image integrals from pulled-back densities
-- statement:
--   Pulling an integrable density back along a measurable embedding gives its image integrals via the comap withDensity measure.
-- source:
--   MovingSofa/ForMathlib/MeasureTheory/VectorMeasure/Interval.lean (second theorem)

import Mathlib.MeasureTheory.VectorMeasure.WithDensity
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
open Set MeasureTheory

namespace MeasurableEmbedding

theorem exists_vectorMeasure_image_integral
    {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : α → β} (hf : MeasurableEmbedding f) (μ : Measure β) (g : β → E)
    (hg : Integrable g μ) :
    ∃ ν : VectorMeasure α E, ∀ s, MeasurableSet s → ν s = ∫ x in f '' s, g x ∂μ := by sorry

end MeasurableEmbedding
