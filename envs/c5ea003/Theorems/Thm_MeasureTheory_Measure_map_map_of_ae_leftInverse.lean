-- Prove2me | Theorems.Thm_MeasureTheory_Measure_map_map_of_ae_leftInverse
-- name    : MeasureTheory.Measure.map_map_of_ae_leftInverse
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-29T23:03:44.848891+00:00
-- url     : https://prove2.me/theorems/9445a526-dc2d-4c59-b680-4c8dff443032
-- title:
--   Pushforward twice along an a.e. retraction
-- statement:
--   Let $f,g$ be measurable with $g\circ f=\mathrm{id}$ $\mu$-a.e. Then $$(\mu.\mathrm{map}\,f).\mathrm{map}\,g=\mu.$$ Follows from `map_map`, `map_congr`, `map_id`.
-- source:
--   https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofa/ForMathlib/MeasureTheory/Measure/Map.lean#L10-L13

import Mathlib.MeasureTheory.Measure.Map
open MeasureTheory MeasureTheory.Measure

namespace MeasureTheory.Measure

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}

theorem map_map_of_ae_leftInverse {f : α → β} (hf : Measurable f) {g : β → α} (hg : Measurable g) (h : ∀ᵐ a ∂μ, g (f a) = a) : (μ.map f).map g = μ := by sorry

end MeasureTheory.Measure
