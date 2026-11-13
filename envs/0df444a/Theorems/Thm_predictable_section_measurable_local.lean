-- Prove2me | Theorems.Thm_predictable_section_measurable_local
-- name    : predictable_section_measurable_local
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T13:49:19.888501+00:00
-- url     : https://prove2.me/theorems/26d40915-3275-47f1-b9d9-b01aaf8b630c
-- title:
--   predictable_section_measurable_local
-- statement:
--   Automatically extracted helper theorem predictable_section_measurable_local from oversized parent candidate 993793ecac1327d59c382290f371b052c55f3c6b64ae38b51ef3499372ee91de.
-- source:
--   candidate-decomposition:10ef35ab-e13b-45f3-9ed8-046c77d64038:993793ecac1327d59c382290f371b052c55f3c6b64ae38b51ef3499372ee91de

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology

noncomputable section
theorem predictable_section_measurable_local
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (𝓕 : Filtration ℝ≥0 mΩ) (ω : Ω) :
    @Measurable ℝ≥0 (ℝ≥0 × Ω) inferInstance 𝓕.predictable (fun t => (t, ω)) := by sorry
end
