-- Prove2me | Theorems.Thm_occupation_bind_sections_integrable_local
-- name    : occupation_bind_sections_integrable_local
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T13:49:14.916513+00:00
-- url     : https://prove2.me/theorems/b1d59eba-4373-4046-8d79-4f717dd511ca
-- title:
--   occupation_bind_sections_integrable_local
-- statement:
--   Automatically extracted helper theorem occupation_bind_sections_integrable_local from oversized parent candidate 993793ecac1327d59c382290f371b052c55f3c6b64ae38b51ef3499372ee91de.
-- source:
--   candidate-decomposition:10ef35ab-e13b-45f3-9ed8-046c77d64038:993793ecac1327d59c382290f371b052c55f3c6b64ae38b51ef3499372ee91de

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology

noncomputable section
theorem occupation_bind_sections_integrable_local
    {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (P : Measure Ω) (K : Ω → Measure β) (hK : AEMeasurable K P)
    (H : β → ℝ) (hHm : Measurable H) (hHi : Integrable H (P.bind K)) :
    ∀ᵐ ω ∂P, Integrable H (K ω) := by sorry
end
