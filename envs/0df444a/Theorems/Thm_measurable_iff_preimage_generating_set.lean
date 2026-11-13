-- Prove2me | Theorems.Thm_measurable_iff_preimage_generating_set
-- name    : measurable_iff_preimage_generating_set
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T18:41:50.06154+00:00
-- url     : https://prove2.me/theorems/90863ce5-f03d-4f15-af01-e33d1e5050af
-- title:
--   Chapter 4, thm_4_4: measurable_iff_preimage_generating_set
-- statement:
--   Source theorem `measurable_iff_preimage_generating_set` from Chapter 4, module `thm_4_4`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_04/thm_4_4.lean

import Mathlib.MeasureTheory.MeasurableSpace.Basic

section Theorem_4_4

open MeasureTheory Set

universe u v

variable {Ω : Type u} {Ω' : Type v}

theorem measurable_iff_preimage_generating_set
    [mF : MeasurableSpace Ω]
    {C : Set (Set Ω')}
    (f : Ω → Ω') :
    @Measurable Ω Ω' mF (MeasurableSpace.generateFrom C) f ↔
    ∀ A ∈ C, MeasurableSet (f ⁻¹' A) := by sorry

end Theorem_4_4
