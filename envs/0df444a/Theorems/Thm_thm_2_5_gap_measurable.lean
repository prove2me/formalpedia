-- Prove2me | Theorems.Thm_thm_2_5_gap_measurable
-- name    : thm_2_5_gap_measurable
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T23:52:57.062539+00:00
-- url     : https://prove2.me/theorems/9701a7e6-d230-436c-98d1-ff033b54cd17
-- title:
--   Source theorem: thm_2_5_gap_measurable
-- statement:
--   Source theorem extracted from ProbabilityTheory.chapter_02.thm_2_5, with its proposition and original proof recorded separately.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_02/thm_2_5.lean

import Definitions.Def_ProbabilityTheory_chapter_02_thm_2_5_F000
import Definitions.Def_ProbabilityTheory_chapter_02_def_2_6_F000
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic
open MeasureTheory Set

theorem thm_2_5_gap_measurable {Ω : Type*} [MeasurableSpace Ω]
    {A : ℕ → Set Ω} (hMeas : ∀ i, MeasurableSet (A i)) :
    ∀ i, MeasurableSet (thm_2_5_gap A i) := by
  sorry
