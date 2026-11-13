-- Prove2me | Theorems.Thm_nullMeasurableSet_of_mem_completionCollection
-- name    : nullMeasurableSet_of_mem_completionCollection
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:01:50.467929+00:00
-- url     : https://prove2.me/theorems/1a07fe63-5505-4eab-bae4-82cc20bcd625
-- title:
--   ProbabilityTheory_chapter_03_thm_3_6_F000: nullMeasurableSet_of_mem_completionCollection
-- statement:
--   Source theorem `nullMeasurableSet_of_mem_completionCollection` extracted from `ProbabilityTheory.chapter_03.thm_3_6`. The formal Lean declaration specifies the proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_03/thm_3_6.lean

import Definitions.Def_ProbabilityTheory_chapter_03_thm_3_6_F000
import Definitions.Def_ProbabilityTheory_chapter_03_def_3_9_F000
import Mathlib.MeasureTheory.Measure.NullMeasurable
open MeasureTheory
open Set

theorem nullMeasurableSet_of_mem_completionCollection {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {s : Set Ω} (hs : s ∈ completionCollection μ) :
    NullMeasurableSet s μ := by
  sorry
