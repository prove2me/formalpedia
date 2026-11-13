-- Prove2me | Theorems.Thm_mem_completionCollection_iff_nullMeasurableSet
-- name    : mem_completionCollection_iff_nullMeasurableSet
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:02:18.539208+00:00
-- url     : https://prove2.me/theorems/7970bdd3-337b-46ce-b2cd-9b8094c1346c
-- title:
--   ProbabilityTheory_chapter_03_thm_3_6_F000: mem_completionCollection_iff_nullMeasurableSet
-- statement:
--   Source theorem `mem_completionCollection_iff_nullMeasurableSet` extracted from `ProbabilityTheory.chapter_03.thm_3_6`. The formal Lean declaration specifies the proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_03/thm_3_6.lean

import Definitions.Def_ProbabilityTheory_chapter_03_thm_3_6_F000
import Definitions.Def_ProbabilityTheory_chapter_03_def_3_9_F000
import Mathlib.MeasureTheory.Measure.NullMeasurable
open MeasureTheory
open Set

theorem mem_completionCollection_iff_nullMeasurableSet {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (s : Set Ω) :
    s ∈ completionCollection μ ↔ NullMeasurableSet s μ := by
  sorry
