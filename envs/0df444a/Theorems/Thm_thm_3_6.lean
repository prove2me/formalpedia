-- Prove2me | Theorems.Thm_thm_3_6
-- name    : thm_3_6
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:02:41.958191+00:00
-- url     : https://prove2.me/theorems/63d1c285-3040-4557-a05a-ca28941e2aac
-- title:
--   ProbabilityTheory_chapter_03_thm_3_6_F000: thm_3_6
-- statement:
--   Source theorem `thm_3_6` extracted from `ProbabilityTheory.chapter_03.thm_3_6`. The formal Lean declaration specifies the proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_03/thm_3_6.lean

import Definitions.Def_ProbabilityTheory_chapter_03_thm_3_6_F000
import Definitions.Def_ProbabilityTheory_chapter_03_def_3_9_F000
import Mathlib.MeasureTheory.Measure.NullMeasurable
open MeasureTheory
open Set

theorem thm_3_6 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) :
    (∀ s, s ∈ completionCollection μ ↔ NullMeasurableSet s μ) ∧
      (∀ A N, @MeasurableSet Ω ‹MeasurableSpace Ω› A →
        IsNullSet μ N → completionMeasure μ (A ∪ N) = μ A) ∧
      Measure.IsComplete (completionMeasure μ) := by
  sorry
