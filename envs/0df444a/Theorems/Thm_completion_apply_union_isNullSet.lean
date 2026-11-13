-- Prove2me | Theorems.Thm_completion_apply_union_isNullSet
-- name    : completion_apply_union_isNullSet
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:02:32.469182+00:00
-- url     : https://prove2.me/theorems/41752336-86e1-4a9e-9043-0150b20718b2
-- title:
--   ProbabilityTheory_chapter_03_thm_3_6_F000: completion_apply_union_isNullSet
-- statement:
--   Source theorem `completion_apply_union_isNullSet` extracted from `ProbabilityTheory.chapter_03.thm_3_6`. The formal Lean declaration specifies the proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_03/thm_3_6.lean

import Definitions.Def_ProbabilityTheory_chapter_03_thm_3_6_F000
import Definitions.Def_ProbabilityTheory_chapter_03_def_3_9_F000
import Mathlib.MeasureTheory.Measure.NullMeasurable
open MeasureTheory
open Set

theorem completion_apply_union_isNullSet {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {A N : Set Ω} (_hA : MeasurableSet A) (hN : IsNullSet μ N) :
    completionMeasure μ (A ∪ N) = μ A := by
  sorry
