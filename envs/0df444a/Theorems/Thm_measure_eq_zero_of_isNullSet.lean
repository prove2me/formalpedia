-- Prove2me | Theorems.Thm_measure_eq_zero_of_isNullSet
-- name    : measure_eq_zero_of_isNullSet
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:01:31.549176+00:00
-- url     : https://prove2.me/theorems/6da900c5-e58f-4b87-8914-3f4daa2d4782
-- title:
--   ProbabilityTheory_chapter_03_thm_3_6_F000: measure_eq_zero_of_isNullSet
-- statement:
--   Source theorem `measure_eq_zero_of_isNullSet` extracted from `ProbabilityTheory.chapter_03.thm_3_6`. The formal Lean declaration specifies the proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_03/thm_3_6.lean

import Definitions.Def_ProbabilityTheory_chapter_03_thm_3_6_F000
import Definitions.Def_ProbabilityTheory_chapter_03_def_3_9_F000
import Mathlib.MeasureTheory.Measure.NullMeasurable
open MeasureTheory
open Set

theorem measure_eq_zero_of_isNullSet {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {N : Set Ω}
    (hN : IsNullSet μ N) : μ N = 0 := by
  sorry
