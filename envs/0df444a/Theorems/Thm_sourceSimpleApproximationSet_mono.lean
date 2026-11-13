-- Prove2me | Theorems.Thm_sourceSimpleApproximationSet_mono
-- name    : sourceSimpleApproximationSet_mono
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:00:36.915432+00:00
-- url     : https://prove2.me/theorems/957f7d46-fe62-47e5-8cea-b6b1f2ce0cb7
-- title:
--   ProbabilityTheory_chapter_06_thm_6_3_F000: sourceSimpleApproximationSet_mono
-- statement:
--   Source theorem `sourceSimpleApproximationSet_mono` extracted from `ProbabilityTheory.chapter_06.thm_6_3`. The formal Lean declaration specifies the proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_06/thm_6_3.lean

import Definitions.Def_ProbabilityTheory_chapter_06_thm_6_3_F000
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
open MeasureTheory
open scoped ENNReal
variable {Ω : Type*} [MeasurableSpace Ω]

theorem sourceSimpleApproximationSet_mono {X Y : Ω → ENNReal} (hXY : X ≤ Y) :
    sourceSimpleApproximationSet X ⊆ sourceSimpleApproximationSet Y := by
  sorry
