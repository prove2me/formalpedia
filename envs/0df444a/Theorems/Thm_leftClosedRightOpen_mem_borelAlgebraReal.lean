-- Prove2me | Theorems.Thm_leftClosedRightOpen_mem_borelAlgebraReal
-- name    : leftClosedRightOpen_mem_borelAlgebraReal
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:11:42.966096+00:00
-- url     : https://prove2.me/theorems/427fa112-b64f-4819-a69d-64eae00514f5
-- title:
--   ProbabilityTheory_chapter_02_def_2_8_F001: leftClosedRightOpen_mem_borelAlgebraReal
-- statement:
--   Source theorem `leftClosedRightOpen_mem_borelAlgebraReal` extracted from `ProbabilityTheory.chapter_02.def_2_8`. The formal Lean declaration specifies the proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_02/def_2_8.lean

import Definitions.Def_ProbabilityTheory_chapter_02_def_2_8_F001
import Definitions.Def_ProbabilityTheory_chapter_02_def_2_8_F000
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic
open Set MeasureTheory

theorem leftClosedRightOpen_mem_borelAlgebraReal (a b : ℝ) :
    @MeasurableSet ℝ borelAlgebraReal (Set.Ico a b) := by
  sorry
