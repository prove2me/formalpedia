-- Prove2me | Theorems.Thm_leftOpenRightClosed_mem_borelAlgebraReal
-- name    : leftOpenRightClosed_mem_borelAlgebraReal
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:11:18.047946+00:00
-- url     : https://prove2.me/theorems/a6aea46b-370a-4127-a12a-cab8466c6521
-- title:
--   ProbabilityTheory_chapter_02_def_2_8_F001: leftOpenRightClosed_mem_borelAlgebraReal
-- statement:
--   Source theorem `leftOpenRightClosed_mem_borelAlgebraReal` extracted from `ProbabilityTheory.chapter_02.def_2_8`. The formal Lean declaration specifies the proposition.
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

theorem leftOpenRightClosed_mem_borelAlgebraReal (a b : ℝ) :
    @MeasurableSet ℝ borelAlgebraReal (Set.Ioc a b) := by
  sorry
