-- Prove2me | Theorems.Thm_leftClosedInfinite_mem_borelAlgebraReal
-- name    : leftClosedInfinite_mem_borelAlgebraReal
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:09:52.46105+00:00
-- url     : https://prove2.me/theorems/747b01f8-e105-4f59-af33-70a9560b2cdf
-- title:
--   ProbabilityTheory_chapter_02_def_2_8_F001: leftClosedInfinite_mem_borelAlgebraReal
-- statement:
--   Source theorem `leftClosedInfinite_mem_borelAlgebraReal` extracted from `ProbabilityTheory.chapter_02.def_2_8`. The formal Lean declaration specifies the proposition.
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

theorem leftClosedInfinite_mem_borelAlgebraReal (b : ℝ) :
    @MeasurableSet ℝ borelAlgebraReal (Set.Iic b) := by
  sorry
