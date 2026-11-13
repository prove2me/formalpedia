-- Prove2me | Theorems.Thm_thm_2_7_openInterval_mem_generateFrom_strictClosed
-- name    : thm_2_7_openInterval_mem_generateFrom_strictClosed
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:13:49.680634+00:00
-- url     : https://prove2.me/theorems/fd9527f6-7234-49e1-9651-da3ea84d2e87
-- title:
--   ProbabilityTheory_chapter_02_thm_2_7_F000: thm_2_7_openInterval_mem_generateFrom_strictClosed
-- statement:
--   Source theorem `thm_2_7_openInterval_mem_generateFrom_strictClosed` extracted from `ProbabilityTheory.chapter_02.thm_2_7`. The formal Lean declaration specifies the proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_02/thm_2_7.lean

import Definitions.Def_ProbabilityTheory_chapter_02_thm_2_7_F000
import Definitions.Def_ProbabilityTheory_chapter_02_def_2_8_F000
import Definitions.Def_ProbabilityTheory_chapter_02_def_2_8_F001
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic
open Set MeasureTheory

theorem thm_2_7_openInterval_mem_generateFrom_strictClosed
    {a b : ℝ} (hab : a < b) :
    @MeasurableSet ℝ (MeasurableSpace.generateFrom realStrictClosedIntervals)
      (Set.Ioo a b) := by
  sorry
