-- Prove2me | Theorems.Thm_thm_2_7_closedApprox_mem_generateFrom_strictClosed
-- name    : thm_2_7_closedApprox_mem_generateFrom_strictClosed
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:12:53.245202+00:00
-- url     : https://prove2.me/theorems/1513192c-9c68-4d38-8115-6f74d4c9384b
-- title:
--   ProbabilityTheory_chapter_02_thm_2_7_F000: thm_2_7_closedApprox_mem_generateFrom_strictClosed
-- statement:
--   Source theorem `thm_2_7_closedApprox_mem_generateFrom_strictClosed` extracted from `ProbabilityTheory.chapter_02.thm_2_7`. The formal Lean declaration specifies the proposition.
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

theorem thm_2_7_closedApprox_mem_generateFrom_strictClosed
    (a b : ℝ) (n : ℕ) :
    @MeasurableSet ℝ (MeasurableSpace.generateFrom realStrictClosedIntervals)
      (thm_2_7_closedApprox a b n) := by
  sorry
