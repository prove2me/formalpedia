-- Prove2me | Theorems.Thm_dirac_step_measure_eq_dirac
-- name    : dirac_step_measure_eq_dirac
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T19:58:28.082127+00:00
-- url     : https://prove2.me/theorems/2489a72f-3202-4c3a-a112-e3e3ed623e20
-- title:
--   Chapter 3, ex_3_3_4: dirac_step_measure_eq_dirac
-- statement:
--   Source theorem `dirac_step_measure_eq_dirac` from Chapter 3, module `ex_3_3_4`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_03/ex_3_3_4.lean

import Definitions.Def_ProbabilityTheory_chapter_03_ex_3_3_4_F000
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Tactic

open MeasureTheory Set Function Filter

theorem dirac_step_measure_eq_dirac (x₀ : ℝ) :
    (dirac_step_function x₀).measure = Measure.dirac x₀ := by sorry
