-- Prove2me | Theorems.Thm_dirac_step_function_apply
-- name    : dirac_step_function_apply
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T18:40:49.169199+00:00
-- url     : https://prove2.me/theorems/dbf5842f-97b2-43d2-aee2-c5b321ab56b6
-- title:
--   Chapter 3, ex_3_3_4: dirac_step_function_apply
-- statement:
--   Source theorem `dirac_step_function_apply` from Chapter 3, module `ex_3_3_4`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_03/ex_3_3_4.lean

import Definitions.Def_ProbabilityTheory_chapter_03_ex_3_3_4_F000
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Tactic

open MeasureTheory Set Function Filter

theorem dirac_step_function_apply (x₀ x : ℝ) :
    dirac_step_function x₀ x = if x < x₀ then 0 else 1 := by sorry
