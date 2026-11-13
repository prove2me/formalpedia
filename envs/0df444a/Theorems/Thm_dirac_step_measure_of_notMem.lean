-- Prove2me | Theorems.Thm_dirac_step_measure_of_notMem
-- name    : dirac_step_measure_of_notMem
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T19:59:33.440218+00:00
-- url     : https://prove2.me/theorems/a63f6fba-dc65-4292-a625-b96de7e9aa00
-- title:
--   03_ex_3_3_4: dirac_step_measure_of_notMem
-- statement:
--   Original source theorem `dirac_step_measure_of_notMem` in the chapter module. The formal Lean declaration below is the authoritative proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_03/ex_3_3_4.lean

import Definitions.Def_ProbabilityTheory_chapter_03_ex_3_3_4_F000
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Tactic
open MeasureTheory Set Function Filter

theorem dirac_step_measure_of_notMem (x₀ : ℝ) (A : Set ℝ) (hx : x₀ ∉ A) :
    (dirac_step_function x₀).measure A = 0 := by
  sorry
