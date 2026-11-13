-- Prove2me | Theorems.Thm_dirac_step_function_tendsto_atBot
-- name    : dirac_step_function_tendsto_atBot
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T19:57:54.206167+00:00
-- url     : https://prove2.me/theorems/17c5b69d-5941-465c-b99b-d3c6d332b303
-- title:
--   03_ex_3_3_4: dirac_step_function_tendsto_atBot
-- statement:
--   Original source theorem `dirac_step_function_tendsto_atBot` in the chapter module. The formal Lean declaration below is the authoritative proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_03/ex_3_3_4.lean

import Definitions.Def_ProbabilityTheory_chapter_03_ex_3_3_4_F000
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Tactic
open MeasureTheory Set Function Filter

theorem dirac_step_function_tendsto_atBot (x₀ : ℝ) :
    Tendsto (dirac_step_function x₀) atBot (nhds 0) := by
  sorry
