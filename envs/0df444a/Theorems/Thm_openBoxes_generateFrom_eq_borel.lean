-- Prove2me | Theorems.Thm_openBoxes_generateFrom_eq_borel
-- name    : openBoxes_generateFrom_eq_borel
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:15:26.383123+00:00
-- url     : https://prove2.me/theorems/8c3a4643-8846-4c0c-8276-9738302b844e
-- title:
--   Chapter 2, thm_2_8: openBoxes_generateFrom_eq_borel
-- statement:
--   Source theorem `openBoxes_generateFrom_eq_borel` from Chapter 2, module `thm_2_8`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_02/thm_2_8.lean

import Definitions.Def_ProbabilityTheory_chapter_02_thm_2_8_F000
import Definitions.Def_ProbabilityTheory_chapter_02_thm_2_8_F001
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.MeasurableSpace.Pi
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic

open Set MeasureTheory MeasurableSpace

open scoped Pointwise

theorem openBoxes_generateFrom_eq_borel (d : ℕ) :
    MeasurableSpace.generateFrom (openBoxes d) = borel (Fin d → ℝ) := by sorry
