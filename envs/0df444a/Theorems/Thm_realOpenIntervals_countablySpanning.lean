-- Prove2me | Theorems.Thm_realOpenIntervals_countablySpanning
-- name    : realOpenIntervals_countablySpanning
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:12:13.274906+00:00
-- url     : https://prove2.me/theorems/0d136fcf-90fb-4cdc-8a69-2fe391259598
-- title:
--   Chapter 2, thm_2_8: realOpenIntervals_countablySpanning
-- statement:
--   Source theorem `realOpenIntervals_countablySpanning` from Chapter 2, module `thm_2_8`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_02/thm_2_8.lean

import Definitions.Def_ProbabilityTheory_chapter_02_def_2_8_F000
import Definitions.Def_ProbabilityTheory_chapter_02_thm_2_8_F000
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.MeasurableSpace.Pi
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic

open Set MeasureTheory MeasurableSpace

open scoped Pointwise

theorem realOpenIntervals_countablySpanning : IsCountablySpanning realOpenIntervals := by sorry
