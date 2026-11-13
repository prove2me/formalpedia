-- Prove2me | Theorems.Thm_thm_2_3
-- name    : thm_2_3
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T19:55:27.287174+00:00
-- url     : https://prove2.me/theorems/8d640160-35da-4b12-a68d-3bdfba61f697
-- title:
--   Chapter 2, thm_2_3: thm_2_3
-- statement:
--   Source theorem `thm_2_3` from Chapter 2, module `thm_2_3`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_02/thm_2_3.lean

import Definitions.Def_ProbabilityTheory_chapter_02_def_2_5_F000
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic

open MeasureTheory Set

theorem thm_2_3 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {A B : Set Ω}
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    μ (A ∪ B) ≤ μ A + μ B := by sorry
