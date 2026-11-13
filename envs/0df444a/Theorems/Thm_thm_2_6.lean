-- Prove2me | Theorems.Thm_thm_2_6
-- name    : thm_2_6
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T18:42:49.779304+00:00
-- url     : https://prove2.me/theorems/3186e1c8-9a35-46d1-a4f8-fffcf1c57a67
-- title:
--   Chapter 2, thm_2_6: thm_2_6
-- statement:
--   Source theorem `thm_2_6` from Chapter 2, module `thm_2_6`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_02/thm_2_6.lean

import Definitions.Def_ProbabilityTheory_chapter_02_thm_2_6_F000
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic

open Set MeasureTheory

theorem thm_2_6 {Ω : Type*} (C : Set (Set Ω)) :
    (∀ s ∈ C, @MeasurableSet Ω (MeasurableSpace.generateFrom C) s) ∧
      ∀ F : MeasurableSpace Ω, (∀ s ∈ C, @MeasurableSet Ω F s) →
        ∀ s, @MeasurableSet Ω (MeasurableSpace.generateFrom C) s → @MeasurableSet Ω F s := by sorry
