-- Prove2me | Theorems.Thm_thm_5_3
-- name    : thm_5_3
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T18:43:16.309956+00:00
-- url     : https://prove2.me/theorems/794bfddd-abeb-4da9-905a-16bfe8837f8d
-- title:
--   Chapter 5, thm_5_3: thm_5_3
-- statement:
--   Source theorem `thm_5_3` from Chapter 5, module `thm_5_3`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_05/thm_5_3.lean

import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic

theorem thm_5_3 {Ω : Type _} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsZeroOrProbabilityMeasure μ]
    (X Y : Ω → ℕ) (hX : Measurable X) (hY : Measurable Y) :
    ProbabilityTheory.IndepFun X Y μ ↔
      ∀ m n : ℕ,
        μ (X ⁻¹' ({m} : Set ℕ) ∩ Y ⁻¹' ({n} : Set ℕ)) =
          μ (X ⁻¹' ({m} : Set ℕ)) * μ (Y ⁻¹' ({n} : Set ℕ)) := by sorry
