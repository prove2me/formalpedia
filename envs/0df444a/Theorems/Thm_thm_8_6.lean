-- Prove2me | Theorems.Thm_thm_8_6
-- name    : thm_8_6
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T18:44:59.00921+00:00
-- url     : https://prove2.me/theorems/2e010b28-690e-4685-8336-907fb32ea45f
-- title:
--   Chapter ?, generated supplement: thm_8_6
-- statement:
--   Source theorem `thm_8_6` from Chapter ?, module `generated supplement`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   Supplemental source module in importer v37; upstream repository https://github.com/wkshum/ProbabilityTheory/tree/e6387d4fd8005d627d2aec40d10f039ddb4e4b40

import Definitions.Def_ProbabilityTheory_chapter_08_thm_8_6_support

open MeasureTheory Set
open TVCore
noncomputable section

theorem thm_8_6 :
    (∀ (P Q : Measure ℕ) (_ : IsProbabilityMeasure P) (_ : IsProbabilityMeasure Q),
      totalVariationDistance P Q = (1 / 2 : ℝ) * ∑' n, |P.real {n} - Q.real {n}|) ∧
    (∀ (f g : ℝ → ℝ),
      Measurable f →
      Measurable g →
      Integrable f volume →
      Integrable g volume →
      (∀ x, 0 ≤ f x) →
      (∀ x, 0 ≤ g x) →
      (∫ x, f x = 1) →
      (∫ x, g x = 1) →
      totalVariationDistance (densityMeasure f) (densityMeasure g)
        = (1 / 2 : ℝ) * ∫ x, |densityDiff f g x|) := by sorry
