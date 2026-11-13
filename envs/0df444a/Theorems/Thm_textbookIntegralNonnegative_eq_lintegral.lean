-- Prove2me | Theorems.Thm_textbookIntegralNonnegative_eq_lintegral
-- name    : textbookIntegralNonnegative_eq_lintegral
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:07:26.058006+00:00
-- url     : https://prove2.me/theorems/8b7d9915-9292-4e2f-9f1b-ed789ba36736
-- title:
--   ProbabilityTheory_chapter_06_def_6_3_F000: textbookIntegralNonnegative_eq_lintegral
-- statement:
--   Source theorem `textbookIntegralNonnegative_eq_lintegral` extracted from `ProbabilityTheory.chapter_06.def_6_3`. The formal Lean declaration specifies the proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_06/def_6_3.lean

import Definitions.Def_ProbabilityTheory_chapter_06_def_6_3_F000
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
open MeasureTheory
variable {Ω : Type*} [MeasurableSpace Ω]

theorem textbookIntegralNonnegative_eq_lintegral
    (μ : Measure Ω) (X : Ω → ENNReal) :
    textbookIntegralNonnegative μ X = ∫⁻ ω, X ω ∂μ := by
  sorry
