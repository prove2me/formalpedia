-- Prove2me | Theorems.Thm_sourceSupIntegral_eq_lintegral
-- name    : sourceSupIntegral_eq_lintegral
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:01:06.081204+00:00
-- url     : https://prove2.me/theorems/0195ccb9-5bd6-408a-86e7-5056d5d6c5ba
-- title:
--   ProbabilityTheory_chapter_06_thm_6_3_F000: sourceSupIntegral_eq_lintegral
-- statement:
--   Source theorem `sourceSupIntegral_eq_lintegral` extracted from `ProbabilityTheory.chapter_06.thm_6_3`. The formal Lean declaration specifies the proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_06/thm_6_3.lean

import Definitions.Def_ProbabilityTheory_chapter_06_thm_6_3_F000
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
open MeasureTheory
open scoped ENNReal
variable {Ω : Type*} [MeasurableSpace Ω]

theorem sourceSupIntegral_eq_lintegral (μ : Measure Ω) (X : Ω → ENNReal) :
    sourceSupIntegral μ X = ∫⁻ ω, X ω ∂μ := by
  sorry
