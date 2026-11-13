-- Prove2me | Theorems.Thm_sourceSupIntegral_mono
-- name    : sourceSupIntegral_mono
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:00:53.968582+00:00
-- url     : https://prove2.me/theorems/2e6b702b-b542-41a4-9cea-04fe3c846541
-- title:
--   ProbabilityTheory_chapter_06_thm_6_3_F000: sourceSupIntegral_mono
-- statement:
--   Source theorem `sourceSupIntegral_mono` extracted from `ProbabilityTheory.chapter_06.thm_6_3`. The formal Lean declaration specifies the proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_06/thm_6_3.lean

import Definitions.Def_ProbabilityTheory_chapter_06_thm_6_3_F000
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
open MeasureTheory
open scoped ENNReal
variable {Ω : Type*} [MeasurableSpace Ω]

theorem sourceSupIntegral_mono (μ : Measure Ω) {X Y : Ω → ENNReal}
    (hsub : sourceSimpleApproximationSet X ⊆ sourceSimpleApproximationSet Y) :
    sourceSupIntegral μ X ≤ sourceSupIntegral μ Y := by
  sorry
