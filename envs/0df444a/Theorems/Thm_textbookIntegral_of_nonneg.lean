-- Prove2me | Theorems.Thm_textbookIntegral_of_nonneg
-- name    : textbookIntegral_of_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:29:21.370539+00:00
-- url     : https://prove2.me/theorems/28def06f-3ba8-49b3-a918-b1fc03aaaf93
-- title:
--   ProbabilityTheory_chapter_06_def_6_5_F000: textbookIntegral_of_nonneg
-- statement:
--   Source theorem `textbookIntegral_of_nonneg` extracted from `ProbabilityTheory.chapter_06.def_6_5`. The formal Lean declaration specifies the proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_06/def_6_5.lean

import Definitions.Def_ProbabilityTheory_chapter_06_def_6_5_F000
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic
open MeasureTheory
namespace Def65Support
end Def65Support
section TextbookIntegralLemmas
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → EReal}

theorem textbookIntegral_of_nonneg
    (_hX : ∀ ω, 0 ≤ X ω)
    (hneg_zero :
      Def65Support.negLIntegral μ X = 0) :
    textbookIntegral μ X = some (Def65Support.posLIntegral μ X : EReal) := by
  sorry
end TextbookIntegralLemmas
