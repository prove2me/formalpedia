-- Prove2me | Theorems.Thm_textbookIntegral_eq_none_iff
-- name    : textbookIntegral_eq_none_iff
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:28:23.755824+00:00
-- url     : https://prove2.me/theorems/824a3329-7d34-4d64-8bfa-ac5980006b35
-- title:
--   ProbabilityTheory_chapter_06_def_6_5_F000: textbookIntegral_eq_none_iff
-- statement:
--   Source theorem `textbookIntegral_eq_none_iff` extracted from `ProbabilityTheory.chapter_06.def_6_5`. The formal Lean declaration specifies the proposition.
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

theorem textbookIntegral_eq_none_iff :
    textbookIntegral μ X = none ↔
      Def65Support.posLIntegral μ X = ⊤ ∧ Def65Support.negLIntegral μ X = ⊤ := by
  sorry
end TextbookIntegralLemmas
