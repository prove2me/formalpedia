-- Prove2me | Theorems.Thm_textbookIntegrable_pos_ne_top
-- name    : textbookIntegrable_pos_ne_top
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:28:38.216147+00:00
-- url     : https://prove2.me/theorems/988fc962-86f5-495b-a3d8-cfd49660f298
-- title:
--   ProbabilityTheory_chapter_06_def_6_5_F000: textbookIntegrable_pos_ne_top
-- statement:
--   Source theorem `textbookIntegrable_pos_ne_top` extracted from `ProbabilityTheory.chapter_06.def_6_5`. The formal Lean declaration specifies the proposition.
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

theorem textbookIntegrable_pos_ne_top (hX : textbookIntegrable μ X) :
    Def65Support.posLIntegral μ X ≠ ⊤ := by
  sorry
end TextbookIntegralLemmas
