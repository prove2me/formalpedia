-- Prove2me | Theorems.Thm_textbookERealFinSum_one
-- name    : textbookERealFinSum_one
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T23:49:49.617732+00:00
-- url     : https://prove2.me/theorems/a231252a-6e4b-46e3-b518-ee896ebaaa98
-- title:
--   Source theorem: textbookERealFinSum_one
-- statement:
--   Source theorem extracted from ProbabilityTheory.chapter_06.def_6_2, with its proposition and original proof recorded separately.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_06/def_6_2.lean

import Definitions.Def_ProbabilityTheory_chapter_06_def_6_2_F001
import Definitions.Def_ProbabilityTheory_chapter_06_def_6_2_F000
import Mathlib.MeasureTheory.Function.SimpleFunc
import Mathlib.Tactic
open MeasureTheory
open scoped BigOperators
variable {Ω : Type*} [MeasurableSpace Ω]

theorem textbookERealFinSum_one (f : Fin 1 → EReal) :
    textbookERealFinSum 1 f = some (f 0) := by
  sorry
