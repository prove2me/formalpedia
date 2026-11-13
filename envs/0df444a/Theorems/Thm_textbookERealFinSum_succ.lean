-- Prove2me | Theorems.Thm_textbookERealFinSum_succ
-- name    : textbookERealFinSum_succ
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T23:49:38.484744+00:00
-- url     : https://prove2.me/theorems/a6c32156-c978-48d4-be0d-4f0afe33039c
-- title:
--   Source theorem: textbookERealFinSum_succ
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

theorem textbookERealFinSum_succ (n : ℕ) (f : Fin (n + 1) → EReal) :
    textbookERealFinSum (n + 1) f =
      textbookIntegralAdd (some (f 0)) (textbookERealFinSum n fun i => f i.succ) := by
  sorry
