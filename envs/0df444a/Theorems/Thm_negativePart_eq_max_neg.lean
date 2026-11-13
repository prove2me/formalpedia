-- Prove2me | Theorems.Thm_negativePart_eq_max_neg
-- name    : negativePart_eq_max_neg
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:06:03.183202+00:00
-- url     : https://prove2.me/theorems/4fe07eea-ef0a-47ab-9714-d31a57e1f7ec
-- title:
--   ProbabilityTheory_chapter_06_def_6_4_F000: negativePart_eq_max_neg
-- statement:
--   Source theorem `negativePart_eq_max_neg` extracted from `ProbabilityTheory.chapter_06.def_6_4`. The formal Lean declaration specifies the proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_06/def_6_4.lean

import Definitions.Def_ProbabilityTheory_chapter_06_def_6_4_F000
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Tactic
open MeasureTheory
section PositiveNegativeParts
variable {Ω : Type*} [MeasurableSpace Ω] {X : Ω → ℝ}

theorem negativePart_eq_max_neg (X : Ω → ℝ) :
    negativePart X = fun ω => max (-X ω) 0 := by
  sorry
end PositiveNegativeParts
