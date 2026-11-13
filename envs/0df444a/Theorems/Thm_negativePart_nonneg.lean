-- Prove2me | Theorems.Thm_negativePart_nonneg
-- name    : negativePart_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:05:47.350206+00:00
-- url     : https://prove2.me/theorems/73e1cbe9-c909-4275-88c0-3968729f5699
-- title:
--   ProbabilityTheory_chapter_06_def_6_4_F000: negativePart_nonneg
-- statement:
--   Source theorem `negativePart_nonneg` extracted from `ProbabilityTheory.chapter_06.def_6_4`. The formal Lean declaration specifies the proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_06/def_6_4.lean

import Definitions.Def_ProbabilityTheory_chapter_06_def_6_4_F000
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Tactic
open MeasureTheory
section PositiveNegativeParts
variable {Ω : Type*} [MeasurableSpace Ω] {X : Ω → ℝ}

theorem negativePart_nonneg (ω : Ω) : 0 ≤ negativePart X ω := by
  sorry
end PositiveNegativeParts
