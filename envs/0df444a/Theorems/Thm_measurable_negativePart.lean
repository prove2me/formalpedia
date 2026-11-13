-- Prove2me | Theorems.Thm_measurable_negativePart
-- name    : measurable_negativePart
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:05:14.44335+00:00
-- url     : https://prove2.me/theorems/188e44af-86f4-422e-96fb-c5f2da2b4143
-- title:
--   ProbabilityTheory_chapter_06_def_6_4_F000: measurable_negativePart
-- statement:
--   Source theorem `measurable_negativePart` extracted from `ProbabilityTheory.chapter_06.def_6_4`. The formal Lean declaration specifies the proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_06/def_6_4.lean

import Definitions.Def_ProbabilityTheory_chapter_06_def_6_4_F000
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Tactic
open MeasureTheory
section PositiveNegativeParts
variable {Ω : Type*} [MeasurableSpace Ω] {X : Ω → ℝ}

theorem measurable_negativePart (hX : Measurable X) : Measurable (negativePart X) := by
  sorry
end PositiveNegativeParts
