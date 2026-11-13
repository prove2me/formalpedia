-- Prove2me | Theorems.Thm_measurable_positivePart
-- name    : measurable_positivePart
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:04:53.135995+00:00
-- url     : https://prove2.me/theorems/adaedc93-7aa5-4b76-aab1-e6d8593075d7
-- title:
--   ProbabilityTheory_chapter_06_def_6_4_F000: measurable_positivePart
-- statement:
--   Source theorem `measurable_positivePart` extracted from `ProbabilityTheory.chapter_06.def_6_4`. The formal Lean declaration specifies the proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_06/def_6_4.lean

import Definitions.Def_ProbabilityTheory_chapter_06_def_6_4_F000
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Tactic
open MeasureTheory
section PositiveNegativeParts
variable {Ω : Type*} [MeasurableSpace Ω] {X : Ω → ℝ}

theorem measurable_positivePart (hX : Measurable X) : Measurable (positivePart X) := by
  sorry
end PositiveNegativeParts
