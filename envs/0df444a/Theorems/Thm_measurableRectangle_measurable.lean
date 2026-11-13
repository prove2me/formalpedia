-- Prove2me | Theorems.Thm_measurableRectangle_measurable
-- name    : measurableRectangle_measurable
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:08:34.676425+00:00
-- url     : https://prove2.me/theorems/ad9075a3-c209-4d34-9737-955123323197
-- title:
--   ProbabilityTheory_chapter_08_def_8_3_F000: measurableRectangle_measurable
-- statement:
--   Source theorem `measurableRectangle_measurable` extracted from `ProbabilityTheory.chapter_08.def_8_3`. The formal Lean declaration specifies the proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_08/def_8_3.lean

import Definitions.Def_ProbabilityTheory_chapter_08_def_8_3_F000
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Tactic
open Set

theorem measurableRectangle_measurable
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {E₁ : Set α} {E₂ : Set β}
    (hE₁ : MeasurableSet E₁) (hE₂ : MeasurableSet E₂) :
    MeasurableSet (MeasurableRectangle E₁ E₂) := by
  sorry
