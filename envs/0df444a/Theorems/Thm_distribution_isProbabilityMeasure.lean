-- Prove2me | Theorems.Thm_distribution_isProbabilityMeasure
-- name    : distribution_isProbabilityMeasure
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T22:17:15.285812+00:00
-- url     : https://prove2.me/theorems/724762cc-b24e-4e1a-a67f-b8a97f80db49
-- title:
--   ProbabilityTheory_chapter_07_def_7_2_F000: distribution_isProbabilityMeasure
-- statement:
--   Source theorem `distribution_isProbabilityMeasure` extracted from `ProbabilityTheory.chapter_07.def_7_2`. The formal Lean declaration specifies the proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_07/def_7_2.lean

import Definitions.Def_ProbabilityTheory_chapter_07_def_7_2_F000
import Definitions.Def_ProbabilityTheory_chapter_07_thm_7_10_F000
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic
open MeasureTheory

theorem distribution_isProbabilityMeasure {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X) :
    MeasureTheory.IsProbabilityMeasure (RandomVariableDistribution μ X) := by
  sorry
