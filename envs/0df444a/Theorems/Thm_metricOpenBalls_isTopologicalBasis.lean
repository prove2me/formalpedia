-- Prove2me | Theorems.Thm_metricOpenBalls_isTopologicalBasis
-- name    : metricOpenBalls_isTopologicalBasis
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:14:49.927664+00:00
-- url     : https://prove2.me/theorems/778f0fa0-5c6e-4224-95a1-b67a255b92cd
-- title:
--   ProbabilityTheory_chapter_02_thm_2_8_F001: metricOpenBalls_isTopologicalBasis
-- statement:
--   Source theorem `metricOpenBalls_isTopologicalBasis` extracted from `ProbabilityTheory.chapter_02.thm_2_8`. The formal Lean declaration specifies the proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_02/thm_2_8.lean

import Definitions.Def_ProbabilityTheory_chapter_02_thm_2_8_F001
import Definitions.Def_ProbabilityTheory_chapter_02_thm_2_8_F000
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.MeasurableSpace.Pi
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic
open Set MeasureTheory MeasurableSpace
open scoped Pointwise

theorem metricOpenBalls_isTopologicalBasis {α : Type*} [PseudoMetricSpace α] :
    TopologicalSpace.IsTopologicalBasis
      {S : Set α | ∃ c : α, ∃ r : ℝ, 0 < r ∧ S = Metric.ball c r} := by
  sorry
