-- Prove2me | Theorems.Thm_temp_blala
-- name    : temp_blala
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:07:02.016947+00:00
-- url     : https://prove2.me/theorems/985da591-3bfc-4196-9aa0-d0248dc83794
-- title:
--   ProbabilityTheory_chapter_03_thm_3_3_F000: temp_blala
-- statement:
--   Source theorem `temp_blala` from `ProbabilityTheory.chapter_03.thm_3_3`. The formal Lean declaration specifies its proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_03/thm_3_3.lean

import Definitions.Def_ProbabilityTheory_chapter_03_def_3_5_F000
import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Topology.Order.Basic
open MeasureTheory Set ENNReal

theorem temp_blala (F : StieltjesMeasureFunction) :
    ∃! μ : Measure ℝ, ∀ a b : ℝ, μ (Ioc a b) = ENNReal.ofReal (F b - F a) := by
  sorry
