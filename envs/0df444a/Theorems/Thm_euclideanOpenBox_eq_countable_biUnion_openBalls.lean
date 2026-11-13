-- Prove2me | Theorems.Thm_euclideanOpenBox_eq_countable_biUnion_openBalls
-- name    : euclideanOpenBox_eq_countable_biUnion_openBalls
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:16:59.971392+00:00
-- url     : https://prove2.me/theorems/febf4a5f-e071-4664-83d3-1b653de69334
-- title:
--   02_thm_2_8: euclideanOpenBox_eq_countable_biUnion_openBalls
-- statement:
--   Original source theorem `euclideanOpenBox_eq_countable_biUnion_openBalls` in the chapter module. The formal Lean declaration below is the authoritative proposition.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_02/thm_2_8.lean

import Definitions.Def_ProbabilityTheory_chapter_02_def_2_8_F000
import Definitions.Def_ProbabilityTheory_chapter_02_thm_2_8_F000
import Definitions.Def_ProbabilityTheory_chapter_02_thm_2_8_F001
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.MeasurableSpace.Pi
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic
open Set MeasureTheory MeasurableSpace
open scoped Pointwise

theorem euclideanOpenBox_eq_countable_biUnion_openBalls
    (d : ℕ) {S : Set (EuclideanSpace ℝ (Fin d))}
    (hS : S ∈ euclideanOpenBoxes d) :
    ∃ T ⊆ euclideanOpenBalls d, T.Countable ∧ S = ⋃ t ∈ T, t := by
  sorry
