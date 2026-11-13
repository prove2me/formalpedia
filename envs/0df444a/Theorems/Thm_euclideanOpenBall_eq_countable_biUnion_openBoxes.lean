-- Prove2me | Theorems.Thm_euclideanOpenBall_eq_countable_biUnion_openBoxes
-- name    : euclideanOpenBall_eq_countable_biUnion_openBoxes
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:16:43.110197+00:00
-- url     : https://prove2.me/theorems/2b76c64d-5c88-49a0-a696-966716768289
-- title:
--   02_thm_2_8: euclideanOpenBall_eq_countable_biUnion_openBoxes
-- statement:
--   Original source theorem `euclideanOpenBall_eq_countable_biUnion_openBoxes` in the chapter module. The formal Lean declaration below is the authoritative proposition.
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

theorem euclideanOpenBall_eq_countable_biUnion_openBoxes
    (d : ℕ) (c : EuclideanSpace ℝ (Fin d)) {r : ℝ} (_hr : 0 < r) :
    ∃ S ⊆ euclideanOpenBoxes d, S.Countable ∧
      Metric.ball c r = ⋃ s ∈ S, s := by
  sorry
