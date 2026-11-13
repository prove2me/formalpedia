-- Prove2me | Theorems.Thm_euclideanOpenBall_mem_generateFrom_openBoxes
-- name    : euclideanOpenBall_mem_generateFrom_openBoxes
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:17:14.109799+00:00
-- url     : https://prove2.me/theorems/a026a65a-45aa-4b7d-ab2a-dc4aac98ebef
-- title:
--   02_thm_2_8: euclideanOpenBall_mem_generateFrom_openBoxes
-- statement:
--   Original source theorem `euclideanOpenBall_mem_generateFrom_openBoxes` in the chapter module. The formal Lean declaration below is the authoritative proposition.
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

theorem euclideanOpenBall_mem_generateFrom_openBoxes
    (d : ℕ) (c : EuclideanSpace ℝ (Fin d)) {r : ℝ} (hr : 0 < r) :
    @MeasurableSet (EuclideanSpace ℝ (Fin d))
      (MeasurableSpace.generateFrom (euclideanOpenBoxes d)) (Metric.ball c r) := by
  sorry
