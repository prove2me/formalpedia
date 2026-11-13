-- Prove2me | Theorems.Thm_euclideanOpenBoxes_generateFrom_eq_borel
-- name    : euclideanOpenBoxes_generateFrom_eq_borel
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T23:47:56.683203+00:00
-- url     : https://prove2.me/theorems/79fa538c-2477-4c5e-8659-0004cb1e9e25
-- title:
--   Chapter 2, thm_2_8: euclideanOpenBoxes_generateFrom_eq_borel
-- statement:
--   Source theorem `euclideanOpenBoxes_generateFrom_eq_borel` from Chapter 2, module `thm_2_8`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_02/thm_2_8.lean

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

theorem euclideanOpenBoxes_generateFrom_eq_borel (d : ℕ) :
    MeasurableSpace.generateFrom (euclideanOpenBoxes d) =
      borel (EuclideanSpace ℝ (Fin d)) := by sorry
