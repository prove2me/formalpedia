-- Prove2me | Theorems.Thm_borelAlgebraEuclidean_eq_borel
-- name    : borelAlgebraEuclidean_eq_borel
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T23:47:39.709751+00:00
-- url     : https://prove2.me/theorems/fe6ccd0a-ab0d-4043-aa52-dc94cabb240a
-- title:
--   Source theorem: borelAlgebraEuclidean_eq_borel
-- statement:
--   Original source theorem extracted from ProbabilityTheory.chapter_02.thm_2_8. Type preserved exactly.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_02/thm_2_8.lean

import Definitions.Def_ProbabilityTheory_chapter_02_def_2_8_F000
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

theorem borelAlgebraEuclidean_eq_borel (d : ℕ) :
    borelAlgebraEuclidean d = borel (EuclideanSpace ℝ (Fin d)) := by
  sorry
