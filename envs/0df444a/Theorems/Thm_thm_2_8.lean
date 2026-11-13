-- Prove2me | Theorems.Thm_thm_2_8
-- name    : thm_2_8
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T20:17:42.038211+00:00
-- url     : https://prove2.me/theorems/f498ea78-fbcd-420b-b144-9f1c1121fb9c
-- title:
--   02_thm_2_8: thm_2_8
-- statement:
--   Original source theorem `thm_2_8` in the chapter module. The formal Lean declaration below is the authoritative proposition.
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

theorem thm_2_8 (d : ℕ) :
    MeasurableSpace.generateFrom (euclideanOpenBoxes d) =
      borelAlgebraEuclidean d := by
  sorry
