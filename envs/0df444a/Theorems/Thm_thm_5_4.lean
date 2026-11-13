-- Prove2me | Theorems.Thm_thm_5_4
-- name    : thm_5_4
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T18:43:43.492448+00:00
-- url     : https://prove2.me/theorems/b7097c49-c01f-449b-a555-891de4b683a2
-- title:
--   Chapter 5, thm_5_4: thm_5_4
-- statement:
--   Source theorem `thm_5_4` from Chapter 5, module `thm_5_4`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_05/thm_5_4.lean

import Definitions.Def_ProbabilityTheory_chapter_05_thm_5_4_F000
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.PiSystem
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic

open MeasureTheory Set

theorem thm_5_4 {Ω : Type _} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y) :
    ProbabilityTheory.IndepFun X Y μ ↔
      ∀ x y : ℝ,
        jointCDF μ X Y x y = marginalCDF μ X x * marginalCDF μ Y y := by sorry
