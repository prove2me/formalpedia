-- Prove2me | Theorems.Thm_levy_foundations_posDefCharFun
-- name    : levy_foundations_posDefCharFun
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T07:41:33.067979+00:00
-- url     : https://prove2.me/theorems/52fe2c61-71ae-42a5-a3b1-8a8771b5c37a
-- title:
--   Characteristic functions are positive definite
-- statement:
--   Every probability measure on ℝ has a positive-definite characteristic function.
-- source:
--   Inspired by Shmuel Link, LeanLevy (MIT), https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Fourier/PositiveDefinite.lean#L273-L327. Positive definiteness of characteristic functions. Independent Prove2Me statement, pending audit and remote compilation.

import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Analysis.Matrix.PosDef
import Definitions.Def_levy_foundations_isPositiveDefinite

open MeasureTheory

theorem levy_foundations_posDefCharFun (μ : ProbabilityMeasure ℝ) :
    LevyFoundations.isPositiveDefinite
      (fun ξ : ℝ => charFun (μ : Measure ℝ) ξ) := by sorry
