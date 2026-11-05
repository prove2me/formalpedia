-- Prove2me | Theorems.Thm_levy_foundations_smallJumpMemLpTwo
-- name    : levy_foundations_smallJumpMemLpTwo
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T15:19:28.975995+00:00
-- url     : https://prove2.me/theorems/98048b6d-4867-49c8-b39b-9001716e7263
-- title:
--   Square-integrability of the small-jump integrand from time zero
-- statement:
--   The jump-size function on (0,t] × (-1,1) has finite L2 norm, including for infinite-activity Lévy measures.
-- source:
--   Inspired by Shmuel Link, LeanLevy (MIT), https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/TimeSpacePoisson.lean#L244-L246. Independently authored Prove2Me draft, awaiting remote compilation.

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Definitions.Def_levy_foundations_isLevyMeasure

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem levy_foundations_smallJumpMemLpTwo
    (ν : Measure ℝ) [SigmaFinite ν]
    (hν : LevyFoundations.isLevyMeasure ν) (t : ℝ) :
    MemLp ((Set.Ioc 0 t ×ˢ Set.Ioo (-1) 1).indicator
      (fun p : ℝ × ℝ => p.2)) 2 (volume.prod ν) := by sorry
