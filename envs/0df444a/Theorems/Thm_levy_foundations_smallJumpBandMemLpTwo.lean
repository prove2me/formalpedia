-- Prove2me | Theorems.Thm_levy_foundations_smallJumpBandMemLpTwo
-- name    : levy_foundations_smallJumpBandMemLpTwo
-- status  : Open
-- author  : @WillR
-- created : 2026-10-30T15:19:16.752963+00:00
-- url     : https://prove2.me/theorems/195a59cb-8a99-4356-b9e1-7fa52519f3a5
-- title:
--   Square-integrability of the small-jump band integrand
-- statement:
--   The spatially truncated jump-size function supported on (s,t] × (-1,1) lies in L2 of the time-space intensity for every Lévy measure.
-- source:
--   Inspired by Shmuel Link, LeanLevy (MIT), https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/TimeSpacePoisson.lean#L232-L242. Independently authored Prove2Me draft, awaiting remote compilation.

import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Definitions.Def_levy_foundations_isLevyMeasure

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem levy_foundations_smallJumpBandMemLpTwo
    (ν : Measure ℝ) [SigmaFinite ν]
    (hν : LevyFoundations.isLevyMeasure ν) (s t : ℝ) :
    MemLp ((Set.Ioc s t ×ˢ Set.Ioo (-1) 1).indicator
      (fun p : ℝ × ℝ => p.2)) 2 (volume.prod ν) := by sorry
