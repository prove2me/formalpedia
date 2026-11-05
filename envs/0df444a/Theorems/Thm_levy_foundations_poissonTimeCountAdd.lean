-- Prove2me | Theorems.Thm_levy_foundations_poissonTimeCountAdd
-- name    : levy_foundations_poissonTimeCountAdd
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T15:18:46.850718+00:00
-- url     : https://prove2.me/theorems/c8224f12-84c0-4d26-b412-3942d11a485d
-- title:
--   Pathwise additivity of time-space Poisson counts
-- statement:
--   The running count at t splits exactly into the count up to s and the number of marks in (s,t], for ordered nonnegative times.
-- source:
--   Inspired by Shmuel Link, LeanLevy (MIT), https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/RandomMeasure/TimeSpacePoisson.lean#L135-L142. Independently authored Prove2Me draft, awaiting remote compilation.

import Mathlib.MeasureTheory.Integral.Prod
import Definitions.Def_levy_foundations_poissonRandomMeasure
import Definitions.Def_levy_foundations_poissonTimeCount

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

theorem levy_foundations_poissonTimeCountAdd
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → ℝ × E)
    (A : Set E) (s t : ℝ) (hA : MeasurableSet A)
    (h0s : 0 ≤ s) (hst : s ≤ t) (ω : Ω) :
    LevyFoundations.poissonTimeCount K X A t ω =
      LevyFoundations.poissonTimeCount K X A s ω +
        LevyFoundations.poissonRandomMeasure K X ω (Set.Ioc s t ×ˢ A) := by sorry
