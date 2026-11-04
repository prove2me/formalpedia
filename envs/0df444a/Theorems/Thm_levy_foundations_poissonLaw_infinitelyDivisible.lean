-- Prove2me | Theorems.Thm_levy_foundations_poissonLaw_infinitelyDivisible
-- name    : levy_foundations_poissonLaw_infinitelyDivisible
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T20:41:01.496888+00:00
-- url     : https://prove2.me/theorems/54d436f5-bdef-4609-8180-4220ba115d49
-- title:
--   Real-embedded Poisson distributions are infinitely divisible
-- statement:
--   For each positive order, a Poisson law on reals has a probability convolution root at rate r/n.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/InfiniteDivisible.lean#L114-L130

import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_levy_foundations_isInfinitelyDivisibleLaw

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Complex
open scoped NNReal Nat

theorem levy_foundations_poissonLaw_infinitelyDivisible
    (r : ℝ≥0) :
    LevyFoundations.isInfinitelyDivisibleLaw
      ((poissonMeasure r).map (Nat.cast : ℕ → ℝ)) := by sorry
