-- Prove2me | Theorems.Thm_levy_foundations_probability_iteratedConvolutionPower
-- name    : levy_foundations_probability_iteratedConvolutionPower
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T18:25:37.405091+00:00
-- url     : https://prove2.me/theorems/2e4a994a-355b-4e26-a22a-a4f4f701d908
-- title:
--   Convolution powers of probability measures remain probabilities
-- statement:
--   Every natural convolution power of a probability measure on a measurable additive commutative monoid is a probability measure.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/InfiniteDivisible.lean#L61-L69, probability preservation.

import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_levy_foundations_iteratedConvolutionPower

open MeasureTheory MeasureTheory.Measure

theorem levy_foundations_probability_iteratedConvolutionPower
    {E : Type*} [AddCommMonoid E] [MeasurableSpace E] [MeasurableAdd₂ E]
    (μ : Measure E) [IsProbabilityMeasure μ] (n : ℕ) :
    IsProbabilityMeasure (LevyFoundations.iteratedConvolutionPower μ n) := by sorry
