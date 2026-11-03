-- Prove2me | Theorems.Thm_levy_foundations_isInfinitelyDivisible_marginal
-- name    : levy_foundations_isInfinitelyDivisible_marginal
-- status  : Open
-- author  : @WillR
-- created : 2026-10-30T20:43:20.229999+00:00
-- url     : https://prove2.me/theorems/7bbdb3df-78bc-4b6a-8357-5c84293e644b
-- title:
--   Every marginal of a Lévy process is infinitely divisible
-- statement:
--   For any nonnegative time, a measurable Lévy-process marginal admits a probability-measure convolution root of each positive integer order, using the generic infinite-divisibility predicate.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/InfiniteDivisible.lean#L197-L250, convolution roots from stationary independent increments.

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_levy_foundations_isLevyProcess
import Definitions.Def_levy_foundations_isInfinitelyDivisibleLaw

open MeasureTheory MeasureTheory.Measure ProbabilityTheory
open scoped NNReal Nat

theorem levy_foundations_isInfinitelyDivisible_marginal
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableAdd₂ E]
    {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (h : LevyFoundations.IsLevyProcess X μ)
    (hX : ∀ t, Measurable (X t)) (t : ℝ≥0) :
    LevyFoundations.isInfinitelyDivisibleLaw (μ.map (X t)) := by sorry
