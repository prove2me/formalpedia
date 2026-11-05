-- Prove2me | Theorems.Thm_levy_foundations_charFun_iteratedConvolutionPower
-- name    : levy_foundations_charFun_iteratedConvolutionPower
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T18:25:53.07982+00:00
-- url     : https://prove2.me/theorems/604e2f0f-5578-4375-beee-288826bf6613
-- title:
--   Characteristic function of a convolution power is a pointwise power
-- statement:
--   For a real inner-product state space satisfying the source measurability assumptions, the characteristic function of the n-fold convolution power of a probability measure is its characteristic function raised to n.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/InfiniteDivisible.lean#L71-L81, characteristic-function recursion.

import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_levy_foundations_iteratedConvolutionPower

open MeasureTheory MeasureTheory.Measure

theorem levy_foundations_charFun_iteratedConvolutionPower
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableAdd₂ E] (μ : Measure E) [IsProbabilityMeasure μ]
    (n : ℕ) (t : E) :
    charFun (LevyFoundations.iteratedConvolutionPower μ n) t =
      (charFun μ t) ^ n := by sorry
