-- Prove2me | Theorems.Thm_levy_foundations_charFun_marginal_nat_pow
-- name    : levy_foundations_charFun_marginal_nat_pow
-- status  : Open
-- author  : @WillR
-- created : 2026-10-30T20:42:14.890602+00:00
-- url     : https://prove2.me/theorems/69595494-5782-4f16-8bd3-74727bdb1db6
-- title:
--   Characteristic function of a Lévy marginal at integer time
-- statement:
--   For a measurable Lévy process on a real inner-product space, the characteristic function of its n-time law is the nth power of the characteristic function of its unit-time law.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/InfiniteDivisible.lean#L148-L190, the natural-time marginal characteristic-function identity.

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_levy_foundations_isLevyProcess
import Definitions.Def_levy_foundations_isInfinitelyDivisibleLaw

open MeasureTheory MeasureTheory.Measure ProbabilityTheory
open scoped NNReal Nat

theorem levy_foundations_charFun_marginal_nat_pow
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableAdd₂ E]
    {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (h : LevyFoundations.IsLevyProcess X μ)
    (hX : ∀ t, Measurable (X t)) (n : ℕ) (ξ : E) :
    charFun (μ.map (X (n : ℝ≥0))) ξ =
      (charFun (μ.map (X 1)) ξ) ^ n := by sorry
