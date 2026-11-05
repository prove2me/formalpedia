-- Prove2me | Theorems.Thm_levy_foundations_charFun_marginal_cpow
-- name    : levy_foundations_charFun_marginal_cpow
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T21:04:40.519991+00:00
-- url     : https://prove2.me/theorems/2c9b1b14-fc48-4ed4-a22d-decba659a8c5
-- title:
--   Complex power identity for Lévy characteristic functions near zero
-- statement:
--   Complex power identity for Lévy characteristic functions near zero.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/CharacteristicExponent.lean#L469

import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Definitions.Def_levy_foundations_isLevyProcess
import Definitions.Def_levy_foundations_charExponent
import Definitions.Def_levy_foundations_levyGoodDomain
import Definitions.Def_levy_foundations_levyLocalCharExponent
import Definitions.Def_levy_foundations_levyExpFormula

open MeasureTheory Filter Topology
open scoped NNReal

theorem levy_foundations_charFun_marginal_cpow
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableAdd₂ E]
    {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (h : LevyFoundations.IsLevyProcess X μ)
    (hX : ∀ t, Measurable (X t)) :
    ∃ ε > 0, ∀ ξ ∈ Metric.ball (0 : E) ε, ∀ t : ℝ≥0,
      charFun (μ.map (X t)) ξ =
        (charFun (μ.map (X 1)) ξ) ^ (↑(t : ℝ) : ℂ) := by sorry
