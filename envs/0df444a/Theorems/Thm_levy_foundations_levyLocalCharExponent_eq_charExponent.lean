-- Prove2me | Theorems.Thm_levy_foundations_levyLocalCharExponent_eq_charExponent
-- name    : levy_foundations_levyLocalCharExponent_eq_charExponent
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T21:03:16.417811+00:00
-- url     : https://prove2.me/theorems/05477e68-006f-49d8-934a-02814e2350bc
-- title:
--   Local logarithmic and limiting Lévy exponents agree near zero
-- statement:
--   Local logarithmic and limiting Lévy exponents agree near zero.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/CharacteristicExponent.lean#L318

import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Definitions.Def_levy_foundations_isLevyProcess
import Definitions.Def_levy_foundations_charExponent
import Definitions.Def_levy_foundations_levyGoodDomain
import Definitions.Def_levy_foundations_levyLocalCharExponent
import Definitions.Def_levy_foundations_levyExpFormula

open MeasureTheory Filter Topology
open scoped NNReal

theorem levy_foundations_levyLocalCharExponent_eq_charExponent
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableAdd₂ E]
    {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (h : LevyFoundations.IsLevyProcess X μ)
    (hX : ∀ t, Measurable (X t)) :
    ∃ ε > 0, ∀ ξ ∈ Metric.ball (0 : E) ε,
      LevyFoundations.levyLocalCharExponent h hX ξ =
        LevyFoundations.charExponent h ξ := by sorry
