-- Prove2me | Theorems.Thm_levy_foundations_continuous_charFun_marginal_t
-- name    : levy_foundations_continuous_charFun_marginal_t
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T21:05:53.933911+00:00
-- url     : https://prove2.me/theorems/70454ca9-cba6-4c7d-bd3a-7bd8ce09cee7
-- title:
--   Continuity in time of Lévy marginal characteristic functions
-- statement:
--   Continuity in time of Lévy marginal characteristic functions.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/CharacteristicExponent.lean#L519

import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Definitions.Def_levy_foundations_isLevyProcess
import Definitions.Def_levy_foundations_charExponent
import Definitions.Def_levy_foundations_levyGoodDomain
import Definitions.Def_levy_foundations_levyLocalCharExponent
import Definitions.Def_levy_foundations_levyExpFormula

open MeasureTheory Filter Topology
open scoped NNReal

theorem levy_foundations_continuous_charFun_marginal_t
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableAdd₂ E]
    {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (h : LevyFoundations.IsLevyProcess X μ)
    (hX : ∀ t, Measurable (X t))
    (ξ : E) :
    Continuous (fun t : ℝ≥0 => charFun (μ.map (X t)) ξ) := by sorry
