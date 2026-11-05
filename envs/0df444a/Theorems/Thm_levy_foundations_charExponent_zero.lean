-- Prove2me | Theorems.Thm_levy_foundations_charExponent_zero
-- name    : levy_foundations_charExponent_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T21:01:51.356738+00:00
-- url     : https://prove2.me/theorems/d1a2ba94-c29b-425d-a171-597a428205de
-- title:
--   Lévy characteristic exponent vanishes at the zero frequency
-- statement:
--   Lévy characteristic exponent vanishes at the zero frequency.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/CharacteristicExponent.lean#L299

import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Definitions.Def_levy_foundations_isLevyProcess
import Definitions.Def_levy_foundations_charExponent
import Definitions.Def_levy_foundations_levyGoodDomain
import Definitions.Def_levy_foundations_levyLocalCharExponent
import Definitions.Def_levy_foundations_levyExpFormula

open MeasureTheory Filter Topology
open scoped NNReal

theorem levy_foundations_charExponent_zero
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableAdd₂ E]
    {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (h : LevyFoundations.IsLevyProcess X μ)
    (hX : ∀ t, Measurable (X t)) :
    LevyFoundations.charExponent h (0 : E) = 0 := by sorry
