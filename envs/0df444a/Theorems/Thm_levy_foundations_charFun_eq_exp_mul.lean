-- Prove2me | Theorems.Thm_levy_foundations_charFun_eq_exp_mul
-- name    : levy_foundations_charFun_eq_exp_mul
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T20:59:57.632381+00:00
-- url     : https://prove2.me/theorems/198d38df-c97c-4d67-b971-b3489b7c647b
-- title:
--   Lévy marginal exponential characteristic-function formula
-- statement:
--   Lévy marginal exponential characteristic-function formula.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/LevyProcess.lean#L261

import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Definitions.Def_levy_foundations_isLevyProcess
import Definitions.Def_levy_foundations_charExponent

open MeasureTheory Filter Topology
open scoped NNReal

theorem levy_foundations_charFun_eq_exp_mul
    {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [MeasurableAdd₂ E]
    {X : ℝ≥0 → Ω → E} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (h : LevyFoundations.IsLevyProcess X μ)
    (hX : ∀ t, Measurable (X t)) (t : ℝ≥0) (ξ : E) :
    charFun (μ.map (X t)) ξ =
      Complex.exp (↑(t : ℝ) * LevyFoundations.charExponent h ξ) := by sorry
