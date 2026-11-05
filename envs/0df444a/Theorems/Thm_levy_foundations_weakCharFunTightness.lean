-- Prove2me | Theorems.Thm_levy_foundations_weakCharFunTightness
-- name    : levy_foundations_weakCharFunTightness
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T21:20:18.805215+00:00
-- url     : https://prove2.me/theorems/2fc4aaad-bbb6-4a7d-aa0a-a2289b051d6b
-- title:
--   Pointwise characteristic convergence implies tightness
-- statement:
--   Pointwise characteristic convergence implies tightness.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Probability/WeakConvergence.lean#L369

import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.IntegralCharFun
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.Sequences
import Definitions.Def_levy_foundations_probabilityCharacteristicFun
import Definitions.Def_levy_foundations_weakCharFunTendsto
import Definitions.Def_levy_foundations_weakExpBCF

open MeasureTheory Complex ComplexConjugate Filter Topology BoundedContinuousFunction

theorem levy_foundations_weakCharFunTightness
    {μs : ℕ → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    (h : LevyFoundations.weakCharFunTendsto μs atTop μ) :
    IsTightMeasureSet (Set.range (fun n => (μs n : Measure ℝ))) := by sorry
