-- Prove2me | Theorems.Thm_levy_foundations_weakCharFunTendstoToWeak
-- name    : levy_foundations_weakCharFunTendstoToWeak
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T21:20:41.966714+00:00
-- url     : https://prove2.me/theorems/000fee4a-3ea8-424a-af7e-7b1934461592
-- title:
--   Lévy continuity theorem: characteristic convergence implies weak convergence
-- statement:
--   Lévy continuity theorem: characteristic convergence implies weak convergence.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Probability/WeakConvergence.lean#L442

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

theorem levy_foundations_weakCharFunTendstoToWeak
    {μs : ℕ → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    (h : LevyFoundations.weakCharFunTendsto μs atTop μ) :
    Tendsto μs atTop (𝓝 μ) := by sorry
