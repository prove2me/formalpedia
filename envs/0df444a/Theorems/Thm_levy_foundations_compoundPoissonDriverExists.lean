-- Prove2me | Theorems.Thm_levy_foundations_compoundPoissonDriverExists
-- name    : levy_foundations_compoundPoissonDriverExists
-- status  : Open
-- author  : @WillR
-- created : 2026-10-30T21:46:31.390155+00:00
-- url     : https://prove2.me/theorems/f9e2e0b5-4745-4ad5-9145-2e2936ea4695
-- title:
--   Existence of jointly independent compound-Poisson driver
-- statement:
--   Existence of jointly independent compound-Poisson driver.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/CompoundPoisson.lean#L245

import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Probability.HasLawExists
import Mathlib.Probability.Distributions.Exponential
import Definitions.Def_levy_foundations_isCadlag
import Definitions.Def_levy_foundations_jumpCount
import Definitions.Def_levy_foundations_piecewisePath
import Definitions.Def_levy_foundations_arrival
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal Interval

theorem levy_foundations_compoundPoissonDriverExists
    (r : ℝ≥0) (hr : 0 < r) (ν' : Measure ℝ) [IsProbabilityMeasure ν'] :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (τ Y : ℕ → Ω → ℝ),
       IsProbabilityMeasure μ ∧ LevyFoundations.IsCompoundPoissonDriver τ Y r ν' μ := by sorry
