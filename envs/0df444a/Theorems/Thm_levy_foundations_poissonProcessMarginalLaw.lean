-- Prove2me | Theorems.Thm_levy_foundations_poissonProcessMarginalLaw
-- name    : levy_foundations_poissonProcessMarginalLaw
-- status  : Open
-- author  : @WillR
-- created : 2026-10-30T21:36:28.854634+00:00
-- url     : https://prove2.me/theorems/74653cb8-930c-4961-abc5-bd2779187231
-- title:
--   Poisson marginal distribution at a fixed time
-- statement:
--   Poisson marginal distribution at a fixed time.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/PoissonProcess.lean#L218

import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_levy_foundations_isPoissonProcess
open MeasureTheory ProbabilityTheory Complex
open scoped NNReal

theorem levy_foundations_poissonProcessMarginalLaw
    {Ω : Type*} [MeasurableSpace Ω]
    {N : ℝ≥0 → Ω → ℕ} {rate : ℝ≥0} {μ : Measure Ω}
    (h : LevyFoundations.IsPoissonProcess N rate μ)
    (t : ℝ≥0) : μ.map (N t) = poissonMeasure (rate * t) := by sorry
