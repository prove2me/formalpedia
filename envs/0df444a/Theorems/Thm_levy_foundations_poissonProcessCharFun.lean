-- Prove2me | Theorems.Thm_levy_foundations_poissonProcessCharFun
-- name    : levy_foundations_poissonProcessCharFun
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T21:36:46.415664+00:00
-- url     : https://prove2.me/theorems/fb33cd6e-9320-41ba-9bef-bec0e6250b07
-- title:
--   Characteristic function of a Poisson counting-process marginal
-- statement:
--   Characteristic function of a Poisson counting-process marginal.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/PoissonProcess.lean#L218

import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_levy_foundations_isPoissonProcess
open MeasureTheory ProbabilityTheory Complex
open scoped NNReal

theorem levy_foundations_poissonProcessCharFun
    {Ω : Type*} [MeasurableSpace Ω]
    {N : ℝ≥0 → Ω → ℕ} {rate : ℝ≥0} {μ : Measure Ω}
    (h : LevyFoundations.IsPoissonProcess N rate μ)
    (t : ℝ≥0) (ξ : ℝ) :
    charFun (μ.map (fun ω => (N t ω : ℝ))) ξ =
      Complex.exp (↑(rate * t : ℝ≥0) * (Complex.exp (↑ξ * Complex.I) - 1)) := by sorry
