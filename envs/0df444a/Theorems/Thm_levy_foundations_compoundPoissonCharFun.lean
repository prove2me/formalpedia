-- Prove2me | Theorems.Thm_levy_foundations_compoundPoissonCharFun
-- name    : levy_foundations_compoundPoissonCharFun
-- status  : Open
-- author  : @WillR
-- created : 2026-10-30T21:56:31.203935+00:00
-- url     : https://prove2.me/theorems/9ae0b1e9-ab2e-4ebb-816c-c9382621ded5
-- title:
--   Characteristic function of compound Poisson with deterministic drift
-- statement:
--   Characteristic function of compound Poisson with deterministic drift.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/CompoundPoissonLaw.lean#L522

import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Independence.Process.Basic
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Definitions.Def_levy_foundations_arrival
import Definitions.Def_levy_foundations_jumpCount
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoisson
import Definitions.Def_levy_foundations_arrivalGammaDensity
open MeasureTheory ProbabilityTheory Filter Complex
open scoped ENNReal NNReal

theorem levy_foundations_compoundPoissonCharFun
    {Ω : Type*} [MeasurableSpace Ω] {τ Y : ℕ → Ω → ℝ}
    {r : ℝ≥0} {ν' : Measure ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y r ν' μ) (hr : 0 < r) (b : ℝ) (t : ℝ≥0) (ξ : ℝ) :
    charFun (μ.map (LevyFoundations.compoundPoisson b τ Y (t : ℝ))) ξ =
      Complex.exp ((t : ℝ) * (Complex.I * b * ξ +
        r * (charFun ν' ξ - 1))) := by sorry
