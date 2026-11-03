-- Prove2me | Theorems.Thm_levy_foundations_arrivalGammaLaw
-- name    : levy_foundations_arrivalGammaLaw
-- status  : Open
-- author  : @WillR
-- created : 2026-10-30T21:50:05.958834+00:00
-- url     : https://prove2.me/theorems/8111ff85-4e49-46f8-ab39-ca88461d3de1
-- title:
--   Arrival of independent exponential interarrivals has Gamma law
-- statement:
--   Arrival of independent exponential interarrivals has Gamma law.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/CompoundPoissonLaw.lean#L208

import Mathlib.Probability.Distributions.Gamma
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Definitions.Def_levy_foundations_arrival
import Definitions.Def_levy_foundations_jumpCount
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_arrivalGammaDensityReal
import Definitions.Def_levy_foundations_arrivalGammaDensity
import Definitions.Def_levy_foundations_arrivalSurvivalPolynomial
open MeasureTheory Filter ProbabilityTheory
open scoped ENNReal NNReal

theorem levy_foundations_arrivalGammaLaw
    {Ω : Type*} [MeasurableSpace Ω] {τ Y : ℕ → Ω → ℝ}
    {r : ℝ≥0} {ν' : Measure ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y r ν' μ) (hr : 0 < r) (n : ℕ) :
    μ.map (LevyFoundations.arrival τ n) =
      volume.withDensity (LevyFoundations.arrivalGammaDensity (r : ℝ) n) := by sorry
