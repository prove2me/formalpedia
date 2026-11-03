-- Prove2me | Theorems.Thm_levy_foundations_arrivalSurvival
-- name    : levy_foundations_arrivalSurvival
-- status  : Open
-- author  : @WillR
-- created : 2026-10-30T21:51:40.29262+00:00
-- url     : https://prove2.me/theorems/bb749c61-5e6f-4d87-acf5-d7939b618ddb
-- title:
--   Gamma arrival-time survival probability formula
-- statement:
--   Gamma arrival-time survival probability formula.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/CompoundPoissonLaw.lean#L359

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

theorem levy_foundations_arrivalSurvival
    {Ω : Type*} [MeasurableSpace Ω] {τ Y : ℕ → Ω → ℝ}
    {r : ℝ≥0} {ν' : Measure ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y r ν' μ) (hr : 0 < r) (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (μ {ω | t < LevyFoundations.arrival τ n ω}).toReal =
      Real.exp (-(r * t)) *
        ∑ k ∈ Finset.range (n + 1), (r * t) ^ k / k.factorial := by sorry
