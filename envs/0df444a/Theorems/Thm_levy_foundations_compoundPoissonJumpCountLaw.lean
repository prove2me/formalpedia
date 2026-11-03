-- Prove2me | Theorems.Thm_levy_foundations_compoundPoissonJumpCountLaw
-- name    : levy_foundations_compoundPoissonJumpCountLaw
-- status  : Open
-- author  : @WillR
-- created : 2026-10-30T21:53:51.111384+00:00
-- url     : https://prove2.me/theorems/5d293a54-7f70-44ee-9430-0818fc1c396f
-- title:
--   Number of compound-Poisson arrivals by time t has a Poisson law
-- statement:
--   Number of compound-Poisson arrivals by time t has a Poisson law.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/CompoundPoissonLaw.lean#L372

import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Distributions.Poisson.Basic
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

theorem levy_foundations_compoundPoissonJumpCountLaw
    {Ω : Type*} [MeasurableSpace Ω] {τ Y : ℕ → Ω → ℝ}
    {r : ℝ≥0} {ν' : Measure ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y r ν' μ) (hr : 0 < r) (t : ℝ≥0) :
    μ.map (fun ω => LevyFoundations.jumpCount
      (fun n => LevyFoundations.arrival τ n ω) (t : ℝ)) =
        poissonMeasure (r * t) := by sorry
