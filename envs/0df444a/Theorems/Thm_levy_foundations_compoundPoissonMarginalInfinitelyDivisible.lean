-- Prove2me | Theorems.Thm_levy_foundations_compoundPoissonMarginalInfinitelyDivisible
-- name    : levy_foundations_compoundPoissonMarginalInfinitelyDivisible
-- status  : Open
-- author  : @WillR
-- created : 2026-10-30T21:57:49.592983+00:00
-- url     : https://prove2.me/theorems/e2a8a617-4633-4172-8f7f-747b7ef8909f
-- title:
--   Compound-Poisson marginals are infinitely divisible
-- statement:
--   Compound-Poisson marginals are infinitely divisible.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/CompoundPoissonLaw.lean

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_levy_foundations_isLevyMeasure
import Definitions.Def_levy_foundations_levyKhintchineTriple
import Definitions.Def_levy_foundations_exponent
import Definitions.Def_levy_foundations_isInfinitelyDivisible
import Definitions.Def_levy_foundations_compoundPoisson
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Definitions.Def_levy_foundations_compoundPoissonTripleGivenLevyMeasure
open MeasureTheory ProbabilityTheory Complex
open scoped ENNReal NNReal

theorem levy_foundations_compoundPoissonMarginalInfinitelyDivisible
    {Ω : Type*} [MeasurableSpace Ω] {τ Y : ℕ → Ω → ℝ}
    {r : ℝ≥0} {ν' : Measure ℝ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν']
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y r ν' μ)
    (hr : 0 < r) (hν' : ν' {0} = 0) (b : ℝ) (t : ℝ≥0) :
    LevyFoundations.isInfinitelyDivisible
      (μ.map (LevyFoundations.compoundPoisson b τ Y (t : ℝ))) := by sorry
