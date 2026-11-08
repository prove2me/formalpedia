-- Prove2me | Theorems.Thm_levy_foundations_compoundPoissonCharFunEqTripleExponent
-- name    : levy_foundations_compoundPoissonCharFunEqTripleExponent
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T21:57:35.649995+00:00
-- url     : https://prove2.me/theorems/1946c465-cbc9-458f-972b-f49740ca4d7b
-- title:
--   Compound-Poisson marginal matches its Levy-Khintchine exponent
-- statement:
--   Compound-Poisson marginal matches its Levy-Khintchine exponent.
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

theorem levy_foundations_compoundPoissonCharFunEqTripleExponent
    {Ω : Type*} [MeasurableSpace Ω] {τ Y : ℕ → Ω → ℝ}
    {r : ℝ≥0} {ν' : Measure ℝ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν']
    (hd : LevyFoundations.IsCompoundPoissonDriver τ Y r ν' μ)
    (hr : 0 < r) (b : ℝ) (t : ℝ≥0)
    (hlevy : LevyFoundations.isLevyMeasure ((r : ℝ≥0∞) • ν'))
    (ξ : ℝ) :
    charFun (μ.map (LevyFoundations.compoundPoisson b τ Y (t : ℝ))) ξ =
      Complex.exp ((t : ℝ) * LevyFoundations.exponent
        (LevyFoundations.compoundPoissonTripleGivenLevyMeasure b r ν' hlevy) ξ) := by sorry
