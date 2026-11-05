-- Prove2me | Theorems.Thm_levy_foundations_compoundPoissonTripleExponentIdentity
-- name    : levy_foundations_compoundPoissonTripleExponentIdentity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T21:57:20.490003+00:00
-- url     : https://prove2.me/theorems/930cedf8-a433-42c9-a15e-7f58be286921
-- title:
--   Compound-Poisson triple exponent cancels its small-jump compensator
-- statement:
--   Compound-Poisson triple exponent cancels its small-jump compensator.
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

theorem levy_foundations_compoundPoissonTripleExponentIdentity
    (b : ℝ) (r : ℝ≥0) (ν' : Measure ℝ) [IsProbabilityMeasure ν']
    (hlevy : LevyFoundations.isLevyMeasure ((r : ℝ≥0∞) • ν'))
    (ξ : ℝ) :
    LevyFoundations.exponent
      (LevyFoundations.compoundPoissonTripleGivenLevyMeasure b r ν' hlevy) ξ =
      Complex.I * b * ξ + r * (charFun ν' ξ - 1) := by sorry
