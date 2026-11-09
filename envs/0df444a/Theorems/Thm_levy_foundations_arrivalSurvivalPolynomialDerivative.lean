-- Prove2me | Theorems.Thm_levy_foundations_arrivalSurvivalPolynomialDerivative
-- name    : levy_foundations_arrivalSurvivalPolynomialDerivative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T21:51:01.879326+00:00
-- url     : https://prove2.me/theorems/47817396-565c-4018-9d05-8f16f39e23d4
-- title:
--   Derivative of Gamma arrival survival polynomial equals minus Gamma density
-- statement:
--   Derivative of Gamma arrival survival polynomial equals minus Gamma density.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/CompoundPoissonLaw.lean#L245

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

theorem levy_foundations_arrivalSurvivalPolynomialDerivative
    (R : ℝ) (n : ℕ) (s : ℝ) :
    HasDerivAt (LevyFoundations.arrivalSurvivalPolynomial R n)
      (-LevyFoundations.arrivalGammaDensityReal R n s) s := by sorry
