-- Prove2me | Theorems.Thm_levy_foundations_arrivalSurvivalPolynomialNonneg
-- name    : levy_foundations_arrivalSurvivalPolynomialNonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T21:50:31.464983+00:00
-- url     : https://prove2.me/theorems/f77ac233-6008-47db-8408-06bb7e74414a
-- title:
--   Gamma survival polynomial is nonnegative on nonnegative arguments
-- statement:
--   Gamma survival polynomial is nonnegative on nonnegative arguments.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/CompoundPoissonLaw.lean#L102

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

theorem levy_foundations_arrivalSurvivalPolynomialNonneg
    {R t : ℝ} (hR : 0 ≤ R) (ht : 0 ≤ t) (n : ℕ) :
    0 ≤ LevyFoundations.arrivalSurvivalPolynomial R n t := by sorry
