-- Prove2me | Theorems.Thm_levy_foundations_arrivalGammaDensityConvolution
-- name    : levy_foundations_arrivalGammaDensityConvolution
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T21:54:18.218236+00:00
-- url     : https://prove2.me/theorems/2002b91e-5527-4a5c-8905-5212cea68b29
-- title:
--   Gamma arrival density convolved with one exponential advances the shape
-- statement:
--   Gamma arrival density convolved with one exponential advances the shape.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/CompoundPoissonLaw.lean#L162

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

theorem levy_foundations_arrivalGammaDensityConvolution
    {R : ℝ} (hR : 0 < R) (n : ℕ) (z : ℝ) :
    (∫⁻ x, LevyFoundations.arrivalGammaDensity R n x *
      LevyFoundations.arrivalGammaDensity R 0 (z - x)) =
       LevyFoundations.arrivalGammaDensity R (n + 1) z := by sorry
