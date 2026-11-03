-- Prove2me | Theorems.Thm_levy_foundations_poissonProbabilityGeneratingFunction
-- name    : levy_foundations_poissonProbabilityGeneratingFunction
-- status  : Open
-- author  : @WillR
-- created : 2026-10-30T21:55:15.459704+00:00
-- url     : https://prove2.me/theorems/0dec784c-de77-4956-999d-c410055b2ba9
-- title:
--   Complex probability-generating function of a Poisson random count
-- statement:
--   Complex probability-generating function of a Poisson random count.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/CompoundPoissonLaw.lean#L434

import Mathlib.Probability.Distributions.Poisson.Basic
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

theorem levy_foundations_poissonProbabilityGeneratingFunction
    (lam : ℝ≥0) (w : ℂ) :
    (∑' k : ℕ, ((poissonMeasure lam).real {k} : ℂ) * w ^ k) =
      Complex.exp ((lam : ℝ) * (w - 1)) := by sorry
