-- Prove2me | Theorems.Thm_levy_foundations_withDensityConvolutionFormula
-- name    : levy_foundations_withDensityConvolutionFormula
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T21:54:05.650862+00:00
-- url     : https://prove2.me/theorems/2bd77a28-948e-42e9-b541-4a1d6c48a115
-- title:
--   Convolution of two real Lebesgue densities has the convolution density
-- statement:
--   Convolution of two real Lebesgue densities has the convolution density.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Processes/CompoundPoissonLaw.lean#L122

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

theorem levy_foundations_withDensityConvolutionFormula
    {f g : ℝ → ℝ≥0∞} [SFinite (volume.withDensity g)]
    (hf : Measurable f) (hg : Measurable g) :
    (volume.withDensity f) ∗ (volume.withDensity g) =
      volume.withDensity (fun z => ∫⁻ x, f x * g (z - x)) := by sorry
