-- Prove2me | Theorems.Thm_levy_foundations_fourierConvolutionCharFun
-- name    : levy_foundations_fourierConvolutionCharFun
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T21:09:18.49381+00:00
-- url     : https://prove2.me/theorems/352d14c1-64d2-402a-b56a-acf1376dfabd
-- title:
--   Fourier transform of convolution factors pointwise
-- statement:
--   Fourier transform of convolution factors pointwise.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Probability/Characteristic.lean#L54

import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_levy_foundations_measureFourier
import Definitions.Def_levy_foundations_probabilityCharacteristicFun

open MeasureTheory Complex ComplexConjugate

theorem levy_foundations_fourierConvolutionCharFun
    (μ ν : FiniteMeasure ℝ) (ξ : ℝ) :
    LevyFoundations.measureFourier μ ξ * LevyFoundations.measureFourier ν ξ =
      charFun ((μ : Measure ℝ) ∗ (ν : Measure ℝ)) ξ := by sorry
