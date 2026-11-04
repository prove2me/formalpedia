-- Prove2me | Theorems.Thm_levy_foundations_probabilityCharacteristicPositiveSemiDefinite
-- name    : levy_foundations_probabilityCharacteristicPositiveSemiDefinite
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T21:11:07.64799+00:00
-- url     : https://prove2.me/theorems/a01d2caf-def5-4619-ad72-cbaaa767930f
-- title:
--   Characteristic functions have nonnegative finite Hermitian quadratic forms
-- statement:
--   Characteristic functions have nonnegative finite Hermitian quadratic forms.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Probability/Characteristic.lean#L106

import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Group.Convolution
import Definitions.Def_levy_foundations_measureFourier
import Definitions.Def_levy_foundations_probabilityCharacteristicFun

open MeasureTheory Complex ComplexConjugate

theorem levy_foundations_probabilityCharacteristicPositiveSemiDefinite
    (μ : ProbabilityMeasure ℝ) {n : ℕ} (ξ : Fin n → ℝ) (c : Fin n → ℂ) :
    0 ≤ (∑ j : Fin n, ∑ k : Fin n, starRingEnd ℂ (c j) * c k *
      LevyFoundations.probabilityCharacteristicFun μ (ξ j - ξ k)).re := by sorry
