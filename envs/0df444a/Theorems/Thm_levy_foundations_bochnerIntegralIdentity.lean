-- Prove2me | Theorems.Thm_levy_foundations_bochnerIntegralIdentity
-- name    : levy_foundations_bochnerIntegralIdentity
-- status  : Open
-- author  : @WillR
-- created : 2026-10-30T21:27:21.394085+00:00
-- url     : https://prove2.me/theorems/9b5d3b8f-384b-400e-83b6-212186e381d4
-- title:
--   A continuous normalised positive-definite function has a probability spectral integral
-- statement:
--   A continuous normalised positive-definite function has a probability spectral integral.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Representation/BochnerGaussian.lean#L60

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Definitions.Def_levy_foundations_covarianceMatrix
import Definitions.Def_levy_foundations_isPositiveDefinite

open MeasureTheory Matrix Complex
open scoped ComplexOrder

theorem levy_foundations_bochnerIntegralIdentity
    (ψ : ℝ → ℂ) (hc : Continuous ψ)
    (hpd : LevyFoundations.isPositiveDefinite ψ) (h0 : ψ 0 = 1) :
    ∃ μ : ProbabilityMeasure ℝ,
      ∀ t : ℝ, ψ t = ∫ x : ℝ,
        Complex.exp (Complex.I * (t : ℂ) * (x : ℂ)) ∂(μ : Measure ℝ) := by sorry
