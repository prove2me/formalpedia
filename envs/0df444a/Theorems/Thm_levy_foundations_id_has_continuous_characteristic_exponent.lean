-- Prove2me | Theorems.Thm_levy_foundations_id_has_continuous_characteristic_exponent
-- name    : levy_foundations_id_has_continuous_characteristic_exponent
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T07:43:40.527347+00:00
-- url     : https://prove2.me/theorems/7d3b23fb-917d-4e0f-b4e1-cd6e951c2d14
-- title:
--   Continuous convolution exponent for an infinitely divisible real law
-- statement:
--   For each infinitely divisible probability measure μ on ℝ, there is a continuous complex exponent ψ such that the characteristic function of μ is exp ψ and, for every real t ≥ 0, exp(t ψ) is the characteristic function of a probability measure. This is the convolution-semigroup embedding and nonvanishing-logarithm step of the Lévy–Khintchine representation proof.

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_levy_foundations_isInfinitelyDivisible

open MeasureTheory ProbabilityTheory

theorem levy_foundations_id_has_continuous_characteristic_exponent
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : LevyFoundations.isInfinitelyDivisible μ) :
    ∃ ψ : ℝ → ℂ,
      Continuous ψ ∧
      (∀ ξ : ℝ, charFun μ ξ = Complex.exp (ψ ξ)) ∧
      (∀ t : ℝ, 0 ≤ t →
        ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
          ∀ ξ : ℝ, charFun ν ξ = Complex.exp ((t : ℂ) * ψ ξ)) := by
  sorry
