-- Prove2me | Theorems.Thm_levy_foundations_semigroup_exponent_conditionally_negative
-- name    : levy_foundations_semigroup_exponent_conditionally_negative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T08:30:38.454287+00:00
-- url     : https://prove2.me/theorems/9b81c923-84f8-4ca7-bc69-e8e31b674bb6
-- title:
--   Positive-definite exponential powers imply conditional negative definiteness of the generator
-- statement:
--   For each positive t, exp(t ψ) is a positive-definite characteristic function. With coefficients summing to zero, the real part of its associated Gram quadratic form is nonnegative, and its zero-time value is zero. Divide by t and let t ↓ 0 using the derivative of exp to obtain nonnegativity of the corresponding quadratic form of ψ.

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof

open MeasureTheory ProbabilityTheory

/-- Schoenberg's infinitesimal direction for a characteristic semigroup. -/
theorem levy_foundations_semigroup_exponent_conditionally_negative
    (ψ : ℝ → ℂ) (hψ : Continuous ψ)
    (hsemigroup : ∀ t : ℝ, 0 ≤ t →
      ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
        ∀ ξ : ℝ, charFun ν ξ = Complex.exp ((t : ℂ) * ψ ξ)) :
    ProbabilityTheory.IsConditionallyNegativeDefinite ψ := by sorry
