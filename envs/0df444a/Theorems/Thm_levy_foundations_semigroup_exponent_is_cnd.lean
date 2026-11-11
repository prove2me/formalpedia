-- Prove2me | Theorems.Thm_levy_foundations_semigroup_exponent_is_cnd
-- name    : levy_foundations_semigroup_exponent_is_cnd
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T08:16:12.719606+00:00
-- url     : https://prove2.me/theorems/36c213d6-a81f-4980-bcc0-c38d87dee0ea
-- title:
--   Exponents of characteristic convolution semigroups are normalised Hermitian and conditionally negative definite
-- statement:
--   Use the characteristic-function normalisation at zero, conjugation symmetry and positive semidefiniteness for each t>0. Differentiate the finite positive-definite quadratic forms at t=0 under zero-sum coefficient constraints to establish conditional negative definiteness of the continuous exponent.

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof

open MeasureTheory ProbabilityTheory

/-- An exponent whose positive scalar exponential multiples are all characteristic functions is a normalised Hermitian conditionally negative definite function. -/
theorem levy_foundations_semigroup_exponent_is_cnd
    (ψ : ℝ → ℂ) (hψ : Continuous ψ)
    (hsemigroup : ∀ t : ℝ, 0 ≤ t →
      ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
        ∀ ξ : ℝ, charFun ν ξ = Complex.exp ((t : ℂ) * ψ ξ)) :
    ψ 0 = 0 ∧
      (∀ ξ : ℝ, ψ (-ξ) = starRingEnd ℂ (ψ ξ)) ∧
      ProbabilityTheory.IsConditionallyNegativeDefinite ψ := by sorry
