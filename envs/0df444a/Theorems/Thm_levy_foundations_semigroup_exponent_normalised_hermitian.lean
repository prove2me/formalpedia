-- Prove2me | Theorems.Thm_levy_foundations_semigroup_exponent_normalised_hermitian
-- name    : levy_foundations_semigroup_exponent_normalised_hermitian
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T08:30:31.60108+00:00
-- url     : https://prove2.me/theorems/8d081b2d-c337-42f9-a051-88b7d1854f06
-- title:
--   A continuous characteristic semigroup exponent vanishes at zero and obeys conjugation symmetry
-- statement:
--   For every t≥0, exp(t ψ(0)) = 1. A continuous one-parameter exponential identically one has generator zero. The identity charFun ν (-ξ)=conj(charFun ν ξ), for all t, similarly makes ψ(-ξ)=conj(ψ ξ).

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof

open MeasureTheory ProbabilityTheory

/-- Characteristic-function normalisation and symmetry determine the continuous semigroup exponent. -/
theorem levy_foundations_semigroup_exponent_normalised_hermitian
    (ψ : ℝ → ℂ) (hψ : Continuous ψ)
    (hsemigroup : ∀ t : ℝ, 0 ≤ t →
      ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
        ∀ ξ : ℝ, charFun ν ξ = Complex.exp ((t : ℂ) * ψ ξ)) :
    ψ 0 = 0 ∧
      ∀ ξ : ℝ, ψ (-ξ) = starRingEnd ℂ (ψ ξ) := by sorry
