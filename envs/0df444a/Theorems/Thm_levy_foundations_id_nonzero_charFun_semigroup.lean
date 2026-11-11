-- Prove2me | Theorems.Thm_levy_foundations_id_nonzero_charFun_semigroup
-- name    : levy_foundations_id_nonzero_charFun_semigroup
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T07:52:01.149067+00:00
-- url     : https://prove2.me/theorems/c5a602ef-1a4e-41fe-9c7e-f19572bd8576
-- title:
--   Continuous logarithm and fractional characteristic powers of a nonvanishing infinitely divisible law
-- statement:
--   If an infinitely divisible real probability law has a nowhere-zero characteristic function, construct a continuous complex logarithm ψ with charFun μ = exp ψ, and prove exp(t ψ) is a probability characteristic function for every nonnegative real t. The difficult step uses rational convolution powers and passage to arbitrary times through Lévy's continuity theorem.

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_levy_foundations_isInfinitelyDivisible

open MeasureTheory ProbabilityTheory

theorem levy_foundations_id_nonzero_charFun_semigroup
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : LevyFoundations.isInfinitelyDivisible μ)
    (hnonzero : ∀ ξ : ℝ, charFun μ ξ ≠ 0) :
    ∃ ψ : ℝ → ℂ,
      Continuous ψ ∧
      (∀ ξ : ℝ, charFun μ ξ = Complex.exp (ψ ξ)) ∧
      (∀ t : ℝ, 0 ≤ t →
        ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
          ∀ ξ : ℝ, charFun ν ξ = Complex.exp ((t : ℂ) * ψ ξ)) := by
  sorry
