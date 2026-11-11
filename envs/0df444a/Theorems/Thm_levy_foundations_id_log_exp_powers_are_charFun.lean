-- Prove2me | Theorems.Thm_levy_foundations_id_log_exp_powers_are_charFun
-- name    : levy_foundations_id_log_exp_powers_are_charFun
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T07:58:51.565938+00:00
-- url     : https://prove2.me/theorems/35a2736d-286a-47a5-abe7-f44b882bb99f
-- title:
--   Convolution roots generate every nonnegative real exponential power of the logarithm
-- statement:
--   For an infinitely divisible law with a specified continuous normalised characteristic exponent ψ, all nonnegative real powers exp(t ψ) are probability characteristic functions. Use uniqueness of normalised convolution roots for rational t and the Lévy continuity theorem to pass to arbitrary nonnegative real times.

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_levy_foundations_isInfinitelyDivisible

open MeasureTheory ProbabilityTheory

/-- Positive real exponential powers of the normalised logarithm of an
infinitely divisible characteristic function are again characteristic functions. -/
theorem levy_foundations_id_log_exp_powers_are_charFun
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : LevyFoundations.isInfinitelyDivisible μ)
    (ψ : ℝ → ℂ) (hcont : Continuous ψ) (hzero : ψ 0 = 0)
    (hchar : ∀ ξ : ℝ, charFun μ ξ = Complex.exp (ψ ξ)) :
    ∀ t : ℝ, 0 ≤ t →
      ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
        ∀ ξ : ℝ, charFun ν ξ = Complex.exp ((t : ℂ) * ψ ξ) := by sorry
