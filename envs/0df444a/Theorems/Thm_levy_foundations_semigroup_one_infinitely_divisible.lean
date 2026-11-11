-- Prove2me | Theorems.Thm_levy_foundations_semigroup_one_infinitely_divisible
-- name    : levy_foundations_semigroup_one_infinitely_divisible
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T10:06:22.269938+00:00
-- url     : https://prove2.me/theorems/75a9690e-dd1c-44f8-91f0-133baa86c18d
-- title:
--   Time-one characteristic law of a continuous characteristic semigroup is infinitely divisible
-- statement:
--   Choose the time-one law μ. For each n>0 choose a law ν with characteristic function exp(ψ/n). The characteristic function of ν's n-fold convolution is exp ψ, so uniqueness of characteristic functions identifies μ with that convolution power. This proves infinite divisibility of μ without any Lévy–Khintchine representation theorem.

import Mathlib
import Definitions.Def_levy_foundations_isInfinitelyDivisible
import Definitions.Def_levy_foundations_iteratedConv
import Definitions.Def_levy_foundations_iteratedConvolutionPower

open MeasureTheory ProbabilityTheory Complex

/-- Every family of characteristic functions of the form exp(t ψ) determines an infinitely divisible time-one law. -/
theorem levy_foundations_semigroup_one_infinitely_divisible
    (ψ : ℝ → ℂ)
    (hsemigroup : ∀ t : ℝ, 0 ≤ t →
      ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧
        ∀ ξ : ℝ, charFun ν ξ = Complex.exp ((t : ℂ) * ψ ξ)) :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧
      LevyFoundations.isInfinitelyDivisible μ ∧
      ∀ ξ : ℝ, charFun μ ξ = Complex.exp (ψ ξ) := by sorry
