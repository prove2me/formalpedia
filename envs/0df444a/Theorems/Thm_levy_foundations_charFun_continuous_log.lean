-- Prove2me | Theorems.Thm_levy_foundations_charFun_continuous_log
-- name    : levy_foundations_charFun_continuous_log
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T07:58:49.157191+00:00
-- url     : https://prove2.me/theorems/1203f625-42b6-419b-8598-37c4423ba471
-- title:
--   A nowhere-zero real characteristic function has a continuous normalised logarithm
-- statement:
--   The characteristic function of a probability measure is continuous and equals one at zero. If it never vanishes, its continuous map from the simply connected real line to nonzero complex numbers lifts through the exponential covering map, with the logarithm normalised at zero.

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_levy_foundations_isInfinitelyDivisible

open MeasureTheory ProbabilityTheory

/-- A nonvanishing characteristic function on ℝ admits a continuous
complex logarithm normalised to vanish at the origin. -/
theorem levy_foundations_charFun_continuous_log
    {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hne : ∀ ξ : ℝ, charFun μ ξ ≠ 0) :
    ∃ ψ : ℝ → ℂ,
      Continuous ψ ∧ ψ 0 = 0 ∧
        ∀ ξ : ℝ, charFun μ ξ = Complex.exp (ψ ξ) := by sorry
