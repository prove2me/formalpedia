-- Prove2me | Theorems.Thm_levy_foundations_exp_posdef_implies_cnd
-- name    : levy_foundations_exp_posdef_implies_cnd
-- status  : Open
-- author  : @WillR
-- created : 2026-11-10T09:08:16.646009+00:00
-- url     : https://prove2.me/theorems/f5c996d6-db61-4814-bd48-baf9f20c331a
-- title:
--   Infinitesimal Schoenberg theorem for positive-definite exponential powers
-- statement:
--   If for every nonnegative real t the complex function exp(t ψ) is positive definite, then the generator ψ is conditionally negative definite in the LeanLevy convention. The proof evaluates finite Gram forms with zero-sum coefficients, divides their nonnegative first-order terms by t>0, and takes t to zero. This isolates the analytic Schoenberg differentiation from the probability-measure to positive-definiteness bridge.

import Mathlib.Probability.Independence.CharacteristicFunction
import Definitions.Def_levy_foundations_isPositiveDefinite
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof

open MeasureTheory ProbabilityTheory

theorem levy_foundations_exp_posdef_implies_cnd
    (ψ : ℝ → ℂ)
    (hpd : ∀ t : ℝ, 0 ≤ t →
      LevyFoundations.isPositiveDefinite
        (fun ξ : ℝ => Complex.exp ((t : ℂ) * ψ ξ))) :
    ProbabilityTheory.IsConditionallyNegativeDefinite ψ := by
  sorry
