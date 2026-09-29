-- Prove2me | Theorems.Thm_BanditAlgorithm_bayesianAdversarialRegret_eq_sum_round_integral
-- name    : BanditAlgorithm.bayesianAdversarialRegret_eq_sum_round_integral
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-01T23:45:00.943034+00:00
-- url     : https://prove2.me/theorems/9f7b6792-f65d-45dc-81c7-c54afc7eaba7
-- title:
--   Bayesian regret decomposes into one-round expectations
-- statement:
--   Let $A^*$ be the action with largest total reward and let $(A_t)_{t=1}^n$ be the actions in the Bayesian adversarial-bandit trajectory. For a prior supported on reward matrices in $[0,1]^{n\times k}$, Bayesian regret decomposes round by round:
--
--   $$
--   \operatorname{BR}_n
--   =\sum_{t=1}^n
--   \mathbb E\!\left[X_{t,A^*}-X_{t,A_t}\right].
--   $$
--
--   The expectation is taken under the terminal joint law of the reward matrix and observed trajectory.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (Cambridge UP, 2020), https://tor-lattimore.com/downloads/book/book.pdf, printed p. 469 (PDF p. 478), definition of BR_n immediately before Theorem 36.5, followed by linearity of expectation.

import Definitions.Def_ThompsonSampling

open MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem BanditAlgorithm.bayesianAdversarialRegret_eq_sum_round_integral {k n : ℕ} [NeZero k]
    (Q : Measure (Fin n → Fin k → ℝ)) [IsProbabilityMeasure Q]
    (hQ : ∀ᵐ X ∂Q, ∀ (t : Fin n) (a : Fin k), X t a ∈ Set.Icc (0 : ℝ) 1)
    (pi : BanditPolicy k) :
    bayesianAdversarialRegret Q pi =
      ∑ t, ∫ p, (p.1 t (bayesianOptimalAction p.1) - p.1 t ((p.2 t).1))
        ∂bayesianAdversarialMeasure Q pi n le_rfl := by
  sorry
