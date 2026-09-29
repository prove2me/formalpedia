-- Prove2me | Theorems.Thm_BanditAlgorithm_bernoulliBandit_isSubgaussian_half
-- name    : BanditAlgorithm.bernoulliBandit_isSubgaussian_half
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-29T04:32:51.026403+00:00
-- url     : https://prove2.me/theorems/37edcd8d-a0ad-440d-bcaa-8a8d016d2a9c
-- title:
--   Bernoulli bandits are sharply subgaussian
-- statement:
--   Every Bernoulli bandit is sharply subgaussian. More precisely, if every arm mean satisfies $\mu_i\in[0,1]$, then for each arm the centered reward $X-\mu_i$ has subgaussian variance proxy $1/4$:
--
--   $$
--   \mathbb E\!\left[\exp\!\left(\lambda(X-\mu_i)\right)\right]
--   \le
--   \exp\!\left(\frac{\lambda^2}{8}\right)
--   \qquad(\lambda\in\mathbb R).
--   $$
--
--   Equivalently, the Bernoulli bandit is $1/2$-subgaussian in the convention where a $\sigma$-subgaussian variable has moment-generating function at most $\exp(\sigma^2\lambda^2/2)$.
--
--   This supplies the sharp Hoeffding constant used in the finite-time KL-UCB concentration estimates.
--
--   Formalization Note: The Bernoulli reward law is represented as the two-point measure $\mu_i\delta_1+(1-\mu_i)\delta_0$. The proof shows that this law is supported on $[0,1]$ and applies Mathlib's bounded-variable form of Hoeffding's lemma.
-- source:
--   Hoeffding's lemma; applied to the Bernoulli bandit model of Lattimore and Szepesvári, Bandit Algorithms (2020), Chapter 10, printed pp. 133–134.

import Definitions.Def_bernoulliRelativeEntropy

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.bernoulliBandit_isSubgaussian_half
    {k : ℕ} (μvec : Fin k → ℝ)
    (hμ : ∀ i, μvec i ∈ Set.Icc (0 : ℝ) 1) :
    BanditAlgorithm.IsSubgaussianBandit (1 / 2)
      (BanditAlgorithm.bernoulliBandit μvec hμ) := by
  sorry
