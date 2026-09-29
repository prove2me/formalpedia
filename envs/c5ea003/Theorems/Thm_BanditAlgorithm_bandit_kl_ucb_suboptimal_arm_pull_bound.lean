-- Prove2me | Theorems.Thm_BanditAlgorithm_bandit_kl_ucb_suboptimal_arm_pull_bound
-- name    : BanditAlgorithm.bandit_kl_ucb_suboptimal_arm_pull_bound
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-29T02:17:39.643718+00:00
-- url     : https://prove2.me/theorems/f670d454-2f28-469c-82b1-e3ef49a9535c
-- title:
--   Expected pull-count bound for a suboptimal arm under KL-UCB
-- statement:
--   This is the per-arm sampling bound underlying the finite-time analysis of KL-UCB.
--
--   Consider a finite Bernoulli bandit with arm means $\mu_i\in[0,1]$, optimal mean $\mu^\star$, and gaps $\Delta_i=\mu^\star-\mu_i$. Let $\pi$ satisfy the KL-UCB selection rule with exploration function $f(n)=1+n(\log n)^2$, and let $T_i(n)$ denote the number of times arm $i$ has been selected by time $n$. For any suboptimal arm $i$ and any $\varepsilon_1,\varepsilon_2>0$ satisfying $\varepsilon_1+\varepsilon_2<\Delta_i$,
--
--   $$
--   \mathbb E_{\nu,\pi}[T_i(n)]
--   \le
--   \frac{\log f(n)}
--   {d(\mu_i+\varepsilon_1,\,\mu^\star-\varepsilon_2)}
--   +\frac{1}{2\varepsilon_1^2}
--   +\frac{2}{\varepsilon_2^2},
--   $$
--
--   where $d$ is the binary relative entropy.
--
--   This bound isolates the expected occupation count of one suboptimal arm. It is the reusable probabilistic estimate that turns the canonical regret decomposition into the finite-horizon KL-UCB regret bound.
--
--   **Formalization Note** Expected pull count is represented as the integral of the finite-history pull-count function against the canonical bandit measure. The ambient bandit is explicitly identified with the Bernoulli bandit determined by the mean vector.
-- source:
--   Tor Lattimore and Csaba Szepesvári, Bandit Algorithms, Cambridge University Press, 2020, proof of Theorem 10.6, printed pp. 139–140, equation obtained by combining Lemmas 10.7 and 10.8 (printed pp. 138–139).

import Definitions.Def_bernoulliRelativeEntropy
import Definitions.Def_banditRegret

open MeasureTheory ProbabilityTheory Filter

theorem BanditAlgorithm.bandit_kl_ucb_suboptimal_arm_pull_bound
    {k : ℕ} (μvec : Fin k → ℝ)
    (hμ : ∀ i, μvec i ∈ Set.Icc (0 : ℝ) 1)
    (ν : StochasticBandit k) (hν : ν = bernoulliBandit μvec hμ)
    (π : BanditPolicy k) (hπ : IsKLUCBPolicy π) :
    ∀ n : ℕ, ∀ i : Fin k, ∀ ε₁ ε₂ : ℝ,
      0 < banditGap ν i →
      0 < ε₁ →
      0 < ε₂ →
      ε₁ + ε₂ < banditGap ν i →
      (∫ h, (armPullCount i h : ℝ) ∂banditMeasure ν π n) ≤
        Real.log (klucbExploration n) /
            bernoulliRelativeEntropy (banditArmMean ν i + ε₁)
              (banditOptimalMean ν - ε₂) +
          1 / (2 * ε₁ ^ 2) + 2 / ε₂ ^ 2 := by
  sorry
