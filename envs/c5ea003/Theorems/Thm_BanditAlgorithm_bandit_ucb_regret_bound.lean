-- Prove2me | Theorems.Thm_BanditAlgorithm_bandit_ucb_regret_bound
-- name    : BanditAlgorithm.bandit_ucb_regret_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-17T20:12:00.366272+00:00
-- url     : https://prove2.me/theorems/29a6d07e-b649-4dd5-b69f-0f12da8b0a98
-- statement:
--   (UCB regret bound, GOAL) Consider UCB (L&S Algorithm 3) on a stochastic $k$-armed 1-subgaussian bandit: play each arm once, then play
--
--   $$A_t = \arg\max_i \left( \hat\mu_i(t-1) + \sqrt{\frac{2\log(1/\delta)}{T_i(t-1)}} \right).$$
--
--   For any horizon $n$, if $\delta = 1/n^2$ then
--
--   $$R_n \le 3\sum_{i=1}^k \Delta_i + \sum_{i : \Delta_i > 0} \frac{16\log n}{\Delta_i}.$$
-- source:
--   L&S Theorem 7.1, p.105

import Definitions.Def_banditRegret
import Definitions.Def_ucbPolicy


open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.bandit_ucb_regret_bound {k : ℕ} (hk : 0 < k) {ν : StochasticBandit k}
    (hν : IsSubgaussianBandit 1 ν) {n : ℕ} (hn : 0 < n)
    {π : BanditPolicy k} (hπ : IsUCBPolicy (1 / (n : ℝ) ^ 2) π) :
    banditRegret ν π n ≤
      3 * ∑ i, banditGap ν i +
        ∑ i ∈ Finset.univ.filter (fun i ↦ 0 < banditGap ν i),
          16 * Real.log n / banditGap ν i := by
  sorry
