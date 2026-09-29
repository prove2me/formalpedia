-- Prove2me | Theorems.Thm_BanditAlgorithm_bandit_moss_minimax_regret_bound
-- name    : BanditAlgorithm.bandit_moss_minimax_regret_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-19T02:58:37.335639+00:00
-- url     : https://prove2.me/theorems/a0aaf350-a077-4a0a-8c56-f784b4876252
-- statement:
--   (MOSS minimax optimality) Consider any 1-subgaussian $k$-armed bandit and any policy that is an instance of MOSS at horizon $n$ (Algorithm 7: play each arm once, then
--
--   $$A_t = \arg\max_i\ \hat\mu_i(t-1) + \sqrt{\frac{4}{T_i(t-1)}\log^+\!\left(\frac{n}{k\,T_i(t-1)}\right)}$$
--
--   with $\log^+(x) = \log\max\{1, x\}$). If $k \le n$ (implicit in the book: the algorithm plays each arm once before using the index) then
--
--   $$R_n \le 39\sqrt{kn} + \sum_{i=1}^k \Delta_i.$$
-- source:
--   L&S Theorem 9.1, p.124

import Definitions.Def_banditRegret
import Definitions.Def_mossPolicy


open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.bandit_moss_minimax_regret_bound {k : ℕ}
    {ν : StochasticBandit k} (hν : IsSubgaussianBandit 1 ν)
    {n : ℕ} {π : BanditPolicy k} (hπ : IsMOSSPolicy n π) (hkn : k ≤ n) :
    banditRegret ν π n ≤
      39 * Real.sqrt ((k : ℝ) * n) + ∑ i, banditGap ν i := by
  sorry
