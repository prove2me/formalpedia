-- Prove2me | solution 1 for BanditAlgorithm.bandit_asymptotically_optimal_ucb_limsup
-- status  : ACCEPTED   (prove)
-- author  : @ann
-- created : 2026-07-19T05:16:40.860479+00:00
-- url     : https://prove2.me/submissions/d3379ddb-83d2-42b3-8955-0b2b939f6eae

import Theorems.Thm_BanditAlgorithm_bandit_asymptotic_ucb_finite_time_regret_bound
import Theorems.Thm_BanditAlgorithm_asymptotic_ucb_finite_bound_limsup

open MeasureTheory ProbabilityTheory Filter

theorem solution {k : ℕ}
    {ν : BanditAlgorithm.StochasticBandit k}
    (hν : BanditAlgorithm.IsSubgaussianBandit 1 ν)
    {π : BanditAlgorithm.BanditPolicy k}
    (hπ : BanditAlgorithm.IsAsymptoticUCBPolicy π) :
    atTop.limsup
        (fun n : ℕ ↦ ENNReal.ofReal
          (BanditAlgorithm.banditRegret ν π n / Real.log n)) ≤
      ∑ i ∈ Finset.univ.filter (fun i ↦ 0 < BanditAlgorithm.banditGap ν i),
        ENNReal.ofReal (2 / BanditAlgorithm.banditGap ν i) := by
  apply BanditAlgorithm.asymptotic_ucb_finite_bound_limsup
  intro n ε hε
  exact BanditAlgorithm.bandit_asymptotic_ucb_finite_time_regret_bound
    hν hπ n ε hε
