-- Prove2me | Theorems.Thm_BanditAlgorithm_bandit_asymptotic_ucb_pull_count_failure_split
-- name    : BanditAlgorithm.bandit_asymptotic_ucb_pull_count_failure_split
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-26T02:10:26.636258+00:00
-- url     : https://prove2.me/theorems/b84e2b4d-b2f8-4e37-9a7d-497923dfc5c6
-- title:
--   Eq. (8.4): split a suboptimal arm’s pulls into two UCB failures
-- statement:
--   Fix an optimal arm $a$ and a target arm $i$. Under Algorithm 6, arm $i$ is pulled at most once during initialization. At every later pull, all arms have nonzero counts and the selected arm maximizes the UCB index. Therefore, pathwise and hence in expectation,
--   $$
--   \mathbb{E}_{\nu}[T_i(n)]\le 1+\mathbb{E}_{\nu}[U_n(a,\varepsilon)]+\mathbb{E}_{\nu}[V_n(i,\varepsilon)],
--   $$
--   where $U_n$ and $V_n$ are the two failure counts in Eq. (8.4).
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (CUP 2020), proof of Theorem 8.1, Eq. (8.4), printed p. 119 / PDF p. 128. This is the formal canonical-policy bridge for that pointwise split.

import Definitions.Def_asymptoticUcbFailureCount

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.bandit_asymptotic_ucb_pull_count_failure_split {k : ℕ}
    {ν : BanditAlgorithm.StochasticBandit k}
    {π : BanditAlgorithm.BanditPolicy k}
    (hπ : BanditAlgorithm.IsAsymptoticUCBPolicy π)
    (n : ℕ) (a i : Fin k) (ε : ℝ)
    (ha : BanditAlgorithm.banditArmMean ν a =
      BanditAlgorithm.banditOptimalMean ν) :
    MeasureTheory.integral (BanditAlgorithm.banditMeasure ν π n)
        (fun h ↦ (BanditAlgorithm.armPullCount i h : ℝ)) ≤
      1 +
        MeasureTheory.integral (BanditAlgorithm.banditMeasure ν π n)
          (fun h ↦
            (BanditAlgorithm.asymptoticUcbFailureCount ν a i ε h).1) +
        MeasureTheory.integral (BanditAlgorithm.banditMeasure ν π n)
          (fun h ↦
            (BanditAlgorithm.asymptoticUcbFailureCount ν a i ε h).2) := by sorry
