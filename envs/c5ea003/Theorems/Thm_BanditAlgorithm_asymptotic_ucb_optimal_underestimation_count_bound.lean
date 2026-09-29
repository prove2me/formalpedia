-- Prove2me | Theorems.Thm_BanditAlgorithm_asymptotic_ucb_optimal_underestimation_count_bound
-- name    : BanditAlgorithm.asymptotic_ucb_optimal_underestimation_count_bound
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-26T02:10:48.804455+00:00
-- url     : https://prove2.me/theorems/4b86f51b-53c9-4a4d-a2cd-bd35021198e8
-- title:
--   Optimal-arm UCB underestimation count
-- statement:
--   Let $\nu$ be a $1$-subgaussian bandit and let $a$ be an optimal arm. For $\varepsilon>0$, let $U_n(a,\varepsilon)$ count initialized rounds $t\le n$ at which
--   $$
--   \widehat{\mu}_a(t-1)+\sqrt{\frac{2\log f(t)}{T_a(t-1)}}\le \mu^*-\varepsilon.
--   $$
--   Then
--   $$
--   \mathbb{E}_{\nu}[U_n(a,\varepsilon)]\le \frac{5}{\varepsilon^2}.
--   $$
--   This is the first expectation estimate after Eq. (8.4), obtained from Corollary 5.5 and Exercise 8.1.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (CUP 2020), proof of Theorem 8.1, first expectation estimate after Eq. (8.4), printed p. 119 / PDF p. 128; Corollary 5.5 and Exercise 8.1.

import Definitions.Def_asymptoticUcbFailureCount

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.asymptotic_ucb_optimal_underestimation_count_bound
    {k : ℕ} {ν : BanditAlgorithm.StochasticBandit k}
    (hν : BanditAlgorithm.IsSubgaussianBandit 1 ν)
    {π : BanditAlgorithm.BanditPolicy k}
    (n : ℕ) (a i : Fin k) (ε : ℝ)
    (ha : BanditAlgorithm.banditArmMean ν a =
      BanditAlgorithm.banditOptimalMean ν)
    (hε : 0 < ε) :
    MeasureTheory.integral (BanditAlgorithm.banditMeasure ν π n)
        (fun h ↦
          (BanditAlgorithm.asymptoticUcbFailureCount ν a i ε h).1) ≤
      5 / ε ^ 2 := by sorry
