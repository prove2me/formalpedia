-- Prove2me | Theorems.Thm_BanditAlgorithm_ucb_suboptimal_arm_expected_pull_count
-- name    : BanditAlgorithm.ucb_suboptimal_arm_expected_pull_count
-- status  : Proved
-- author  : @Hartmann_Psi
-- created : 2026-07-18T15:45:55.159654+00:00
-- url     : https://prove2.me/theorems/f4d2dc54-3ac7-4751-965f-468dcc33ea53
-- title:
--   UCB suboptimal-arm pull-count bound
-- statement:
--   For UCB with confidence level $\delta=1/n^2$ on a finite 1-subgaussian stochastic bandit, every suboptimal arm $i$ with gap $\Delta_i>0$ is pulled in expectation at most $3+16\log(n)/\Delta_i^2$ times by horizon $n$. The statement isolates the core per-arm estimate in the proof of the UCB regret theorem.
-- source:
--   Lattimore--Szepesvari, Bandit Algorithms (2020), proof of Theorem 7.1, Eqs. (7.4)--(7.10), especially the concluding pull-count display, printed pp. 105--108 (online PDF pp. 113--116), https://tor-lattimore.com/downloads/book/book.pdf

import Definitions.Def_banditRegret
import Definitions.Def_ucbPolicy

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

theorem ucb_suboptimal_arm_expected_pull_count
    {k : ℕ} (hk : 0 < k) {ν : StochasticBandit k}
    (hν : IsSubgaussianBandit 1 ν) {n : ℕ} (hn : 0 < n)
    {π : BanditPolicy k} (hπ : IsUCBPolicy (1 / (n : ℝ) ^ 2) π)
    (i : Fin k) (hi : 0 < banditGap ν i) :
    ∫ h, (armPullCount i h : ℝ) ∂(banditMeasure ν π n) ≤
      3 + 16 * Real.log n / (banditGap ν i) ^ 2 := by
  sorry

end BanditAlgorithm
