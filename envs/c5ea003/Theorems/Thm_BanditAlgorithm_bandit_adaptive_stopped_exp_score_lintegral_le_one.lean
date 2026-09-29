-- Prove2me | Theorems.Thm_BanditAlgorithm_bandit_adaptive_stopped_exp_score_lintegral_le_one
-- name    : BanditAlgorithm.bandit_adaptive_stopped_exp_score_lintegral_le_one
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-31T01:08:20.646613+00:00
-- url     : https://prove2.me/theorems/3a6d8240-8f4a-4068-8024-43ef6a7dc52e
-- title:
--   Adaptive stopped exponential-score supermartingale bound
-- statement:
--   Consider any adaptive policy interacting with a stochastic bandit whose centered arm rewards are $1$-subgaussian. Fix an arm $i$, a truncation rank $u$, and a real parameter $t$. Let $S_{i,u}(n)$ be the centered sum of rewards from the first $u$ pulls of arm $i$, stopped at horizon $n$, and let $T_i(n)$ be its pull count. Then
--
--   $$
--   \mathbb E\!\left[
--   \exp\!\left(
--   tS_{i,u}(n)-\frac{t^2}{2}\min\{T_i(n),u\}
--   \right)
--   \right]\le1.
--   $$
--
--   This is the exact exponential-supermartingale estimate for adaptively selected rewards. It is reusable in Chernoff bounds and Laplace-mixture arguments without losing polynomial factors.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (CUP 2020), canonical reward-stack model in Section 4.6, printed p. 65 / PDF p. 74, and bounded optional stopping in Exercise 4.4, printed p. 69 / PDF p. 78; the same stopped exponential process underlies Eqs. (7.6)–(7.10), printed pp. 106–108 / PDF pp. 115–117.

import Definitions.Def_ucbStoppedCenteredSum

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

/-- The stopped exponential score has expectation at most one. -/
theorem bandit_adaptive_stopped_exp_score_lintegral_le_one
    {k n : ℕ} (ν : StochasticBandit k)
    (hν : IsSubgaussianBandit 1 ν) {π : BanditPolicy k}
    (i : Fin k) (u : ℕ) (t : ℝ) :
    (∫⁻ h : BanditHistory k n,
        ENNReal.ofReal
          (Real.exp
            (t * armStoppedCenteredSum ν i u n h -
              t ^ 2 / 2 *
                ((min (armPullCount i h) u : ℕ) : ℝ)))
        ∂banditMeasure ν π n) ≤ 1 := by
  sorry

end BanditAlgorithm
